{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen
-}

module Importer.Preprocess
    (
     preprocessHsModule,
     runTest
    )where

import Maybe
import List
import Control.Monad.Writer
import Control.Monad.Reader
import Language.Haskell.Exts

import Data.Generics.Biplate
import Data.Generics.Str
import Data.Generics.Env
import Data.Generics
import Data.Graph
import Data.Tree

import Importer.Utilities.Misc -- (concatMapM, assert)
import Importer.Utilities.Hsk
import Importer.Utilities.Gensym

import Importer.Test.Generators

import qualified Importer.Msg as Msg

import Importer.Adapt.Raw (used_const_names, used_thy_names)

import Test.QuickCheck
import qualified Test.QuickCheck.Monadic as QC (assert)
import Test.QuickCheck.Monadic hiding (assert)


import Data.Map (Map)
import qualified Data.Map as Map hiding (Map)
import Data.Set (Set)
import qualified Data.Set as Set hiding (Set)
        
{-|
  This function preprocesses the given Haskell module to make things easier for the
  conversion.
-}
preprocessHsModule :: HsModule -> HsModule
preprocessHsModule (HsModule loc modul exports imports topdecls)
    = HsModule loc modul exports imports topdecls4
      where topdecls1    =  map (whereToLet .  deguardify) topdecls
            ((topdecls2 ,topdecls2'), gensymcount) 
                         = runGensym 0 (evalDelocaliser Set.empty (delocaliseAll topdecls1))
            topdecls3    = topdecls2 ++ topdecls2'
            topdecls4    = evalGensym gensymcount (mapM normalizeNames_HsDecl topdecls3)


{-|
  /Delocalization of HsDecls/

  Since Isabelle/HOL does not really support local function
  declarations, we convert the Haskell AST to an equivalent AST
  where every local function declaration is made a global
  declaration. This includes where as well as let expressions.

  Additionally, all variables defined in a where clause
  are converted to an equivalent let expression.


  We keep track of the names that are directly bound by a declaration,
  as functions must not close over them. See below for an explanation.
 -}
newtype DelocaliserM a = DelocaliserM (ReaderT HskNames (WriterT [HsDecl] GensymM) a )
    deriving (Monad, Functor, MonadFix, MonadReader HskNames, MonadWriter [HsDecl])



addTopDecls :: [HsDecl] -> DelocaliserM ()
addTopDecls = tell

addTopDecl :: HsDecl -> DelocaliserM ()
addTopDecl = addTopDecls . (:[])

liftGensym :: GensymM a -> DelocaliserM a
liftGensym = DelocaliserM . lift . lift


{-|
  This function executes the given delocaliser monad starting with an
  empty list of bound variables.
-}
evalDelocaliser :: HskNames -> DelocaliserM a -> GensymM (a,[HsDecl]) 
evalDelocaliser state (DelocaliserM sm) =
    let wm = runReaderT sm state in
    runWriterT wm

delocaliseAll :: GenericM DelocaliserM
delocaliseAll = everywhereEnv boundNamesEnv delocalise

delocalise :: GenericM DelocaliserM
delocalise = mkM delocaliseLet
             `extM` delocaliseClsDecl
                   

delocaliseClsDecl :: HsClassDecl -> DelocaliserM HsClassDecl
delocaliseClsDecl clsDecl@(HsClsDecl decl) = 
    do addTopDecl decl
       return clsDecl

{-|
  This data structure is supposed to comprise the definition
  of a function and possibly its type signature declaration.
-}
data FunDef = FunDef { funBind :: HsDecl, funSig :: Maybe HsDecl, funFreeNames :: HskNames}

funName :: FunDef -> HsName
funName FunDef{funBind = HsFunBind(HsMatch _ name _ _ _  : _)} = name

{-|
  This function renames the function name of the given function definition.
-}
renameFunDef :: [Renaming] -> FunDef -> FunDef
renameFunDef ren def@(FunDef{ funBind = bind, funSig = sig})
    = let bind' = renameHsDecl ren bind
          sig' = liftM (renameHsDecl ren) sig
      in def{ funBind = bind', funSig = sig'}

{-|
  This function partitions bindings into a pair (signature declarations, other bindings)
-}
groupFunDefs :: [HsDecl] -> [FunDef]
groupFunDefs decls = 
    let (funBinds,funSigs) = partition isFunBind decls
        funSigs' = concatMap flattenHsTypeSig funSigs
        sigMap = Map.fromList $ map sigName funSigs'
        mkFunDef bind@(HsFunBind (HsMatch _ name _ _ _  : _))
            = FunDef bind (Map.lookup name sigMap) (extractFreeVarNs bind)
    in map mkFunDef funBinds
    where isFunBind (HsFunBind _) = True
          isFunBind _ = False
          sigName decl@(HsTypeSig _ [name] _) = (name,decl)


funDefComponents :: [FunDef] -> [[FunDef]]
funDefComponents funDefs =
   let names = Set.fromList $ map (UnQual . funName) funDefs
       graphConstr = map graphComp funDefs
       graphComp funDef = (funDef,UnQual . funName $ funDef, Set.toList . Set.intersection names . funFreeNames $ funDef)
       (graph, extr,_) = graphFromEdges graphConstr
       forest = components graph
    in map (map ((\(n,_,_) -> n) . extr) . flatten) forest

{-|
  This function adds an additional argument to the given match that contains the
  environment of a closure.
-}
addEnvArgToMatch :: HsName  -- ^the name of the environment variable
          -> [HsName] -- ^the names of the variables in the environment
          -> HsMatch  -- ^the match that should be enriched by an environment argument
          -> HsMatch  -- ^the resulting match
addEnvArgToMatch envName closureNames match@(HsMatch loc name pats rhs binds)
    = let boundNames = map uname (extractBindingNs pats)
          toPat name = if name `elem` boundNames
                       then HsPWildCard
                       else HsPVar name
          allBound = all (`elem` boundNames) closureNames
          tuple = case closureNames of
                    [closureName] -> toPat closureName
                    _ -> HsPTuple (map toPat closureNames)
          passing = (UnQual envName) `Set.member` extractFreeVarNs match
          envArg = if passing then if allBound
                                   then HsPVar envName
                                   else HsPAsPat envName tuple
                   else if allBound
                        then HsPWildCard
                        else tuple
      in (HsMatch loc name (envArg:pats) rhs binds)                       
    where uname (Qual _ name) = name
          uname (UnQual name) = name

{-|
  This function adds an additional argument to the given function binding that contains the
  environment of a closure.
-}
addEnvArgToDecl :: HsName  -- ^the name of the environment variable
                -> [HsName] -- ^the names of the variables in the environment
                -> HsDecl  -- ^the match that should be enriched by an environment argument
                -> HsDecl  -- ^the resulting match
addEnvArgToDecl envName closureNames (HsFunBind matches)
    = let matches' = map (addEnvArgToMatch envName closureNames) matches
      in HsFunBind matches'

addPatBindsToMatch :: [HsDecl] -> HsMatch -> HsMatch
addPatBindsToMatch patBinds match@(HsMatch loc name pats (HsUnGuardedRhs exp) binds)
    = let neededPatBinds = filter patBindNeeded patBinds
          shadowedPatBinds = map shadowPatBind neededPatBinds
          rhs' = HsUnGuardedRhs (HsLet (HsBDecls shadowedPatBinds) exp)
      in if null neededPatBinds
         then match
         else HsMatch loc name pats rhs' binds
    where patBindNeeded patBind
              = not (Set.null ( Set.fromList (extractBindingNs patBind)
                                `Set.intersection` extractFreeVarNs exp ))
          boundNames = Set.fromList (extractBindingNs pats)
          shadowPatBind :: HsDecl -> HsDecl
          shadowPatBind (HsPatBind loc pat rhs binds) 
              = (HsPatBind loc (shadow pat) rhs binds) 
          shadowPVar :: HsPat -> HsPat
          shadowPVar var@(HsPVar name) 
              | UnQual name `Set.member` boundNames = HsPWildCard
              | otherwise = var
          shadowPVar oth = oth 
                            
          shadow :: GenericT
          shadow = everywhere (mkT shadowPVar)

addPatBindsToDecl :: [HsDecl] -> HsDecl -> HsDecl
addPatBindsToDecl patBinds (HsFunBind matches) = 
    let matches' = map (addPatBindsToMatch patBinds) matches
    in HsFunBind matches'
addPatBindsToDecl _ decl@(HsTypeSig _ _ _) = decl
addPatBindsToDecl patBinds decl = error $ "Function binding expected but found:\n" ++ prettyPrint decl
     

delocaliseFunDefs :: [FunDef] -> DelocaliserM [HsDecl]
delocaliseFunDefs funDefs = 
    do envNames <- boundNames
       let freeNames = Set.unions (map funFreeNames funDefs)
           closureNames = freeNames `Set.intersection` envNames
           closureNameList = Set.toList closureNames
           closureUNameList = map uname closureNameList
           funNames = map (UnQual . funName) funDefs
       renamings <- liftGensym $ freshIdentifiers funNames
       envUName <- liftGensym $ genHsName (HsIdent "env")
       let envName = UnQual envUName
           addEnv (orig,ren) = (orig, HsApp (HsVar ren) (HsVar envName))
           envTuple = case closureNameList of
                        [closureName] -> HsVar closureName
                        _ -> HsTuple (map HsVar closureNameList)
           addEnvTuple (orig,ren) = HsPatBind
                                    (SrcLoc "" 0 0)
                                    (HsPVar $ uname orig)
                                    (HsUnGuardedRhs (HsApp (HsVar ren) envTuple))
                                    (HsBDecls [])
           withoutEnvTuple (orig,ren) = HsPatBind
                                        (SrcLoc "" 0 0)
                                        (HsPVar $ uname orig)
                                        (HsUnGuardedRhs (HsVar ren))
                                        (HsBDecls [])
           subst = Map.fromList $ map addEnv renamings
           funs = map funBind funDefs
           funsRenamed = map (renameHsDecl renamings) funs
           funsNoEnvPassing = map (renameFreeVars renamings) funsRenamed
           funsEnvPassing = applySubst subst funsRenamed
           funsDeloc = if null closureNameList 
                       then funsNoEnvPassing
                       else map (addEnvArgToDecl envUName closureUNameList) funsEnvPassing
           newPatBinds = if null closureNameList
                         then map withoutEnvTuple renamings
                         else map addEnvTuple renamings
       addTopDecls funsDeloc
       return newPatBinds
    where uname (Qual _ name) = name
          uname (UnQual name) = name

delocaliseLet :: HsExp -> DelocaliserM HsExp
delocaliseLet (HsLet binds exp) = 
    let (HsBDecls patBinds, HsBDecls  funBinds) = splitPatBinds binds
        funBinds' = map (addPatBindsToDecl patBinds) funBinds
        funDefs = funDefComponents (groupFunDefs funBinds') 
    in do newPatBinds <- mapM delocaliseFunDefs funDefs
          return $ HsLet (HsBDecls $ (concat newPatBinds) ++ patBinds) exp
delocaliseLet exp = return exp 



{-|
  This predicates checks whether the argument is a pattern binding.
-}
isHsPatBind :: HsDecl -> Bool
isHsPatBind (HsPatBind _ _ _ _) = True
isHsPatBind _ = False


{-|
  This function partitions bindings into a pair (pattern bindings, other bindings)
-}
splitPatBinds :: HsBinds -> (HsBinds, HsBinds)
splitPatBinds (HsBDecls decls) 
    = let (patDecls, typeSigs, otherDecls)    = unzip3 (map split decls)
          (patDecls', typeSigs', otherDecls') = (catMaybes patDecls, 
                                                 concatMap flattenHsTypeSig (catMaybes typeSigs), 
                                                 catMaybes otherDecls)
          (patTypeSigs, otherTypeSigs) 
              = partition (let patNs = concatMap namesFromHsDecl patDecls'
                           in \sig -> head (namesFromHsDecl sig) `elem` patNs)
                          typeSigs'
      in (HsBDecls (patTypeSigs ++ patDecls'), HsBDecls (otherTypeSigs ++ otherDecls'))

    where split decl@(HsPatBind loc pat rhs binds)
              = (Just decl, Nothing, Nothing)
          split decl@(HsTypeSig loc names typ)
              = (Nothing, Just decl, Nothing)
          split decl = (Nothing, Nothing, Just decl)
splitPatBinds junk = error ("splitPatBinds: Fall through. " ++ show junk)

flattenHsTypeSig :: HsDecl -> [HsDecl]
flattenHsTypeSig (HsTypeSig loc names typ)
    = map (\n -> HsTypeSig loc [n] typ) names

---- Normalization of names.
--
-- Function definitions are restricted in Isar/HOL such that names of
-- constants must not be used as a bound variable name in those definitions.
-- 
-- We simply rename all those identifiers.
--

normalizeNames_HsDecl :: HsDecl -> GensymM HsDecl

should_be_renamed :: HsQName -> Bool
should_be_renamed qn = case qn of
                         Qual _ n -> consider n
                         UnQual n -> consider n
    where consider (HsIdent s)  = s `elem` used_const_names
          consider (HsSymbol s) = s `elem` used_const_names

normalizeNames_HsDecl (HsFunBind matchs)
    = do matchs' <- mapM normalizePatterns_HsMatch matchs
         return (HsFunBind matchs')
    where
      normalizePatterns_HsMatch (HsMatch loc name pats (HsUnGuardedRhs body) where_binds)
          = let bound_var_ns = bindingsFromPats pats
                clashes      = filter should_be_renamed bound_var_ns
            in do renames <- freshIdentifiers clashes
                  pats'   <- return (map (renameHsPat renames) pats)
                  body'   <- return (renameFreeVars renames body)
                  binds'  <- normalizeNames_HsBinds where_binds
                  return (HsMatch loc name pats' (HsUnGuardedRhs body') binds') 

      normalizeNames_HsBinds (HsBDecls decls)
          = do decls' <- mapM normalizeNames_HsDecl decls
               return (HsBDecls decls')

normalizeNames_HsDecl decl 
    -- There aren't any subdecls in decl anymore after delocalization.
    = return decl

-- normalizeModuleName :: String -> String


whereToLet :: HsDecl -> HsDecl
whereToLet =
    everywhere $ mkT 
    whereToLetDecl `extT`
    whereToLetMatch `extT`
    whereToLetAlt

isEmptyBinds :: HsBinds -> Bool
isEmptyBinds (HsBDecls []) = True
isEmptyBinds (HsIPBinds []) = True
isEmptyBinds _ = False

whereToLetDecl :: HsDecl -> HsDecl
whereToLetDecl (HsPatBind loc pat rhs binds)
    | not $ isEmptyBinds binds = 
        case rhs of
          HsGuardedRhss _ -> assert False undefined
          HsUnGuardedRhs exp -> 
              let rhs' = HsUnGuardedRhs $ HsLet binds exp
              in HsPatBind loc pat rhs' (HsBDecls [])
whereToLetDecl decl = decl

whereToLetMatch :: HsMatch -> HsMatch
whereToLetMatch match@(HsMatch loc name pat rhs binds)
    | isEmptyBinds binds = match
    | otherwise =
        case rhs of
          HsGuardedRhss _ -> assert False undefined
          HsUnGuardedRhs exp -> 
              let rhs' = HsUnGuardedRhs $ HsLet binds exp
              in HsMatch loc name pat rhs' (HsBDecls [])

whereToLetAlt :: HsAlt -> HsAlt
whereToLetAlt orig@(HsAlt loc pat alt binds) 
    | isEmptyBinds binds = orig
    | otherwise =
        case alt of
          HsGuardedAlts _ -> assert False undefined
          HsUnGuardedAlt exp -> 
              let alt' = HsUnGuardedAlt $ HsLet binds exp
              in HsAlt loc pat alt' (HsBDecls [])


---- Deguardification

deguardify :: HsDecl -> HsDecl
deguardify =
    everywhere $ mkT
    deguardifyRhs `extT` deguardifyAlts

deguardifyRhs :: HsRhs -> HsRhs
deguardifyRhs rhs@(HsUnGuardedRhs _) = rhs
deguardifyRhs (HsGuardedRhss guards) = HsUnGuardedRhs $ deguardifyGuards guards

deguardifyAlts :: HsGuardedAlts -> HsGuardedAlts
deguardifyAlts alt@(HsUnGuardedAlt _) = alt
deguardifyAlts (HsGuardedAlts guards) = 
    HsUnGuardedAlt .
    deguardifyGuards .
    (map (\(HsGuardedAlt l ss e) -> HsGuardedRhs l ss e)) $
    guards
deguardifyGuards :: [HsGuardedRhs] -> HsExp
deguardifyGuards guards
    = let (guards', otherwise_expr) = findOtherwiseExpr guards
      in foldr deguardify otherwise_expr guards'
    where 
      deguardify x@(HsGuardedRhs loc stmts clause) body
          = HsIf (makeGuardExpr stmts) clause body
   
      makeGuardExpr stmts = if null stmts
                            then (HsVar (UnQual (HsIdent "True")))
                            else foldl1 andify (map expify stmts)
          where expify (HsQualifier exp) = exp
                andify e1 e2 = HsInfixApp e1 (HsQVarOp (Qual (Module "Prelude") (HsSymbol "&&"))) e2

      findOtherwiseExpr guards
          = let otherwise_stmt = HsQualifier (HsVar (UnQual (HsIdent "otherwise")))
                true_stmt      = HsQualifier (HsVar (UnQual (HsIdent "True")))
                bottom         = HsVar (Qual (Module "Prelude") (HsSymbol "_|_"))
            in case break (\(HsGuardedRhs _ stmts _) -> stmts `elem` [[otherwise_stmt], [true_stmt]])
                          guards of
                 (guards', (HsGuardedRhs _ _ last_expr):_) -> (guards', last_expr)
                 (guards', [])                             ->
                     let HsGuardedRhs srcLoc _ _ = last guards'
                     in error $ srcloc2string srcLoc ++ ": "
                            ++ "Guards can be translated only if they are closed"
                            ++ " with a trivial guard, i.e., True or otherwise."

------------------------------------------------------------
------------------------------------------------------------
--------------------------- Tests --------------------------
------------------------------------------------------------
------------------------------------------------------------

runTest = quickCheck prop_NoWhereDecls

onlyPatBinds (HsBDecls binds) = all isPat binds
    where isPat HsPatBind{} = True
          isPat HsTypeSig{} = True
          isPat _ = False
noPatBinds (HsBDecls binds) = all noPat binds
    where noPat HsPatBind{} = False
          noPat _ = True


prop_splitPatBindsCorrect binds = let (pat,nonPat) = splitPatBinds binds
                                  in onlyPatBinds pat && noPatBinds nonPat

noLocalDecl :: HsModule -> Bool
noLocalDecl m = True


hasWhereDecls :: Data a => a -> Bool
hasWhereDecls node = everything (||) (mkQ False fromDecl `extQ` fromMatch) node
    where fromDecl (HsPatBind _ _ _ binds) = isNonEmpty binds
          fromDecl _ = False
          fromMatch (HsMatch _ _ _ _ binds) = isNonEmpty binds
          isNonEmpty (HsBDecls binds) = not (null binds)
          isNonEmpty (HsIPBinds binds) = not (null binds)

prop_NoWhereDecls mod = not $ hasWhereDecls $ preprocessHsModule mod

prop_NoLocalDecl mod = noLocalDecl $ preprocessHsModule mod

checkDelocM :: PropertyM DelocaliserM a -> Property
checkDelocM deloc = forAll arbitrary $ \ (NonNegative gsState, delocState) ->
              monadic (fst . evalGensym gsState . evalDelocaliser delocState) deloc


                          

{-|
  'flattenHsTypeSig' really flattens the type declaration.
-}
prop_flattenHsTypeSig_isFlat = forAll typeSigDecl $ \ decl ->
                        all isFlat $ flattenHsTypeSig decl
    where isFlat (HsTypeSig _src names _type) = length names `elem` [0,1]
          isFlat _ = False

prop_flattenHsTypeSig_isEquiv = forAll typeSigDecl $ \ decl ->
                               let flat = flattenHsTypeSig decl in
                               flat `equiv` [decl]
    where d `subOf` e = (`all` d) $ \ (HsTypeSig _src names typ) -> 
                        (`all` names) $ \ name ->
                        (`any` e) $ \ (HsTypeSig _src' names' typ') ->
                        (`any` names) $ \ name' -> name == name' && typ == typ'
          d `equiv` e = d `subOf` e && e `subOf` d