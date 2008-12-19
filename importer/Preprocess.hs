{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-| Author:     Tobias C. Rittweiler, TU Muenchen

-}

module Importer.Preprocess (preprocessModule) where

import Maybe
import List
import Control.Monad.Writer
import Control.Monad.Reader
import Language.Haskell.Exts as Hs

import Data.Generics.Biplate
import Data.Generics.Str
import Importer.Utilities.Env
import Data.Generics
import Data.Graph
import Data.Tree

import Importer.Utilities.Misc -- (concatMapM, assert)
import Importer.Utilities.Hsk
import Importer.Utilities.Gensym

-- import Importer.Test.Generators

import qualified Importer.Msg as Msg

import Importer.Adapt.Raw (used_const_names, used_thy_names)

-- import Test.QuickCheck
-- import qualified Test.QuickCheck.Monadic as QC (assert)
-- import Test.QuickCheck.Monadic hiding (assert)

import Data.Map (Map)
import qualified Data.Map as Map hiding (Map)
import Data.Set (Set)
import qualified Data.Set as Set hiding (Set)
        
{-|
  This function preprocesses the given Haskell module to make things easier for the
  conversion.
-}
preprocessModule :: Hs.Module -> Hs.Module
preprocessModule (Hs.Module loc modul pragmas warning exports imports topdecls)
    = Hs.Module loc modul pragmas warning exports imports topdecls4
      where topdecls1    =  map (whereToLet .  deguardify) topdecls
            ((topdecls2 ,topdecls2'), gensymcount) 
                         = runGensym 0 (evalDelocaliser Set.empty (delocaliseAll topdecls1))
            topdecls3    = topdecls2 ++ topdecls2'
            topdecls4    = evalGensym gensymcount (mapM normalizeNames_Decl topdecls3)


{-|
  /Delocalization of Hs.Decls/

  Since Isabelle/HOL does not really support local function
  declarations, we convert the Haskell AST to an equivalent AST
  where every local function declaration is made a global
  declaration. This includes where as well as let expressions.

  Additionally, all variables defined in a where clause
  are converted to an equivalent let expression.


  We keep track of the names that are directly bound by a declaration,
  as functions must not close over them. See below for an explanation.
 -}
newtype DelocaliserM a = DelocaliserM (ReaderT HskNames (WriterT [Hs.Decl] GensymM) a )
    deriving (Monad, Functor, MonadFix, MonadReader HskNames, MonadWriter [Hs.Decl])



addTopDecls :: [Hs.Decl] -> DelocaliserM ()
addTopDecls = tell

addTopDecl :: Hs.Decl -> DelocaliserM ()
addTopDecl = addTopDecls . (:[])

liftGensym :: GensymM a -> DelocaliserM a
liftGensym = DelocaliserM . lift . lift


{-|
  This function executes the given delocaliser monad starting with an
  empty list of bound variables.
-}
evalDelocaliser :: HskNames -> DelocaliserM a -> GensymM (a,[Hs.Decl]) 
evalDelocaliser state (DelocaliserM sm) =
    let wm = runReaderT sm state in
    runWriterT wm

delocaliseAll :: GenericM DelocaliserM
delocaliseAll = everywhereEnv boundNamesEnv delocalise

delocalise :: GenericM DelocaliserM
delocalise = mkM delocaliseLet
             `extM` delocaliseClsDecl
                   

delocaliseClsDecl :: Hs.ClassDecl -> DelocaliserM Hs.ClassDecl
delocaliseClsDecl clsDecl@(Hs.ClsDecl decl) = 
    do addTopDecl decl
       return clsDecl

{-|
  This data structure is supposed to comprise the definition
  of a function and possibly its type signature declaration.
-}
data FunDef = FunDef { funBind :: Hs.Decl, funSig :: Maybe Hs.Decl, funFreeNames :: HskNames}

funName :: FunDef -> Hs.Name
funName FunDef{funBind = Hs.FunBind(Hs.Match _ name _ _ _  : _)} = name

{-|
  This function renames the function name of the given function definition.
-}
renameFunDef :: [Renaming] -> FunDef -> FunDef
renameFunDef ren def@(FunDef{ funBind = bind, funSig = sig})
    = let bind' = renameDecl ren bind
          sig' = liftM (renameDecl ren) sig
      in def{ funBind = bind', funSig = sig'}

{-|
  This function partitions bindings into a pair (signature declarations, other bindings)
-}
groupFunDefs :: [Hs.Decl] -> [FunDef]
groupFunDefs decls = 
    let (funBinds,funSigs) = partition isFunBind decls
        funSigs' = concatMap flattenTypeSig funSigs
        sigMap = Map.fromList $ map sigName funSigs'
        mkFunDef bind@(Hs.FunBind (Hs.Match _ name _ _ _  : _))
            = FunDef bind (Map.lookup name sigMap) (extractFreeVarNs bind)
    in map mkFunDef funBinds
    where isFunBind (Hs.FunBind _) = True
          isFunBind _ = False
          sigName decl@(Hs.TypeSig _ [name] _) = (name,decl)


funDefComponents :: [FunDef] -> [[FunDef]]
funDefComponents funDefs =
   let names = Set.fromList $ map (Hs.UnQual . funName) funDefs
       graphConstr = map graphComp funDefs
       graphComp funDef = (funDef,Hs.UnQual . funName $ funDef, Set.toList . Set.intersection names . funFreeNames $ funDef)
       (graph, extr,_) = graphFromEdges graphConstr
       forest = components graph
    in map (map ((\(n,_,_) -> n) . extr) . flatten) forest

{-|
  This function adds an additional argument to the given match that contains the
  environment of a closure.
-}
addEnvArgToMatch :: Hs.Name  -- ^the name of the environment variable
          -> [Hs.Name] -- ^the names of the variables in the environment
          -> Hs.Match  -- ^the match that should be enriched by an environment argument
          -> Hs.Match  -- ^the resulting match
addEnvArgToMatch envName closureNames match@(Hs.Match loc name pats rhs binds)
    = let boundNames = map uname (extractBindingNs pats)
          toPat name = if name `elem` boundNames
                       then Hs.PWildCard
                       else Hs.PVar name
          allBound = all (`elem` boundNames) closureNames
          tuple = case closureNames of
                    [closureName] -> toPat closureName
                    _ -> Hs.PTuple (map toPat closureNames)
          passing = (Hs.UnQual envName) `Set.member` extractFreeVarNs match
          envArg = if passing then if allBound
                                   then Hs.PVar envName
                                   else Hs.PAsPat envName tuple
                   else if allBound
                        then Hs.PWildCard
                        else tuple
      in (Hs.Match loc name (envArg:pats) rhs binds)                       
    where uname (Hs.Qual _ name) = name
          uname (Hs.UnQual name) = name

{-|
  This function adds an additional argument to the given function binding that contains the
  environment of a closure.
-}
addEnvArgToDecl :: Hs.Name  -- ^the name of the environment variable
                -> [Hs.Name] -- ^the names of the variables in the environment
                -> Hs.Decl  -- ^the match that should be enriched by an environment argument
                -> Hs.Decl  -- ^the resulting match
addEnvArgToDecl envName closureNames (Hs.FunBind matches)
    = let matches' = map (addEnvArgToMatch envName closureNames) matches
      in Hs.FunBind matches'

addPatBindsToMatch :: [Hs.Decl] -> Hs.Match -> Hs.Match
addPatBindsToMatch patBinds match@(Hs.Match loc name pats (Hs.UnGuardedRhs exp) binds)
    = let neededPatBinds = filter patBindNeeded patBinds
          shadowedPatBinds = map shadowPatBind neededPatBinds
          rhs' = Hs.UnGuardedRhs (Hs.Let (Hs.BDecls shadowedPatBinds) exp)
      in if null neededPatBinds
         then match
         else Hs.Match loc name pats rhs' binds
    where patBindNeeded patBind
              = not (Set.null ( Set.fromList (extractBindingNs patBind)
                                `Set.intersection` extractFreeVarNs exp ))
          boundNames = Set.fromList (extractBindingNs pats)
          shadowPatBind :: Hs.Decl -> Hs.Decl
          shadowPatBind (Hs.PatBind loc pat rhs binds) 
              = (Hs.PatBind loc (shadow pat) rhs binds) 
          shadowPVar :: Hs.Pat -> Hs.Pat
          shadowPVar var@(Hs.PVar name) 
              | Hs.UnQual name `Set.member` boundNames = Hs.PWildCard
              | otherwise = var
          shadowPVar oth = oth 
                            
          shadow :: GenericT
          shadow = everywhere (mkT shadowPVar)

addPatBindsToDecl :: [Hs.Decl] -> Hs.Decl -> Hs.Decl
addPatBindsToDecl patBinds (Hs.FunBind matches) = 
    let matches' = map (addPatBindsToMatch patBinds) matches
    in Hs.FunBind matches'
addPatBindsToDecl _ decl@(Hs.TypeSig _ _ _) = decl
addPatBindsToDecl patBinds decl = error $ "Function binding expected but found:\n" ++ prettyPrint decl
     

delocaliseFunDefs :: [FunDef] -> DelocaliserM [Hs.Decl]
delocaliseFunDefs funDefs = 
    do envNames <- boundNames
       let freeNames = Set.unions (map funFreeNames funDefs)
           closureNames = freeNames `Set.intersection` envNames
           closureNameList = Set.toList closureNames
           closureUNameList = map uname closureNameList
           funNames = map (Hs.UnQual . funName) funDefs
       renamings <- liftGensym $ freshIdentifiers funNames
       envUName <- liftGensym $ genHsName (Hs.Ident "env")
       let envName = Hs.UnQual envUName
           addEnv (orig,ren) = (orig, Hs.App (Hs.Var ren) (Hs.Var envName))
           envTuple = case closureNameList of
                        [closureName] -> Hs.Var closureName
                        _ -> Hs.Tuple (map Hs.Var closureNameList)
           addEnvTuple (orig,ren) = Hs.PatBind
                                    (SrcLoc "" 0 0)
                                    (Hs.PVar $ uname orig)
                                    (Hs.UnGuardedRhs (Hs.App (Hs.Var ren) envTuple))
                                    (Hs.BDecls [])
           withoutEnvTuple (orig,ren) = Hs.PatBind
                                        (SrcLoc "" 0 0)
                                        (Hs.PVar $ uname orig)
                                        (Hs.UnGuardedRhs (Hs.Var ren))
                                        (Hs.BDecls [])
           subst = Map.fromList $ map addEnv renamings
           funs = map funBind funDefs
           funsRenamed = map (renameDecl renamings) funs
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
    where uname (Hs.Qual _ name) = name
          uname (Hs.UnQual name) = name

delocaliseLet :: Hs.Exp -> DelocaliserM Hs.Exp
delocaliseLet (Hs.Let binds exp) = 
    let (Hs.BDecls patBinds, Hs.BDecls  funBinds) = splitPatBinds (checkBindings binds)
        funBinds' = map (addPatBindsToDecl patBinds) funBinds
        funDefs = funDefComponents (groupFunDefs funBinds') 
    in do newPatBinds <- mapM delocaliseFunDefs funDefs
          let newBinds = Hs.BDecls $ (concat newPatBinds) ++ patBinds
          return $ Hs.Let newBinds exp
delocaliseLet exp = return exp 



{-|
  This predicates checks whether the argument is a pattern binding.
-}
isPatBind :: Hs.Decl -> Bool
isPatBind (Hs.PatBind _ _ _ _) = True
isPatBind _ = False


{-|
  This function partitions bindings into a pair (pattern bindings, other bindings)
-}
splitPatBinds :: Hs.Binds -> (Hs.Binds, Hs.Binds)
splitPatBinds (Hs.BDecls decls) 
    = let (patDecls, typeSigs, otherDecls)    = unzip3 (map split decls)
          (patDecls', typeSigs', otherDecls') = (catMaybes patDecls, 
                                                 concatMap flattenTypeSig (catMaybes typeSigs), 
                                                 catMaybes otherDecls)
          (patTypeSigs, otherTypeSigs) 
              = partition (let patNs = concatMap namesFromDecl patDecls'
                           in \sig -> head (namesFromDecl sig) `elem` patNs)
                          typeSigs'
      in (Hs.BDecls (patTypeSigs ++ patDecls'), Hs.BDecls (otherTypeSigs ++ otherDecls'))

    where split decl@(Hs.PatBind loc pat rhs binds)
              = (Just decl, Nothing, Nothing)
          split decl@(Hs.TypeSig loc names typ)
              = (Nothing, Just decl, Nothing)
          split decl = (Nothing, Nothing, Just decl)
splitPatBinds junk = error ("splitPatBinds: Fall through. " ++ show junk)

getPatDecls :: Hs.Binds -> [Hs.Decl]
getPatDecls bindings
    = let Hs.BDecls patdecls = fst (splitPatBinds bindings) in patdecls

flattenTypeSig :: Hs.Decl -> [Hs.Decl]
flattenTypeSig (Hs.TypeSig loc names typ)
    = map (\n -> Hs.TypeSig loc [n] typ) names

---- Normalization of names.
--
-- Function definitions are restricted in Isar/HOL such that names of
-- constants must not be used as a bound variable name in those definitions.
-- 
-- We simply rename all those identifiers.
--

normalizeNames_Decl :: Hs.Decl -> GensymM Hs.Decl

should_be_renamed :: Hs.QName -> Bool
should_be_renamed qn = case qn of
                         Hs.Qual _ n -> consider n
                         Hs.UnQual n -> consider n
    where consider (Hs.Ident s)  = s `elem` used_const_names
          consider (Hs.Symbol s) = s `elem` used_const_names

normalizeNames_Decl (Hs.FunBind matchs)
    = do matchs' <- mapM normalizePatterns_Match matchs
         return (Hs.FunBind matchs')
    where
      normalizePatterns_Match (Hs.Match loc name pats (Hs.UnGuardedRhs body) where_binds)
          = let bound_var_ns = bindingsFromPats pats
                clashes      = filter should_be_renamed bound_var_ns
            in do renames <- freshIdentifiers clashes
                  pats'   <- return (map (renamePat renames) pats)
                  body'   <- return (renameFreeVars renames body)
                  binds'  <- normalizeNames_Binds where_binds
                  return (Hs.Match loc name pats' (Hs.UnGuardedRhs body') binds') 

      normalizeNames_Binds (Hs.BDecls decls)
          = do decls' <- mapM normalizeNames_Decl decls
               return (Hs.BDecls decls')

normalizeNames_Decl decl 
    -- There aren't any subdecls in decl anymore after delocalization.
    = return decl

-- normalizeModuleNameName :: String -> String


whereToLet :: Hs.Decl -> Hs.Decl
whereToLet =
    everywhere $ mkT 
    whereToLetDecl `extT`
    whereToLetMatch `extT`
    whereToLetAlt

isEmptyBinds :: Hs.Binds -> Bool
isEmptyBinds (Hs.BDecls []) = True
isEmptyBinds (Hs.IPBinds []) = True
isEmptyBinds _ = False

whereToLetDecl :: Hs.Decl -> Hs.Decl
whereToLetDecl (Hs.PatBind loc pat rhs binds)
    | not $ isEmptyBinds binds = 
        case rhs of
          Hs.GuardedRhss _ -> assert False undefined
          Hs.UnGuardedRhs exp -> 
              let rhs' = Hs.UnGuardedRhs $ Hs.Let binds exp
              in Hs.PatBind loc pat rhs' (Hs.BDecls [])
whereToLetDecl decl = decl

whereToLetMatch :: Hs.Match -> Hs.Match
whereToLetMatch match@(Hs.Match loc name pat rhs binds)
    | isEmptyBinds binds = match
    | otherwise =
        case rhs of
          Hs.GuardedRhss _ -> assert False undefined
          Hs.UnGuardedRhs exp -> 
              let rhs' = Hs.UnGuardedRhs $ Hs.Let binds exp
              in Hs.Match loc name pat rhs' (Hs.BDecls [])

whereToLetAlt :: Hs.Alt -> Hs.Alt
whereToLetAlt orig@(Hs.Alt loc pat alt binds) 
    | isEmptyBinds binds = orig
    | otherwise =
        case alt of
          Hs.GuardedAlts _ -> assert False undefined
          Hs.UnGuardedAlt exp -> 
              let alt' = Hs.UnGuardedAlt $ Hs.Let binds exp
              in Hs.Alt loc pat alt' (Hs.BDecls [])


---- Deguardification

type DeguardifyEnv = Reader Bool

runDeguardifyEnv :: DeguardifyEnv a -> a
runDeguardifyEnv m = runReader m False

{-|
  This environment defines a Boolean value indicating whether we are inside
  the last match in a function definition
-}
deguardifyEnv :: (Monad m) => EnvDef m Bool
deguardifyEnv = mkE fromMatches
    where fromMatches :: [Hs.Match] -> Envs (Repl Bool)
          fromMatches [] = Envs []
          fromMatches [_] = Envs [Set True,Set False]
          fromMatches (_:_) = Envs [Set False,Set False]

deguardify :: Hs.Decl -> Hs.Decl
deguardify decl = runDeguardifyEnv $ everywhereEnv deguardifyEnv deguardifyLocal decl

deguardifyLocal :: GenericM DeguardifyEnv
deguardifyLocal = mkM deguardifyRhs
                  `extM` deguardifyAlts


deguardifyRhs :: Hs.Rhs -> DeguardifyEnv Hs.Rhs
deguardifyRhs rhs@(Hs.UnGuardedRhs _) = return rhs
deguardifyRhs (Hs.GuardedRhss guards) = liftM Hs.UnGuardedRhs $ deguardifyGuards guards

deguardifyAlts :: Hs.GuardedAlts -> DeguardifyEnv Hs.GuardedAlts
deguardifyAlts alt@(Hs.UnGuardedAlt _) = return alt
deguardifyAlts (Hs.GuardedAlts guards) = 
    liftM Hs.UnGuardedAlt .
    deguardifyGuards .
    (map (\(Hs.GuardedAlt l ss e) -> Hs.GuardedRhs l ss e)) $
    guards
deguardifyGuards :: [Hs.GuardedRhs] -> DeguardifyEnv Hs.Exp
deguardifyGuards guards = 
    do isLast <- ask
       let findOtherwiseExpr guards
               = case break isTrivial guards of
                   (guards', (Hs.GuardedRhs _ _ last_expr):_) -> (guards', last_expr)
                   (guards',[])
                       | isLast -> let Hs.GuardedRhs srcLoc _ _ = last guards'
                                   in error $ Msg.found_inconsistency_in_guards srcLoc
                       | otherwise -> (guards', bottom)
           (guards', otherwise_expr) = findOtherwiseExpr guards
       return $ foldr deguardify otherwise_expr guards'
    where otherwise_stmt = Hs.Qualifier (Hs.Var (Hs.UnQual (Hs.Ident "otherwise")))
          true_stmt      = Hs.Qualifier (Hs.Var (Hs.UnQual (Hs.Ident "True")))
          bottom         = Hs.Var (Hs.Qual (Hs.ModuleName "Prelude") (Hs.Symbol "_|_")) 
          isTrivial (Hs.GuardedRhs _ stmts _) =
              stmts `elem` [[otherwise_stmt], [true_stmt]]
          deguardify x@(Hs.GuardedRhs loc stmts clause) body
              = Hs.If (makeGuardExpr stmts) clause body
          makeGuardExpr stmts = if null stmts
                                then (Hs.Var (Hs.UnQual (Hs.Ident "True")))
                                else foldl1 andify (map expify stmts)
              where expify (Hs.Qualifier exp) = exp
                    andify e1 e2 = Hs.InfixApp e1 (Hs.QVarOp (Hs.Qual (Hs.ModuleName "Prelude") (Hs.Symbol "&&"))) e2


-- `let' in Haskell is actually a letrec, but Isar/HOL does not allow
-- recursive let expressions. We hence check the bindings in question
-- whether or not we can deal with them.
--
checkBindings :: Hs.Binds -> Hs.Binds
checkBindings bindings
    = checkForRecursiveBinds . checkForForwardRefs $ bindings

-- Check for forward references, e.g. prohibit
--
--    let a = b * 42 
--        b = 23 in ... 
-- 
-- as `b' is referenced before its binding is established.
--
-- Notice that do allow forward referencing to functions like for
-- instance in
--
--    let a x = 32 + b x
--        b y = c (- y)
--        c z = 42 * z in ...
-- 
-- We can allow this because the function will be globalized, and
-- hence moved out of the `let' expression.
--
checkForForwardRefs bindings
    = let vardecls = getPatDecls bindings
      in case filter (\(decl, forwardNss) 
                          -> any (`elem` concat forwardNss) $ Set.toList (extractFreeVarNs decl))
                $ zip vardecls
                      -- These are the consecutively following binding names:
                      (tails (map extractBindingNs vardecls))
      of []          -> bindings
         (decl, _):_ -> error (Msg.forward_bindings_disallowed (getSrcLoc decl))

-- Check for recursive binding attempts, e.g. prohibit
--
--    let ones = 1 : ones in ...
--
-- For the same reasons as above (forward refs), we do all recursive
-- local function definitions.
--
checkForRecursiveBinds bindings
    = let find_recursive_binds = filter (\d -> any (`elem` extractBindingNs d) 
                                                 $ extractVarNs d)
      in case find_recursive_binds (getPatDecls bindings) of
        []  -> bindings
        d:_ -> error (Msg.recursive_bindings_disallowed (getSrcLoc d))




------------------------------------------------------------
------------------------------------------------------------
--------------------------- Tests --------------------------
------------------------------------------------------------
------------------------------------------------------------

{-

runTest = quickCheck prop_NoWhereDecls

onlyPatBinds (Hs.BDecls binds) = all isPat binds
    where isPat Hs.PatBind{} = True
          isPat Hs.TypeSig{} = True
          isPat _ = False
noPatBinds (Hs.BDecls binds) = all noPat binds
    where noPat Hs.PatBind{} = False
          noPat _ = True


prop_splitPatBindsCorrect binds = let (pat,nonPat) = splitPatBinds binds
                                  in onlyPatBinds pat && noPatBinds nonPat

noLocalDecl :: Hs.ModuleName -> Bool
noLocalDecl m = True


hasWhereDecls :: Data a => a -> Bool
hasWhereDecls node = everything (||) (mkQ False fromDecl `extQ` fromMatch) node
    where fromDecl (Hs.PatBind _ _ _ binds) = isNonEmpty binds
          fromDecl _ = False
          fromMatch (Hs.Match _ _ _ _ binds) = isNonEmpty binds
          isNonEmpty (Hs.BDecls binds) = not (null binds)
          isNonEmpty (Hs.IPBinds binds) = not (null binds)

prop_NoWhereDecls mod = not $ hasWhereDecls $ preprocessHs.ModuleName mod

prop_NoLocalDecl mod = noLocalDecl $ preprocessHs.ModuleName mod

checkDelocM :: PropertyM DelocaliserM a -> Property
checkDelocM deloc = forAll arbitrary $ \ (NonNegative gsState, delocState) ->
              monadic (fst . evalGensym gsState . evalDelocaliser delocState) deloc


                          

{-|
  'flattenHs.TypeSig' really flattens the type declaration.
-}
prop_flattenHs.TypeSig_isFlat = forAll typeSigDecl $ \ decl ->
                        all isFlat $ flattenHs.TypeSig decl
    where isFlat (Hs.TypeSig _src names _type) = length names `elem` [0,1]
          isFlat _ = False

prop_flattenHs.TypeSig_isEquiv = forAll typeSigDecl $ \ decl ->
                               let flat = flattenHs.TypeSig decl in
                               flat `equiv` [decl]
    where d `subOf` e = (`all` d) $ \ (Hs.TypeSig _src names typ) -> 
                        (`all` names) $ \ name ->
                        (`any` e) $ \ (Hs.TypeSig _src' names' typ') ->
                        (`any` names) $ \ name' -> name == name' && typ == typ'
          d `equiv` e = d `subOf` e && e `subOf` d
-}