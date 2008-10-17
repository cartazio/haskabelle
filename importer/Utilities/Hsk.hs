{-# OPTIONS_GHC -fallow-undecidable-instances #-}

{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen

Auxiliary.
-}

{-|
  Auxiliary function to work on Haskell ASTs.
 -}
module Importer.Utilities.Hsk
    (
     -- * Types
     Renaming,
     HskNames,
     -- * Functions
      srcloc2string,
      extractBindingNs,
      freshIdentifiers,
      bindingsFromDecls,
      renameFreeVars,
      bindingsFromPats,
      extractFreeVarNs,
      orderDeclsBySourceLine,
      renameHsPat,
      renameHsDecl,
      module2FilePath,
      moduleFileLocation,
      namesFromHsDecl,
      string2HsName,
      extractSuperclassNs,
      extractMethodSigs,
      hsk_nil,
      hsk_cons,
      hsk_pair,
      hsk_negate,
      isHaskellSourceFile,
      isOperator,
      moduleHierarchyDepth,
      showModule,
      typeConName,
      returnType,
      boundNames,
      boundNamesEnv,
      applySubst
    ) where
  
import Maybe
import List (sort)
import Array (inRange)
import Char (toLower)

import Control.Monad.Reader
import Data.Generics.Basics
import Data.Generics.PlateData
import Language.Haskell.Exts


import Data.Generics
import Data.Generics.Env

import Data.Map (Map)
import qualified Data.Map as Map hiding (Map)
import Data.Set (Set)
import qualified Data.Set as Set hiding (Set)

import Importer.Utilities.Misc (concatMapM, assert, hasDuplicates, wordsBy, trace, prettyShow')
import Importer.Utilities.Gensym

{-|
  The prelude's module name
-}
hsk_prelude :: Module
hsk_prelude = Module "Prelude"

{-|
  This function takes a constant identifier name and converts it into a
  Haskell expression of a qualified 
-}
prelude_fn :: String -> HsExp
prelude_fn fn_name = HsVar (Qual hsk_prelude (HsIdent fn_name))

{-|
  This function provides the return type of a type. E.g.
  returnType (a -> b -> c) = c
-}
returnType :: HsType -> HsType
returnType (HsTyForall _ _ ty) = ty
returnType (HsTyFun _ ty) = ty
returnType (HsTyKind ty _) = ty
returnType ty = ty


{-|
  This function provides the (unqualified) name of the type constructor that constructed
  the given type or nothing if the given type is not a constructor application.
-}
typeConName :: HsType -> Maybe String
typeConName (HsTyApp (HsTyCon qname) _) =
    case qname of
      Qual _ (HsIdent name) -> Just name
      UnQual (HsIdent name) -> Just name
      _                     -> Nothing
typeConName _ = Nothing


isHskSymbol :: Char -> Bool
isHskSymbol = flip elem ['_', ':', '"', '[', ']', '!', '#', '$', '%', '&',
                         '*', '+', '.', '/', '<', '=', '>', '?', '@',
                         '\\', '^', '|', '-', '~' ]

isOperator :: String -> Bool
isOperator = all isHskSymbol

{-|
  This function takes a Haskell expression and applies it to the argument
  given in the list
-}
hsk_apply :: HsExp -> [HsExp] -> HsExp
hsk_apply fn_expr args
    = foldl HsApp fn_expr args

{-|
  The Haskell empty list.
-}
hsk_nil :: HsExp
hsk_nil             = HsList []

{-|
  The Haskell list constructor. This function takes two Haskell expressions and applies
  the list constructor @(:)@ to it.
-}
hsk_cons :: HsExp -> HsExp -> HsExp
hsk_cons x y        = HsApp (HsApp (HsCon (Special HsCons)) x) y

{-|
  The Haskell pair constructor. This function takes two Haskell expressions and applies
  the pair constructor @(,)@ to them.
-}
hsk_pair :: HsExp -> HsExp -> HsExp
hsk_pair x y        = HsApp (HsApp (HsCon (Special (HsTupleCon 2))) x) y

{-|
  The Haskell logical negation. This function takes a Haskell expression and applies
  the negation 'negate' to it.
-}
hsk_negate :: HsExp -> HsExp
hsk_negate e        = hsk_apply (prelude_fn "negate") [e]

{-|
  The Haskell if-then-else. This function takes three arguments - condition, if branch, else branch -
  and forms a corresponding if-then-else expression.
-}
hsk_if ::  HsExp -> HsExp -> HsExp -> HsExp
hsk_if = HsIf

{-|
  The Haskell lambda abstraction.
-}
hsk_lambda :: SrcLoc -> [HsPat] -> HsExp -> HsExp
hsk_lambda = HsLambda

{-|
  The Haskell (ungarded!) case expression.
-}
hsk_case :: SrcLoc -> HsExp -> [(HsPat, HsExp)] -> HsExp
hsk_case loc e cases
    = HsCase e [ HsAlt loc pat (HsUnGuardedAlt exp) (HsBDecls []) | (pat, exp) <- cases ]

{-|
  This function turns a string into a Haskell name. Depending on the
  actual string it is considered a symbol (cf. 'HsSymbol') or an
  identifier (cf. 'HsIdent').
-}
string2HsName :: String -> HsName
string2HsName string = case isSymbol string of
                         True  -> HsSymbol string
                         False -> HsIdent string
    where isSymbol string = and $ map (`elem` symbols) string
          symbols = "!@$%&*+./<=>?¹\\^|~"

{-|
  This function turns a source location into a human readable string.
-}
srcloc2string :: SrcLoc -> String
srcloc2string (SrcLoc { srcFilename=filename, srcLine=line, srcColumn=column })
    = filename ++ ":" ++ (show line) ++ ":" ++ (show column)

{-|
  This function computes the relative file path to the given module name.
  E.g.  \"Some.Module.Name\" ==> \"Some\/Module\/Name\"
-}
module2FilePath :: Module -> FilePath
module2FilePath (Module name)
    = map (\c -> if c == '.' then '/' else c) name ++ ".hs"

moduleFileLocation :: HsModule -> FilePath
moduleFileLocation (HsModule SrcLoc{srcFilename = file} _ _ _ _) = file

moduleHierarchyDepth :: Module -> Int
moduleHierarchyDepth (Module name) = length $ filter (== '.') name

{-|
  This predicate checks whether the given file path refers to a Haskell
  source file.
-}
isHaskellSourceFile :: FilePath -> Bool
isHaskellSourceFile fp = map toLower (last (wordsBy (== '.') fp)) == "hs"

{-|
  This function takes a context (from a class definition) and extracts
  the super classes' names.

  TODO: This is to specific: Contexts can be more complex. This function only returns
  the \"super classes\" if the context's assertion have the class' type variable as their
  only argument. Also other kinds of assertions are not considered.
-}
extractSuperclassNs :: HsContext -> [HsQName]
extractSuperclassNs ctx = map extract ctx
    where extract (HsClassA qn _) = qn

{-|
  This function extracts the type declarations of the given list of
  class-internal declarations.
-}
extractMethodSigs :: [HsClassDecl] -> [HsDecl]
extractMethodSigs class_decls
    = filter isTypeSig (map (\(HsClsDecl d) -> d) class_decls)
    where isTypeSig (HsTypeSig _ _ _) = True
          isTypeSig _                 = False

{-|
  This function extracts all Haskell names that are affected by the given
  declaration. If the given kind of declaration is not supported an exception
  is thrown.
-}
namesFromHsDecl :: HsDecl -> [HsQName]
namesFromHsDecl (HsTypeDecl _ name _ _)        = [UnQual name]
namesFromHsDecl (HsDataDecl _ _ _ name _ _ _)  = [UnQual name]
namesFromHsDecl (HsClassDecl _ _ name _ _ _)   = [UnQual name]
namesFromHsDecl (HsInstDecl _ _ qname _ _)     = [qname]
namesFromHsDecl (HsTypeSig _ names _)          = map UnQual names
namesFromHsDecl (HsInfixDecl _ _ _ ops)        = [UnQual n | n <- (universeBi ops :: [HsName])]
namesFromHsDecl (HsPatBind _ pat _ _)          = bindingsFromPats [pat]
namesFromHsDecl (HsFunBind (HsMatch _ fname _ _ _ : ms ))
                                               = [UnQual fname]
namesFromHsDecl decl                           = error $ "Internal error: The given declaration " ++ show decl ++ " is not supported!"

{-|
  Instances of this class represent pieces of Haskell syntax that can bind 
  variables.
-}

class HasBindings a where
    {-|
      This function is supposed to provide a list of all Haskell variables that
      are bound by the given syntax.
     -}
    extractBindingNs :: a -> [HsQName]

{-|
  Lift all instances to lists.
-}
instance HasBindings a => HasBindings [a] where
    extractBindingNs list = concatMap extractBindingNs list

instance HasBindings HsPat where
    extractBindingNs pattern = bindingsFromPats [pattern]

instance HasBindings HsDecl where
    extractBindingNs decl = bindingsFromDecls [decl] 

instance HasBindings HsBinds where
    extractBindingNs (HsBDecls decls) = extractBindingNs decls
    extractBindingNs (HsIPBinds (HsIPBind loc _ _ : _))
        = error $ srcloc2string loc ++ ": Implicit parameter bindings are not supported!"
    extractBindingNs (HsIPBinds []) = []

instance HasBindings HsStmt where
    extractBindingNs (HsQualifier b)         = []
    extractBindingNs (HsGenerator _ pat exp) = extractBindingNs pat
    extractBindingNs (HsLetStmt binds)       = extractBindingNs binds



{-|
  This function extracts from the given Haskell pattern a list of all Haskell variables
  that are bound by the pattern.
-}
bindingsFromPats          :: [HsPat] -> [HsQName]
bindingsFromPats pattern  = [ UnQual n | HsPVar n <- universeBi pattern ] 

{-|
  This function extracts the variables bound by the given declaration.
-}
bindingsFromDecls       :: [HsDecl] -> [HsQName]
bindingsFromDecls decls = assert (not (hasDuplicates bindings)) bindings
    -- Type signatures do not create new bindings, but simply annotate them.
    where bindings = concatMap namesFromHsDecl (filter (not . isTypeSig) decls)
          isTypeSig (HsTypeSig _ _ _) = True
          isTypeSig _                 = False


type HskNames = Set HsQName
newtype BindingM a = BindingM (Reader HskNames a)
    deriving (Monad, MonadReader HskNames, Functor)

runBindingM :: BindingM a -> a
runBindingM (BindingM m) = runReader m Set.empty

class BindingMonad m where
    boundNames :: m HskNames
    isBound :: HsQName -> m Bool
    

instance MonadReader HskNames m => BindingMonad m where
    isBound name = ask >>=  (return . Set.member name)
    boundNames = ask

type Subst = Map HsQName HsExp

{-|
  This function extracts the set of the names that are bound by
  the given piece of Haskell Syntax.
-}

boundNamesEnv :: EnvTrans HskNames
boundNamesEnv = mkEa fromExp
             `extEau` fromAlt
             `extEau` fromDecl
             `extEau` fromMatch
             `extEa` fromStmts
    where fromExp :: HsExp -> [HskNames]
          fromExp (HsLet binds _)
              = let bound = Set.fromList $ extractBindingNs binds
                in [bound,bound]
          fromExp (HsLambda _ pats _)
              = let bound = Set.fromList $ extractBindingNs pats
                in [Set.empty,bound, bound]
          fromExp (HsMDo stmts)
              = let bound = Set.fromList $ extractBindingNs stmts
                in [bound]
          fromExp (HsListComp _ stmts)
              = let bound = Set.fromList $ extractBindingNs stmts
                in [bound, Set.empty]
          fromExp exp = uniEloc exp Set.empty
                            
          fromAlt :: HsAlt -> HskNames
          fromAlt (HsAlt _ pat _ _) = Set.fromList $ extractBindingNs pat

          fromDecl :: HsDecl -> HskNames
          fromDecl (HsPatBind _ _ _ whereBinds) = Set.fromList $
                                                       extractBindingNs whereBinds
          fromDecl _ = Set.empty

          fromMatch :: HsMatch -> HskNames
          fromMatch (HsMatch _ _ pats _ whereBinds)
              = Set.fromList $ 
                extractBindingNs whereBinds ++ extractBindingNs pats

          fromStmts :: [HsStmt] -> [HskNames]
          fromStmts [] = []
          fromStmts (HsGenerator loc pat exp : _)
              = let bound = Set.fromList $ extractBindingNs pat
                in [Set.empty, bound]
          fromStmts (HsQualifier _ : _)
              = [Set.empty, Set.empty]
          fromStmts (HsLetStmt binds : _)
              = let bound = Set.fromList $ extractBindingNs binds
                in [bound, bound]

{-|
  This is a monadic query function that returns
  if the argument is a free name a singleton set
  containing that name and otherwise an empty set.
-}
freeNamesLocal :: GenericQ (BindingM HskNames)
freeNamesLocal hs = case name hs of
                Nothing -> return Set.empty
                Just name ->
                    do bound <- isBound name
                       if bound
                         then return Set.empty
                         else return (Set.singleton name)
    where name :: GenericQ (Maybe HsQName)
          name = mkQ Nothing fromExp
                  `extQ`fromQOp
          fromExp :: HsExp -> Maybe HsQName
          fromExp (HsVar name) = Just name
          fromExp _ = Nothing
                      
          fromQOp :: HsQOp -> Maybe HsQName
          fromQOp (HsQVarOp name) = Just name
          fromQOp _ = Nothing


{-|
  This function returns the set of names of free variables
  in the given pieces of Haskell syntax.
-}
extractFreeVarNs :: Data a => a -> HskNames
extractFreeVarNs node = runBindingM $ everythingEnv boundNamesEnv (Set.union) freeNamesLocal node


applySubst :: Subst -> GenericT
applySubst subst node = runBindingM $ everywhereEnv boundNamesEnv (applySubstLocal subst) node

applySubstLocal :: Subst -> GenericM BindingM
applySubstLocal subst node =
    do bound <- boundNames
       let apply :: GenericT
           apply = mkT applyExp

           applyExp :: HsExp -> HsExp
           applyExp exp@(HsVar name)
               = case doSubst name of
                   Nothing -> exp
                   Just new -> new
           applyExp exp@(HsInfixApp exp1 (HsQVarOp name) exp2)
               = case doSubst name of
                   Nothing -> exp
                   Just new -> HsApp (HsApp new exp1) exp2
           applyExp exp@(HsLeftSection exp' (HsQVarOp name))
               = case doSubst name of
                   Nothing -> exp
                   Just new -> (HsApp new exp')
           applyExp exp@(HsRightSection (HsQVarOp name) exp')
               = case doSubst name of
                   Nothing -> exp
                   Just new -> (HsApp (HsApp (HsVar (UnQual (HsIdent "flip"))) new) exp')
           applyExp exp = exp

           doSubst :: HsQName -> Maybe HsExp
           doSubst  name
                 | name `Set.member` bound
                     = Nothing
                 | otherwise
                     = (Map.lookup name subst)
       return (apply node)

renameFreeVarsLocal :: [Renaming] -> GenericM BindingM
renameFreeVarsLocal renamings node =
    do bound <- boundNames
       let apply :: GenericT
           apply = mkT applyExp
                   `extT` applyQOp

           applyExp :: HsExp -> HsExp
           applyExp (HsVar name) = HsVar (ren name)
           applyExp exp = exp
                      
           applyQOp :: HsQOp -> HsQOp
           applyQOp (HsQVarOp name) = HsQVarOp (ren name)
           applyQOp qop = qop
           
           ren :: HsQName -> HsQName
           ren name
                 | name `Set.member` bound
                     = name
                 | otherwise
                     = fromMaybe name (lookup name renamings)
       return (apply node)

renameFreeVars :: Data a => [Renaming] -> a -> a
renameFreeVars renamings node = runBindingM $ everywhereEnv boundNamesEnv (renameFreeVarsLocal renamings) node

{-|
  This type is used to describe renamings of variables.
-}
type Renaming = (HsQName, HsQName)

{-|
  This function generates renamings for all variables given in the
  list to provide fresh names.
-}
freshIdentifiers :: [HsQName] -> GensymM [Renaming]
freshIdentifiers qnames
    = do freshs <- mapM genHsQName qnames
         return (zip qnames freshs)

{-|
  This function takes a list of variables (which are supposed to be bound) and a renaming
  and reduces this renaming such that it does not affect bound variables.
-}
shadow :: [HsQName] -> [Renaming] -> [Renaming]
shadow boundNs renamings  = filter ((`notElem` boundNs) . fst) renamings

{-|
  This function applies the given renaming to the given variable.
-}
qtranslate :: [Renaming] -> HsQName -> HsQName
qtranslate renamings qname 
    = fromMaybe qname (lookup qname renamings)

{-|
  This function applies the given renaming to the given unqualified variable.
-}
translate :: [Renaming] -> HsName -> HsName
translate renamings name 
    = let (UnQual name') = qtranslate renamings (UnQual name) in name'

{-|
  This function applies the given renaming to all variables in the given
  pattern.
-}
renameHsPat :: [Renaming] -> HsPat -> HsPat
renameHsPat renams pat
    = case pat of
        HsPVar name                 -> HsPVar (translate renams name)
        HsPLit lit                  -> HsPLit lit
        HsPNeg pat                  -> HsPNeg (renameHsPat renams pat)
        HsPInfixApp pat1 qname pat2 -> HsPInfixApp pat1' qname' pat2'
            where pat1'  = renameHsPat renams pat1 
                  qname' = qtranslate renams qname
                  pat2'  = renameHsPat renams pat2
        HsPApp qname pats           -> HsPApp qname' pats'
            where qname' = qtranslate renams qname
                  pats'  = map (renameHsPat renams) pats
        HsPTuple pats               -> HsPTuple (map (renameHsPat renams) pats)
        HsPList  pats               -> HsPList (map (renameHsPat renams) pats)
        HsPParen pat                -> HsPParen (renameHsPat renams pat)
        HsPWildCard                 -> HsPWildCard
        _ -> error ("renameHsPat: Fall through: " ++ show pat)

{-|
  This function applies the given renaming to names bound by the given
  Haskell declaration (only type signatures, function and pattern bindings
  are affected).
-}
renameHsDecl :: [Renaming] -> HsDecl -> HsDecl
renameHsDecl renamings decl = 
    case decl of
      HsTypeSig loc names typ
          -> HsTypeSig loc (map (translate renamings) names) typ
      HsFunBind matches
          -> HsFunBind (map renMatch matches)
      HsPatBind loc pat rhs binds 
          -> HsPatBind loc (renameHsPat renamings pat) rhs binds
      _ -> decl
    where renMatch :: HsMatch -> HsMatch
          renMatch (HsMatch loc name pats rhs binds)
                   = HsMatch loc (translate renamings name) pats rhs binds

{-|
  This function compares the two given declarations w.r.t. the 
  source location.
-}
orderDeclsBySourceLine :: HsDecl -> HsDecl -> Ordering
orderDeclsBySourceLine decl1 decl2
    = compare (getSourceLine decl1) (getSourceLine decl2) 

{-|
  This function provides the source line where the given
  declaration is made.
-}
getSourceLine :: HsDecl -> Int
getSourceLine decl
    = let srclocs = childrenBi decl :: [SrcLoc]
          lines   = map srcLine srclocs
      in head (sort lines)

showModule :: Module -> String
showModule (Module name) = name