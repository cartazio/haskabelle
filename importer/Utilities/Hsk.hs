{-# LANGUAGE
  UndecidableInstances,
  FlexibleInstances,
  GeneralizedNewtypeDeriving #-}

{-| Author: Tobias C. Rittweiler, TU Muenchen

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
      extractFieldNs,
      extractFreeVarNs,
      extractVarNs,
      extractDataConNs,
      extractTypeConNs,
      extractImplDeclNs,
      orderDeclsBySourceLine,
      renamePat,
      renameDecl,
      module2FilePath,
      moduleFileLocation,
      namesFromDecl,
      string2Name,
      extractSuperclassNs,
      extractMethodSigs,
      hskPNil,
      hskPCons,
      hsk_nil,
      hsk_cons,
      hsk_pair,
      hskPPair,
      hsk_negate,
      isHaskellSourceFile,
      isOperator,
      moduleHierarchyDepth,
      showModuleName,
      typeConName,
      returnType,
      boundNames,
      boundNamesEnv,
      applySubst,
      flattenRecFields,
      unBang,
      getSrcLoc
    ) where
  
import Maybe
import List (sort, sortBy)
import Array (inRange)
import Char (toLower)

import Control.Monad.Reader
import Data.Generics.Basics
import Data.Generics.PlateData
import Language.Haskell.Exts as Hs

import Data.Generics

import Importer.Utilities.Env

import Data.Map (Map)
import qualified Data.Map as Map hiding (Map)
import Data.Set (Set)
import qualified Data.Set as Set hiding (Set)

import Importer.Utilities.Misc (concatMapM, assert, hasDuplicates, wordsBy, trace, prettyShow')
import Importer.Utilities.Gensym

{-|
  The prelude's module name
-}
hsk_prelude :: Hs.ModuleName
hsk_prelude = Hs.ModuleName "Prelude"

{-|
  This function takes a constant identifier name and converts it into a
  Haskell expression of a qualified 
-}
prelude_fn :: String -> Hs.Exp
prelude_fn fn_name = Hs.Var (Hs.Qual hsk_prelude (Hs.Ident fn_name))

{-|
  This function provides the return type of a type. E.g.
  returnType (a -> b -> c) = c
-}
returnType :: Hs.Type -> Hs.Type
returnType (Hs.TyForall _ _ ty) = ty
returnType (Hs.TyFun _ ty) = ty
returnType (Hs.TyKind ty _) = ty
returnType ty = ty


{-|
  This function provides the (unqualified) name of the type constructor that constructed
  the given type or nothing if the given type is not a constructor application.
-}
typeConName :: Hs.Type -> Maybe String
typeConName (Hs.TyApp (Hs.TyCon qname) _) =
    case qname of
      Hs.Qual _ (Hs.Ident name) -> Just name
      Hs.UnQual (Hs.Ident name) -> Just name
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
hsk_apply :: Hs.Exp -> [Hs.Exp] -> Hs.Exp
hsk_apply fn_expr args
    = foldl Hs.App fn_expr args

{-|
  The Haskell empty list.
-}
hskPNil :: Hs.Pat
hskPNil = Hs.PList []

{-|
  The Haskell list constructor. This function takes two Haskell expressions and applies
  the list constructor @(:)@ to it.
-}
hskPCons :: Hs.Pat -> Hs.Pat -> Hs.Pat
hskPCons x y = Hs.PApp (Special Hs.Cons) [x, y]

{-|
  The Haskell empty list.
-}
hsk_nil :: Hs.Exp
hsk_nil             = Hs.List []

{-|
  The Haskell list constructor. This function takes two Haskell expressions and applies
  the list constructor @(:)@ to it.
-}
hsk_cons :: Hs.Exp -> Hs.Exp -> Hs.Exp
hsk_cons x y        = Hs.App (Hs.App (Hs.Con (Special Hs.Cons)) x) y

{-|
  The Haskell pair constructor. This function takes two Haskell expressions and applies
  the pair constructor @(,)@ to them.
-}
hskPPair :: Hs.Pat -> Hs.Pat -> Hs.Pat
hskPPair x y = Hs.PApp (Special (Hs.TupleCon 2)) [x, y]

{-|
  The Haskell pair constructor. This function takes two Haskell expressions and applies
  the pair constructor @(,)@ to them.
-}
hsk_pair :: Hs.Exp -> Hs.Exp -> Hs.Exp
hsk_pair x y        = Hs.App (Hs.App (Hs.Con (Special (Hs.TupleCon 2))) x) y

{-|
  The Haskell logical negation. This function takes a Haskell expression and applies
  the negation 'negate' to it.
-}
hsk_negate :: Hs.Exp -> Hs.Exp
hsk_negate e        = hsk_apply (prelude_fn "negate") [e]

{-|
  The Haskell if-then-else. This function takes three arguments - condition, if branch, else branch -
  and forms a corresponding if-then-else expression.
-}
hsk_if ::  Hs.Exp -> Hs.Exp -> Hs.Exp -> Hs.Exp
hsk_if = Hs.If

{-|
  The Haskell lambda abstraction.
-}
hsk_lambda :: SrcLoc -> [Hs.Pat] -> Hs.Exp -> Hs.Exp
hsk_lambda = Hs.Lambda

{-|
  The Haskell (ungarded!) case expression.
-}
hsk_case :: SrcLoc -> Hs.Exp -> [(Hs.Pat, Hs.Exp)] -> Hs.Exp
hsk_case loc e cases
    = Hs.Case e [ Hs.Alt loc pat (Hs.UnGuardedAlt exp) (Hs.BDecls []) | (pat, exp) <- cases ]

{-|
  This function turns a string into a Haskell name. Depending on the
  actual string it is considered a symbol (cf. 'Hs.Symbol') or an
  identifier (cf. 'Hs.Ident').
-}
string2Name :: String -> Hs.Name
string2Name string = case isSymbol string of
                         True  -> Hs.Symbol string
                         False -> Hs.Ident string
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
  E.g.  \"Some.Hs.ModuleName.Name\" ==> \"Some\/Hs.ModuleName\/Name\"
-}
module2FilePath :: Hs.ModuleName -> FilePath
module2FilePath (Hs.ModuleName name)
    = map (\c -> if c == '.' then '/' else c) name ++ ".hs"

moduleFileLocation :: Hs.Module -> FilePath
moduleFileLocation (Hs.Module SrcLoc{srcFilename = file} _ _ _ _ _ _) = file

moduleHierarchyDepth :: Hs.ModuleName -> Int
moduleHierarchyDepth (Hs.ModuleName name) = length $ filter (== '.') name

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
extractSuperclassNs :: Hs.Context -> [Hs.QName]
extractSuperclassNs ctx = map extract ctx
    where extract (Hs.ClassA qn _) = qn

{-|
  This function extracts the type declarations of the given list of
  class-internal declarations.
-}
extractMethodSigs :: [Hs.ClassDecl] -> [Hs.Decl]
extractMethodSigs class_decls
    = filter isTypeSig (map (\(Hs.ClsDecl d) -> d) class_decls)
    where isTypeSig (Hs.TypeSig _ _ _) = True
          isTypeSig _                 = False

{-|
  This function extracts all Haskell names that are affected by the given
  declaration. If the given kind of declaration is not supported an exception
  is thrown.
-}
namesFromDecl :: Hs.Decl -> [Hs.QName]
namesFromDecl (Hs.TypeDecl _ name _ _)        = [Hs.UnQual name]
namesFromDecl (Hs.DataDecl _ _ _ name _ _ _)  = [Hs.UnQual name]
namesFromDecl (Hs.ClassDecl _ _ name _ _ _)   = [Hs.UnQual name]
namesFromDecl (Hs.InstDecl _ _ qname _ _)     = [qname]
namesFromDecl (Hs.TypeSig _ names _)          = map Hs.UnQual names
namesFromDecl (Hs.InfixDecl _ _ _ ops)        = [Hs.UnQual n | n <- (universeBi ops :: [Hs.Name])]
namesFromDecl (Hs.PatBind _ pat _ _)          = bindingsFromPats [pat]
namesFromDecl (Hs.FunBind (Hs.Match _ fname _ _ _ : ms ))
                                               = [Hs.UnQual fname]
namesFromDecl decl                           = error $ "Internal error: The given declaration " ++ show decl ++ " is not supported!"

{-|
  Instances of this class represent pieces of Haskell syntax that can bind 
  variables.
-}

class HasBindings a where
    {-|
      This function is supposed to provide a list of all Haskell variables that
      are bound by the given syntax.
     -}
    extractBindingNs :: a -> [Hs.QName]

{-|
  Lift all instances to lists.
-}
instance HasBindings a => HasBindings [a] where
    extractBindingNs list = concatMap extractBindingNs list

instance HasBindings Hs.Pat where
    extractBindingNs pattern = bindingsFromPats [pattern]

instance HasBindings Hs.Decl where
    extractBindingNs decl = bindingsFromDecls [decl] 

instance HasBindings Hs.Binds where
    extractBindingNs (Hs.BDecls decls) = extractBindingNs decls
    extractBindingNs (Hs.IPBinds (Hs.IPBind loc _ _ : _))
        = error $ srcloc2string loc ++ ": Implicit parameter bindings are not supported!"
    extractBindingNs (Hs.IPBinds []) = []

instance HasBindings Hs.Stmt where
    extractBindingNs (Hs.Qualifier b)         = []
    extractBindingNs (Hs.Generator _ pat exp) = extractBindingNs pat
    extractBindingNs (Hs.LetStmt binds)       = extractBindingNs binds



{-|
  This function extracts from the given Haskell pattern a list of all Haskell variables
  that are bound by the pattern.
-}
bindingsFromPats          :: [Hs.Pat] -> [Hs.QName]
bindingsFromPats pattern  = [ Hs.UnQual n | Hs.PVar n <- universeBi pattern ]
                            ++ [ Hs.UnQual n | Hs.PAsPat n _ <- universeBi pattern ]

{-|
  This function extracts the variables bound by the given declaration.
-}
bindingsFromDecls       :: [Hs.Decl] -> [Hs.QName]
bindingsFromDecls decls = assert (not (hasDuplicates bindings)) bindings
    -- Type signatures do not create new bindings, but simply annotate them.
    where bindings = concatMap namesFromDecl (filter (not . isTypeSig) decls)
          isTypeSig (Hs.TypeSig _ _ _) = True
          isTypeSig _                 = False


type HskNames = Set Hs.QName
newtype BindingM a = BindingM (Reader HskNames a)
    deriving (Monad, MonadReader HskNames, Functor)

runBindingM :: BindingM a -> a
runBindingM (BindingM m) = runReader m Set.empty

class BindingMonad m where
    boundNames :: m HskNames
    isBound :: Hs.QName -> m Bool
    

instance MonadReader HskNames m => BindingMonad m where
    isBound name = ask >>=  (return . Set.member name)
    boundNames = ask

type Subst = Map Hs.QName Hs.Exp

{-|
  This function extracts the set of the names that are bound by
  the given piece of Haskell Syntax.
-}

boundNamesEnv :: (Monad m) => EnvDef m HskNames
boundNamesEnv = mkE fromExp
             `extE` fromAlt
             `extE` fromDecl
             `extE` fromMatch
             `extE` fromStmts
    where fromExp :: Hs.Exp -> Envs HskNames
          fromExp (Hs.Let binds _)
              = let bound = Set.fromList $ extractBindingNs binds
                in Envs [bound,bound]
          fromExp (Hs.Lambda _ pats _)
              = let bound = Set.fromList $ extractBindingNs pats
                in Envs [Set.empty,bound, bound]
          fromExp (Hs.MDo stmts)
              = let bound = Set.fromList $ extractBindingNs stmts
                in Envs [bound]
          fromExp (Hs.ListComp _ stmts)
              = let bound = Set.fromList $ extractBindingNs stmts
                in Envs [bound, Set.empty]
          fromExp exp = uniEloc exp Set.empty
                            
          fromAlt :: Hs.Alt -> HskNames
          fromAlt (Hs.Alt _ pat _ _) = Set.fromList $ extractBindingNs pat

          fromDecl :: Hs.Decl -> HskNames
          fromDecl (Hs.PatBind _ _ _ whereBinds) = Set.fromList $
                                                       extractBindingNs whereBinds
          fromDecl _ = Set.empty

          fromMatch :: Hs.Match -> HskNames
          fromMatch (Hs.Match _ _ pats _ whereBinds)
              = Set.fromList $ 
                extractBindingNs whereBinds ++ extractBindingNs pats

          fromStmts :: [Hs.Stmt] -> Envs HskNames
          fromStmts [] = Envs []
          fromStmts (Hs.Generator loc pat exp : _)
              = let bound = Set.fromList $ extractBindingNs pat
                in Envs [Set.empty, bound]
          fromStmts (Hs.Qualifier _ : _)
              = Envs [Set.empty, Set.empty]
          fromStmts (Hs.LetStmt binds : _)
              = let bound = Set.fromList $ extractBindingNs binds
                in Envs [bound, bound]

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
    where name :: GenericQ (Maybe Hs.QName)
          name = mkQ Nothing fromExp
                  `extQ`fromQOp
          fromExp :: Hs.Exp -> Maybe Hs.QName
          fromExp (Hs.Var name) = Just name
          fromExp _ = Nothing
                      
          fromQOp :: Hs.QOp -> Maybe Hs.QName
          fromQOp (Hs.QVarOp name) = Just name
          fromQOp _ = Nothing


{-|
  This function extracts names that are implicitly declared, such as data constructors
  and record fields.
-}
extractImplDeclNs :: Hs.Decl -> HskNames
extractImplDeclNs decl@(Hs.DataDecl _ _ _ _ _ _ _) =
    everything Set.union (mkQ Set.empty fromConDecl) decl
    where fromConDecl (Hs.ConDecl name _) = Set.singleton (Hs.UnQual name)
          fromConDecl (Hs.RecDecl name fields) = 
              Set.singleton (Hs.UnQual name) 
                     `Set.union` Set.fromList (map Hs.UnQual (concatMap fst fields))

extractImplDeclNs _ = Set.empty

{-|
  This function extracts the names of data constructors used
  in patters from the given piece of Haskell syntax.
-}

extractDataConNs :: Data a => a -> HskNames
extractDataConNs node = everything Set.union (mkQ Set.empty fromPat) node
    where fromPat (Hs.PApp name _) = Set.singleton name
          fromPat (Hs.PRec name _) = Set.singleton name
          fromPat (Hs.PInfixApp _ name _) = Set.singleton name
          fromPat _ = Set.empty

{-|
  This function extracts the names of type constructors in the given piece of
  Haskell syntax
-}
extractTypeConNs :: Data a => a -> HskNames
extractTypeConNs node = everything Set.union (mkQ Set.empty fromType) node
    where fromType :: Hs.Type -> HskNames
          fromType (Hs.TyCon name) = Set.singleton name
          fromType _ = Set.empty

{-|
  This function returns the set of names of free variables
  in the given piece of Haskell syntax.
-}
extractFreeVarNs :: Data a => a -> HskNames
extractFreeVarNs node = runBindingM $ everythingEnv boundNamesEnv (Set.union) freeNamesLocal node

{-|
  This function extracts all used field labels
-}
extractFieldNs :: Data a => a -> HskNames
extractFieldNs node = everything Set.union (mkQ Set.empty fromPat `extQ` fromExp) node
    where fromPat :: Hs.PatField -> HskNames
          fromPat (Hs.PFieldPat field _) = Set.singleton field
          fromExp :: Hs.FieldUpdate -> HskNames
          fromExp (Hs.FieldUpdate field _) = Set.singleton field

applySubst :: Subst -> GenericT
applySubst subst node = runBindingM $ everywhereEnv boundNamesEnv (applySubstLocal subst) node

applySubstLocal :: Subst -> GenericM BindingM
applySubstLocal subst node =
    do bound <- boundNames
       let apply :: GenericT
           apply = mkT applyExp

           applyExp :: Hs.Exp -> Hs.Exp
           applyExp exp@(Hs.Var name)
               = case doSubst name of
                   Nothing -> exp
                   Just new -> new
           applyExp exp@(Hs.InfixApp exp1 (Hs.QVarOp name) exp2)
               = case doSubst name of
                   Nothing -> exp
                   Just new -> Hs.App (Hs.App new exp1) exp2
           applyExp exp@(Hs.LeftSection exp' (Hs.QVarOp name))
               = case doSubst name of
                   Nothing -> exp
                   Just new -> (Hs.App new exp')
           applyExp exp@(Hs.RightSection (Hs.QVarOp name) exp')
               = case doSubst name of
                   Nothing -> exp
                   Just new -> (Hs.App (Hs.App (Hs.Var (Hs.UnQual (Hs.Ident "flip"))) new) exp')
           applyExp exp = exp

           doSubst :: Hs.QName -> Maybe Hs.Exp
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

           applyExp :: Hs.Exp -> Hs.Exp
           applyExp (Hs.Var name) = Hs.Var (ren name)
           applyExp exp = exp
                      
           applyQOp :: Hs.QOp -> Hs.QOp
           applyQOp (Hs.QVarOp name) = Hs.QVarOp (ren name)
           applyQOp qop = qop
           
           ren :: Hs.QName -> Hs.QName
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
type Renaming = (Hs.QName, Hs.QName)

{-|
  This function generates renamings for all variables given in the
  list to provide fresh names.
-}
freshIdentifiers :: [Hs.QName] -> GensymM [Renaming]
freshIdentifiers qnames
    = do freshs <- mapM genHsQName qnames
         return (zip qnames freshs)

{-|
  This function takes a list of variables (which are supposed to be bound) and a renaming
  and reduces this renaming such that it does not affect bound variables.
-}
shadow :: [Hs.QName] -> [Renaming] -> [Renaming]
shadow boundNs renamings  = filter ((`notElem` boundNs) . fst) renamings

{-|
  This function applies the given renaming to the given variable.
-}
qtranslate :: [Renaming] -> Hs.QName -> Hs.QName
qtranslate renamings qname 
    = fromMaybe qname (lookup qname renamings)

{-|
  This function applies the given renaming to the given unqualified variable.
-}
translate :: [Renaming] -> Hs.Name -> Hs.Name
translate renamings name 
    = let (Hs.UnQual name') = qtranslate renamings (Hs.UnQual name) in name'

{-|
  This function applies the given renaming to all variables in the given
  pattern.
-}
renamePat :: [Renaming] -> Hs.Pat -> Hs.Pat
renamePat renams pat
    = case pat of
        Hs.PVar name                 -> Hs.PVar (translate renams name)
        Hs.PLit lit                  -> Hs.PLit lit
        Hs.PNeg pat                  -> Hs.PNeg (renamePat renams pat)
        Hs.PInfixApp pat1 qname pat2 -> Hs.PInfixApp pat1' qname' pat2'
            where pat1'  = renamePat renams pat1 
                  qname' = qtranslate renams qname
                  pat2'  = renamePat renams pat2
        Hs.PApp qname pats           -> Hs.PApp qname' pats'
            where qname' = qtranslate renams qname
                  pats'  = map (renamePat renams) pats
        Hs.PTuple pats               -> Hs.PTuple (map (renamePat renams) pats)
        Hs.PList  pats               -> Hs.PList (map (renamePat renams) pats)
        Hs.PParen pat                -> Hs.PParen (renamePat renams pat)
        Hs.PWildCard                 -> Hs.PWildCard
        Hs.PAsPat name pat'          -> Hs.PAsPat (translate renams name) (renamePat renams pat')
        Hs.PRec name fields          -> Hs.PRec name fields'
                                       where fields' = map ren fields
                                             ren (Hs.PFieldPat n p) = Hs.PFieldPat n (renamePat renams p)
        _ -> error ("rename.Pat: Fall through: " ++ show pat)

{-|
  This function applies the given renaming to names bound by the given
  Haskell declaration (only type signatures, function and pattern bindings
  are affected).
-}
renameDecl :: [Renaming] -> Hs.Decl -> Hs.Decl
renameDecl renamings decl = 
    case decl of
      Hs.TypeSig loc names typ
          -> Hs.TypeSig loc (map (translate renamings) names) typ
      Hs.FunBind matches
          -> Hs.FunBind (map renMatch matches)
      Hs.PatBind loc pat rhs binds 
          -> Hs.PatBind loc (renamePat renamings pat) rhs binds
      _ -> decl
    where renMatch :: Hs.Match -> Hs.Match
          renMatch (Hs.Match loc name pats rhs binds)
                   = Hs.Match loc (translate renamings name) pats rhs binds
extractVarNs thing
    = let varNs   = [ qn | Hs.Var qn <- universeBi thing ]
          varopNs = [ qn | Hs.QVarOp qn <- universeBi thing ] 
                    ++ [ qn | Hs.QConOp qn <- universeBi thing ]
      in varNs ++ varopNs

{-|
  This function compares the two given declarations w.r.t. the 
  source location.
-}
orderDeclsBySourceLine :: Hs.Decl -> Hs.Decl -> Ordering
orderDeclsBySourceLine decl1 decl2
    = compare (getSourceLine decl1) (getSourceLine decl2) 

getSrcLoc :: Hs.Decl -> SrcLoc
getSrcLoc decl
    = head . sortBy compareLines $ (childrenBi decl :: [SrcLoc])
    where compareLines loc1 loc2 
              = compare (srcLine loc1) (srcLine loc2)


{-|
  This function provides the source line where the given
  declaration is made.
-}
getSourceLine :: Hs.Decl -> Int
getSourceLine decl
    = let srclocs = childrenBi decl :: [SrcLoc]
          lines   = map srcLine srclocs
      in head (sort lines)

showModuleName :: Hs.ModuleName -> String
showModuleName (Hs.ModuleName name) = name


unBang :: Hs.BangType -> Hs.Type
unBang (Hs.UnBangedTy t) = t
unBang (Hs.BangedTy t) = t

flattenRecFields :: [([Hs.Name],Hs.BangType)] -> [(Hs.Name,Hs.Type)]
flattenRecFields = concatMap flatten
    where flatten (ns,bType) = zip ns (replicate (length ns) (unBang bType))
