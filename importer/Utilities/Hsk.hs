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
import Data.Map (Map)
import qualified Data.Map as Map hiding (Map)
import Data.Set (Set)
import qualified Data.Set as Set hiding (Set)
import Array (inRange)
import Char (toLower)

import Data.Generics
import Data.Generics.Basics
import Data.Generics.PlateData

import Control.Monad.Reader

import Language.Haskell.Exts as Hsx

import Importer.Utilities.Misc
import Importer.Utilities.Gensym
import Importer.Utilities.Env


{-|
  The prelude's module name
-}
hsk_prelude :: Hsx.ModuleName
hsk_prelude = Hsx.ModuleName "Prelude"

{-|
  This function takes a constant identifier name and converts it into a
  Haskell expression of a qualified 
-}
prelude_fn :: String -> Hsx.Exp
prelude_fn fn_name = Hsx.Var (Hsx.Qual hsk_prelude (Hsx.Ident fn_name))

{-|
  This function provides the return type of a type. E.g.
  returnType (a -> b -> c) = c
-}
returnType :: Hsx.Type -> Hsx.Type
returnType (Hsx.TyForall _ _ ty) = ty
returnType (Hsx.TyFun _ ty) = ty
returnType (Hsx.TyKind ty _) = ty
returnType ty = ty


{-|
  This function provides the (unqualified) name of the type constructor that constructed
  the given type or nothing if the given type is not a constructor application.
-}
typeConName :: Hsx.Type -> Maybe String
typeConName (Hsx.TyApp (Hsx.TyCon qname) _) =
    case qname of
      Hsx.Qual _ (Hsx.Ident name) -> Just name
      Hsx.UnQual (Hsx.Ident name) -> Just name
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
hsk_apply :: Hsx.Exp -> [Hsx.Exp] -> Hsx.Exp
hsk_apply fn_expr args
    = foldl Hsx.App fn_expr args

{-|
  The Haskell empty list.
-}
hskPNil :: Hsx.Pat
hskPNil = Hsx.PList []

{-|
  The Haskell list constructor. This function takes two Haskell expressions and applies
  the list constructor @(:)@ to it.
-}
hskPCons :: Hsx.Pat -> Hsx.Pat -> Hsx.Pat
hskPCons x y = Hsx.PApp (Special Hsx.Cons) [x, y]

{-|
  The Haskell empty list.
-}
hsk_nil :: Hsx.Exp
hsk_nil             = Hsx.List []

{-|
  The Haskell list constructor. This function takes two Haskell expressions and applies
  the list constructor @(:)@ to it.
-}
hsk_cons :: Hsx.Exp -> Hsx.Exp -> Hsx.Exp
hsk_cons x y        = Hsx.App (Hsx.App (Hsx.Con (Special Hsx.Cons)) x) y

{-|
  The Haskell pair constructor. This function takes two Haskell expressions and applies
  the pair constructor @(,)@ to them.
-}
hskPPair :: Hsx.Pat -> Hsx.Pat -> Hsx.Pat
hskPPair x y = Hsx.PApp (Special (Hsx.TupleCon 2)) [x, y]

{-|
  The Haskell pair constructor. This function takes two Haskell expressions and applies
  the pair constructor @(,)@ to them.
-}
hsk_pair :: Hsx.Exp -> Hsx.Exp -> Hsx.Exp
hsk_pair x y        = Hsx.App (Hsx.App (Hsx.Con (Special (Hsx.TupleCon 2))) x) y

{-|
  The Haskell logical negation. This function takes a Haskell expression and applies
  the negation 'negate' to it.
-}
hsk_negate :: Hsx.Exp -> Hsx.Exp
hsk_negate e        = hsk_apply (prelude_fn "negate") [e]

{-|
  The Haskell if-then-else. This function takes three arguments - condition, if branch, else branch -
  and forms a corresponding if-then-else expression.
-}
hsk_if ::  Hsx.Exp -> Hsx.Exp -> Hsx.Exp -> Hsx.Exp
hsk_if = Hsx.If

{-|
  The Haskell lambda abstraction.
-}
hsk_lambda :: SrcLoc -> [Hsx.Pat] -> Hsx.Exp -> Hsx.Exp
hsk_lambda = Hsx.Lambda

{-|
  The Haskell (ungarded!) case expression.
-}
hsk_case :: SrcLoc -> Hsx.Exp -> [(Hsx.Pat, Hsx.Exp)] -> Hsx.Exp
hsk_case loc e cases
    = Hsx.Case e [ Hsx.Alt loc pat (Hsx.UnGuardedAlt exp) (Hsx.BDecls []) | (pat, exp) <- cases ]

{-|
  This function turns a string into a Haskell name. Depending on the
  actual string it is considered a symbol (cf. 'Hsx.Symbol') or an
  identifier (cf. 'Hsx.Ident').
-}
string2Name :: String -> Hsx.Name
string2Name string = case isSymbol string of
                         True  -> Hsx.Symbol string
                         False -> Hsx.Ident string
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
  E.g.  \"Some.Hsx.ModuleName.Name\" ==> \"Some\/Hsx.ModuleName\/Name\"
-}
module2FilePath :: Hsx.ModuleName -> FilePath
module2FilePath (Hsx.ModuleName name)
    = map (\c -> if c == '.' then '/' else c) name ++ ".hs"

moduleFileLocation :: Hsx.Module -> FilePath
moduleFileLocation (Hsx.Module SrcLoc{srcFilename = file} _ _ _ _ _ _) = file

moduleHierarchyDepth :: Hsx.ModuleName -> Int
moduleHierarchyDepth (Hsx.ModuleName name) = length $ filter (== '.') name

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
extractSuperclassNs :: Hsx.Context -> [Hsx.QName]
extractSuperclassNs ctx = map extract ctx
    where extract (Hsx.ClassA qn _) = qn

{-|
  This function extracts the type declarations of the given list of
  class-internal declarations.
-}
extractMethodSigs :: [Hsx.ClassDecl] -> [Hsx.Decl]
extractMethodSigs class_decls
    = filter isTypeSig (map (\(Hsx.ClsDecl d) -> d) class_decls)
    where isTypeSig (Hsx.TypeSig _ _ _) = True
          isTypeSig _                 = False

{-|
  This function extracts all Haskell names that are affected by the given
  declaration. If the given kind of declaration is not supported an exception
  is thrown.
-}
namesFromDecl :: Hsx.Decl -> [Hsx.QName]
namesFromDecl (Hsx.TypeDecl _ name _ _)        = [Hsx.UnQual name]
namesFromDecl (Hsx.DataDecl _ _ _ name _ _ _)  = [Hsx.UnQual name]
namesFromDecl (Hsx.ClassDecl _ _ name _ _ _)   = [Hsx.UnQual name]
namesFromDecl (Hsx.InstDecl _ _ qname _ _)     = [qname]
namesFromDecl (Hsx.TypeSig _ names _)          = map Hsx.UnQual names
namesFromDecl (Hsx.InfixDecl _ _ _ ops)        = [Hsx.UnQual n | n <- (universeBi ops :: [Hsx.Name])]
namesFromDecl (Hsx.PatBind _ pat _ _)          = bindingsFromPats [pat]
namesFromDecl (Hsx.FunBind (Hsx.Match _ fname _ _ _ : ms ))
                                               = [Hsx.UnQual fname]
namesFromDecl (Hsx.UnknownDeclPragma _ _ _) = []
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
    extractBindingNs :: a -> [Hsx.QName]

{-|
  Lift all instances to lists.
-}
instance HasBindings a => HasBindings [a] where
    extractBindingNs list = concatMap extractBindingNs list

instance HasBindings Hsx.Pat where
    extractBindingNs pattern = bindingsFromPats [pattern]

instance HasBindings Hsx.Decl where
    extractBindingNs decl = bindingsFromDecls [decl] 

instance HasBindings Hsx.Binds where
    extractBindingNs (Hsx.BDecls decls) = extractBindingNs decls
    extractBindingNs (Hsx.IPBinds (Hsx.IPBind loc _ _ : _))
        = error $ srcloc2string loc ++ ": Implicit parameter bindings are not supported!"
    extractBindingNs (Hsx.IPBinds []) = []

instance HasBindings Hsx.Stmt where
    extractBindingNs (Hsx.Qualifier b)         = []
    extractBindingNs (Hsx.Generator _ pat exp) = extractBindingNs pat
    extractBindingNs (Hsx.LetStmt binds)       = extractBindingNs binds



{-|
  This function extracts from the given Haskell pattern a list of all Haskell variables
  that are bound by the pattern.
-}
bindingsFromPats          :: [Hsx.Pat] -> [Hsx.QName]
bindingsFromPats pattern  = [ Hsx.UnQual n | Hsx.PVar n <- universeBi pattern ]
                            ++ [ Hsx.UnQual n | Hsx.PAsPat n _ <- universeBi pattern ]

{-|
  This function extracts the variables bound by the given declaration.
-}
bindingsFromDecls       :: [Hsx.Decl] -> [Hsx.QName]
bindingsFromDecls decls = assert (not (has_duplicates bindings)) bindings
    -- Type signatures do not create new bindings, but simply annotate them.
    where bindings = concatMap namesFromDecl (filter (not . isTypeSig) decls)
          isTypeSig (Hsx.TypeSig _ _ _) = True
          isTypeSig _                 = False


type HskNames = Set Hsx.QName
newtype BindingM a = BindingM (Reader HskNames a)
    deriving (Monad, MonadReader HskNames, Functor)

runBindingM :: BindingM a -> a
runBindingM (BindingM m) = runReader m Set.empty

class BindingMonad m where
    boundNames :: m HskNames
    isBound :: Hsx.QName -> m Bool
    

instance MonadReader HskNames m => BindingMonad m where
    isBound name = ask >>=  (return . Set.member name)
    boundNames = ask

type Subst = Map Hsx.QName Hsx.Exp

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
    where fromExp :: Hsx.Exp -> Envs HskNames
          fromExp (Hsx.Let binds _)
              = let bound = Set.fromList $ extractBindingNs binds
                in Envs [bound,bound]
          fromExp (Hsx.Lambda _ pats _)
              = let bound = Set.fromList $ extractBindingNs pats
                in Envs [Set.empty,bound, bound]
          fromExp (Hsx.MDo stmts)
              = let bound = Set.fromList $ extractBindingNs stmts
                in Envs [bound]
          fromExp (Hsx.ListComp _ stmts)
              = let bound = Set.fromList $ extractBindingNs stmts
                in Envs [bound, Set.empty]
          fromExp exp = uniEloc exp Set.empty
                            
          fromAlt :: Hsx.Alt -> HskNames
          fromAlt (Hsx.Alt _ pat _ _) = Set.fromList $ extractBindingNs pat

          fromDecl :: Hsx.Decl -> HskNames
          fromDecl (Hsx.PatBind _ _ _ whereBinds) = Set.fromList $
                                                       extractBindingNs whereBinds
          fromDecl _ = Set.empty

          fromMatch :: Hsx.Match -> HskNames
          fromMatch (Hsx.Match _ _ pats _ whereBinds)
              = Set.fromList $ 
                extractBindingNs whereBinds ++ extractBindingNs pats

          fromStmts :: [Hsx.Stmt] -> Envs HskNames
          fromStmts [] = Envs []
          fromStmts (Hsx.Generator loc pat exp : _)
              = let bound = Set.fromList $ extractBindingNs pat
                in Envs [Set.empty, bound]
          fromStmts (Hsx.Qualifier _ : _)
              = Envs [Set.empty, Set.empty]
          fromStmts (Hsx.LetStmt binds : _)
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
    where name :: GenericQ (Maybe Hsx.QName)
          name = mkQ Nothing fromExp
                  `extQ`fromQOp
          fromExp :: Hsx.Exp -> Maybe Hsx.QName
          fromExp (Hsx.Var name) = Just name
          fromExp _ = Nothing
                      
          fromQOp :: Hsx.QOp -> Maybe Hsx.QName
          fromQOp (Hsx.QVarOp name) = Just name
          fromQOp _ = Nothing


{-|
  This function extracts names that are implicitly declared, such as data constructors
  and record fields.
-}
extractImplDeclNs :: Hsx.Decl -> HskNames
extractImplDeclNs decl@(Hsx.DataDecl _ _ _ _ _ _ _) =
    everything Set.union (mkQ Set.empty fromConDecl) decl
    where fromConDecl (Hsx.ConDecl name _) = Set.singleton (Hsx.UnQual name)
          fromConDecl (Hsx.RecDecl name fields) = 
              Set.singleton (Hsx.UnQual name) 
                     `Set.union` Set.fromList (map Hsx.UnQual (concatMap fst fields))

extractImplDeclNs _ = Set.empty

{-|
  This function extracts the names of data constructors used
  in patters from the given piece of Haskell syntax.
-}

extractDataConNs :: Data a => a -> HskNames
extractDataConNs node = everything Set.union (mkQ Set.empty fromPat) node
    where fromPat (Hsx.PApp name _) = Set.singleton name
          fromPat (Hsx.PRec name _) = Set.singleton name
          fromPat (Hsx.PInfixApp _ name _) = Set.singleton name
          fromPat _ = Set.empty

{-|
  This function extracts the names of type constructors in the given piece of
  Haskell syntax
-}
extractTypeConNs node = everything Set.union (mkQ Set.empty fromType) node where
  fromType :: Hsx.Type -> HskNames
  fromType (Hsx.TyCon name) = Set.singleton name
  fromType (Hsx.TyVar _) = Set.empty
  fromType (Hsx.TyTuple Hsx.Boxed typs) = Set.unions (map fromType typs)
  fromType (Hsx.TyFun typ1 typ2) = Set.union (fromType typ1) (fromType typ2)
  fromType (Hsx.TyForall _ _ typ)  = fromType typ
  fromType (Hsx.TyApp typ1 typ2) = Set.union (fromType typ1) (fromType typ2)
  fromType typ = error ("extractTypeConNs: bad type " ++ show typ)

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
    where fromPat :: Hsx.PatField -> HskNames
          fromPat (Hsx.PFieldPat field _) = Set.singleton field
          fromExp :: Hsx.FieldUpdate -> HskNames
          fromExp (Hsx.FieldUpdate field _) = Set.singleton field

applySubst :: Subst -> GenericT
applySubst subst node = runBindingM $ everywhereEnv boundNamesEnv (applySubstLocal subst) node

applySubstLocal :: Subst -> GenericM BindingM
applySubstLocal subst node =
    do bound <- boundNames
       let apply :: GenericT
           apply = mkT applyExp

           applyExp :: Hsx.Exp -> Hsx.Exp
           applyExp exp@(Hsx.Var name)
               = case doSubst name of
                   Nothing -> exp
                   Just new -> new
           applyExp exp@(Hsx.InfixApp exp1 (Hsx.QVarOp name) exp2)
               = case doSubst name of
                   Nothing -> exp
                   Just new -> Hsx.App (Hsx.App new exp1) exp2
           applyExp exp@(Hsx.LeftSection exp' (Hsx.QVarOp name))
               = case doSubst name of
                   Nothing -> exp
                   Just new -> (Hsx.App new exp')
           applyExp exp@(Hsx.RightSection (Hsx.QVarOp name) exp')
               = case doSubst name of
                   Nothing -> exp
                   Just new -> (Hsx.App (Hsx.App (Hsx.Var (Hsx.UnQual (Hsx.Ident "flip"))) new) exp')
           applyExp exp = exp

           doSubst :: Hsx.QName -> Maybe Hsx.Exp
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

           applyExp :: Hsx.Exp -> Hsx.Exp
           applyExp (Hsx.Var name) = Hsx.Var (ren name)
           applyExp exp = exp
                      
           applyQOp :: Hsx.QOp -> Hsx.QOp
           applyQOp (Hsx.QVarOp name) = Hsx.QVarOp (ren name)
           applyQOp qop = qop
           
           ren :: Hsx.QName -> Hsx.QName
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
type Renaming = (Hsx.QName, Hsx.QName)

{-|
  This function generates renamings for all variables given in the
  list to provide fresh names.
-}
freshIdentifiers :: [Hsx.QName] -> GensymM [Renaming]
freshIdentifiers qnames
    = do freshs <- mapM genHsQName qnames
         return (zip qnames freshs)

{-|
  This function takes a list of variables (which are supposed to be bound) and a renaming
  and reduces this renaming such that it does not affect bound variables.
-}
shadow :: [Hsx.QName] -> [Renaming] -> [Renaming]
shadow boundNs renamings  = filter ((`notElem` boundNs) . fst) renamings

{-|
  This function applies the given renaming to the given variable.
-}
qtranslate :: [Renaming] -> Hsx.QName -> Hsx.QName
qtranslate renamings qname 
    = fromMaybe qname (lookup qname renamings)

{-|
  This function applies the given renaming to the given unqualified variable.
-}
translate :: [Renaming] -> Hsx.Name -> Hsx.Name
translate renamings name 
    = let (Hsx.UnQual name') = qtranslate renamings (Hsx.UnQual name) in name'

{-|
  This function applies the given renaming to all variables in the given
  pattern.
-}
renamePat :: [Renaming] -> Hsx.Pat -> Hsx.Pat
renamePat renams pat
    = case pat of
        Hsx.PVar name                 -> Hsx.PVar (translate renams name)
        Hsx.PLit lit                  -> Hsx.PLit lit
        Hsx.PNeg pat                  -> Hsx.PNeg (renamePat renams pat)
        Hsx.PInfixApp pat1 qname pat2 -> Hsx.PInfixApp pat1' qname' pat2'
            where pat1'  = renamePat renams pat1 
                  qname' = qtranslate renams qname
                  pat2'  = renamePat renams pat2
        Hsx.PApp qname pats           -> Hsx.PApp qname' pats'
            where qname' = qtranslate renams qname
                  pats'  = map (renamePat renams) pats
        Hsx.PTuple pats               -> Hsx.PTuple (map (renamePat renams) pats)
        Hsx.PList  pats               -> Hsx.PList (map (renamePat renams) pats)
        Hsx.PParen pat                -> Hsx.PParen (renamePat renams pat)
        Hsx.PWildCard                 -> Hsx.PWildCard
        Hsx.PAsPat name pat'          -> Hsx.PAsPat (translate renams name) (renamePat renams pat')
        Hsx.PRec name fields          -> Hsx.PRec name fields'
                                       where fields' = map ren fields
                                             ren (Hsx.PFieldPat n p) = Hsx.PFieldPat n (renamePat renams p)
        _ -> error ("rename.Pat: Fall through: " ++ show pat)

{-|
  This function applies the given renaming to names bound by the given
  Haskell declaration (only type signatures, function and pattern bindings
  are affected).
-}
renameDecl :: [Renaming] -> Hsx.Decl -> Hsx.Decl
renameDecl renamings decl = 
    case decl of
      Hsx.TypeSig loc names typ
          -> Hsx.TypeSig loc (map (translate renamings) names) typ
      Hsx.FunBind matches
          -> Hsx.FunBind (map renMatch matches)
      Hsx.PatBind loc pat rhs binds 
          -> Hsx.PatBind loc (renamePat renamings pat) rhs binds
      _ -> decl
    where renMatch :: Hsx.Match -> Hsx.Match
          renMatch (Hsx.Match loc name pats rhs binds)
                   = Hsx.Match loc (translate renamings name) pats rhs binds
extractVarNs thing
    = let varNs   = [ qn | Hsx.Var qn <- universeBi thing ]
          varopNs = [ qn | Hsx.QVarOp qn <- universeBi thing ] 
                    ++ [ qn | Hsx.QConOp qn <- universeBi thing ]
      in varNs ++ varopNs

{-|
  This function compares the two given declarations w.r.t. the 
  source location.
-}
orderDeclsBySourceLine :: Hsx.Decl -> Hsx.Decl -> Ordering
orderDeclsBySourceLine decl1 decl2
    = compare (getSourceLine decl1) (getSourceLine decl2) 

getSrcLoc :: Hsx.Decl -> SrcLoc
getSrcLoc decl
    = head . sortBy compareLines $ (childrenBi decl :: [SrcLoc])
    where compareLines loc1 loc2 
              = compare (srcLine loc1) (srcLine loc2)


{-|
  This function provides the source line where the given
  declaration is made.
-}
getSourceLine :: Hsx.Decl -> Int
getSourceLine decl
    = let srclocs = childrenBi decl :: [SrcLoc]
          lines   = map srcLine srclocs
      in head (sort lines)

showModuleName :: Hsx.ModuleName -> String
showModuleName (Hsx.ModuleName name) = name


unBang :: Hsx.BangType -> Hsx.Type
unBang (Hsx.UnBangedTy t) = t
unBang (Hsx.BangedTy t) = t

flattenRecFields :: [([Hsx.Name],Hsx.BangType)] -> [(Hsx.Name,Hsx.Type)]
flattenRecFields = concatMap flatten
    where flatten (ns,bType) = zip ns (replicate (length ns) (unBang bType))
