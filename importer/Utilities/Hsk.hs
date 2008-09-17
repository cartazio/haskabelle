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
     -- * Functions
      srcloc2string,
      extractBindingNs,
      letify,
      freshIdentifiers,
      bindingsFromDecls,
      renameFreeVars,
      renameHsDecl,
      isFreeVar,
      bindingsFromPats,
      extractFreeVarNs,
      orderDeclsBySourceLine,
      renameHsPat,
      module2FilePath,
      namesFromHsDecl,
      string2HsName,
      extractSuperclassNs,
      extractMethodSigs,
      hsk_nil,
      hsk_cons,
      hsk_pair,
      hsk_negate,
      isHaskellSourceFile
    ) where
  
import Maybe
import List (sort)
import Array (inRange)
import Char (toLower)

import Control.Monad.State
import Data.Generics.Basics
import Data.Generics.PlateData
import Language.Haskell.Exts


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
  declaration. If the given kind of declaration is not supported 'Nothing' is
  returned.
-}
namesFromHsDecl :: HsDecl -> Maybe [HsQName]
namesFromHsDecl (HsTypeDecl _ name _ _)        = Just [UnQual name]
namesFromHsDecl (HsDataDecl _ _ _ name _ _ _)  = Just [UnQual name]
namesFromHsDecl (HsClassDecl _ _ name _ _ _)   = Just [UnQual name]
namesFromHsDecl (HsInstDecl _ _ qname _ _)     = Just [qname]
namesFromHsDecl (HsTypeSig _ names _)          = Just (map UnQual names)
namesFromHsDecl (HsInfixDecl _ _ _ ops)        = Just [UnQual n | n <- (universeBi ops :: [HsName])]
namesFromHsDecl (HsPatBind _ pat _ _)          = case bindingsFromPats [pat] of [] -> Nothing
                                                                                bs -> Just bs
namesFromHsDecl (HsFunBind (m:ms))             = case m of 
                                                   HsMatch _ fname _ _ _ -> Just [UnQual fname]
namesFromHsDecl _                              = Nothing

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
    where bindings = concatMap (fromJust . namesFromHsDecl) (filter (not . isTypeSig) decls)
          isTypeSig (HsTypeSig _ _ _) = True
          isTypeSig _                 = False

{-|
  Instances of this class are supposed to be pieces of Haskell syntax that can be 
  decorated with a let expression
-}
class Letifiable a where
    {-|
      Instance declaration are supposed to define only this method. This function is used
      by the 'letify' default definition in the case the list of bindings is non-empty.
      This approach avoids unnecessary syntax clutter
     -}
    letify' :: HsBinds -> a -> a
    {-|
      This function decorates the given the given Haskell syntax element with a let expression
      using the given bindings.
     -}
    letify  :: HsBinds -> a -> a
    letify (HsBDecls []) body = body
    letify bindings body      = letify' bindings body

instance Letifiable HsExp where
    letify' bindings body = HsLet bindings body

instance Letifiable HsRhs where
    letify' bindings (HsUnGuardedRhs body)  = HsUnGuardedRhs (letify bindings body)


{-|
  This type is used to describe renamings of variables.
-}
type Renaming = (HsQName, HsQName)

{-|
  This function generates renamings for all variables given in the
  list to provide fresh names.
-}
freshIdentifiers :: [HsQName] -> State GensymCount [Renaming]
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
  This function applies the given renaming to the given qualified operator.
-}
qoptranslate :: [Renaming] -> HsQOp -> HsQOp
qoptranslate renamings qop
    = case qop of HsQVarOp qname -> HsQVarOp (qtranslate renamings qname)
                  HsQConOp qname -> HsQConOp (qtranslate renamings qname)

{-|
  This function applies the given renaming to the given unqualified operator.
-}
optranslate :: [Renaming] -> HsOp -> HsOp
optranslate renamings op
    = case op of HsVarOp qname -> HsVarOp (translate renamings qname)
                 HsConOp qname -> HsConOp (translate renamings qname)

{-|
  ???
-}
not_supported_conversion :: (Show a) => [Char] -> a -> b
not_supported_conversion ctx junk
    = error ("renameFreeVars (" ++ ctx ++ "): Fall through: " ++ show junk)


{-|
  Instances of this class are supposed to be pieces of Haskell syntax that allow
  variable renamings to be applied on them.
 
  Note: Despite the name it is plain renaming of unbound variables. No alpha-conversion!
-}
class AlphaConvertable a where
    renameFreeVars :: [Renaming] -> a -> a

instance AlphaConvertable HsOp where
    renameFreeVars renams op
        = case op of HsVarOp name -> HsVarOp (translate renams name)
                     HsConOp name -> HsConOp (translate renams name)

instance AlphaConvertable HsExp where
    renameFreeVars renams hsexp
        = case hsexp of
            HsVar qname -> HsVar (qtranslate renams qname)
            HsCon qname -> HsVar (qtranslate renams qname)
            HsLit lit   -> HsLit lit
            HsInfixApp e1 qop e2
                -> HsInfixApp e1' qop' e2'
                     where e1'  = renameFreeVars renams e1
                           qop' = qoptranslate renams qop
                           e2'  = renameFreeVars renams e2
            HsLeftSection e qop
                -> HsLeftSection e' qop'
                     where e'   = renameFreeVars renams e
                           qop' = qoptranslate renams qop
            HsRightSection qop e
                -> HsRightSection qop' e'
                     where e'   = renameFreeVars renams e
                           qop' = qoptranslate renams qop
            HsLambda loc pats body
                -> HsLambda loc pats body'
                     where body' = let boundNs = bindingsFromPats pats
                                   in renameFreeVars (shadow boundNs renams) body
            HsCase exp alternatives
                -> HsCase exp' alternatives'
                     where declNs        = bindingsFromDecls (childrenBi alternatives :: [HsDecl])
                           renams'       = shadow declNs renams
                           exp'          = renameFreeVars renams' exp
                           alternatives' = map (renameFreeVars renams') alternatives
            HsLet (HsBDecls decls) body 
                -> HsLet (HsBDecls decls') body'
                      where declNs  = bindingsFromDecls decls
                            renams' = shadow declNs renams
                            body'   = renameFreeVars renams' body
                            decls'  = map (renameFreeVars renams') decls
            HsRecConstr qname updates
                -> HsRecConstr qname updates
            HsRecUpdate exp updates
                -> HsRecUpdate (renameFreeVars renams exp) updates
            HsListComp e stmts
                -> HsListComp e' stmts'
                   where stmts'  = renameFreeVars renams stmts
                         boundNs = concatMap extractBindingNs stmts
                         renams' = shadow boundNs renams
                         e'      = renameFreeVars renams' e

            exp -> assert (isTriviallyDescendable exp)
                     $ descend (renameFreeVars renams :: HsExp -> HsExp) exp
{-|
  ???
-}
isTriviallyDescendable :: HsExp -> Bool
isTriviallyDescendable hsexp 
    = case hsexp of
        HsApp      _ _   -> True
        HsNegApp   _     -> True
        HsIf       _ _ _ -> True
        HsTuple    _     -> True
        HsList     _     -> True
        HsParen    _     -> True
        _                -> False -- rest is not supported at the moment.



instance AlphaConvertable HsDecl where
    renameFreeVars renams hsdecl
        = case hsdecl of
            HsFunBind matchs        -> HsFunBind $ map (renameFreeVars renams) matchs
            HsTypeSig loc names typ -> HsTypeSig loc names typ
            HsPatBind loc pat (HsUnGuardedRhs body) binds
                -> HsPatBind loc pat (HsUnGuardedRhs body') binds'
                      where (HsLet binds' body') = renameFreeVars renams' (HsLet binds body)
                            renams' = shadow (bindingsFromPats [pat]) renams
            HsClassDecl loc ctx classN varNs fundeps class_decls
                -> HsClassDecl loc ctx classN varNs fundeps decls'
                      where decls'  = map (renameFreeVars renams') class_decls
                            renams' = shadow [UnQual classN] renams
            HsInstDecl loc ctx qname tys inst_decls
                -> HsInstDecl loc ctx qname tys decls'
                      where decls'  = map (renameFreeVars renams') inst_decls
                            renams' = shadow [qname] renams
            _   -> not_supported_conversion "HsDecl" hsdecl

instance AlphaConvertable HsClassDecl where
    renameFreeVars renams (HsClsDecl decl)
        = HsClsDecl (renameFreeVars renams decl)
    renameFreeVars _ junk = not_supported_conversion "HsClassDecl" junk

instance AlphaConvertable HsInstDecl where
    renameFreeVars renams (HsInsDecl decl)
        = HsInsDecl (renameFreeVars renams decl) 
    renameFreeVars _ junk = not_supported_conversion "HsClassDecl" junk

instance AlphaConvertable HsAlt where
    renameFreeVars renams hsalt@(HsAlt _ pat _ _)
        = fromHsPatBind (renameFreeVars renams (toHsPatBind hsalt))
          where
            toHsPatBind :: HsAlt -> HsDecl
            toHsPatBind (HsAlt loc pat guards wherebinds)
                = HsPatBind loc pat (guards2rhs guards) wherebinds
                  where guards2rhs (HsUnGuardedAlt body) = HsUnGuardedRhs body

            fromHsPatBind (HsPatBind loc pat rhs wherebinds)
                = HsAlt loc pat (rhs2guards rhs) wherebinds
                  where rhs2guards (HsUnGuardedRhs body) = HsUnGuardedAlt body


instance AlphaConvertable HsMatch where
    renameFreeVars renams (HsMatch loc name pats rhs (HsBDecls decls))
        = HsMatch loc name pats rhs' (HsBDecls decls')
      where patNs  = extractBindingNs pats
            declNs = extractBindingNs decls 
            rhs'   = renameFreeVars (shadow ([UnQual name] ++ patNs ++ declNs) renams) rhs
            decls' = map (renameFreeVars (shadow (UnQual name : declNs) renams)) decls

instance AlphaConvertable HsBinds where
    renameFreeVars renams (HsBDecls decls) = HsBDecls decls'
        where declNs = extractBindingNs decls
              decls' = map (renameFreeVars (shadow declNs renams)) decls
    renameFreeVars _ junk = not_supported_conversion "HsBinds" junk

instance AlphaConvertable HsRhs where
    renameFreeVars renams (HsUnGuardedRhs exp)
        = HsUnGuardedRhs (renameFreeVars renams exp)
    renameFreeVars _ junk = not_supported_conversion "HsBinds" junk

instance AlphaConvertable [HsStmt] where
    renameFreeVars renams [] = []
    renameFreeVars renams (HsQualifier b : rest)
        = HsQualifier (renameFreeVars renams b) : renameFreeVars renams rest
    renameFreeVars renams (HsGenerator loc pat exp : rest)
        = let exp'    = renameFreeVars renams exp
              renams' = shadow (extractBindingNs pat) renams
              rest'   = renameFreeVars renams' rest
          in HsGenerator loc pat exp' : rest'
    renameFreeVars renams (HsLetStmt binds : rest)
        = let (HsLet binds' _)  =  renameFreeVars renams (HsLet binds (HsLit (HsInt 42)))
              renams'           =  shadow (extractBindingNs binds') renams
              rest'             =  renameFreeVars renams' rest
          in HsLetStmt binds' : rest'

{-|
  This function applies the given renaming to the variables bound by the given
  declaration.
-}
renameHsDecl :: [Renaming] -> HsDecl -> HsDecl

renameHsDecl renams (HsTypeDecl loc tyconN tyvarNs typ)
    = HsTypeDecl loc (translate renams tyconN) tyvarNs typ

renameHsDecl renams (HsDataDecl loc kind context tyconN tyvarNs condecls derives)
    = HsDataDecl loc kind context (translate renams tyconN) tyvarNs condecls derives

renameHsDecl renams (HsInfixDecl loc assoc prio ops)
    = HsInfixDecl loc assoc prio (map (optranslate renams) ops)

renameHsDecl renams (HsTypeSig loc names typ)
    = HsTypeSig loc (map (translate renams) names) typ

renameHsDecl renams (HsFunBind matchs)
    = HsFunBind (map rename matchs)
      where rename (HsMatch loc name pats rhs wbinds)
                = HsMatch loc (translate renams name) pats rhs wbinds

renameHsDecl renams (HsPatBind loc pat rhs wbinds)
    = HsPatBind loc (renameHsPat renams pat) rhs wbinds

renameHsDecl renams (HsClassDecl loc ctx classN varNs fundeps class_decls)
    = HsClassDecl loc ctx (translate renams classN) varNs fundeps class_decls

renameHsDecl renams (HsInstDecl loc ctx classqN tys inst_decls)
    = HsInstDecl loc ctx (qtranslate renams classqN) tys inst_decls

renameHsDecl _ junk = error ("renameHsDecl: Fall through: " ++ show junk)

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


-- Kludge.
--

{-|
  ???
-}
isFreeVar :: (Data from , AlphaConvertable from) =>
             HsQName -> from -> Bool
isFreeVar (Special _) _ = False
isFreeVar qname body
    = occurs qname body && let body' = renameFreeVars (evalGensym 9999 (freshIdentifiers [qname])) body
                           in not (occurs qname body')
    where occurs qname body 
              = let varNs   = [ qn | HsVar qn <- universeBi body ]
                    varopNs = [ qn | HsQVarOp qn <- universeBi body ] 
                              ++ [ qn | HsQConOp qn <- universeBi body ]
                in qname `elem` varNs || qname `elem` varopNs


{-|
  ???
-}
extractFreeVarNs :: (Data from, AlphaConvertable from) =>
                    from -> [HsQName]
extractFreeVarNs thing
    = filter (flip isFreeVar thing) (universeBi thing :: [HsQName])

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

------------------------------------------------------------------
-- In the following we define predicates that define the supported
-- syntax fragment 
------------------------------------------------------------------

isValidInput_module :: HsModule -> [String]
isValidInput_module (HsModule _loc _name _exp _imp decls) = concatMap isValidInput_topDecl decls

isValidInput_topDecl :: HsDecl -> [String]
-- generally supported
isValidInput_topDecl (HsTypeDecl _loc _name _args _type) = []
isValidInput_topDecl (HsDataDecl _loc _dataOrNew _cxt _name _args _constrDecls _deriving) = []
isValidInput_topDecl (HsInfixDecl _loc _assoc _prec _ops) = []
isValidInput_topDecl (HsClassDecl _loc _cxt _name _args _funcDeps _decls) = []
isValidInput_topDecl (HsInstDecl _loc _cxt _name _args _decls) = []
isValidInput_topDecl (HsDerivDecl  _loc _cxt _name _args) = []
isValidInput_topDecl (HsTypeSig _loc _names _type) = []
isValidInput_topDecl (HsFunBind _matches) = []
isValidInput_topDecl (HsPatBind _loc _pat _rhs _whereBinds) = []
-- generally unsupported
isValidInput_topDecl (HsGDataDecl loc _dataOrNew _cxt _name _args _kind _gadtDecls) = [(srcloc2string loc) ++ ":\nGADTs are not supported"]
isValidInput_topDecl (HsTypeFamDecl  loc _name _arg _kind) = [(srcloc2string loc) ++ ":\nType family declarations are not supported"]
isValidInput_topDecl (HsDataFamDecl  loc _cxt _name _args _kind) = [(srcloc2string loc) ++ ":\nDatatype family declarations are not supported"]
isValidInput_topDecl (HsTypeInsDecl  loc _type1 _type2) = [(srcloc2string loc) ++ ":\nType ins declarations are not supported"]
isValidInput_topDecl (HsDataInsDecl  loc _dataOrNew _type _constrDecls _deriving) =  [(srcloc2string loc) ++ ":\nDatatype ins declarations are not supported"]
isValidInput_topDecl (HsGDataInsDecl loc _dataOrNew _type _kind _gadtDecls) = [(srcloc2string loc) ++ ":\nGADT ins declarations are not supported"]
isValidInput_topDecl (HsDefaultDecl  loc _types) = [(srcloc2string loc) ++ ":\nDefault type declarations are not supported"]
isValidInput_topDecl (HsSpliceDecl   loc _splice) = [(srcloc2string loc) ++ ":\nSplice declarations are not supported"]
isValidInput_topDecl (HsForImp loc _callConv _safety _string _name _type) =  [(srcloc2string loc) ++ ":\nFor imps are not supported"]
isValidInput_topDecl (HsForExp loc _callConv _string _name _type) = [(srcloc2string loc) ++ ":\nFor exps are not supported"]




