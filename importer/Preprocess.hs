{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen
-}

module Importer.Preprocess
    (
     preprocessHsModule
    )where

import Maybe
import List
import Control.Monad.State
import Language.Haskell.Exts

import Data.Generics.Biplate
import Data.Generics.Str

import Importer.Utilities.Misc -- (concatMapM, assert)
import Importer.Utilities.Hsk
import Importer.Utilities.Gensym

import Importer.Test.Generators

import qualified Importer.Msg as Msg

import Importer.Adapt.Raw (used_const_names, used_thy_names)

import Test.QuickCheck
        
{-|
  This function preprocesses the given Haskell module to make things easier for the
  conversion.
-}
preprocessHsModule :: HsModule -> HsModule
preprocessHsModule (HsModule loc modul exports imports topdecls)
    = HsModule loc modul exports imports topdecls4
      where topdecls1    = map deguardify_HsDecl topdecls
            (topdecls2, gensymcount) 
                         = runGensym 0 (runDelocalizer (concatMapM delocalize_topdecl topdecls1))
            topdecls3    = map normalizePatterns_HsDecl topdecls2
            topdecls4    = evalGensym gensymcount (mapM normalizeNames_HsDecl topdecls3) 
--          modul'      = (let (Module n) = modul in Module (normalizeModuleName n))


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
type DelocalizerM a = StateT [HsQName] (State GensymCount) a

{-|
  This function modifies the given delocaliser monad by adding the given
  list of variables to the list of bound variables before and restoring
  the original list afterwards.
-}
withAddBindings :: [HsQName] -> DelocalizerM v -> DelocalizerM v
withAddBindings names m = do
  old <- getBindings
  put (names ++ old)
  r <- m
  put old
  return r

{-|
  This function extracts the bindings from the @DelocalizerM@'s state.x
-}
getBindings :: DelocalizerM [HsQName]
getBindings = get

{-|
  This function executes the given delocaliser monad starting with an
  empty list of bound variables.
-}
runDelocalizer :: DelocalizerM [HsDecl] -> State GensymCount [HsDecl]
runDelocalizer d = evalStateT d []

{-|
  This is the main function. It takes a declaration, and returns a list
  of itself and all local declarations that were delocalised.
 -}
delocalize_topdecl  :: HsDecl  -> DelocalizerM [HsDecl]
delocalize_topdecl decl 
    = do (decl', localdecls) <- delocalize_HsDecl decl
         return (localdecls ++ [decl'])

------------------------------------------------------------------------------
-- Helper functions. Return a properly alpha-converted version of their argument 
-- plus a list of globalized declarations.
------------------------------------------------------------------------------

{-|
  This function delocalises all local declarations in the given Haskell declaration.
  It returns the delocalised local declarations and the properly alpha-converted form
  of the input.
-}
delocalize_HsDecl      :: HsDecl      -> DelocalizerM (HsDecl,     [HsDecl])
delocalize_HsDecl (HsPatBind loc pat rhs wbinds)
    = withAddBindings (extractBindingNs pat)
      $ do (rhs', localdecls)  <- delocalize_HsRhs (letify wbinds rhs)
           return (HsPatBind loc pat rhs' (HsBDecls []), localdecls)
delocalize_HsDecl (HsFunBind matchs)
    = do (matchs', localdecls) <- liftM (\(xs, ys) -> (xs, concat ys))
                                  $ mapAndUnzipM delocalize_HsMatch matchs
         return (HsFunBind matchs', localdecls)
delocalize_HsDecl (HsClassDecl loc ctx classN varNs fundeps class_decls)
    = do (decls', localdeclss) <- mapAndUnzipM delocalize_HsClassDecl class_decls
         return (HsClassDecl loc ctx classN varNs fundeps decls', concat localdeclss)
delocalize_HsDecl (HsInstDecl loc ctx qname tys inst_decls)
    = do (decls', localdeclss) <- mapAndUnzipM delocalize_HsInstDecl inst_decls
         return (HsInstDecl loc ctx qname tys decls', concat localdeclss)
delocalize_HsDecl decl  = assert (check decl) $ return (decl,[])
    -- Safety check to make sure we didn't miss anything.
    where check decl   = and [null (universeBi decl :: [HsBinds]),
                              null [ True | HsLet _ _ <- universeBi decl ]]
          isHsLet expr = case expr of HsLet _ _ -> True; _ -> False

{-|
  The argument is supposed to be a TypeSig here (will be checked later in "Importer.Convert").
  It will be explicitly delocalised (i.e. included in the returned list) to make the later
  process aware of its presence. (The stuff defined by a Class will be used  by other
  functions, and the later process will barf on things it doesn't know about.
-}
delocalize_HsClassDecl :: HsClassDecl -> DelocalizerM (HsClassDecl,[HsDecl])
delocalize_HsClassDecl (HsClsDecl decl) 
    = do (decl', localdecls) <- delocalize_HsDecl decl
         return (HsClsDecl decl', localdecls ++ [decl'])

{-|
  This function delocalises all local declarations in the given instance-internal declaration.
  It returns the delocalised local declarations and the properly alpha-converted form
  of the input. The input is supposed to be a function binding.
-}
delocalize_HsInstDecl  :: HsInstDecl  -> DelocalizerM (HsInstDecl, [HsDecl])
delocalize_HsInstDecl (HsInsDecl decl)
    = do (decl', localdecls) <- delocalize_HsDecl decl
         return (HsInsDecl decl', localdecls)


{-|
  This function delocalises all local declarations in the given function binding clause.
  It returns the delocalised local declarations and the properly alpha-converted form
  of the input.
-}
delocalize_HsMatch     :: HsMatch     -> DelocalizerM (HsMatch,    [HsDecl])
delocalize_HsMatch (HsMatch loc name pats rhs wbinds)
    = withAddBindings (extractBindingNs pats)
      $ do (rhs', localdecls)  <- delocalize_HsRhs (letify wbinds rhs)
           return (HsMatch loc name pats rhs' (HsBDecls []), localdecls)


-- This . This is necessary, beacuse the body of the caller 
-- where these where-binds apply to, must also be alpha converted.
{-|
  Here the actual renaming takes place. The given local bindings (NOTE: implicit parameters are not 
  supported) are delocalised. Additionally, the renamings that reflect how the bindings
  were renamed are returned.
-}
delocalize_HsBinds :: HsBinds -> DelocalizerM (HsBinds, [HsDecl], [Renaming])
delocalize_HsBinds (HsBDecls localdecls)
    -- First rename the bindings that are established by LOCALDECLS to fresh identifiers,
    -- then also rename all occurences (i.e. recursive invocations) of these bindings
    -- within the body of the declarations.
    = do renamings    <- lift (freshIdentifiers (bindingsFromDecls localdecls))
         let localdecls' = map (renameFreeVars renamings . renameHsDecl renamings) localdecls
         localdecls'' <- concatMapM delocalize_topdecl localdecls'
         closedVarNs  <- getBindings
         return (HsBDecls [], checkForClosures closedVarNs localdecls'', renamings)

{-|
  This function delocalises local declarations in the given RHS. It returns the delocalised
  declarations together with the properly alpha-converted input.
-}
delocalize_HsRhs       :: HsRhs       -> DelocalizerM (HsRhs,      [HsDecl])
delocalize_HsRhs (HsUnGuardedRhs exp)
    = do (exp', decls) <- delocalize_HsExp exp
         return (HsUnGuardedRhs exp', decls)
delocalize_HsRhs (HsGuardedRhss guards)
    = do (guards', declss) <- mapAndUnzipM delocalize_HsGuardedRhs guards
         return (HsGuardedRhss guards', concat declss)
{-|
  This function delocalises local declarations in the given RHS guard clause. It returns the delocalised
  declarations together with the properly alpha-converted input.
-}
delocalize_HsGuardedRhs :: HsGuardedRhs -> DelocalizerM (HsGuardedRhs, [HsDecl])
delocalize_HsGuardedRhs (HsGuardedRhs loc stmts clause_body)
    = do (clause_body', decls) <- delocalize_HsExp clause_body
         return (HsGuardedRhs loc stmts clause_body', decls)

{-|
  This function delocalises the local declarations of the given case expression alternative.
  It returns the delocalised declarations along with the properly alpha-converted input.
-}
delocalize_HsAlt       :: HsAlt       -> DelocalizerM (HsAlt,      [HsDecl])
delocalize_HsAlt (HsAlt loc pat (HsUnGuardedAlt body) wbinds)
    = withAddBindings (extractBindingNs pat)
        $ do (body', localdecls) <- delocalize_HsExp (letify wbinds body)
             return (HsAlt loc pat (HsUnGuardedAlt body') (HsBDecls []), localdecls)                              

{-|
  This function delocalises local declarations in the given expression (i.e.
  let bindings). It returns the delocalised declarations along with the properly
  alpha-converted input.
 -}
delocalize_HsExp       :: HsExp       -> DelocalizerM (HsExp,      [HsDecl])
delocalize_HsExp (HsLet binds body)
    -- The let expression in Isabelle/HOL supports simple pattern matching. So we
    -- differentiate between pattern and other (e.g. function) bindings; the first
    -- ones are kept, the latter ones are converted to global bindings.
    = let (patBinds, otherBinds) = splitPatBinds binds
      in withAddBindings (extractBindingNs patBinds)
         $ do (otherBinds', decls, renamings) <- delocalize_HsBinds otherBinds
              (body', moredecls)              <- delocalize_HsExp (renameFreeVars renamings body)
              return (letify (renameFreeVars renamings patBinds) body', decls ++ moredecls)

delocalize_HsExp (HsCase body alternatives)
    = do (body', localdecls)    <- delocalize_HsExp body
         (alternatives', decls) <- liftM (\(xs, ys) -> (xs, concat ys))
                                      $ mapAndUnzipM delocalize_HsAlt alternatives
         return (HsCase body' alternatives', localdecls ++ decls)
    where

delocalize_HsExp exp = descendM (\(e, ds) -> do (e', ds') <- delocalize_HsExp e
                                                return (e', ds++ds')) 
                         (exp, [])

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
              = partition (let patNs = concatMap (fromJust . namesFromHsDecl) patDecls'
                           in \sig -> head (fromJust (namesFromHsDecl sig)) `elem` patNs)
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


-- Closures over variables can obviously not be delocalized, as for instance
--
--    foo x = let bar y = y * x 
--            in bar 42
--
-- would otherwise be delocalized to the bogus
--
--    bar0 y = y * x
--
--    foo x  = bar0 42
--

checkForClosures :: [HsQName] -> [HsDecl] -> [HsDecl]
checkForClosures closedNs decls 
    = map check decls
    where check decl = let loc:_  = childrenBi decl :: [SrcLoc]
                           freeNs = filter (flip isFreeVar decl) closedNs
                       in if (null freeNs) then decl 
                                           else error (Msg.free_vars_found loc freeNs)

---- Normalization of As-patterns

normalizePatterns_HsDecl :: HsDecl -> HsDecl

normalizePatterns_HsDecl (HsFunBind matchs)
    = HsFunBind (map normalizePatterns_HsMatch matchs)
    where
      normalizePatterns_HsMatch (HsMatch loc name pats (HsUnGuardedRhs body) where_binds)
          = let (pats', as_bindings) = unzip (map normalizePattern pats) in
            let body' = normalizePatterns_HsExp (makeCase loc (concat as_bindings) body)
            in HsMatch loc name pats' (HsUnGuardedRhs body') where_binds

normalizePatterns_HsDecl decl 
    = descendBi normalizePatterns_HsExp decl


normalizePatterns_HsExp :: HsExp -> HsExp

normalizePatterns_HsExp (HsCase exp alts)
    = HsCase exp (map normalizePatterns_HsAlt alts)
    where
      normalizePatterns_HsAlt (HsAlt loc pat (HsUnGuardedAlt clause_body) where_binds)
          = let (pat', as_bindings) = normalizePattern pat in
            let clause_body'   = normalizePatterns_HsExp 
                                   $ if (null as_bindings) then clause_body
                                     else (makeCase loc as_bindings clause_body)
                 in HsAlt loc pat' (HsUnGuardedAlt clause_body') where_binds

normalizePatterns_HsExp (HsLambda loc pats body)
    = let (pats', as_bindings) = unzip (map normalizePattern pats) in
      let body' = normalizePatterns_HsExp (makeCase loc (concat as_bindings) body)
      in HsLambda loc pats' body'

normalizePatterns_HsExp exp = descend normalizePatterns_HsExp exp


makeCase :: SrcLoc -> [(HsName, HsPat)] -> HsExp -> HsExp
makeCase _ [] body = body
makeCase loc bindings body
    = let (names, pats) = unzip bindings
      in HsCase (HsTuple (map (HsVar . UnQual) names))
           [HsAlt loc (HsPTuple pats) (HsUnGuardedAlt body) (HsBDecls [])]

normalizePattern :: HsPat -> (HsPat, [(HsName, HsPat)])

normalizePattern p@(HsPVar _)    = (p, [])
normalizePattern p@(HsPLit _)    = (p, [])
normalizePattern p@(HsPWildCard) = (p, [])
normalizePattern (HsPNeg p)      = let (p', as_pats) = normalizePattern p in (HsPNeg p', as_pats)
normalizePattern (HsPParen p)    = let (p', as_pats) = normalizePattern p in (HsPParen p', as_pats)

normalizePattern (HsPAsPat n pat) 
    = (HsPVar n, [(n, pat)])

normalizePattern (HsPTuple pats)  
    = let (pats', as_pats) = unzip (map normalizePattern pats)
      in (HsPTuple pats', concat as_pats)

normalizePattern (HsPList pats)
    = let (pats', as_pats) = unzip (map normalizePattern pats)
      in (HsPList pats', concat as_pats)

normalizePattern (HsPApp qn pats) 
    = let (pats', as_pats) = unzip (map normalizePattern pats)
      in (HsPApp qn pats', concat as_pats)

normalizePattern (HsPInfixApp p1 qn p2)
    = let (p1', as_pats1) = normalizePattern p1
          (p2', as_pats2) = normalizePattern p2
      in (HsPInfixApp p1' qn p2', concat [as_pats1, as_pats2])

normalizePattern p = error ("Pattern not supported: " ++ show p)


---- Normalization of names.
--
-- Function definitions are restricted in Isar/HOL such that names of
-- constants must not be used as a bound variable name in those definitions.
-- 
-- We simply rename all those identifiers.
--

normalizeNames_HsDecl :: HsDecl -> State GensymCount HsDecl

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


---- Deguardification

deguardify_HsDecl :: HsDecl -> HsDecl

deguardify_HsDecl d@(HsFunBind matchs)
    = HsFunBind (map deguardify_HsMatch matchs)
    where deguardify_HsMatch (HsMatch loc name pats rhs where_binds)
              = HsMatch loc name pats (deguardify_HsRhs rhs) (deguardify_HsBinds where_binds)

-- deguardify_HsDecl (HsPatBind)

deguardify_HsDecl decl = descend deguardify_HsDecl (descendBi deguardify_HsExp decl)


deguardify_HsRhs (HsUnGuardedRhs body)
    = HsUnGuardedRhs (deguardify_HsExp body)
deguardify_HsRhs (HsGuardedRhss guards)
    = HsUnGuardedRhs (deguardify_HsGuardedRhss guards)

deguardify_HsBinds (HsBDecls decls)
    = HsBDecls (map deguardify_HsDecl decls)

-- deguardify_HsExp (HsCase)

deguardify_HsExp :: HsExp -> HsExp
deguardify_HsExp exp = descend deguardify_HsExp exp

deguardify_HsAlt (HsAlt loc pat (HsUnGuardedAlt clause_body) wbinds)
    = HsAlt loc pat (HsUnGuardedAlt clause_body) wbinds'
    where wbinds' = deguardify_HsBinds wbinds

deguardify_HsAlt (HsAlt loc pat (HsGuardedAlts guarded_alts) wbinds)
    = let guarded_rhss = map (\(HsGuardedAlt l ss e) -> HsGuardedRhs l ss e) guarded_alts
          wbinds'      = deguardify_HsBinds wbinds
      in HsAlt loc pat (HsUnGuardedAlt (deguardify_HsGuardedRhss guarded_rhss)) wbinds'

deguardify_HsGuardedRhss :: [HsGuardedRhs] -> HsExp
deguardify_HsGuardedRhss guards
    = let (guards', otherwise_expr) = findOtherwiseExpr guards
      in deguardify_HsExp (foldr deguardify otherwise_expr guards')
    where 
      deguardify x@(HsGuardedRhs loc stmts clause) body
          = HsIf (makeGuardExpr stmts) clause body
   
      makeGuardExpr stmts = foldl1 andify (map expify stmts)
          where expify (HsQualifier exp) = exp
                andify e1 e2 = HsInfixApp e1 (HsQVarOp (Qual (Module "Prelude") (HsSymbol "&&"))) e2

      findOtherwiseExpr guards
          = let otherwise_stmt = HsQualifier (HsVar (UnQual (HsIdent "otherwise")))
                true_stmt      = HsQualifier (HsVar (UnQual (HsIdent "True")))
                bottom         = HsVar (Qual (Module "Prelude") (HsSymbol "_|_"))
            in case break (\(HsGuardedRhs _ stmts _) -> stmts `elem` [[otherwise_stmt], [true_stmt]])
                          guards of
                 (guards', (HsGuardedRhs _ _ last_expr):_) -> (guards', last_expr)
                 (guards', [])                             -> (guards', bottom)


-- expandListComprehensions_HsDecl :: HsDecl -> HsDecl
-- expandListComprehensions_HsDecl decl
--     = descendBi expandListComprehensions_HsExp decl

-- expandListComprehensions_HsExp :: HsExp -> HsExp
-- expandListComprehensions_HsExp expr
--     = case expr of
--         HsListComp e stmts -> descend expandListComprehensions_HsExp 
--                                 (expandListCompr e stmts)
--         _ -> descend expandListComprehensions_HsExp expr

-- expandListCompr e stmts = expand e stmts
--     where
--       expand e [] = e
--       expand e (HsQualifier b : rest)
--           = hsk_if b (expand e rest) hsk_nil
--       expand e (HsGenerator loc pat exp : rest)
--           = let argN  = (HsIdent "arg")
--                 argqN = UnQual argN
--                 fn    = hsk_lambda loc [HsPVar argN]
--                          $ hsk_case loc (HsVar argqN) 
--                                [(pat,         (expand e rest)), 
--                                 (HsPWildCard, hsk_nil)]
--             in hsk_concatMap fn exp
--       expand e (HsLetStmt _ : _) 
--           = error "Let statements not supported in List Comprehensions."


------------------------------------------------------------
------------------------------------------------------------
--------------------------- Tests --------------------------
------------------------------------------------------------
------------------------------------------------------------

noLocalDecl :: HsModule -> Bool
noLocalDecl m = True

prop_NoLocalDecl mod = noLocalDecl $ preprocessHsModule mod