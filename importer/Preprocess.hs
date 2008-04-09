{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen
-}

module Importer.Preprocess (preprocessHsModule) where

import Maybe
import List
import Control.Monad.State
import Language.Haskell.Hsx

import Data.Generics.Biplate

import Importer.Utilities.Misc -- (concatMapM, assert)
import Importer.Utilities.Hsk
import Importer.Utilities.Gensym

import qualified Importer.Msg as Msg

preprocessHsModule :: HsModule -> HsModule

preprocessHsModule (HsModule loc modul exports imports topdecls)
    = HsModule loc modul exports imports topdecls'
      where topdecls' = runGensym 0 (runDelocalizer (concatMapM delocalize_HsDecl topdecls))

-- Delocalization of HsDecls:
--
--  Since Isabelle/HOL does not really support local function
--  declarations, we convert the Haskell AST to an equivalent AST
--  where every local function declaration is made a global
--  declaration. This includes where as well as let expressions.
--
--  Additionally, all variables defined in a where clause
--  are converted to an equivalent let expression.


-- We keep track of the names that are directly bound by a declaration,
-- as functions must not close over them. See below for an explanation.
type DelocalizerM a = StateT [HsQName] (State GensymCount) a

withBindings       :: [HsQName] -> DelocalizerM v -> DelocalizerM v
withBindings names m = do old <- getBindings; put (names ++ old); r <- m; put old; return r

getBindings :: DelocalizerM [HsQName]
getBindings = get

runDelocalizer :: DelocalizerM [HsDecl] -> State GensymCount [HsDecl]
runDelocalizer d = evalStateT d []

-- Main function. Takes a declaration, and returns a list of itself and all
-- priorly local declarations.
delocalize_HsDecl  :: HsDecl  -> DelocalizerM [HsDecl]

-- Helper functions. Return a properly alpha-converted version of their argument 
-- plus a list of globalized declarations.
delocalize_HsMatch :: HsMatch -> DelocalizerM (HsMatch, [HsDecl])
delocalize_HsRhs   :: HsRhs   -> DelocalizerM (HsRhs, [HsDecl])
delocalize_HsExp   :: HsExp   -> DelocalizerM (HsExp, [HsDecl])
delocalize_HsAlt   :: HsAlt -> DelocalizerM (HsAlt, [HsDecl])

-- This additionally returns the renamings that reflect how the where-binds
-- were renamed. This is necessary, beacuse the body of the caller 
-- where these where-binds apply to, must also be alpha converted.
delocalize_HsBinds :: HsBinds -> DelocalizerM (HsBinds, [HsDecl], [Renaming])


delocalize_HsDecl (HsPatBind loc pat rhs wbinds)
    = withBindings (extractBindingNs pat)
      $ do (rhs', localdecls)  <- delocalize_HsRhs (letify wbinds rhs)
           return $ localdecls ++ [HsPatBind loc pat rhs' (HsBDecls [])]

delocalize_HsDecl (HsFunBind matchs)
    = do (matchs', localdecls) <- liftM (\(xs, ys) -> (xs, concat ys))
                                    $ mapAndUnzipM delocalize_HsMatch matchs
         return (localdecls ++ [HsFunBind matchs'])

delocalize_HsDecl decl  = assert (check decl) $ return [decl]
          -- Safety check to make sure we didn't miss anything.
    where check decl   = and [null (universeBi decl :: [HsBinds]),
                              null [ True | HsLet _ _ <- universeBi decl ]]
          isHsLet expr = case expr of HsLet _ _ -> True; _ -> False

delocalize_HsMatch (HsMatch loc name pats rhs wbinds)
    = withBindings (extractBindingNs pats)
      $ do (rhs', localdecls)  <- delocalize_HsRhs (letify wbinds rhs)
           return (HsMatch loc name pats rhs' (HsBDecls []), localdecls)

delocalize_HsBinds (HsBDecls localdecls)
    -- First rename the bindings that are established by LOCALDECLS to fresh identifiers,
    -- then also rename all occurences (i.e. recursive invocations) of these bindings
    -- within the body of the declarations.
    = do renamings    <- lift (freshIdentifiers (bindingsFromDecls localdecls))
         let localdecls' = map (renameFreeVars renamings . renameHsDecl renamings) localdecls
         localdecls'' <- concatMapM delocalize_HsDecl localdecls'
         closedVarNs  <- getBindings
         return (HsBDecls [], checkForClosures closedVarNs localdecls'', renamings)

delocalize_HsRhs (HsUnGuardedRhs exp)
    = do (exp', decls) <- delocalize_HsExp exp
         return (HsUnGuardedRhs exp', decls)

delocalize_HsExp (HsLet binds body)
    -- The let expression in Isabelle/HOL supports simple pattern matching. So we
    -- differentiate between pattern and other (e.g. function) bindings; the first
    -- ones are kept, the latter ones are converted to global bindings.
    = let (patBinds, otherBinds) = splitPatBinds binds
      in withBindings (extractBindingNs patBinds)
         $ do (otherBinds', decls, renamings) <- delocalize_HsBinds otherBinds
              (body', moredecls)              <- delocalize_HsExp (renameFreeVars renamings body)
              return (letify (renameFreeVars renamings patBinds) body', decls ++ moredecls)

delocalize_HsExp (HsCase body alternatives)
    = do (body', localdecls)    <- delocalize_HsExp body
         (alternatives', decls) <- liftM (\(xs, ys) -> (xs, concat ys))
                                      $ mapAndUnzipM delocalize_HsAlt alternatives

         return (HsCase body' alternatives', localdecls ++ decls)

delocalize_HsExp hsexp
     = let (subexpressions, regenerate) = uniplate hsexp
       in do (subexpressions', decls) <- liftM (\(xs, ys) -> (xs, concat ys))
                                          $ mapAndUnzipM delocalize_HsExp subexpressions
             let finalexps = regenerate subexpressions'
             assert (null (universeBi finalexps :: [HsDecl])) -- Safety check, so we haven't missed something.
               $ return (regenerate subexpressions', decls)

delocalize_HsAlt (HsAlt loc pat (HsUnGuardedAlt body) wbinds)
    = withBindings (extractBindingNs pat)
      $ do (body', localdecls) <- delocalize_HsExp (letify wbinds body)
           return (HsAlt loc pat (HsUnGuardedAlt body') (HsBDecls []), localdecls)


-- Partitions HsBinds into (pattern bindings, other bindings).
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
checkForClosures closedNs decls = map check decls
    where check decl = trace (prettyShow' "locs"  (childrenBi decl :: [SrcLoc])
                              ++ "\n" ++ prettyShow' "exprs" (childrenBi decl :: [HsExp]))
                         $ let [loc]  = childrenBi decl :: [SrcLoc]
                               exprs  = childrenBi decl :: [HsExp]
                               freeNs = concatMap (\e -> filter (flip isFreeVar e) closedNs) exprs
                           in if (null freeNs) then decl else error (Msg.free_vars_found loc freeNs)