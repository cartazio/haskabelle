
module Importer.Preprocess (preprocessHsModule) where

import Control.Monad.State
import Language.Haskell.Hsx

import Data.Generics.Biplate

import Importer.Utilities.Misc (concatMapM, assert)
import Importer.Utilities.Hsx
import Importer.Utilities.Gensym

import qualified Importer.Msg as Msg

preprocessHsModule :: HsModule -> HsModule

preprocessHsModule (HsModule loc modul exports imports topdecls)
    = HsModule loc modul exports imports topdecls'
      where topdecls' = runGensym 0 (runDelocalizer (concatMapM delocalize_HsDecl topdecls))

-- Delocalization of HsDecls:
--
--  Since Isabelle/HOL does not really support local variable / function 
--  declarations, we convert the Haskell AST to an equivalent AST where
--  every local declaration is made a global declaration. This also
--  includes let expression.
--
--  For each toplevel declaration, this is done as follows:
--
--     * separate the decl from itself and its local declarations; 
--
--     * rename the local declarations to fresh identifiers;
--
--     * alpha convert decl (sans local decls), and alpha convert the 
--       bodies of the local decls themselves to reflect the new names;
--
--     * delocalize the bodies of the local declarations (as they can
--       themselves contain local declarations);
--
--     * and finally concatenate everything.
--

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

-- This additionally returns the renamings that reflect how the where-binds
-- were renamed. This is necessary, beacuse the body of the caller 
-- where these where-binds apply to, must also be alpha converted.
delocalize_HsBinds :: HsBinds -> DelocalizerM (HsBinds, [HsDecl], [Renaming])

delocalize_HsAlt :: HsAlt -> DelocalizerM (HsAlt, [HsDecl])

delocalize_HsDecl (HsPatBind loc pat rhs wbinds)
    = withBindings (bindingsFromPats [pat])
      $ do (wbinds', localdecls, renamings) <- delocalize_HsBinds wbinds
           (rhs',    morelocaldecls)        <- delocalize_HsRhs (renameFreeVars renamings rhs)
           return $ localdecls ++ morelocaldecls ++ [HsPatBind loc pat rhs' wbinds']

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
    = withBindings (bindingsFromPats pats)
      $ do (wbinds', localdecls, renamings) <- delocalize_HsBinds wbinds
           (rhs',    morelocaldecls)        <- delocalize_HsRhs (renameFreeVars renamings rhs)
           return (HsMatch loc name pats rhs' wbinds', localdecls ++ morelocaldecls)

delocalize_HsBinds (HsBDecls localdecls)
    -- First rename the bindings that are established by LOCALDECLS to fresh identifiers,
    -- then also rename all occurences (i.e. recursive invocations) of these bindings
    -- within the body of the declarations.
    = do renamings    <- lift (freshIdentifiers (bindingsFromDecls localdecls))
         let localdecls' = map (renameFreeVars renamings . renameHsDecl renamings) localdecls
         localdecls'' <- concatMapM delocalize_HsDecl localdecls'
         closedVarNs     <- getBindings
         return (HsBDecls [], checkForClosures closedVarNs localdecls'', renamings)

delocalize_HsRhs (HsUnGuardedRhs exp)
    = do (exp', decls) <- delocalize_HsExp exp
         return (HsUnGuardedRhs exp', decls)

delocalize_HsExp (HsLet binds body)
    = do (binds', decls, renamings) <- delocalize_HsBinds binds
         (body',  moredecls)        <- delocalize_HsExp (renameFreeVars renamings body)
         return (body', decls ++ moredecls)

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
             assert (null (universeBi finalexps :: [HsDecl]))
               $ return (regenerate subexpressions', decls)

delocalize_HsAlt (HsAlt loc pat (HsUnGuardedAlt body) wbinds)
    = withBindings (bindingsFromPats [pat])
      $ do (wbinds', decls, renamings) <- delocalize_HsBinds wbinds
           (body',   moredecls)        <- delocalize_HsExp (renameFreeVars renamings body)
           return (HsAlt loc pat (HsUnGuardedAlt body') wbinds', decls ++ moredecls)



-- Closures over variables /that are directly bound by declarations/,
-- can obviously not be delocalized, as for instance
--
--    foo x = let bar y = y * x 
--            in bar 42
--
-- would otherwise be delocalized to the bogus
--
--    bar0 y = y * x
--
--    foo x  = bar0 42

-- Notice, however, that this does not apply to closures that close
-- over bindings that will themselves be delocalized, as e.g the
-- following
--
--    foo x = let z = 42
--                bar y = y * z in bar x
--
-- _can_ (and will) be delocalized to
--
--    z0 = 42
--    bar1 y = y * z0
--    foo x = bar1 x

checkForClosures :: [HsQName] -> [HsDecl] -> [HsDecl]
checkForClosures closedNs decls = map check decls
    where check decl = let [loc]  = childrenBi decl :: [SrcLoc]
                           exprs  = childrenBi decl :: [HsExp]
                           freeNs = concatMap (\e -> filter (flip isFreeVar e) closedNs) exprs
                       in if (null freeNs) then decl else error (Msg.free_vars_found loc freeNs)



