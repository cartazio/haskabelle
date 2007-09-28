
module Importer.Preprocess (preprocessHsModule) where

import Control.Monad.State
import Language.Haskell.Hsx

import Data.Generics.Biplate

import Importer.Utilities.Misc -- (concatMapM, assert)
import Importer.Utilities.Hsx
import Importer.Utilities.Gensym

preprocessHsModule :: HsModule -> HsModule

preprocessHsModule (HsModule loc modul exports imports topdecls)
    = HsModule loc modul exports imports 
        $ runGensym 0 (concatMapM (delocalize_HsDecl modul) topdecls)


-- Delocalization of HsDecls:
--
--  Since Isabelle/HOL does not really support local variable / function 
--  declarations, we convert the Haskell AST to an equivalent AST where
--  every local declaration is made a global declaration. This also
--  includes let expression which are also converted to global 
--  declarations.
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

-- Main function. Takes a declaration, and returns a list of itself and all
-- priorly local declarations.
delocalize_HsDecl  :: Module -> HsDecl  -> State GensymCount [HsDecl]

-- Helper functions. Return a properly alpha-converted version of their argument 
-- plus a list of globalized declarations.
delocalize_HsMatch :: Module -> HsMatch -> State GensymCount (HsMatch, [HsDecl])
delocalize_HsRhs   :: Module -> HsRhs   -> State GensymCount (HsRhs, [HsDecl])
delocalize_HsExp   :: Module -> HsExp   -> State GensymCount (HsExp, [HsDecl])

-- This additionally returns the renamings that reflect how the where-binds
-- were renamed. This is necessary, beacuse the body of the caller 
-- where these where-binds apply to, must also be alpha converted.
delocalize_HsBinds :: Module -> HsBinds -> State GensymCount (HsBinds, [HsDecl], [Renaming])


delocalize_HsDecl m (HsPatBind loc pat rhs wbinds)
    = do (wbinds', localdecls, renamings) <- delocalize_HsBinds m wbinds
         (rhs',    morelocaldecls)        <- delocalize_HsRhs m (alphaconvert m renamings rhs)
         return $ localdecls ++ morelocaldecls ++ [HsPatBind loc pat rhs' wbinds']

delocalize_HsDecl m (HsFunBind matchs)
    = do (matchs', localdecls) <- liftM (\(xs, ys) -> (xs, concat ys))
                                    $ mapAndUnzipM (delocalize_HsMatch m) matchs
         return (localdecls ++ [HsFunBind matchs'])

delocalize_HsDecl m decl  = assert (check decl) $ return [decl]
          -- Safety check to make sure we didn't miss anything.
    where check decl   = and [null (universeBi decl :: [HsBinds]),
                              null (filter isHsLet (universeBi decl :: [HsExp]))]
          isHsLet expr = case expr of HsLet _ _ -> True; _ -> False

delocalize_HsMatch m (HsMatch loc name pats rhs wbinds)
    = do (wbinds', localdecls, renamings) <- delocalize_HsBinds m wbinds
         (rhs',    morelocaldecls)        <- delocalize_HsRhs m (alphaconvert m renamings rhs)
         return (HsMatch loc name pats rhs' wbinds', localdecls ++ morelocaldecls)

delocalize_HsBinds m (HsBDecls localdecls)
    = do renamings    <- renameToFreshIdentifiers (bindingsFromDecls m localdecls)
         let localdecls' = map (alphaconvert m renamings) localdecls
         localdecls'' <- concatMapM (delocalize_HsDecl m) localdecls'
         return (HsBDecls [], localdecls'', renamings)

delocalize_HsRhs m (HsUnGuardedRhs exp)
    = do (exp', decls) <- delocalize_HsExp m exp
         return (HsUnGuardedRhs exp', decls)

delocalize_HsExp m (HsLet wbinds body)
    = do (wbinds', decls, renamings) <- delocalize_HsBinds m wbinds
         (body',   moredecls)        <- delocalize_HsExp m (alphaconvert m renamings body)
         return (body', decls ++ moredecls)

delocalize_HsExp m hsexp
     = let (subexpressions, regenerate) = uniplate hsexp
       in do (subexpressions', decls) <- liftM (\(xs, ys) -> (xs, concat ys))
                                          $ mapAndUnzipM (delocalize_HsExp m) subexpressions
             return (regenerate subexpressions', decls)


renameToFreshIdentifiers :: [HsQName] -> State GensymCount [(HsQName, HsQName)]
renameToFreshIdentifiers qnames
    = do freshs <- mapM genHsQName qnames
         return (zip qnames freshs)

