
module Importer.Preprocess (preprocessHsModule) where

import Control.Monad.State
import Language.Haskell.Hsx

import Data.Generics.Biplate

import Importer.Utilities.Misc -- (concatMapM, assert)
import Importer.Utilities.Hsx (bindingsFromDecls, alphaconvert)
import Importer.Utilities.Gensym

preprocessHsModule :: HsModule -> HsModule

preprocessHsModule (HsModule loc modul exports imports topdecls)
    = HsModule loc modul exports imports 
        $ runGensym 0 (concatMapM (delocalizeDecl modul) topdecls)

-- Delocalization of HsDecls:
--
--  Since Isabelle/HOL does not really support local variable / function 
--  declarations, we convert the Haskell AST to an equivalent AST where
--  every local declaration is made a global declaration.
--
--  For each toplevel declaration, this is done as follows:
--
--     * separate the decl from itself and its local declarations; 
--
--     * rename the local declarations to fresh identifiers;
--
--     * alpha convert decl (sans local decls) and alpha convert the 
--       bodies of the local decls themselves to reflect the new names;
--
--     * delocalize the bodies of the local declarations (as they can
--       themselves contain local declarations);
--
--     * and finally concatenate everything.
--


delocalizeDecl :: Module -> HsDecl -> State GensymCount [HsDecl]

delocalizeDecl m (HsPatBind loc pat rhs wbinds)
    = do (localdecls, renamings) <- delocalizeWhereBinds m wbinds
         (rhs', morelocaldecls)  <- delocalizeRhs m (alphaconvert m renamings rhs)

         return $ localdecls ++ morelocaldecls ++ [HsPatBind loc pat rhs' (HsBDecls [])]

delocalizeDecl m (HsFunBind matchs)
    = do (matchs', localdecls) <- liftM (\(xs, ys) -> (xs, concat ys))
                                    $ mapAndUnzipM (delocalizeMatch m) matchs
         return (localdecls ++ [HsFunBind matchs'])

delocalizeDecl m decl = assert (check decl) $ return [decl]
    where check decl = and [null (universeBi decl :: [HsBinds]),
                            null (filter isHsLet (universeBi decl :: [HsExp]))]
          isHsLet expr = case expr of HsLet _ _ -> True; _ -> False


delocalizeMatch m (HsMatch loc name pats rhs wbinds)
    = do (localdecls, renamings) <- delocalizeWhereBinds m wbinds
         (rhs', morelocaldecls)  <- delocalizeRhs m (alphaconvert m renamings rhs)
         return (HsMatch loc name pats rhs' (HsBDecls []), 
                localdecls ++ morelocaldecls)

delocalizeWhereBinds m (HsBDecls localdecls)
    = do renamings <- renameToFreshIdentifiers (bindingsFromDecls m localdecls)
         let localdecls' = map (alphaconvert m renamings) localdecls
         localdecls'' <- concatMapM (delocalizeDecl m) localdecls'
         return (localdecls'', renamings)

delocalizeRhs m (HsUnGuardedRhs exp)
    = do (exp', decls) <- delocalizeLets m exp; return (HsUnGuardedRhs exp', decls)

delocalizeLets m (HsLet wbinds body)
    = do (decls, renamings) <- delocalizeWhereBinds m wbinds
         (body', moredecls) <- delocalizeLets m (alphaconvert m renamings body)
         return (body', decls ++ moredecls)

delocalizeLets m hsexp
     = let (subexpressions, storer) = uniplate hsexp
       in do (subexpressions', decls) <- liftM (\(xs, ys) -> (xs, concat ys))
                                          $ mapAndUnzipM (delocalizeLets m) subexpressions
             return (storer subexpressions', decls)

renameToFreshIdentifiers :: [HsQName] -> State GensymCount [(HsQName, HsQName)]
renameToFreshIdentifiers qnames
    = do freshs <- mapM genHsQName qnames
         return (zip qnames freshs)

