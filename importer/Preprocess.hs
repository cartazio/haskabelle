
module Importer.Preprocess (preprocessHsModule) where

import Control.Monad.State
import Data.Generics.PlateData (biplate)
import Language.Haskell.Hsx

import Importer.Utilities.Misc (concatMapM)
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
delocalizeDecl m decl 
    = do (localdecls, decl') <- delocalizeDeclAux m decl
         return (localdecls ++ decl')
      
delocalizeDeclAux :: Module -> HsDecl -> State GensymCount ([HsDecl], [HsDecl])
delocalizeDeclAux m decl
    = let (wherebinds, contextgen) = biplate decl
          localdecls               = concat [ decls | HsBDecls decls <- wherebinds ]
      in do renamings <- renameToFreshIdentifiers (bindingsFromDecls m localdecls)
            let decl'       = alphaconvert m renamings (contextgen (map (\_ -> (HsBDecls [])) wherebinds))
            let localdecls' = map (alphaconvert m renamings) localdecls
            (sublocaldecls, localdecls'') 
                      <- liftM (\(xs,ys) -> (concat xs, concat ys))
                           $ (mapAndUnzipM (delocalizeDeclAux m) localdecls')
            return (sublocaldecls ++ localdecls'', [decl'])

renameToFreshIdentifiers :: [HsQName] -> State GensymCount [(HsQName, HsQName)]
renameToFreshIdentifiers qnames
    = do freshs <- mapM genHsQName qnames
         return (zip qnames freshs)

