{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen
-}

module Importer.DeclDependencyGraph 
    (HskDeclDepGraph(..), makeDeclDepGraph, flattenDeclDepGraph) where

import Monad
import Maybe
import List (groupBy, sortBy)

import Data.Graph
import Data.Tree
import Language.Haskell.Hsx

import Importer.Utilities.Misc
import Importer.Utilities.Hsk

import qualified Importer.LexEnv as Env
import qualified Importer.Msg as Msg


-- We have to canonicalize the names in our graph, as there may appear
-- "some_fun", and "Foo.some_fun", and they may be reffering to the
-- same. We use our GlobalEnv for this purpose.
data HskDeclDepGraph = HskDeclDepGraph (Graph, 
                                        Vertex -> (HsDecl, Env.EnvName, [Env.EnvName]), 
                                        Env.EnvName -> Maybe Vertex)

makeDeclDepGraph :: Env.GlobalE -> Module -> [HsDecl] -> HskDeclDepGraph
makeDeclDepGraph globalEnv modul decls = HskDeclDepGraph declDepGraph
    where declDepGraph = graphFromEdges
                           $ handleDuplicateEdges
                               $ concatMap (makeEdgesFromHsDecl globalEnv modul) decls

makeEdgesFromHsDecl :: Env.GlobalE -> Module -> HsDecl -> [(HsDecl, Env.EnvName, [Env.EnvName])]
makeEdgesFromHsDecl globalEnv modul decl
    = let canonicalize hsqname = Env.resolve globalEnv (Env.fromHsk modul) (Env.fromHsk hsqname)
      in do defname <- fromJust $ namesFromHsDecl decl
            let used_names = extractFreeVarNs decl
            return (decl, canonicalize defname, map canonicalize used_names)
             

handleDuplicateEdges :: [(HsDecl, Env.EnvName, [Env.EnvName])] -> [(HsDecl, Env.EnvName, [Env.EnvName])]
handleDuplicateEdges edges
    = concatMap handleGroup (groupBy (\(_,x,_) (_,y,_) -> x == y) edges)
    where handleGroup edges
              = let edges' = filter (not . isTypeAnnotation) edges
                in if (length edges' > 1) then error (Msg.ambiguous_decl_definitions edges')
                                          else edges'
          isTypeAnnotation ((HsTypeSig _ _ _, _ , _)) = True
          isTypeAnnotation _ = False

flattenDeclDepGraph :: HskDeclDepGraph -> [[HsDecl]]
flattenDeclDepGraph (HskDeclDepGraph (graph, fromVertex, _))
    -- We sort each declaration within a component (consisting of inter-dependent decls)
    -- source-line wise, and then sort each such component also source-line wise.
    -- Objective: To preserve the ordering of the original source code file as
    --            much as possible.
    = sortBy (\decls1 decls2 -> orderDeclsBySourceLine (head decls1) (head decls2))
        $ map (sortBy orderDeclsBySourceLine . map declFromVertex . flatten) $ scc graph
    where declFromVertex v = let (decl,_,_) = fromVertex v in decl 
