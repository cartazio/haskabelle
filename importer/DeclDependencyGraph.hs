
module Importer.DeclDependencyGraph 
    (HsxDeclDepGraph(..), makeDeclDepGraph, flattenDeclDepGraph) where

import Monad
import Maybe
import List (groupBy, sortBy)

import Data.Graph
import Data.Tree
import Language.Haskell.Hsx

import Importer.Utilities.Misc
import Importer.Utilities.Hsx

import qualified Importer.Msg as Msg


data HsxDeclDepGraph = HsxDeclDepGraph (Graph, 
                                        Vertex -> (HsDecl, HsQName, [HsQName]), 
                                        HsQName -> Maybe Vertex)

makeDeclDepGraph :: [HsDecl] -> HsxDeclDepGraph
makeDeclDepGraph decls = HsxDeclDepGraph declDepGraph
    where declDepGraph = graphFromEdges
                           $ handleDuplicateEdges
                               $ concatMap makeEdgesFromHsDecl decls

makeEdgesFromHsDecl :: HsDecl -> [(HsDecl, HsQName, [HsQName])]
makeEdgesFromHsDecl decl
    = [ (decl, name, extractFreeVarNs decl) | name <- fromJust $ namesFromHsDecl decl ]

handleDuplicateEdges :: [(HsDecl, HsQName, [HsQName])] -> [(HsDecl, HsQName, [HsQName])]
handleDuplicateEdges edges
    = concatMap handleGroup (groupBy (\(_,x,_) (_,y,_) -> x == y) edges)
    where handleGroup edges
              = let edges' = filter (not . isTypeAnnotation) edges
                in if (length edges' > 1) then error (Msg.ambiguous_decl_definitions edges')
                                          else edges'
          isTypeAnnotation ((HsTypeSig _ _ _, _ , _)) = True
          isTypeAnnotation _ = False

flattenDeclDepGraph :: HsxDeclDepGraph -> [[HsDecl]]
flattenDeclDepGraph (HsxDeclDepGraph (graph, fromVertex, _))
    -- We sort each declaration within a component (consisting of inter-dependent decls)
    -- source-line wise, and then sort each such component also source-line wise.
    -- Objective: To preserve the ordering of the original source code file as
    --            much as possible.
    = sortBy (\decls1 decls2 -> orderDeclsBySourceLine (head decls1) (head decls2))
        $ map (sortBy orderDeclsBySourceLine . map declFromVertex . flatten) $ scc graph
    where declFromVertex v = let (decl,_,_) = fromVertex v in decl 
