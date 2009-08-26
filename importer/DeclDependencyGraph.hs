{-| Author: Tobias C. Rittweiler, TU Muenchen
-}

module Importer.DeclDependencyGraph 
    (arrangeDecls) where

import Maybe
import List (groupBy, sortBy, intersect)
import Data.Graph
import Data.Set (Set)
import qualified Data.Set as Set hiding (Set)
import Data.Tree

import Monad

import Importer.Library

import qualified Language.Haskell.Exts as Hsx

import Importer.Utilities.Hsk

import qualified Importer.LexEnv as Env
import qualified Importer.Msg as Msg


-- We have to canonicalize the names in our graph, as there may appear
-- "some_fun", and "Foo.some_fun", and they may be reffering to the
-- same. We use our GlobalEnv for this purpose.

{-|
  This data structure represents the dependency graph of Haskell declarations.
  The nodes of this graph are elements of type 'Hsx.Decl' keys are of type 'Env.EnvName'.
-}
data HskDeclDepGraph = HskDeclDepGraph (Graph, 
                                        Vertex -> (Hsx.Decl, Env.EnvName, [Env.EnvName]), 
                                        Env.EnvName -> Maybe Vertex)

{-|
  This function computes the dependency graph of the given Haskell declarations of the
  given module in the given environment. An edge from a declaration A to declaration B
  means the definition of A depends on B.
-}
makeDeclDepGraph :: Env.GlobalE -> Hsx.ModuleName -> [Hsx.Decl] -> HskDeclDepGraph
makeDeclDepGraph globalEnv modul decls = HskDeclDepGraph declDepGraph
    where declDepGraph = graphFromEdges
                           $ handleDuplicateEdges
                               $ concatMap (makeEdgesFromDecl globalEnv modul) decls

{-|
  This function constructs the outgoing edges of the given declaration in the given environment
  module.
-}
makeEdgesFromDecl :: Env.GlobalE -> Hsx.ModuleName -> Hsx.Decl -> [(Hsx.Decl, Env.EnvName, [Env.EnvName])]
makeEdgesFromDecl globalEnv modul decl =
  let
    canonicalize hsqname = Env.resolveEnvName_OrLose globalEnv (Env.fromHsk modul) (Env.fromHsk hsqname)
    names = map canonicalize $ namesFromDecl decl
    used_names = Set.map canonicalize $ Set.unions [extractFreeVarNs decl, extractDataConNs decl, extractFieldNs decl]
    used_types = Set.map canonicalize $ extractTypeConNs decl
    impl_types = catMaybes $ Set.toList $ Set.map (Env.getDepDataType globalEnv (Env.fromHsk modul)) used_names
  in
    [ (decl, name, Set.toList (Set.union used_names used_types) ++ impl_types) | name <- names ]

{-|
  ???
-}
handleDuplicateEdges :: [(Hsx.Decl, Env.EnvName, [Env.EnvName])] -> [(Hsx.Decl, Env.EnvName, [Env.EnvName])]
handleDuplicateEdges edges
    = concatMap handleGroup (groupBy (\(_,x,_) (_,y,_) -> x == y) edges)
    where handleGroup edges
              = let edges' = filter (not . isTypeAnnotation) edges
                in if ambiguous_edges edges' then error (Msg.ambiguous_decl_definitions edges')
                                             else edges'
          ambiguous_edges edges
              = length edges > 1 && any (\e -> not (isClass e || isInstance e)) edges

          isTypeAnnotation (Hsx.TypeSig _ _ _, _ , _) = True
          isTypeAnnotation _ = False
          isInstance (Hsx.InstDecl _ _ _ _ _, _, _) = True
          isInstance _ = False
          isClass (Hsx.ClassDecl _ _ _ _ _ _, _, _) = True
          isClass _ = False



-- In Haskell definitions may appear anywhere in a source file, but in
-- Isar/HOL (like in ML), definitions that are used in another definition
-- must appear lexically before that other definition.

{-|
  This function takes a dependency graph of Haskell declarations and linearises it, such that
  functions are declared before they are used by another function definition. The result is a
  list of list of declaration each list of declarations forms a set of declarations that depend
  on each other in a mutually recursive way.
-}

flattenDeclDepGraph :: HskDeclDepGraph -> [[Hsx.Decl]]
flattenDeclDepGraph (HskDeclDepGraph (graph, fromVertex, _))
    -- We first partition the graph into groups of mutually-dependent declarations
    -- (i.e. its strongly-connected components); we then sort these components according
    -- their dependencies (decls used later must come first.)
    -- 
    -- Additionally we sort each declaration in such a component source-line wise, 
    -- and also sort source-line wise if two components are completely independent.
    -- Objective: To preserve the ordering of the original source code file as
    --            much as possible.
    = let declFromVertex v = (let (decl,_,_) = fromVertex v in decl)
      in map (map declFromVertex)
             $ sortBy orderComponents_ByDependencies
                 (map (sortBy orderVertices_BySourceLine . flatten) $ scc graph)
    where
      orderVertices_BySourceLine v1 v2
          = let (decl1,_,_) = fromVertex v1
                (decl2,_,_) = fromVertex v2
            in orderDeclsBySourceLine decl1 decl2

      orderComponents_ByDependencies vs1 vs2
          = let used_vs_in_1 = concatMap (reachable graph) vs1
                used_vs_in_2 = concatMap (reachable graph) vs2
            in if (isContained used_vs_in_1 vs2)      -- does vs2 define stuff needed in vs1?
               then assert (not (isContained used_vs_in_2 vs1)) $ GT
               else if (isContained used_vs_in_2 vs1) -- does vs1 define stuff needed in vs2?
                    then assert (not (isContained used_vs_in_1 vs2)) $ LT
                    else                              -- vs1 and vs2 are independant.
                        let (decl1,_,_) = fromVertex (head vs1)
                            (decl2,_,_) = fromVertex (head vs2)
                        in orderDeclsBySourceLine decl1 decl2
            where 
              isContained xs ys = not (null (intersect xs ys))

arrangeDecls :: Env.GlobalE -> Hsx.ModuleName -> [Hsx.Decl] -> [[Hsx.Decl]]
arrangeDecls globalEnv modul = flattenDeclDepGraph . makeDeclDepGraph globalEnv modul

