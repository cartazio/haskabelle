{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen
-}

module Importer.ConversionUnit
    ( HskUnit(..),
      IsaUnit(..),
      makeHskUnitFromFile
    ) where

import Maybe
import IO
import Monad
import Data.Graph
import Data.Tree
import Language.Haskell.Exts

import qualified Importer.IsaSyntax as Isa
import qualified Importer.Msg as Msg
import qualified Importer.LexEnv as Env

import Importer.Utilities.Misc
import Importer.Utilities.Hsk


-- A Conversion Unit

{-|
  This data structure combines several Haskell modules and the corresponding environment.
  into one coherent unit.
-}
data HskUnit = HskUnit [HsModule] Env.GlobalE
  deriving (Show)

{-|
  This data structure combines several Isabelle theories and the corresponding environment
  into one coherent unit.
-}
data IsaUnit = IsaUnit [Isa.Cmd] Env.GlobalE
  deriving (Show)

{-|
  This function takes a file path to a Haskell module and parses it to
  a unit, i.e. also parsing all its dependencies as well.
-}
makeHskUnitFromFile :: FilePath -> IO HskUnit
makeHskUnitFromFile fp
    = parseFileOrLose fp >>= makeHskUnit                     
      where parseFileOrLose fp 
                = do result <- parseFile fp
                     case result of
                       ParseOk hsm         -> return hsm
                       ParseFailed loc msg -> error (Msg.failed_parsing loc msg)

{-|
  This function takes a parsed Haskell module and produces a Haskell unit by parsing
  all module imported by the given module and add including the initial global environment
  as given by 'Env.initialGlobalEnv'.
-}
makeHskUnit :: HsModule -> IO HskUnit
makeHskUnit hsmodule
    = do (depGraph, fromVertex, _) <- makeDependencyGraph hsmodule
         let cycles = cyclesFromGraph depGraph
         when (not (null cycles)) -- not a DAG?
              $ let toModuleName v = case fromVertex v of (_,Module n,_) -> n
                in fail (Msg.cycle_in_dependency_graph (map toModuleName (head cycles)))
         let toHsModule v = case fromVertex v of (m,_,_) -> m
         let [hsmodules]  = map (map toHsModule . flatten) (components depGraph)
         return (HskUnit hsmodules Env.initialGlobalEnv)

{-|
  This function computes a list of all cycles in the given graph.
  The cycles are represented by the vertexes which constitute them.
-}
cyclesFromGraph :: Graph -> [[Vertex]]
cyclesFromGraph graph
    = filter ((>1) . length) $ map flatten (scc graph)

{-|
  This function computes the graph depicting the dependencies between all modules
  imported by the given module plus itself. The result comes with two functions to convert
  between the modules an the vertices of the graph (as provided by 'Data.Graph.graphFromEdges').
-}
makeDependencyGraph ::  HsModule
                    -> IO (Graph,
                          Vertex -> (HsModule, Module, [Module]),
                          Module -> Maybe Vertex)
makeDependencyGraph hsmodule
    = do hsmodules <- transitiveClosure hsmodule
         return $ graphFromEdges (map makeEdge hsmodules)
    where makeEdge hsmodule@(HsModule _loc modul _exports imports _decls)
              = let imported_modules = map importModule imports
                in (hsmodule, modul, imported_modules)

{-|
  This function computes a list of all modules that are imported (directly or
  indirectly, including itself) by the given module.
-}
transitiveClosure :: HsModule -> IO [HsModule]
transitiveClosure hsmodule = grovelHsModules [] hsmodule

{-|
  This function computes a list of all modules that are imported (directly or
  indirectly, including itself) by the given module. It ignores all modules that
  are mentions in the argument list (of visited modules).
-}
grovelHsModules :: [Module] -> HsModule -> IO [HsModule]
grovelHsModules visited hsmodule@(HsModule _loc modul _exports imports _decls) 
    = let imports' = filter ((`notElem` visited) . importModule) imports
          modules  = map importModule imports'
      in do hsmodules  <- mapM parseImportOrFail imports'
            hsmodules' <- concatMapM (grovelHsModules ([modul] ++ modules ++ visited)) hsmodules
            return (hsmodule : hsmodules')

{-|
  This method tries to parse the Haskell module identified by the given
  import declaration.
-}

parseImportOrFail :: HsImportDecl -> IO HsModule
parseImportOrFail (HsImportDecl { importLoc=importloc, importModule=m })
    = do putStr $ "importing module " ++ (show m) ++" ...\n"
         result <- try (parseFile (module2FilePath m))
         case result of
           Left ioerror                -> fail (Msg.failed_import importloc m (show ioerror))
           Right (ParseFailed loc msg) -> fail (Msg.failed_import importloc m 
                                                 $ Msg.failed_parsing loc msg)
           Right (ParseOk m)           -> return m
