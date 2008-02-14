
module Importer.ConversionUnit 
    (ConversionUnit(..), makeConversionUnitFromFile, 
     HsxDeclDepGraph(..), makeDeclDepGraph, flattenDeclDepGraph) where

import Maybe
import IO
import Monad
import List (groupBy, sortBy)
import Data.Graph
import Data.Tree
import Language.Haskell.Hsx

import qualified Importer.IsaSyntax as Isa
import qualified Importer.Msg as Msg
import qualified Importer.LexEnv as Env

import Importer.Utilities.Misc
import Importer.Utilities.Hsx


-- A Conversion Unit

data ConversionUnit = HsxUnit [HsModule]
                    | IsaUnit [Isa.Cmd]
  deriving (Show)

makeConversionUnitFromFile :: FilePath -> IO ConversionUnit
makeConversionUnitFromFile fp
    = parseFileOrLose fp >>= makeConversionUnit                     
      where parseFileOrLose fp 
                = do result <- parseFile fp
                     case result of
                       ParseOk hsm         -> return hsm
                       ParseFailed loc msg -> error (Msg.failed_parsing loc msg)

makeConversionUnit :: HsModule -> IO ConversionUnit
makeConversionUnit hsmodule
    = do (depGraph, fromVertex, _) <- makeDependencyGraph hsmodule
         let cycles = cyclesFromGraph depGraph
         when (not (null cycles)) -- not a DAG?
              $ let toModuleName v = case fromVertex v of (_,Module n,_) -> n
                in fail (Msg.cycle_in_dependency_graph (map toModuleName (head cycles)))
         let toHsModule v = case fromVertex v of (m,_,_) -> m
         let [hsmodules]  = map (map toHsModule . flatten) (dff depGraph)
         return (HsxUnit hsmodules)

cyclesFromGraph :: Graph -> [[Vertex]]
cyclesFromGraph graph
    = filter ((>1) . length) $ map flatten (scc graph)

makeDependencyGraph hsmodule
    = do hsmodules <- transitiveClosure hsmodule
         return $ graphFromEdges (map makeEdge hsmodules)
    where makeEdge hsmodule@(HsModule _loc modul _exports imports _decls)
              = let imported_modules = map importModule imports
                in (hsmodule, modul, imported_modules)

transitiveClosure :: HsModule -> IO [HsModule]
transitiveClosure hsmodule = grovelHsModules [] hsmodule

grovelHsModules :: [Module] -> HsModule -> IO [HsModule]
grovelHsModules visited hsmodule@(HsModule _loc modul _exports imports _decls) 
    = let imports' = filter ((`notElem` visited) . importModule) imports
          modules  = map importModule imports'
      in do hsmodules  <- mapM parseImportOrFail imports'
            hsmodules' <- concatMapM (grovelHsModules ([modul] ++ modules ++ visited)) hsmodules
            return (hsmodule : hsmodules')

parseImportOrFail :: HsImportDecl -> IO HsModule
parseImportOrFail (HsImportDecl { importLoc=importloc, importModule=m })
    = do result <- try (parseFile (module2FilePath m))
         case result of
           Left ioerror                -> fail (Msg.failed_import importloc m (show ioerror))
           Right (ParseFailed loc msg) -> fail (Msg.failed_import importloc m 
                                                       (Msg.failed_parsing loc msg))
           Right (ParseOk m)           -> return m



-- An Haskell Declaration Graph

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
    = map (sortBy orderDeclsBySourceLine . map declFromVertex . flatten) $ scc graph
    where declFromVertex v = let (decl,_,_) = fromVertex v in decl 
          



