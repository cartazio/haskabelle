{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen
-}

module Importer.ConversionUnit
    ( HskUnit(..),
      IsaUnit(..),
      Conversion,
      makeHskUnitFromFile,
      getCustomisations,
      getInputFilesRecursively,
      getOutputDir,
      runConversion,
      liftIO
    ) where

import Maybe
import IO
import Monad
import Data.Graph
import qualified Data.Set as Set hiding (Set)
import Data.Set (Set)
import Data.Tree
import qualified Data.Map as Map hiding (Map)
import Data.Map (Map)
import Language.Haskell.Exts
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error

import System.FilePath
import System.Directory

import qualified Importer.IsaSyntax as Isa
import qualified Importer.Msg as Msg
import qualified Importer.LexEnv as Env

import qualified Importer.Configuration as Config (getCustomTheory)
import Importer.Configuration hiding (getCustomTheory)
import Importer.Utilities.Misc
import Importer.Utilities.Hsk


-- A Conversion Unit

{-|
  This data structure combines several Haskell modules and the corresponding environment.
  into one coherent unit.
-}
data HskUnit = HskUnit [HsModule] CustomTranslations Env.GlobalE
  deriving (Show)

{-|
  This data structure combines several Isabelle theories and the corresponding environment
  into one coherent unit.
-}
data IsaUnit = IsaUnit [Isa.Cmd] [CustomTheory] Env.GlobalE
  deriving (Show)

newtype Conversion a = Conversion (ReaderT Config IO a)
    deriving (Functor, Monad, MonadReader Config, MonadIO, MonadError IOError)

isCustomModule :: Module -> Conversion Bool
isCustomModule
    = liftM isJust . getCustomTheory

getCustomisations :: Conversion Customisations
getCustomisations = ask >>= return . customisations

getCustomTheory :: Module -> Conversion (Maybe CustomTheory)
getCustomTheory mod =
    ask >>= return . (`Config.getCustomTheory` mod) . customisations

getInputFilesRecursively :: Conversion [FilePath]
getInputFilesRecursively
    = do config <- ask
         let locs = inputLocations config
         liftIO $ liftM concat $ mapM getFiles locs
    where getFiles :: Location -> IO [FilePath]
          getFiles (FileLocation path)
              = do fileEx <- doesFileExist path
                   if fileEx
                     then return [path]
                     else do dirEx <- doesDirectoryExist path
                             if dirEx
                               then getFilesRecursively path
                               else putStr ("Warning: File or directory \"" ++ path ++ "\" does not exist!") >> return []  

     
{-|
  This function recursively searches the given directory for Haskell source files.
-}
getFilesRecursively :: FilePath -> IO [FilePath]
getFilesRecursively dir = traverseDir dir action
    where action fp = return fp

{-|
  This function traverses the file system beneath the given path executing the given
  action at every file and directory that is encountered. The result of each action is
  accumulated to a list which is returned.
-}
traverseDir :: FilePath -> (FilePath -> IO a) -> IO [a]
traverseDir dirpath op = do
  fps <- getDirectoryContents dirpath `catch` const (return [])
  let fps' = (map (\ d -> dirpath ++ "/" ++ d)) . (filter (`notElem` [".", ".."])) $ fps
  fmap concat $ mapM work fps'
      where work f = do
              res <- op f
              res' <- traverseDir f op
              return $ res:res'

getOutputDir :: Conversion FilePath
getOutputDir = ask >>= return . fileLocation . outputLocation

runConversion :: Config -> Conversion a -> IO a
runConversion config (Conversion parser) = runReaderT parser config

{-|
  This function takes a file path to a Haskell module and parses it to
  a unit, i.e. also parsing all its dependencies as well.
-}
makeHskUnitFromFile :: FilePath -> Conversion HskUnit
makeHskUnitFromFile fp
    = do mod <- liftIO $ parseFileOrLose fp
         makeHskUnit mod
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
makeHskUnit :: HsModule -> Conversion HskUnit
makeHskUnit hsmodule
    = do (hsmodules,custTrans) <- transitiveClosure hsmodule
         (depGraph, fromVertex, _) <- makeDependencyGraph hsmodules
         let cycles = cyclesFromGraph depGraph
         when (not (null cycles)) -- not a DAG?
              $ let toModuleName v = case fromVertex v of (_,Module n,_) -> n
                in fail (Msg.cycle_in_dependency_graph (map toModuleName (head cycles)))
         let toHsModule v = case fromVertex v of (m,_,_) -> m
         case map (map toHsModule . flatten) (components depGraph) of
           [hsmodules] -> return (HskUnit hsmodules custTrans Env.initialGlobalEnv)
           -- this should not happen
           [] -> fail $ "Internal error: No Haskell module was parsed!"
           -- this should not happen either (this occurs if there is a
           -- discrepancy between the file name and the module name of
           -- a loaded module. This should be caught beforehand.
           _ -> fail $ "Internal error: Parsing of Haskell module invoked loading of independent Haskell modules"
               
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
makeDependencyGraph ::  [HsModule]
                    -> Conversion (Graph,
                          Vertex -> (HsModule, Module, [Module]),
                          Module -> Maybe Vertex)
makeDependencyGraph hsmodules
    = do edges <- (mapM makeEdge hsmodules)
         return $ graphFromEdges edges
    where makeEdge hsmodule@(HsModule _loc modul _exports imports _decls)
              = do let imported_modules = map importModule imports
                   imported_modules'  <- filterM isCustomModule imported_modules
                   return (hsmodule, modul, imported_modules)

{-|
  This function computes a list of all modules that are imported (directly or
  indirectly, including itself) by the given module.
-}
transitiveClosure :: HsModule -> Conversion ([HsModule],CustomTranslations)
transitiveClosure hsmodule = grovelHsModules hsmodule `evalStateT` Set.empty

type GrovelM a = StateT (Set Module) Conversion a

{-|
  This function computes a list of all modules that are imported (directly or
  indirectly, including itself) by the given module. It ignores all modules that
  are mentions in the argument list (of visited modules).
-}
grovelHsModules :: HsModule -> GrovelM ([HsModule], CustomTranslations)
grovelHsModules hsmodule@(HsModule loc modul _exports imports _decls)
    = do visited <- get
         let newModules = filter (`Set.notMember` visited) . map importModule $ imports
         put $ visited `Set.union` (Set.fromList newModules)
         (realModules, custTrans) <- lift $ partitionMaybeM getCustomTranslation newModules
         let custTrans' = custTrans
         let basePath = srcFilename loc
         hsmodules  <- lift $ mapM (parseImportOrFail modul basePath)  realModules
         rec <-  mapM grovelHsModules hsmodules
         let rec' = foldr
                    (\(ms,cust) (ms',cust') -> (ms ++ ms', cust ++ cust'))
                    ([],[])
                    (([hsmodule],custTrans') : rec)
         return rec'

getCustomTranslation :: Module -> Conversion (Maybe CustomTranslation)
getCustomTranslation mod = 
    do mbCustThy <- getCustomTheory mod
       case mbCustThy of
         Nothing -> return Nothing
         Just custThy -> return $ Just (mod, custThy)

partitionMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m ([a],[b])
partitionMaybeM _ []        = return ([],[])
partitionMaybeM pred (x:xs) =
    do mb <- pred x
       (nothing, just) <- partitionMaybeM pred xs
       return $ case mb of
                  Nothing -> (x:nothing,just)
                  Just y -> (nothing, y:just)   
  

{-|
  This function computes the path where to look for an imported module.
-}

computeSrcPath :: Module      -- ^the module that is importing
               -> FilePath     -- ^the path to the importing module
               -> Module       -- ^the module that is to be imported
               -> FilePath     -- ^the assumed path to the module to be imported
computeSrcPath importingMod basePath m
    = let curDir = takeDirectory basePath
          baseDir =  joinPath $ (splitPath curDir) ++ replicate (moduleHierarchyDepth importingMod) ".."
      in combine baseDir (module2FilePath m)
{-|
  This method tries to parse the Haskell module identified by the given
  import declaration.
-}

parseImportOrFail :: Module -> FilePath -> Module -> Conversion HsModule
parseImportOrFail baseModName importloc importModName 
    = do liftIO $ putStr $ "importing module " ++ showModule importModName ++" ...\n"
         let filePath = computeSrcPath baseModName importloc importModName
         result <- liftIO $ parseFile filePath `catch`
                  (\ioError -> fail $ Msg.failed_import importModName (show ioError))
         case result of
           (ParseFailed loc msg) ->
               fail $ Msg.failed_import importModName $ Msg.failed_parsing loc msg
           (ParseOk m@(HsModule _ mName _ _ _)) ->
               if mName == importModName
                 then return m
                 else fail $ Msg.failed_import importModName $ 
                          "Name mismatch: Name of imported module is " ++ showModule mName ++ ", expected was " ++ showModule importModName
