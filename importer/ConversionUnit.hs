{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-| Author:     Tobias C. Rittweiler, TU Muenchen
-}

module Importer.ConversionUnit
    ( HskUnit(..),
      IsaUnit(..),
      Conversion,
      parseHskFiles,
      getCustomisations,
      getInputFilesRecursively,
      getOutputDir,
      runConversion,
      liftIO
    ) where

import Importer.Library

import Maybe
import qualified Data.Set as Set hiding (Set)
import Data.Set (Set)
import qualified Data.Map as Map hiding (Map)
import Data.Map (Map)
import Data.Tree
import Data.Graph

import Control.Monad.Reader (ReaderT, MonadReader, MonadIO, ask, liftIO, runReaderT, lift)
import Control.Monad.State (StateT, MonadState, get, put, modify, execStateT)
import Control.Monad.Error (MonadError)

import System.FilePath
import System.Directory
import IO

import qualified Importer.Msg as Msg
import qualified Importer.Ident_Env as Ident_Env
import qualified Importer.Configuration as Config (getCustomTheory)
import Importer.Configuration hiding (getCustomTheory)

import qualified Language.Haskell.Exts as Hsx
import qualified Importer.Hsx as Hsx
import qualified Importer.Isa as Isa


-- A Conversion Unit

{-|
  This data structure combines several Haskell modules and the corresponding environment.
  into one coherent unit.
-}
data HskUnit = HskUnit [Hsx.Module] CustomTranslations Ident_Env.GlobalE
  deriving (Show)

{-|
  This data structure combines several Isabelle theories and the corresponding environment
  into one coherent unit.
-}
data IsaUnit = IsaUnit [Isa.Module] [CustomTheory] Ident_Env.GlobalE
  deriving (Show)

newtype Conversion a = Conversion (ReaderT Config IO a)
    deriving (Functor, Monad, MonadReader Config, MonadIO, MonadError IOError)

isCustomModule :: Hsx.ModuleName -> Conversion Bool
isCustomModule
    = liftM isJust . getCustomTheory

getCustomisations :: Conversion Customisations
getCustomisations = ask >>= return . customisations

getCustomTheory :: Hsx.ModuleName -> Conversion (Maybe CustomTheory)
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
  let fps' = map (combine dirpath) . filter (`notElem` [".", ".."]) $ fps
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
  This function takes a parsed Haskell module and produces a Haskell unit by parsing
  all module imported by the given module and add including the initial global environment
  as given by 'Ident_Env.initialGlobalEnv'.
-}
parseHskFiles :: [FilePath] -> Conversion [HskUnit]
parseHskFiles paths
    = do (hsmodules,custTrans) <- parseFilesAndDependencies paths
         (depGraph, fromVertex, _) <- makeDependencyGraph hsmodules
         let cycles = cyclesFromGraph depGraph
      --   when (not (null cycles)) -- not a DAG?
      --        $ let toModuleName v = case fromVertex v of (_, Hsx.ModuleName n,_) -> n
      -- |           in fail (Msg.cycle_in_dependency_graph (map toModuleName (head cycles)))
         let toModule v = case fromVertex v of (m,_,_) -> m
         case map (map toModule . flatten) (components depGraph) of
           -- this should not happen
           [] -> fail $ "Internal error: No Haskell module was parsed!"
           modss -> 
               let mkUnit mods = HskUnit mods custTrans Ident_Env.initialGlobalEnv
               in return $ map mkUnit modss 
               
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
makeDependencyGraph ::  [Hsx.Module]
                    -> Conversion (Graph,
                          Vertex -> (Hsx.Module, Hsx.ModuleName, [Hsx.ModuleName]),
                          Hsx.ModuleName -> Maybe Vertex)
makeDependencyGraph hsmodules
    = do edges <- (mapM makeEdge hsmodules)
         return $ graphFromEdges edges
    where makeEdge hsmodule@(Hsx.Module _loc modul _ _ _exports imports _decls)
              = do let imported_modules = map Hsx.importModule imports
                   imported_modules'  <- filterM isCustomModule imported_modules
                   return (hsmodule, modul, imported_modules)


type ModuleImport = (FilePath, Maybe Hsx.ModuleName)

data GrovelS = GrovelS{gVisitedPaths :: Set FilePath,
                       gRemainingPaths :: [ModuleImport],
                       gParsedModules :: [Hsx.Module],
                       gCustTrans :: CustomTranslations}

newtype GrovelM a = GrovelM (StateT GrovelS Conversion a)
    deriving (Monad, Functor, MonadState GrovelS, MonadIO)



liftConv :: Conversion a -> GrovelM a 
liftConv = GrovelM . lift

checkVisited :: FilePath -> GrovelM Bool
checkVisited path = liftM (Set.member path . gVisitedPaths) get
                    
addModule :: Hsx.Module -> GrovelM ()
addModule mod@(Hsx.Module loc _ _ _ _ _ _)
    = modify (\ state@(GrovelS{gVisitedPaths = visited, gParsedModules = mods}) -> 
              state{gVisitedPaths = Set.insert (Hsx.srcFilename loc)  visited, gParsedModules = mod:mods})

addImports :: [ModuleImport] -> GrovelM ()
addImports imps = modify (\state@(GrovelS{gRemainingPaths = files}) -> state{gRemainingPaths = imps ++ files})
                  
{-|
  This function checks if the given module is a custom module. If it
  is it is added to the set of custom modules in the state and @True@
  is returned. Otherwise just @False@ is returned.
-}       
-- addCustMod :: Hsx.ModuleName -> GrovelM Bool
addCustMod mod =
    do state <- get
       mbCustThy <- liftConv $ getCustomTheory mod
       case mbCustThy of
         Nothing -> return False
         Just custThy ->
             put state{gCustTrans = Map.insert mod custThy (gCustTrans state)}
                 >> return True
         
{-|
  Same as 'addCustMod' but @True@ and @False@ are swapped.
-}
addCustMod' :: Hsx.ModuleName -> GrovelM Bool 
addCustMod' = liftM not . addCustMod
                   
nextImport :: GrovelM (Maybe ModuleImport)
nextImport =
    do state <- get
       case gRemainingPaths state of
         [] -> return Nothing
         p:ps ->
             do put $ state{gRemainingPaths = ps}
                return$ Just p

parseFilesAndDependencies :: [FilePath] -> Conversion ([Hsx.Module],CustomTranslations)
parseFilesAndDependencies files = 
    let GrovelM grovel = grovelImports
        mkImp file = (file,Nothing)
        imps = map mkImp files
        state = GrovelS Set.empty imps [] Map.empty
    in do state' <- execStateT grovel state
          return (gParsedModules state' , gCustTrans state')

grovelImports :: GrovelM ()
grovelImports = 
    do mbFile <- nextImport
       case mbFile of
         Nothing -> return ()
         Just file -> grovelFile file

grovelFile :: ModuleImport -> GrovelM ()
grovelFile imp@(file,_) = 
    do v <- checkVisited file
       if v 
        then grovelImports
        else do mod@(Hsx.Module _ name _ _ _ _ _) <- parseHskFile imp
                cust <- addCustMod name
                if cust then grovelImports
                 else addModule mod
                      >> grovelModule mod

-- grovelModule :: Hsx.ModuleName -> GrovelM ()
grovelModule hsmodule@(Hsx.Module loc baseMod _ _ _ imports _) = 
    do let newModules = map Hsx.importModule imports
       realModules <- filterM addCustMod' newModules
       let modImps = map mkModImp realModules
       liftIO $ mapM_ checkImp modImps
       addImports modImps
       grovelImports
    where baseLoc = Hsx.srcFilename loc
          mkModImp mod = (computeSrcPath baseMod baseLoc mod, Just mod)
          checkImp (file,Just mod) =
              do ext <- doesFileExist file
                 when (not ext) $ fail $ "The module \"" ++ Hsx.showModuleName mod
                          ++ "\" imported from module \"" ++ Hsx.showModuleName baseMod 
                                 ++ "\" cannot be found at \"" ++ file ++ "\"!"

{-|
  This function computes the path where to look for an imported module.
-}

computeSrcPath :: Hsx.ModuleName      -- ^the module that is importing
               -> FilePath     -- ^the path to the importing module
               -> Hsx.ModuleName       -- ^the module that is to be imported
               -> FilePath     -- ^the assumed path to the module to be imported
computeSrcPath importingMod basePath m
    = let curDir = takeDirectory basePath
          baseDir = shrinkPath . joinPath $ (splitPath curDir) ++ replicate (Hsx.moduleHierarchyDepth importingMod) ".."
      in combine baseDir (Hsx.module2FilePath m)   

shrinkPath :: FilePath -> FilePath
shrinkPath = joinPath . shrinkPath' . splitPath
    where shrinkPath' [] = []
          shrinkPath' [x] = [x]
          shrinkPath' (x:y:xs)
              | x /= "/" && y `elem` ["..", "../"] = shrinkPath' xs
              | otherwise = x : shrinkPath' (y:xs)
    
parseHskFile :: ModuleImport -> GrovelM Hsx.Module
parseHskFile (file, mbMod)  = 
    do result <- liftIO $ Hsx.parseFile file `catch`
                (\ioError -> fail $ "An error occurred while reading module file \"" ++ file ++ "\": " ++ show ioError)
       case result of
         (Hsx.ParseFailed loc msg) ->
             fail $ "An error occurred while parsing module file: " ++ Msg.failed_parsing loc msg
         (Hsx.ParseOk m@(Hsx.Module _ mName _ _ _ _ _)) ->
             case mbMod of
               Nothing -> return m
               Just expMod ->
                   if mName == expMod
                   then return m
                   else fail $ "Name mismatch: Name of imported module in \"" 
                            ++ file ++"\" is " ++ Hsx.showModuleName mName
                                   ++ ", expected was " ++ Hsx.showModuleName expMod

