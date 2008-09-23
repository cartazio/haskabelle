{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen

Toplevel interface to importer.
-}

module Importer (
  module Importer.Convert,
  module Importer.IsaSyntax,
  module Importer.Printer,
  convertFiles, importFiles, importDir, importProject,
  convertSingleFile, preprocessFile, withCurrentDirectory
) where

import Prelude hiding (catch)
import System.FilePath
import System.Directory
import IO hiding (catch,bracket_)
import Directory

import List (intersperse)
import Control.Monad
import Control.Exception

import Data.Tree
import Text.PrettyPrint (render, vcat, text, (<>), Doc)

import Language.Haskell.Exts (ParseResult(..), parseFile, HsModule(..))
import Language.Haskell.Exts.Pretty 
import Language.Haskell.Exts.Syntax 
import Importer.IsaSyntax (Cmd(..), Theory(..))

import Importer.Configuration
import Importer.Preprocess
import Importer.Utilities.Hsk (srcloc2string, module2FilePath, isHaskellSourceFile)
import Importer.Utilities.Misc
import Importer.ConversionUnit
import Importer.Convert
import Importer.Printer (pprint)
import Importer.LexEnv


{-|
  Converts a Haskell unit identified by the given file path (i.e., the module defined
  therein and all imported modules) to a Isabelle unit. Furthermore a list of all 
  Haskell files that were converted is returned.
-}
convertSingleFile :: FilePath -> IO (IsaUnit, [FilePath])
convertSingleFile fp =
    let dir      = takeDirectory fp
        filename = takeFileName fp
    in withCurrentDirectory (if dir == "" then "./" else dir) $
       do unit@(HskUnit hsmodules _) <- makeHskUnitFromFile filename 
          let dependentModuleNs = map (\(HsModule _ m _ _ _) -> m) hsmodules
          let dependentFiles    = map module2FilePath dependentModuleNs
          let isaUnit = convertHskUnit unit
          return (isaUnit,dependentFiles)
{-|
  This function converts all Haskell files into Isabelle units.
-}
convertFiles :: [FilePath] -> IO [IsaUnit]
convertFiles []   = return []
convertFiles (fp:fps) = do
  (isaUnit,dependentFiles) <-
      do
        putStr $ "converting " ++ (takeFileName fp) ++ " ...\n"
        (unit,files) <- convertSingleFile fp
        return ([unit],files)        
      `catch` (\ exc -> do
                 print exc
                 return ([],[]))
--  units <- convertFiles fps
  units <- convertFiles (filter (`notElem` dependentFiles) fps) 
  return  (isaUnit ++ units)
     
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

{-|
  This function changes the current directory to that given in the first argument
  and executes the given IO monad in that context. Afterwards the previous current
  directory is restored.
-}    
withCurrentDirectory :: FilePath -> IO a -> IO a
withCurrentDirectory fp body
    = do oldcwd <- getCurrentDirectory
         bracket_ (setCurrentDirectory fp) (setCurrentDirectory oldcwd) body

{-|
  This function imports all Haskell files given in the list of files into Isabelle theories
  that are written into files in the given destination directory.
-}
importFiles :: [FilePath] -- ^source files
            -> FilePath    -- ^destination directory
            -> IO ()
importFiles sources dstdir
    = do exists <- doesDirectoryExist dstdir
         when (not exists) $ createDirectory dstdir
         do convertedUnits <- convertFiles sources
            withCurrentDirectory dstdir
              $ sequence_ (map writeIsaUnit convertedUnits)

{-|
  This function imports all Haskell files that are contained in the given directory an its
  subdirectories (recursively) to Isabelle theories that are written in files in the given
  destination directory.
-}
importDir :: FilePath -- ^source directory
          -> FilePath -- ^destination directory
          -> IO ()
importDir srcdir dstdir
    = do exists <- doesDirectoryExist dstdir
         when (not exists) $ createDirectory dstdir
         fps   <- getFilesRecursively srcdir
         convertedUnits <- convertFiles (filter isHaskellSourceFile fps)
         withCurrentDirectory dstdir
              $ sequence_ (map writeIsaUnit convertedUnits)



importProject :: Config -> IO ()
importProject conf
    = do let outDir = outputLocation conf
         inFiles <- liftM concat $ mapM getFiles $ inputLocations conf 
         exists <- doesDirectoryExist outDir
         when (not exists) $ createDirectory outDir
         convertedUnits <- convertFiles (filter isHaskellSourceFile inFiles)
         withCurrentDirectory outDir
              $ sequence_ (map writeIsaUnit convertedUnits)
    where getFiles :: InputLocation -> IO [FilePath]
          getFiles (FileInputLocation path) = do ex <- doesFileExist path
                                                 if ex
                                                   then return [path]
                                                   else putStr ("Warning: File \"" ++ path ++ "\"does not exist!") >> return []
          getFiles (DirInputLocation path) = do ex <- doesDirectoryExist path
                                                if ex
                                                  then getFilesRecursively path
                                                  else putStr ("Warning: Directory \"" ++ path ++ "\"does not exist!") >> return []

{-|
  This function writes all Isabelle theories contained in the given unit to corresponding
  files (named @/\<theory name\>/.thy@) in the current directory.
-}
writeIsaUnit :: IsaUnit -> IO ()
writeIsaUnit (IsaUnit thys env)
    = mapM_ (flip writeTheory env) thys

{-|
  This function writes the given Isabelle theory in the given environment to a file
  @/\<theory name\>/.thy@ in the current directory.
-}
writeTheory :: Cmd ->  GlobalE -> IO ()
writeTheory thy@(TheoryCmd (Theory thyname) _) env 
    = do let content = render (pprint thy env)
         let dstName = content `seq` map (\c -> if c == '.' then '_' else c) thyname ++ ".thy"
         putStr $ "writing " ++ dstName ++ "...\n"
         writeFile dstName content


{-|
  This function pretty prints the given Isabelle Unit.
-}
pprintIsaUnit :: IsaUnit -> Doc
pprintIsaUnit (IsaUnit thys env)
    = vcat (map (dashes . flip pprint env) thys)
    where dashes d = d <> (text "\n") <> (text (replicate 60 '-'))

printIsaUnit_asAST :: IsaUnit -> Doc
printIsaUnit_asAST (IsaUnit thys env)
    = vcat (map (dashes . text . prettyShow) thys)
    where dashes d = d <> (text "\n") <> (text (replicate 60 '-'))



{-|
  This function turns a relative path into an absolute path using
  the current directory as provided by 'getCurrentDirectory'.
-}

makeAbsolute :: FilePath -> IO FilePath
makeAbsolute fp = liftM2 combine getCurrentDirectory (return fp)

----------------------------------------------------------
------------ Preprocessing Only --------------------------
----------------------------------------------------------

{-|
  This function writes the given Haskell unit into the given directory.
-}
writeHskUnit :: HskUnit -> FilePath -> IO ()
writeHskUnit (HskUnit modules _) outDir
    = mapM_ (`writeHskModule` outDir) modules


{-|
  This function writes a single Haskell module into the given
  destination directory.
-}
writeHskModule :: HsModule -> FilePath -> IO ()
writeHskModule mod@(HsModule _ (Module modName) _ _ _) dir = do
  let modCont = prettyPrint mod
  let dstName = map (\c -> if c == '.' then '_' else c) modName ++ ".hs"
  withCurrentDirectory dir $
                       writeFile dstName modCont

{-|
  This function preprocesses the given Haskell file an stores
  the resulting Haskell file into the given destination directory.
-}
preprocessFile :: FilePath -> FilePath -> IO ()
preprocessFile inFile outDir = do
  hskUnit <- makeHskUnitFromFile inFile
  let HskUnit modules env = hskUnit
  let ppModules = map preprocessHsModule modules
  let ppUnit = HskUnit ppModules env
  writeHskUnit ppUnit outDir
