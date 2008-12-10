{-  Author:     Tobias C. Rittweiler, TU Muenchen

Toplevel interface to Haskabelle importer.
-}

module Importer (
  module Importer.Convert,
  module Importer.IsaSyntax,
  module Importer.Printer,
  importFiles, importDir, importProject,
  preprocessFile, 
  defaultCustomisations
) where

import Prelude hiding (catch)
import System.FilePath
import System.Directory
import IO hiding (catch,bracket_)
import Directory

import List (intersperse)
import Control.Monad
import Control.Monad.Error
import Control.Exception

import Data.Tree
import Text.PrettyPrint (render, vcat, text, (<>), Doc)

import Language.Haskell.Exts (ParseResult(..), parseFile, HsModule(..))
import Language.Haskell.Exts.Pretty 
import Language.Haskell.Exts.Syntax 
import Importer.IsaSyntax (Cmd(..), Theory(..))

import Importer.Configuration
import Importer.Preprocess
import Importer.Utilities.Hsk
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
convertFiles :: [FilePath] -> Conversion [IsaUnit]
convertFiles files
    =do units <- parseHskFiles files 
        custs <- getCustomisations
        let isaUnits = map (convertHskUnit custs) units
        return isaUnits

importDir :: FilePath -> FilePath -> IO ()
importDir file out = importProject $ defaultConfig [file] out defaultCustomisations

importFiles :: [FilePath] -> FilePath -> IO ()
importFiles files out = importProject $ defaultConfig files out defaultCustomisations

importProject :: Config -> IO ()
importProject config = runConversion config importProject'

importProject' :: Conversion ()
importProject' 
    = do inFiles <- getInputFilesRecursively
         outDir <- getOutputDir
         exists <- liftIO $ doesDirectoryExist outDir
         when (not exists) $ liftIO $ createDirectory outDir
         convertedUnits <- convertFiles (filter isHaskellSourceFile inFiles)
         sequence_ (map writeIsaUnit convertedUnits)

{-|
  This function writes all Isabelle theories contained in the given unit to corresponding
  files (named @/\<theory name\>/.thy@) in the current directory.
-}
writeIsaUnit :: IsaUnit -> Conversion ()
writeIsaUnit (IsaUnit thys custThys env)
    = mapM_ writeCustomTheory custThys >>
      mapM_ (flip writeTheory env) thys

writeCustomTheory :: CustomTheory -> Conversion ()
writeCustomTheory cust = 
    do let src = getCustomTheoryPath cust
           filename = takeFileName src
       outDir <- getOutputDir
       let dest = combine outDir filename
       liftIO $ copyFile src dest
       
    

{-|
  This function writes the given Isabelle theory in the given environment to a file
  @/\<theory name\>/.thy@ in the current directory.
-}
writeTheory :: Cmd ->  GlobalE -> Conversion ()
writeTheory thy@(TheoryCmd (Theory thyname)_ _) env 
    = do let content = render (pprint thy env)
         let dstName = content `seq` map (\c -> if c == '.' then '_' else c) thyname ++ ".thy"
         outLoc <- getOutputDir
         let dstPath = combine outLoc dstName
         liftIO $ putStr $ "writing " ++ dstName ++ "...\n"
         liftIO $ writeFile dstPath content

{-|
  This function pretty prints the given Isabelle Unit.
-}
pprintIsaUnit :: IsaUnit -> Doc
pprintIsaUnit (IsaUnit thys _ env)
    = vcat (map (dashes . flip pprint env) thys)
    where dashes d = d <> (text "\n") <> (text (replicate 60 '-'))

printIsaUnit_asAST :: IsaUnit -> Doc
printIsaUnit_asAST (IsaUnit thys _ env)
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
writeHskUnit (HskUnit modules _ _) outDir
    = mapM_ (`writeHskModule` outDir) modules


{-|
  This function writes a single Haskell module into the given
  destination directory.
-}
writeHskModule :: HsModule -> FilePath -> IO ()
writeHskModule mod@(HsModule _ (Module modName) _ _ _) dir
    = do let modCont = prettyPrint mod
         let dstName = map (\c -> if c == '.' then '_' else c) modName ++ ".hs"
         let dstPath = combine dir dstName
         writeFile dstPath modCont

{-|
  This function preprocesses the given Haskell file an stores
  the resulting Haskell file into the given destination directory.
-}
preprocessFile :: FilePath -> FilePath -> IO ()
preprocessFile inFile outDir = do
  hskUnits <- runConversion (defaultConfig [] outDir defaultCustomisations) $ parseHskFiles [inFile]
  let [HskUnit modules custMods env] = hskUnits
  let ppModules = map preprocessHsModule modules
  let ppUnit = HskUnit ppModules custMods env
  writeHskUnit ppUnit outDir