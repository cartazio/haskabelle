{-  Author:     Tobias C. Rittweiler, TU Muenchen

Importing and writing whole bunches of files.
-}

module Importer.FilePrinter (importFiles, importProject) where

import Control.Monad.Error
import System.FilePath
import System.Directory
import Text.PrettyPrint (render)

import Importer.ConversionUnit
import Importer.Convert
import Importer.Configuration
import Importer.Printer (pprint)
import Importer.LexEnv
import Importer.IsaSyntax (Cmd(..), Theory(..))
import Importer.Utilities.Hsk

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

importProject' :: Conversion ()
importProject' 
    = do inFiles <- getInputFilesRecursively
         outDir <- getOutputDir
         exists <- liftIO $ doesDirectoryExist outDir
         when (not exists) $ liftIO $ createDirectory outDir
         convertedUnits <- convertFiles (filter isHaskellSourceFile inFiles)
         sequence_ (map writeIsaUnit convertedUnits)

importProject :: Config -> IO ()
importProject config = runConversion config importProject'

importFiles :: [FilePath] -> FilePath -> IO ()
importFiles files out = importProject $ defaultConfig files out defaultCustomisations


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
