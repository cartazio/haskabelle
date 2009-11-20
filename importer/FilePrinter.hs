{-| Author: Tobias C. Rittweiler, TU Muenchen

Importing whole bunches of files.
-}

module Importer.FilePrinter (importFiles, importProject) where

import Importer.Library

import Text.PrettyPrint (render)

import System.FilePath
import System.Directory
import System.IO

import Importer.Adapt (Adaption (..), AdaptionTable, readAdapt, preludeFile)
import Importer.Configuration
import Importer.ConversionUnit
import Importer.Convert
import Importer.Printer (pprint)

import qualified Importer.Ident_Env as Ident_Env (GlobalE)
import qualified Importer.Isa as Isa (Module(..), ThyName(..))
import qualified Importer.Hsx as Hsx

{-|
  Converts a Haskell unit identified by the given file path (i.e., the module defined
  therein and all imported modules) to a Isabelle unit. Furthermore a list of all 
  Haskell files that were converted is returned.
-}
convertFiles :: Adaption -> [FilePath] -> Conversion (AdaptionTable, [IsaUnit])
convertFiles adapt files = do
  units <- parseHskFiles files 
  custs <- getCustomisations
  let (adaptTable : _, convs) = unzip (map (convertHskUnit custs adapt) units)
  return (adaptTable, convs)

importProject' :: Adaption -> Conversion ()
importProject' adapt = do
  inFiles <- getInputFilesRecursively
  outDir <- getOutputDir
  exists <- liftIO $ doesDirectoryExist outDir
  when (not exists) $ liftIO $ createDirectory outDir
  (adaptTable, convertedUnits) <- convertFiles adapt (filter Hsx.isHaskellSourceFile inFiles)
  liftIO $ copyFile (preludeFile adapt) (combine outDir (takeFileName (preludeFile adapt)))
  sequence_ (map (writeIsaUnit adaptTable (reservedKeywords adapt)) convertedUnits)

importProject :: Config -> FilePath -> IO ()
importProject config adaptDir = do
  adapt <- readAdapt adaptDir
  runConversion config (importProject' adapt)

importFiles :: FilePath -> [FilePath] -> FilePath -> IO ()
importFiles adaptDir files out
  = importProject (defaultConfig files out defaultCustomisations) adaptDir


{-|
  This function writes all Isabelle theories contained in the given unit to corresponding
  files (named @/\<theory name\>/.thy@) in the current directory.
-}
writeIsaUnit :: AdaptionTable -> [String] -> IsaUnit -> Conversion ()
writeIsaUnit adapt reserved (IsaUnit thys custThys env)
    = mapM_ writeCustomTheory custThys >>
      mapM_ (writeTheory adapt reserved env) thys

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
writeTheory :: AdaptionTable -> [String] -> Ident_Env.GlobalE -> Isa.Module -> Conversion ()
writeTheory adapt reserved env thy @ (Isa.Module (Isa.ThyName thyname) _ _) = do
  let content = render (pprint adapt reserved env thy)
  let dstName = content `seq` map (\c -> if c == '.' then '_' else c) thyname ++ ".thy"
  outLoc <- getOutputDir
  let dstPath = combine outLoc dstName
  liftIO $ putStr $ "writing " ++ dstName ++ "...\n"
  liftIO $ writeFile dstPath content
