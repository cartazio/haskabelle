{-| Author: Tobias C. Rittweiler, TU Muenchen

Internal importer main interfaces.
-}

module Importer.Conversion (importFiles, importProject) where

import Importer.Library

import Text.PrettyPrint (render)

import System.FilePath
import System.Directory
import System.IO

import Importer.Adapt (Adaption (..), AdaptionTable, readAdapt, preludeFile)
import Importer.Configuration
import Importer.Convert
import Importer.Printer (pprint)

import qualified Importer.Ident_Env as Ident_Env (GlobalE)
import qualified Importer.Isa as Isa (Module (..), ThyName (..))
import qualified Importer.Hsx as Hsx


importProject :: Config -> FilePath -> IO ()
importProject config adaptDir = do
  adapt <- readAdapt adaptDir
  runConversion config (convertFiles adapt)

importFiles :: FilePath -> [FilePath] -> FilePath -> IO ()
importFiles adaptDir files out
  = importProject (defaultConfig files out defaultCustomisations) adaptDir

convertFiles :: Adaption -> Conversion ()
convertFiles adapt = do

  inFiles <- getInputFilesRecursively
  outDir <- getOutputDir
  custs <- getCustomisations
  
  exists <- liftIO $ doesDirectoryExist outDir
  when (not exists) $ liftIO $ createDirectory outDir

  units <- parseHskFiles (filter Hsx.isHaskellSourceFile inFiles)
  let (adaptTable : _, convertedUnits) = map_split (convertHskUnit custs adapt) units

  liftIO $ copyFile (preludeFile adapt) (combine outDir (takeFileName (preludeFile adapt)))
  sequence_ (map (writeIsaUnit adaptTable (reservedKeywords adapt)) convertedUnits)


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

writeTheory :: AdaptionTable -> [String] -> Ident_Env.GlobalE -> Isa.Module -> Conversion ()
writeTheory adapt reserved env thy @ (Isa.Module (Isa.ThyName thyname) _ _) = do
  let content = render (pprint adapt reserved env thy)
  let dstName = content `seq` map (\c -> if c == '.' then '_' else c) thyname ++ ".thy"
  outLoc <- getOutputDir
  let dstPath = combine outLoc dstName
  liftIO $ putStr $ "writing " ++ dstName ++ "...\n"
  liftIO $ writeFile dstPath content
