{-# OPTIONS_GHC -fglasgow-exts -O -o bin/haskabelle_bin -odir build -hidir build -stubdir build #-}

{-  Author: Florian Haftmann, TU Muenchen

Toplevel interface to Haskabelle importer.
-}

module Main where

import System.Environment (getArgs, getProgName)
import System.Exit (exitWith, ExitCode (ExitFailure))

import Importer.FilePrinter (importProject, importFiles)
import Importer.Adapt.Read (readAdapt, Adaption (..))
import Importer.Configuration (readConfig)
import Importer.Version

usage :: String -> IO ()
usage executableName = do
  putStrLn ("This is " ++ version ++ ".")
  putStrLn ""
  putStrLn ("Usage: " ++ executableName  ++ " [--adapt <ADAPT>] <SRC1> .. <SRCn> <DST> | --config <CONFIG>")
  putStrLn ""
  putStrLn "  Import Haskell files <SRC1> .. <SRCn> into Isabelle theories in directory DST,"
  putStrLn "    optionally using customary adaption in directory <ADAPT>"
  putStrLn "    OR import Haskell files according to configuration file <CONFIG>"
  putStrLn ""
  exitWith (ExitFailure 1)

mainInterface :: [String] -> IO ()
mainInterface [executableName, defaultAdaptDir, "--config", configFile] = do
  config <- readConfig configFile
  importProject config defaultAdaptDir
mainInterface (executableName : _ : "--adapt" : adaptDir : srcs_dst @ (_ : _ : _)) =
  importFiles adaptDir (init srcs_dst) (last srcs_dst)
mainInterface (executableName : defaultAdaptDir : srcs_dst @ (_ : _ : _)) =
  importFiles defaultAdaptDir (init srcs_dst) (last srcs_dst)
mainInterface (executableName : _) =
  usage executableName 

main :: IO ()
main = getArgs >>= mainInterface
