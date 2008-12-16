{-  Author:     Florian Haftmann, TU Muenchen

Toplevel interface to Haskabelle importer.
-}

module Main where

import System.Environment(getArgs, getProgName)
import System.Exit(exitWith, ExitCode(ExitFailure))

import Importer(importProject, importFiles)
import Importer.Configuration(readConfig)

usage :: IO ()
usage = do
  executable <- getProgName
  putStrLn ""
  putStrLn ("Usage: " ++ executable ++ " <SRC1> .. <SRCn> <DST> | --config <CONFIG>")
  putStrLn ""
  putStrLn "  Import Haskell files <SRC1> .. <SRCn> into Isabelle theories in directory DST"
  putStrLn "    OR import Haskell files according to configuration file <CONFIG>"
  putStrLn ""
  exitWith (ExitFailure 1)

mainInterface :: [String] -> IO ()
mainInterface ["--config", configFile] = do
  config <- readConfig configFile
  importProject config
mainInterface srcs_dst @ (_ : _ : _) =
  importFiles (init srcs_dst) (last srcs_dst)
mainInterface _ =
  usage

main :: IO ()
main = getArgs >>= mainInterface
