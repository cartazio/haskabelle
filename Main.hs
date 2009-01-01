{-# OPTIONS_GHC -fglasgow-exts -O -o bin/haskabelle_bin -odir build -hidir build -stubdir build #-}

{-  Author: Florian Haftmann, TU Muenchen

Toplevel interface to Haskabelle importer.
-}

module Main where

import System.Environment (getArgs, getProgName)
import System.Exit (exitWith, ExitCode (ExitFailure))

import Importer.FilePrinter (importProject, importFiles)
import Importer.Adapt.Read (readAdapt, Adaption (..))
import qualified Importer.Adapt.Raw as Adapt -- FIXME
import Importer.Configuration (readConfig)
import Importer.Version

-- FIXME
staticAdaption :: Adaption
staticAdaption = Adaption {
  rawAdaptionTable = Adapt.raw_adaption_table,
  reservedKeywords = Adapt.reserved_keywords,
  usedConstNames = Adapt.used_const_names,
  usedThyNames = Adapt.used_thy_names }

usage :: String -> IO ()
usage executableName = do
  putStrLn ("This is " ++ version ++ ".")
  putStrLn ""
  putStrLn ("Usage: " ++ executableName  ++ " <SRC1> .. <SRCn> <DST> | --config <CONFIG>")
  putStrLn ""
  putStrLn "  Import Haskell files <SRC1> .. <SRCn> into Isabelle theories in directory DST"
  putStrLn "    OR import Haskell files according to configuration file <CONFIG>"
  putStrLn ""
  exitWith (ExitFailure 1)

mainInterface :: [String] -> IO ()
mainInterface [executableName, "--config", configFile] = do
  config <- readConfig configFile
  importProject config staticAdaption
mainInterface (executableName : srcs_dst @ (_ : _ : _)) =
  importFiles staticAdaption (init srcs_dst) (last srcs_dst)
mainInterface (executableName : _) =
  usage executableName 

main :: IO ()
main = getArgs >>= mainInterface
