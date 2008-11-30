{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen

Toplevel interface to importer.
-}

module Main where

import Prelude hiding (catch)
import Importer
import Control.Monad
import Control.Exception
import System.Environment(getArgs, getProgName)
import System.Directory
import Importer.Configuration


import Importer.Preprocess

main = runTest

main' :: IO ()
main' = do
  progname <- getProgName
  args     <- getArgs
  mainProgArgs progname args

mainArgs :: [String] -> IO()
mainArgs args = mainProgArgs "importer" args


mainProgArgs :: String -> [String] -> IO ()
mainProgArgs progname args
    = case args of
        [configFile] -> 
            do config <- readConfig configFile
               importProject config
        _ -> error $ "Usage: " ++ progname ++ " <config file>"
