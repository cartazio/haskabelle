{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen

Toplevel interface to importer.
-}

module Main where

import Importer
import Control.Monad
import Control.Exception
import System.Environment(getArgs, getProgName)
import System.Directory

main :: IO ()
main = do
  progname <- getProgName
  args     <- getArgs
  case args of
    []   -> ioError $ userError ("Usage: " ++ progname ++ " [[source_file | source_dir]]* destination_dir")
    args -> let destdir = last args 
                fps     = init args
            in do dirs  <- filterM doesDirectoryExist fps
                  files <- filterM doesFileExist fps
                  assert (all (`elem` dirs ++ files) fps)
                    $ sequence_ ([importFiles files destdir] 
                                 ++ map (\srcdir -> importDir srcdir destdir) dirs)
