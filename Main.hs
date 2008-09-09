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

main :: IO ()
main = do
  progname <- getProgName
  args     <- getArgs
  mainProgArgs progname args

mainArgs :: [String] -> IO()
mainArgs args = mainProgArgs "importer" args


mainProgArgs :: String -> [String] -> IO ()
mainProgArgs progname args =
  case args of
    []   -> ioError $ userError ("Usage: " ++ progname ++ " [[source_file | source_dir]]* destination_dir")
    args -> let
           destdirRel = last args
           fpsRel     = init args 
           in do 
             -- make paths absolute
             destdir <- makeAbsolute destdirRel
             fps <- mapM makeAbsolute fpsRel
             dirs  <- filterM doesDirectoryExist fps
             files <- filterM doesFileExist fps
             assert (all (`elem` dirs ++ files) fps) $
                    sequence_ ([importFiles files destdir] ++ map (\srcdir -> importDir srcdir destdir) dirs) 
                              `catch` (\ e -> print e >> putStr "\nProcess finished with uncaught exceptions!\n")
             putStr "done"
