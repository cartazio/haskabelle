module Parsing
where

import Control.Monad
import Data.List
import System.Directory (getDirectoryContents)
import Language.Haskell.Exts (ParseResult(..), parseFile, HsModule(..))

traverseDir :: FilePath -> (FilePath -> IO ()) -> IO ()
traverseDir dirpath op = do
  fps <- getDirectoryContents dirpath `catch` const (return [])
  let fps' = (map (\ d -> dirpath ++ "/" ++ d)) . (filter (`notElem` [".", ".."])) $ fps
  mapM_ work fps'
        where work f = do
                op f
                traverseDir f op

parseTest =let d = "/home/paba/studies/NICTA/hsimp/ref/hsimp_testing/Test.hs" in do
  res <- parseFile "/home/paba/studies/NICTA/hsimp/ref/hsimp_testing/Test.hs"
  case res of
    ParseOk _ -> putStrLn ("OK: " ++ d)
    ParseFailed loc msg -> do
              putStrLn ("Failed: " ++ d)
              putStrLn ("  Message: " ++ msg)
              putStrLn ("  Location: " ++ (show loc))


parse = traverseDir "/home/paba/studies/NICTA/hsimp/ref/refine/haskell/src"
        (\ d -> when (".hspp" `isSuffixOf` d) $ do
                  res <- parseFile d
                  case res of
                    ParseOk _ -> putStrLn ("OK: " ++ d)
                    ParseFailed loc msg -> do
                             putStrLn ("Failed: " ++ d)
                             putStrLn ("  Message: " ++ msg)
                             putStrLn ("  Location: " ++ (show loc))
        )