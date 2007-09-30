{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Munich

Toplevel interface to importer.
-}

module Main (
  module Importer.Convert,
  module Importer.IsaSyntax,
  module Importer.Printer,
  convertFile, -- importFile, cnvFile
) where

import IO
import Control.Monad
import System.Environment (getArgs)
import Text.PrettyPrint (render, vcat, text, (<>))

import Language.Haskell.Hsx (ParseResult(..), parseFile, HsModule(..))

import Importer.ConversionUnit
import Importer.Preprocess
import Importer.LexEnv
import Importer.Convert
import Importer.IsaSyntax (Cmd)
import Importer.Printer (pprint)


-- The main function, takes a path to a Haskell source file and
-- returns its convertion, that is an AST for Isar/HOL as defined in
-- Importer.IsaSyntax.
--
-- The AST can then be feed to the pretty printer (Importer.Printer.pprint)
-- to return a Text.PrettyPrinter.doc datum.
--
-- E.g.
--
--    do (ConvSuccess ast _) <- convertFile "/path/foo.hs"
--       return (pprint ast)
--
convertFile   :: FilePath -> IO ConversionUnit
convertFile fp = do (ParseOk initHsModule) <- parseFile fp
                    unit <- try (makeConversionUnit initHsModule)
                    case unit of
                      Left ioerror -> error (show ioerror)
                      Right (HsxUnit hsmodules) 
                          -> let hsmodules' = map preprocessHsModule hsmodules
                                 globalenv  = makeGlobalEnv_Hsx hsmodules'
                                 isathys    = map (convertHsModule globalenv) hsmodules' 
                             in return (IsaUnit (map (\(ConvSuccess cmd _) -> cmd) isathys))

pprintConversionUnit (IsaUnit thys)
    = vcat (map (dashes . pprint) thys)
    where dashes d = d <> (text "\n") <> (text (replicate 60 '-'))
                    

-- importFile :: FilePath -> FilePath -> IO ()
-- importFile src dst = do
--   ConvSuccess abstract _ <- convertFile src
--   let concrete = (render . pprint) abstract ++ "\n"
--   writeFile dst concrete

-- Like `convertFile' but returns the textual representation of the
-- AST itself. 
-- cnvFile :: FilePath -> IO String
-- cnvFile = liftM cnvFileContents . readFile

-- main :: IO ()
-- main = do
--   args <- getArgs
--   case args of
--     [src, dst] -> importFile src dst
--     _ -> ioError (userError "exactly two arguments expected")
