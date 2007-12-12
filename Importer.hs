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
import Directory
import Control.Monad
import System.Environment (getArgs)
import Text.PrettyPrint (render, vcat, text, (<>))

import Language.Haskell.Hsx (ParseResult(..), parseFile, HsModule(..))
import Importer.IsaSyntax (Cmd(..), Theory(..))

import Importer.Utilities.Hsx (srcloc2string)
import Importer.ConversionUnit
import Importer.Convert
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
convertFile fp = do hsModule <- parseFileOrLose fp
                    unit <- try (makeConversionUnit hsModule)
                    case unit of
                      Left ioerror  -> error (show ioerror)
                      Right hsxunit -> return (convertHsxUnit hsxunit)
    where parseFileOrLose fp = do result <- parseFile fp
                                  case result of
                                    ParseOk hsm -> return hsm
                                    ParseFailed loc msg
                                        -> error (srcloc2string loc ++ ": " ++ msg)



pprintConversionUnit (IsaUnit thys)
    = vcat (map (dashes . pprint) thys)
    where dashes d = d <> (text "\n") <> (text (replicate 60 '-'))
                    

importFile :: FilePath -> FilePath -> IO ()
importFile src dstdir
    = do exists <- doesDirectoryExist dstdir
         when (not exists) $ createDirectory dstdir
         do IsaUnit thys <- convertFile src
            setCurrentDirectory dstdir
            sequence_ (map writeTheory thys)
    where writeTheory thy@(TheoryCmd (Theory thyname) _)
              = do let content = render (pprint thy)
                   let dstName = map (\c -> if c == '.' then '_' else c) thyname
                   writeFile (dstName++".thy") content
  

-- Like `convertFile' but returns the textual representation of the
-- AST itself. 
-- cnvFile :: FilePath -> IO String
-- cnvFile = liftM cnvFileContents . readFile

main :: IO ()
main = do
  args <- getArgs
  case args of
    [src, dstdir] -> importFile src dstdir
    _ -> ioError (userError "exactly two arguments expected")
