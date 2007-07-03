
module Hsimp (
    module Hsimp.Convert, 
    module Hsimp.IsaSyntax,
    module Hsimp.Printer, -- especially `pprint'
    convertFile, cnvFile
 ) where

import Hsimp.Convert
import Hsimp.IsaSyntax
import Hsimp.Printer

-- The main function, takes a path to a Haskell source file and
-- returns its convertion, that is an AST for Isar/HOL as defined in
-- Hsimp.IsaSyntax.
--
-- The AST can then be feed to the pretty printer (Hsimp.Printer.pprint)
-- to return a Text.PrettyPrinter.doc datum.
--
-- E.g.
--
--    do (ConvSuccess ast _) <- convertFile "/path/foo.hs"
--       return (pprint ast)
--
convertFile :: FilePath -> IO (Convertion Hsimp.IsaSyntax.Cmd)
convertFile fp = readFile fp >>= (return . convertFileContents)

-- Like `convertFile' but returns the textual representation of the
-- AST itself. 
cnvFile :: FilePath -> IO String
cnvFile fp = readFile fp >>= cnvFileContents

