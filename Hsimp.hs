
module Hsimp (
    module Hsimp.Convert, 
    module Hsimp.IsaSyntax,
    module Hsimp.Printer,
    convertFile, cnvFile
 ) where

import Hsimp.Convert
import Hsimp.IsaSyntax
import Hsimp.Printer

convertFile fp = readFile fp >>= (return . convertFileContents)

cnvFile fp = readFile fp >>= cnvFileContents

