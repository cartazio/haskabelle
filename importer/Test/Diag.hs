{-| Author: Tobias Rittweiler, TU Muenchen

Collection of various diagnostic function
-}

module Importer.Test.Diag where

import System.FilePath
import Data.Tree
import Text.PrettyPrint (render, vcat, text, (<>), Doc)

import Language.Haskell.Exts.Pretty 
import Language.Haskell.Exts.Syntax 

import Importer.ConversionUnit
import Importer.Configuration
import Importer.Printer (pprint)
import Importer.Preprocess
import Importer.Utilities.Misc


{-|
  This function pretty prints the given Isabelle Unit.
-}
pprintIsaUnit :: IsaUnit -> Doc
pprintIsaUnit (IsaUnit thys _ env)
    = vcat (map (dashes . flip pprint env) thys)
    where dashes d = d <> (text "\n") <> (text (replicate 60 '-'))

printIsaUnit_asAST :: IsaUnit -> Doc
printIsaUnit_asAST (IsaUnit thys _ env)
    = vcat (map (dashes . text . prettyShow) thys)
    where dashes d = d <> (text "\n") <> (text (replicate 60 '-'))

{-|
  This function writes the given Haskell unit into the given directory.
-}
writeHskUnit :: HskUnit -> FilePath -> IO ()
writeHskUnit (HskUnit modules _ _) outDir
    = mapM_ (`writeHskModule` outDir) modules


{-|
  This function writes a single Haskell module into the given
  destination directory.
-}
writeHskModule :: HsModule -> FilePath -> IO ()
writeHskModule mod@(HsModule _ (Module modName) _ _ _) dir
    = do let modCont = prettyPrint mod
         let dstName = map (\c -> if c == '.' then '_' else c) modName ++ ".hs"
         let dstPath = combine dir dstName
         writeFile dstPath modCont

{-|
  This function preprocesses the given Haskell file an stores
  the resulting Haskell file into the given destination directory.
-}
preprocessFile :: FilePath -> FilePath -> IO ()
preprocessFile inFile outDir = do
  hskUnits <- runConversion (defaultConfig [] outDir defaultCustomisations) $ parseHskFiles [inFile]
  let [HskUnit modules custMods env] = hskUnits
  let ppModules = map preprocessHsModule modules
  let ppUnit = HskUnit ppModules custMods env
  writeHskUnit ppUnit outDir
 