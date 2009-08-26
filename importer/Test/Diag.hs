{-| Author: Tobias Rittweiler, TU Muenchen

Collection of various diagnostic function
-}

module Importer.Test.Diag where

import System.FilePath
import Data.Tree
import Text.PrettyPrint (render, vcat, text, (<>), Doc)

import Importer.Library

import Language.Haskell.Exts.Pretty 
import Language.Haskell.Exts.Syntax 

import Importer.ConversionUnit
import Importer.Configuration
import Importer.Printer (pprint)
import Importer.Preprocess


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
    = mapM_ (`writeHskHs.ModuleName` outDir) modules


{-|
  This function writes a single Haskell module into the given
  destination directory.
-}
writeHskHs.ModuleName :: Hs.ModuleName -> FilePath -> IO ()
writeHskHs.ModuleName mod@(Hs.ModuleName _ (Hs.ModuleName modName) _ _ _) dir
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
  let ppHs.ModuleNames = map preprocessHs.ModuleName modules
  let ppUnit = HskUnit ppHs.ModuleNames custMods env
  writeHskUnit ppUnit outDir
 