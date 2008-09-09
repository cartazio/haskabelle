{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen

Toplevel interface to importer.
-}

module Importer (
  module Importer.Convert,
  module Importer.IsaSyntax,
  module Importer.Printer,
  convertFile, convertDir, convertFiles, importFiles, importDir,
  makeAbsolute, convertSingleFile
) where

import Prelude hiding (catch)
import System.FilePath
import IO hiding (catch,bracket_)
import Directory

import List (intersperse)
import Control.Monad
import Control.Exception

import Data.Tree
import Text.PrettyPrint (render, vcat, text, (<>))

import Language.Haskell.Exts (ParseResult(..), parseFile, HsModule(..))
import Language.Haskell.Exts.Pretty 
import Language.Haskell.Exts.Syntax 
import Importer.IsaSyntax (Cmd(..), Theory(..))

import Importer.Preprocess
import Importer.Utilities.Hsk (srcloc2string, module2FilePath, isHaskellSourceFile)
import Importer.Utilities.Misc (assert, wordsBy, prettyShow)
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
--    do unit <- convertFile "/path/foo.hs"
--       return (pprintIsaUnit unit)
--

convertFile :: FilePath -> IO IsaUnit
convertFile fp = do
  (unit,files) <- convertSingleFile fp
  return unit

{-|
  Converts a Haskell unit identified by the given file path (i.e., the module defined
  therein and all imported modules) to a Isabelle unit. Furthermore a list of all 
  Haskell files that were converted is returned.
-}
convertSingleFile :: FilePath -> IO (IsaUnit, [FilePath])
convertSingleFile fp =
    let dir      = dirname fp
        filename = basename fp
    in withCurrentDirectory (if dir == "" then "./" else dir) $
       do unit@(HskUnit hsmodules _) <- makeHskUnitFromFile filename 
          let dependentModuleNs = map (\(HsModule _ m _ _ _) -> m) hsmodules
          let dependentFiles    = map module2FilePath dependentModuleNs
          let isaUnit = convertHskUnit unit
          return (isaUnit,dependentFiles)



convertFiles :: [FilePath] -> IO [IsaUnit]
convertFiles []   = return []
convertFiles (fp:fps) = do
  (isaUnit,dependentFiles) <-
      do
        putStr $ "converting " ++ (basename fp) ++ " ...\n"
        (unit,files) <- convertSingleFile fp
        return ([unit],files)        
      `catch` (\ exc -> do
                 print exc
                 return ([],[]))
--  units <- convertFiles fps
  units <- convertFiles (filter (`notElem` dependentFiles) fps) 
  return  (isaUnit ++ units)
                

dirname :: FilePath -> FilePath
dirname fp = reverse $ dropWhile (/= '/') (reverse fp)

basename :: FilePath -> FilePath
basename fp = reverse $ takeWhile (/= '/') (reverse fp)

getDirectoryTree :: FilePath -> IO (Tree FilePath)
getDirectoryTree dirpath
    = do fps <- getDirectoryContents dirpath `catch` const (return [])
         let fps' = filter (`notElem` [".", ".."]) fps
         subtrees <- mapM getDirectoryTree fps'
         return (Node { rootLabel = dirpath, subForest = subtrees })
     
{-|
  This function recursively searches the given directory for Haskell source files.
-}
getFilesRecursively :: FilePath -> IO [FilePath]
getFilesRecursively dirpath 
    = getDirectoryTree dirpath >>= filterM doesFileExist . flatten . absolutify ""
    where absolutify cwd (Node { rootLabel = filename, subForest = children })
              = Node { rootLabel = cwd ++ filename, 
                       subForest = map (absolutify (cwd ++ filename ++ "/")) children }

{-|
  This function searches recursively in the given directory for
  Haskell source files (using 'getFilesRecursively') and converts them using 'convertFiles'.
-}
convertDir :: FilePath -> IO [IsaUnit]
convertDir dirpath
    = do fps   <- getFilesRecursively dirpath
         units <- convertFiles (filter isHaskellSourceFile fps)
         return units


pprintIsaUnit (IsaUnit thys env)
    = vcat (map (dashes . flip pprint env) thys)
    where dashes d = d <> (text "\n") <> (text (replicate 60 '-'))

printIsaUnit_asAST (IsaUnit thys env)
    = vcat (map (dashes . text . prettyShow) thys)
    where dashes d = d <> (text "\n") <> (text (replicate 60 '-'))

      
withCurrentDirectory :: FilePath -> IO a -> IO a
withCurrentDirectory fp body
    = do oldcwd <- getCurrentDirectory
         bracket_ (setCurrentDirectory fp) (setCurrentDirectory oldcwd) body

importFiles :: [FilePath] -> FilePath -> IO ()
importFiles sources dstdir
    = do exists <- doesDirectoryExist dstdir
         when (not exists) $ createDirectory dstdir
         do convertedUnits <- convertFiles sources
            withCurrentDirectory dstdir
              $ sequence_ (map writeIsaUnit convertedUnits)

{-|
  
-}
importDir :: FilePath -> FilePath -> IO ()
importDir srcdir dstdir
    = do exists <- doesDirectoryExist dstdir
         when (not exists) $ createDirectory dstdir
         do convertedUnits <- convertDir srcdir
            withCurrentDirectory dstdir
              $ sequence_ (map writeIsaUnit convertedUnits)

writeIsaUnit (IsaUnit thys env)
    = mapM (flip writeTheory env) thys

writeTheory thy@(TheoryCmd (Theory thyname) _) env 
    = do let content = render (pprint thy env)
         let dstName = content `seq` map (\c -> if c == '.' then '_' else c) thyname ++ ".thy"
         putStr $ "writing " ++ dstName ++ "...\n"
         writeFile dstName content

{-|
  This function turns a relative path into an absolute path using
  the current directory as provided by 'getCurrentDirectory'.
-}

makeAbsolute :: FilePath -> IO FilePath
makeAbsolute fp = liftM2 combine getCurrentDirectory (return fp)


----------------------------------------------------------
------------ Preprocessing Only --------------------------
----------------------------------------------------------

writeHskUnit :: HskUnit -> FilePath -> IO ()
writeHskUnit (HskUnit modules _) outDir
    = mapM_ (`writeHskModule` outDir) modules

writeHskModule :: HsModule -> FilePath -> IO ()
writeHskModule mod@(HsModule _ (Module modName) _ _ _) dir = do
  let modCont = prettyPrint mod
  let dstName = map (\c -> if c == '.' then '_' else c) modName ++ ".hs"
  withCurrentDirectory dir $
                       writeFile dstName modCont

preprocessFile :: FilePath -> FilePath -> IO ()
preprocessFile inFile outDir = do
  hskUnit <- makeHskUnitFromFile inFile
  let HskUnit modules env = hskUnit
  let ppModules = map preprocessHsModule modules
  let ppUnit = HskUnit ppModules env
  writeHskUnit ppUnit outDir

exPP = withCurrentDirectory "/home/paba/studies/NICTA/hsimp/ref/refine/haskell/src/" $ preprocessFile "/home/paba/studies/NICTA/hsimp/ref/refine/haskell/src/SEL4/Kernel.hs" "/home/paba/studies/NICTA/hsimp/workspace/nicta/ex/dst_hs"