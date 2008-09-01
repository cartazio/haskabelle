{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen

Toplevel interface to importer.
-}

module Importer (
  module Importer.Convert,
  module Importer.IsaSyntax,
  module Importer.Printer,
  convertFile, convertDir, convertFiles, importFiles, importDir
) where

import IO
import Directory

import List (intersperse)
import Control.Monad

import Data.Tree
import Text.PrettyPrint (render, vcat, text, (<>))

import Language.Haskell.Exts (ParseResult(..), parseFile, HsModule(..))
import Language.Haskell.Exts.Pretty 
import Language.Haskell.Exts.Syntax 
---import Language.Haskell.Pretty
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
convertFile fp = do [unit] <- convertFiles [fp]; return unit

convertFiles :: [FilePath] -> IO [IsaUnit]
convertFiles []   = return []
convertFiles (fp:fps)
    = let dir      = dirname fp
          filename = basename fp
      -- We have to do this to find the source files of imported modules.
      in withCurrentDirectory (if dir == "" then "./" else dir)
          $ do unit@(HskUnit hsmodules _) <- makeHskUnitFromFile filename
               let dependentModuleNs = map (\(HsModule _ m _ _ _) -> m) hsmodules
               let dependentFiles    = map module2FilePath dependentModuleNs
               units <- convertFiles (filter (`notElem` dependentFiles) fps) 
               return (convertHskUnit unit : units)

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
     
getFilesRecursively :: FilePath -> IO [FilePath]
getFilesRecursively dirpath 
    = getDirectoryTree dirpath >>= filterM doesFileExist . flatten . absolutify ""
    where absolutify cwd (Node { rootLabel = filename, subForest = children })
              = Node { rootLabel = cwd ++ filename, 
                       subForest = map (absolutify (cwd ++ filename ++ "/")) children }

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
         bracket_ (setCurrentDirectory fp) (const (setCurrentDirectory oldcwd)) body

importFiles :: [FilePath] -> FilePath -> IO ()
importFiles sources dstdir
    = do exists <- doesDirectoryExist dstdir
         when (not exists) $ createDirectory dstdir
         do convertedUnits <- convertFiles sources
            withCurrentDirectory dstdir
              $ sequence_ (map writeIsaUnit convertedUnits)

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
         writeFile dstName content


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

exPP = preprocessFile "/home/paba/studies/NICTA/hsimp/workspace/nicta/ex/src_hs/AsPatterns.hs" "/home/paba/studies/NICTA/hsimp/workspace/nicta/ex/dst_hs"