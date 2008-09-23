module Importer.Configuration
    ( Config (..),
      Customisation (..),
      InputLocation (..),
      readConfig
    ) where
import Importer.IsaSyntax (Theory (..))
import Language.Haskell.Exts.Syntax (Module (..))
import Text.XML.Light hiding (findAttr)
import qualified Text.XML.Light as XML
import Control.Monad
import Data.Maybe
import Control.Monad.Error
import Data.Generics
import System.FilePath
import System.Directory

data Config = Config{inputLocations :: [InputLocation], outputLocation :: OutputLocation, customisations :: [Customisation]}
              deriving (Show, Eq, Data, Typeable)

data Customisation = Replace Module Theory FilePath
                     deriving (Show, Eq, Data, Typeable)

data InputLocation = FileInputLocation FilePath
                   | DirInputLocation FilePath
                     deriving (Show, Eq, Data, Typeable)

type OutputLocation = FilePath

type XMLParser a = Either String a


{-|
  This function reads the XML configuration file located at the given file path
  and provides the parsed configuration data structure.
-}

readConfig :: FilePath -> IO Config
readConfig path =
    do content <- readFile path 
       let maybeRoot = parseXMLDoc content
       when (isNothing maybeRoot) $
            error $ "Parsing error: The configuration file \"" ++ path ++ "\" is not a well-formed XML document!"
       let Just root = maybeRoot
       let res = parseConfigDoc root
       config <- either (\msg -> error $ "Parsing error: " ++ msg) return res
       wd <- getCurrentDirectory
       let path' = combine wd path
       return $ makePathsAbsolute (takeDirectory path') config
       


parseConfigDoc :: Element -> XMLParser Config
parseConfigDoc el
    = do checkSName el "translation"
         inputEl <- findSingleSElem "input" el
         outputEl <- findSingleSElem "output" el
         custEl <- findSingleSElem "customisation" el
         input <- parseInputElem inputEl
         output <- parseOutputElem outputEl
         cust <- parseCustElem custEl
         return $ Config {inputLocations=input,
                          outputLocation=output,
                          customisations=cust}
                     
parseInputElem :: Element -> XMLParser [InputLocation]
parseInputElem el =  mapM parseInputLocElem $ onlyElems $ elContent el

parseInputLocElem :: Element -> XMLParser InputLocation
parseInputLocElem el
    | elName el == simpName "file" = parseFile
    | elName el == simpName "dir" = parseDir
    | otherwise = fail $ "Unexpected element \"" ++ (show.qName.elName $ el) ++ "\"" ++ (showLine.elLine $ el) ++ "!"
    where parseFile = liftM FileInputLocation $ findSAttr "location" el
          parseDir = liftM DirInputLocation $ findSAttr "location" el
                       

parseOutputElem :: Element -> XMLParser OutputLocation
parseOutputElem  el = findSAttr "location" el


parseCustElem :: Element -> XMLParser [Customisation]
parseCustElem el = mapM parseCustOptElem $ onlyElems $ elContent el

parseCustOptElem :: Element -> XMLParser Customisation
parseCustOptElem el
    | elName el == simpName "replace" = parseReplaceElem el
    | otherwise = fail $ "Unexpected element \"" ++ (show.qName.elName $ el) ++ "\"" ++ (showLine.elLine $ el) ++ "!"



findSingleSElem :: String -> Element -> XMLParser Element
findSingleSElem name el = findSingleElem (simpName name) el

findSingleElem :: QName -> Element -> XMLParser Element
findSingleElem name el = case findChildren name el of
                           [] -> failAt el $ "Required element \""++ (showName name) ++"\" not found"
                           _:_:_ -> failAt el $ "Only one element \""++ (showName name) ++"\" is allowed"
                           [e] -> return e

parseReplaceElem :: Element -> XMLParser Customisation
parseReplaceElem  el
    = do moduleEl <- findSingleSElem "module" el
         theoryEl <- findSingleSElem "theory" el
         mod <- parseModuleElem moduleEl
         (thy,path) <- parseTheoryElem theoryEl
         return $  Replace mod thy path


parseTheoryElem :: Element -> XMLParser (Theory,FilePath)
parseTheoryElem el = do thy <- findSAttr "name" el
                        path <- findSAttr "location" el
                        return (Theory thy, path)        
                     
parseModuleElem :: Element -> XMLParser Module
parseModuleElem el = liftM Module $ findSAttr "name" el

simpName :: String -> QName
simpName name = QName {qName = name, qURI = Nothing, qPrefix = Nothing}

checkSName :: Element -> String -> XMLParser ()
checkSName el sname = checkName el (simpName sname)

checkName :: Element -> QName -> XMLParser ()
checkName el name 
    = let foundName = elName el in
      if foundName /= name
      then failAt el $ "Expected \""++ (showName name) ++"\" element but found \"" ++ (showName foundName)
      else return ()

failAt :: Element -> String -> XMLParser a
failAt el msg = fail $ msg ++ (showLine $ elLine el) ++ "!"

showLine :: Maybe Line -> String
showLine Nothing = ""
showLine (Just line) = " at line " ++ (show line)

showName :: QName -> String
showName name = qName name

findSAttr :: String -> Element -> XMLParser String
findSAttr name el = findAttr (simpName name) el

findAttr :: QName -> Element -> XMLParser String
findAttr name el = maybe
                     (fail $ "Expected attribute \"" ++ (showName name) ++ "\" not found" ++ (showLine $ elLine el) ++ "!")
                     return
                     (XML.findAttr name el)


makePathsAbsolute :: FilePath -> Config -> Config
makePathsAbsolute base = foldr1 (.) all
    where top (Config inp outp cust) = Config inp (alterPath outp) cust
          cust (Replace mod thy path) = Replace mod thy (alterPath path)
          inp (FileInputLocation path) = FileInputLocation (alterPath path)
          inp (DirInputLocation path) = DirInputLocation (alterPath path)
          all = map everywhere [mkT top, mkT cust, mkT inp]
          alterPath path = combine base path
