module Importer.Configuration
    ( Config (..),
      Customisations,
      CustomTheory,
      Location (..),
      CustomTranslations,
      CustomTranslation,
      MonadInstance (..),
      DoSyntax (..),
      readConfig,
      defaultConfig,
      defaultCustomisations,
      getCustomTheory,
      getCustomConstants,
      getCustomTypes,
      getCustomTheoryPath,
      getMonadInstance,
      getMonadConstant,
      getMonadDoSyntax,
      getMonadLift
    ) where
import Importer.IsaSyntax (Theory (..))
import Language.Haskell.Exts.Syntax (Module (..), HsType(..), HsQName(..))
import Text.XML.Light hiding (findAttr)
import qualified Text.XML.Light as XML
import Control.Monad
import Data.Maybe
import Data.List
import Control.Monad.Error
import Data.Generics
import System.FilePath
import System.Directory
import Data.Map (Map)
import qualified Data.Map as Map hiding (Map)

---------------------
-- Data Structures --
---------------------

type CustomTranslations = [CustomTranslation]
type CustomTranslation = (Module, CustomTheory)

newtype Location = FileLocation{ fileLocation :: FilePath}
    deriving (Show, Eq, Data, Typeable)

data Customisations = Customisations{ customTheoryCust :: Map Module CustomTheory, monadInstanceCust ::  Map String MonadInstance}
    deriving (Show, Eq, Data, Typeable)

data Customisation = CustReplace Replace
                   | CustMonadInstance MonadInstance
                     deriving (Show, Eq, Data, Typeable)

data CustomTheory = CustomTheory {
      custThyName :: Theory,
      custThyLocation :: Location,
      custThyConstants :: [String],
      custThyTypes :: [String],
      custThyMonads :: Either [String] [MonadInstance] }
                    deriving (Show, Eq, Data, Typeable)


data Config = Config{inputLocations :: [InputLocation], outputLocation :: OutputLocation, customisations :: Customisations}
              deriving (Show, Eq, Data, Typeable)

data Replace = Replace{ moduleRepl :: Module, customTheoryRepl :: CustomTheory}
               deriving (Show, Eq, Data, Typeable)

data MonadInstance = MonadInstance {monadName :: String, doSyntax :: DoSyntax, monadConstants :: MonadConstants, monadLifts :: MonadLifts}
                   deriving (Show, Eq, Data, Typeable)
{-|
  A mapping from lift functions to monads.
-}
type MonadLifts = Either [(String,String)] (Map String MonadInstance)

data DoSyntax = DoParen String String
                deriving (Show, Eq, Data, Typeable)
data MonadConstants = ExplicitMonadConstants {explMonConstants :: Map String String}
                      deriving (Show, Eq, Data, Typeable)


type InputLocation = Location

type OutputLocation = Location

type XMLParser a = Either String a

--------------------
-- Default Values --
--------------------

defaultConfig ::[FilePath] -> FilePath -> Customisations -> Config
defaultConfig inFiles outDir custs = Config {
                                      inputLocations = map FileLocation inFiles,
                                      outputLocation = FileLocation outDir,
                                      customisations = custs}

defaultCustomisations :: Customisations
defaultCustomisations = Customisations Map.empty Map.empty

noMonadConstants = ExplicitMonadConstants (Map.empty)


---------------------------------------
-- Data Structure Accessor Functions --
---------------------------------------

getCustomTheory :: Customisations -> Module -> Maybe CustomTheory
getCustomTheory Customisations{ customTheoryCust = custs} mod = Map.lookup mod custs

getCustomTheoryPath :: CustomTheory -> String
getCustomTheoryPath CustomTheory{custThyLocation = FileLocation src} = src

getCustomConstants :: CustomTheory -> [String]
getCustomConstants cust = 
    let expl = custThyConstants cust
        Right mons = custThyMonads cust
        impl = concatMap (Map.keys . explMonConstants . monadConstants) mons
        impl' = concatMap (names . monadLifts) mons
    in expl `union` impl `union` impl'
        where names (Right x) = Map.keys x
              names (Left x) = map fst x
        

getCustomTypes :: CustomTheory -> [String]
getCustomTypes  = custThyConstants

getMonadInstance :: Customisations -> String -> Maybe MonadInstance
getMonadInstance Customisations{monadInstanceCust = insts} monadName = Map.lookup monadName insts

getMonadDoSyntax :: MonadInstance -> DoSyntax
getMonadDoSyntax = doSyntax

getMonadConstants :: MonadInstance -> [String]
getMonadConstants mon = 
    let ExplicitMonadConstants transl = monadConstants mon in
    Map.keys transl

getMonadLift :: MonadInstance -> String -> Maybe MonadInstance
getMonadLift MonadInstance{monadLifts = Right consts} name =
    Map.lookup name consts

getMonadConstant :: MonadInstance -> String -> String
getMonadConstant mon name =
    case monadConstants mon of
      ExplicitMonadConstants funMap -> 
          case Map.lookup name funMap  of
            Nothing -> name
            Just name' -> name'

-----------------
-- XML Parsing --
-----------------


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
       config <- either (\msg -> error $ "Malformed configuration file: " ++ msg) return res
       wd <- getCurrentDirectory
       let path' = combine wd path
       return $ makePathsAbsolute (takeDirectory path') config
       
-----------------------
-- General Structure --
-----------------------

parseConfigDoc :: Element -> XMLParser Config
parseConfigDoc el
    = do checkSName el "translation"
         inputEl <- findSingleSElem "input" el
         outputEl <- findSingleSElem "output" el
         mbCustEl <- ((findSingleSElem "customisation" el >>= (return . Just))
                     `catchError` (const $ return Nothing))
         input <- parseInputElem inputEl
         output <- parseOutputElem outputEl
         cust <- case mbCustEl of
                  Nothing -> return defaultCustomisations
                  Just custEl -> parseCustElem custEl
         cust' <- processCustomisations cust
         return $ Config {inputLocations=input,
                          outputLocation=output,
                          customisations=cust'}

processCustomisations :: Customisations -> XMLParser Customisations
processCustomisations custs = processCustThys custs >>= processLifts

processLifts :: Customisations -> XMLParser Customisations
processLifts (Customisations thys mons) = 
    let mons' = Map.map lookup mons
        lookup mon@MonadInstance{monadLifts = Left lifts} = 
            let lifts' = Map.fromList $ map lookupLift lifts in
            mon{monadLifts = Right lifts'}
        lookupLift (cons,monName) = (cons, fromJust $ Map.lookup monName mons')
    in case (check,cycle) of
         (monName:_,_) -> fail $ "Monad instance " ++ monName ++ " not found in configuration!"
         (_,mon:_) -> fail $ "Monad instance " ++ monadName mon ++ " has a lifting function to itself!"
         ([],[]) -> return (Customisations thys mons')
    where check = filter (`Map.notMember` mons) $ concatMap monNames monList
          cycle = filter (\mon -> monadName mon `elem` monNames mon) monList
          monNames MonadInstance{monadLifts = Left lifts} = map snd lifts
          monList = Map.elems mons

processCustThys :: Customisations -> XMLParser Customisations
processCustThys (Customisations thys mons) = 
    let thys' = Map.map lookup thys in
    case check of
      [] -> return $ Customisations thys' mons
      monName:_ -> fail $ "Monad instance " ++ monName ++ " not found in configuration!"
    where monNames CustomTheory{custThyMonads = (Left ns)} = ns
          lookup thy = thy{custThyMonads = Right $ map (fromJust . (flip Map.lookup mons)) (monNames thy)}
          check = filter (`Map.notMember` mons) $ concatMap monNames (Map.elems thys)

-----------
-- Input --
-----------
          
parseInputElem :: Element -> XMLParser [InputLocation]
parseInputElem el =  mapM parseInputLocElem $ onlyElems $ elContent el

parseInputLocElem :: Element -> XMLParser InputLocation
parseInputLocElem el
    | elName el `elem`  map simpName ["file", "dir", "path"]
        = liftM FileLocation $ findSAttr "location" el
    | otherwise = fail $ "Unexpected element \"" ++ (show.qName.elName $ el) ++ "\"" ++ (showLine.elLine $ el) ++ "!"

------------                       
-- Output --
------------

parseOutputElem :: Element -> XMLParser OutputLocation
parseOutputElem  el = liftM FileLocation $ findSAttr "location" el

--------------------
-- Customisations --
--------------------

partitionCustomisations :: [Customisation] -> ([Replace],[MonadInstance])
partitionCustomisations [] = ([],[])
partitionCustomisations (cust: custs) =
    let (repls,mons) = partitionCustomisations custs in
    case cust of
      CustReplace repl -> (repl:repls,mons)
      CustMonadInstance mon -> (repls, mon:mons)

makeCustomisations :: [Customisation] -> Customisations
makeCustomisations custs = Customisations replsMap monsMap
    where (repls,mons) = partitionCustomisations custs
          monsMap = Map.fromList $ map (\mon -> (monadName mon,mon)) mons
          replsMap = Map.fromList $ map (\repl-> (moduleRepl repl, customTheoryRepl repl)) repls

parseCustElem :: Element -> XMLParser Customisations
parseCustElem el =liftM makeCustomisations $ mapM parseCustOptElem $ onlyElems $ elContent el

parseCustOptElem :: Element -> XMLParser Customisation
parseCustOptElem el
    | elName el == simpName "replace" = liftM CustReplace $ parseReplaceElem el
    | elName el == simpName "monadInstance" = liftM CustMonadInstance $ parseMonadInstanceElem el
    | otherwise = fail $ "Unexpected element \"" ++ (show.qName.elName $ el) ++ "\"" ++ (showLine.elLine $ el) ++ "!"

---------------------
-- Custom Theories --
---------------------

parseReplaceElem :: Element -> XMLParser Replace
parseReplaceElem  el
    = do moduleEl <- findSingleSElem "module" el
         theoryEl <- findSingleSElem "theory" el
         mod <- parseModuleElem moduleEl
         custThy <- parseTheoryElem theoryEl
         return $  Replace mod custThy

parseTheoryElem :: Element -> XMLParser CustomTheory
parseTheoryElem el = do thy <- findSAttr "name" el
                        path <- findSAttr "location" el
                        types <- getTypes
                        monads <- getMonads
                        constants <- getConstants
                        return $ CustomTheory (Theory thy)  (FileLocation path) constants types (Left monads)
    where getTypes = (findSingleSElem "types" el >>=
                      parseThyTypesElem)
                     `defaultVal` []
          getMonads = (findSingleSElem "monads" el >>=
                       parseThyMonadsElem)
                      `defaultVal` []
          getConstants = (findSingleSElem "constants" el >>=
                          parseThyConstantsElem)
                         `defaultVal` []

parseThyConstantsElem :: Element -> XMLParser [String]
parseThyConstantsElem el = return . words . strContent $ el

parseThyTypesElem :: Element -> XMLParser [String]
parseThyTypesElem el = return . words . strContent $ el

parseThyMonadsElem :: Element -> XMLParser [String]
parseThyMonadsElem el = return .words . strContent $ el
                     
parseModuleElem :: Element -> XMLParser Module
parseModuleElem el = liftM Module $ findSAttr "name" el

---------------------
-- Monad Instances --
---------------------

parseMonadInstanceElem :: Element -> XMLParser MonadInstance
parseMonadInstanceElem el
    = do name <- findSAttr "name" el
         doSyn <- getDoSyntax
         constants <- getConstants
         lifts <- getLifts
         return $ MonadInstance name doSyn constants (Left lifts)
    where getLifts = (findSingleSElem "lifts" el >>=
                      parseLiftsElem)
                     `defaultVal` []
          getConstants = (findSingleSElem "constants" el >>= 
                          parseMonConstantsElem)
                         `defaultVal` noMonadConstants
          getDoSyntax = findSingleSElem "doSyntax" el >>=
                        parseDoSyntaxElem

parseLiftsElem :: Element -> XMLParser [(String,String)]
parseLiftsElem el = findSElems "lift" el >>= mapM parseLiftElem

parseLiftElem :: Element -> XMLParser (String,String)
parseLiftElem el = 
    do from <- findSAttr "from" el
       by <- findSAttr "by" el
       return (by, from)

parseDoSyntaxElem :: Element -> XMLParser DoSyntax
parseDoSyntaxElem el =
    let [begin, end] = words . strContent $ el
    in return $ DoParen begin end

parseMonConstantsElem :: Element -> XMLParser MonadConstants
parseMonConstantsElem = return . ExplicitMonadConstants . Map.fromList . pair . words . strContent
    where pair [] = []
          pair (a:b:rest) = (a,b) : pair rest



-------------------
-- XML utilities -- 
-------------------

defaultVal :: XMLParser a -> a -> XMLParser a
defaultVal parse val = parse `catchError` const (return val)

findSingleSElem :: String -> Element -> XMLParser Element
findSingleSElem name el = findSingleElem (simpName name) el

findSingleElem :: QName -> Element -> XMLParser Element
findSingleElem name el = case findChildren name el of
                           [] -> failAt el $ "Required element \""++ (showName name) ++"\" not found"
                           _:_:_ -> failAt el $ "Only one element \""++ (showName name) ++"\" is allowed"
                           [e] -> return e

findSElems :: String -> Element -> XMLParser [Element]
findSElems name el = findElems (simpName name) el

findElems :: QName -> Element -> XMLParser [Element]
findElems name el = return $ findChildren name el

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
makePathsAbsolute base = everywhere $ mkT alterPath
    where alterPath (FileLocation path) = FileLocation $ combine base path
