{-# LANGUAGE DeriveDataTypeable #-}

{-|
  This module provides functionality to read configurations from an XML 
  file into a data structure and to access this data structure.
-}

module Importer.Configuration
    ( 
     -- * Types
      Config (..),
      Customisations,
      CustomTheory,
      Location (..),
      CustomTranslations,
      CustomTranslation,
      MonadInstance (..),
      DoSyntax (..),
      -- * XML Parsing
      readConfig,
      -- * Default Configurations
      defaultConfig,
      defaultCustomisations,
      -- * Accessor Functions
      getCustomTheory,
      getCustomTheoryName,
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

{-|
  This type represents sets of custom translations, i.e., mappings from Haskell
  modules to custom theories.
-}
type CustomTranslations = Map Module CustomTheory

{-|
  This type represents single custom translations.
-}
type CustomTranslation = (Module, CustomTheory)

{-|
  This type represents locations  declared in a configuration.
-}
newtype Location = FileLocation{ fileLocation :: FilePath}
    deriving (Show, Eq, Data, Typeable)

{-|
  This type represents information that customise the actual translation.
-}
data Customisations = Customisations{ customTheoryCust :: Map Module CustomTheory, monadInstanceCust ::  Map String MonadInstance}
    deriving (Show, Eq, Data, Typeable)

{-|
  An element of this type represents a single customisation option.
-}
data Customisation = CustReplace Replace
                   | CustMonadInstance MonadInstance
                     deriving (Show, Eq, Data, Typeable)

{-|
  This type represents Isabelle theories that can be declared to be substitutes
  to actual translations (which might be impossible) of necessary Haskell modules.
-}
data CustomTheory = CustomTheory {
      custThyName :: Theory, -- ^The name of the theory.
      custThyLocation :: Location, -- ^The location of the @*.thy@ file containing the theory.
      custThyConstants :: [String], -- ^The constants that the theory is supposed to define.
      custThyTypes :: [String], -- ^The types that the theory is supposed to define.
      custThyMonads :: Either [String] [MonadInstance] -- ^The monads that the theory is supposed to define.
                                                       -- After the list of monad names was read from the XML
                                                       -- data the corresponding monad instances are inserted
                                                       -- instead in the post-processing phase.
    } deriving (Show, Eq, Data, Typeable)

{-|
  An element of this type represents configuration information for this application.
-}
data Config = Config{inputLocations :: [InputLocation], outputLocation :: OutputLocation, customisations :: Customisations}
              deriving (Show, Eq, Data, Typeable)

{-|
  This type represents a particular kind of a translation customisation. An element
  of this type describes how a Haskell module can be replaced by an Isabelle theory.
-}
data Replace = Replace{ moduleRepl :: Module, customTheoryRepl :: CustomTheory}
               deriving (Show, Eq, Data, Typeable)

{-|
  This type represents a particular kind of a translation customisation. An element
  of this type describes how monadic code of one particular monad should be translated.
-}
data MonadInstance = MonadInstance {
      monadName :: String,  -- ^The name of the considered monad.
      doSyntax :: DoSyntax, -- ^Describes how @do@ expressions should be translated.
      monadConstants :: MonadConstants, -- ^Describes how particular monad constants should be translated.
      monadLifts :: MonadLifts -- ^Describes how particular lift functions should be treated.
    } deriving (Show, Eq, Data, Typeable)
{-|
  A mapping from lift functions to monads. When first reading the XML data the 'Left'
  of the 'Either' type is produced. In the post-processing phase this is replaced by
  the 'Right' resolving the dependencies.
-}
type MonadLifts = Either [(String,String)] (Map String MonadInstance)

{-|
  Elements of this type describe how @do@ expressions should be translated into Isabelle 
  syntax.
-}
data DoSyntax = DoParen String String -- ^Translate @do@ expressions as
                                      -- @\<pre\> \<stmt1\>\; \<stmt2\>; ... \<stmtn\> \<post\>@ 
                                      -- were @\<pre\>@ and @\<post\>@ are the first and 
                                      -- the last constructor's argument respectively.
                deriving (Show, Eq, Data, Typeable)


{-|
  This type represents renamings of monad constants. E.g. this allow to declare
  that @return@ should be renamed to @returnE@ in one particular monad.
-}
data MonadConstants = ExplicitMonadConstants {
      explMonConstants :: Map String String
    } deriving (Show, Eq, Data, Typeable)

{-|
  This type represents input locations.
-}
type InputLocation = Location

{-|
  This type represents output locations.
-}
type OutputLocation = Location

{-|
  This type represents the monad where the processing of the XML
  data takes place.
-}
type XMLReader a = Either String a

--------------------
-- Default Values --
--------------------

{-|
  This function constructs a default configuration depending on the input files,
  output directory and customisation.
-}
defaultConfig ::[FilePath] -> FilePath -> Customisations -> Config
defaultConfig inFiles outDir custs = Config {
                                      inputLocations = map FileLocation inFiles,
                                      outputLocation = FileLocation outDir,
                                      customisations = custs}

{-|
  This constant represents a default customisations option.
-}
defaultCustomisations :: Customisations
defaultCustomisations = Customisations Map.empty Map.empty

{-|
  This constant represents a monad constants option without any constants.
-}
noMonadConstants = ExplicitMonadConstants (Map.empty)


---------------------------------------
-- Data Structure Accessor Functions --
---------------------------------------

{-|
  This function provides the custom theory the given module should be
  replaced with according to the given customisations or @nothing@ if
  no such translation was declared for the given module.
-}
getCustomTheory :: Customisations -> Module -> Maybe CustomTheory
getCustomTheory Customisations{ customTheoryCust = custs} mod = Map.lookup mod custs


{-|
  This function provides the path of where given custom theories was declared
  to be found.
-}
getCustomTheoryPath :: CustomTheory -> String
getCustomTheoryPath CustomTheory{custThyLocation = FileLocation src} = src

getCustomTheoryName :: CustomTheory -> Theory
getCustomTheoryName CustomTheory{custThyName = name} = name

{-|
  This function provides the constants that are exported by the given custom
  theory. This includes explicitly given one as well as indirectly given ones
  (by including a monad instance).
-}
getCustomConstants :: CustomTheory -> [String]
getCustomConstants cust = 
    let expl = custThyConstants cust
        Right mons = custThyMonads cust
        impl = concatMap (Map.keys . explMonConstants . monadConstants) mons
        impl' = concatMap (names . monadLifts) mons
    in expl `union` impl `union` impl'
        where names (Right x) = Map.keys x
              names (Left x) = map fst x
        
{-|
  This function provides the types that the given custom theory is declared to export.
-}
getCustomTypes :: CustomTheory -> [String]
getCustomTypes  = custThyConstants

{-|
  This function provides the monad instance declaration of the given monad name
  or @Nothing@ if the given monad name was not declared in the given customisation
  set.
-}
getMonadInstance :: Customisations -> String -> Maybe MonadInstance
getMonadInstance Customisations{monadInstanceCust = insts} monadName = Map.lookup monadName insts

{-|
  This function provides the @do@ syntax information for the given monad
  instance.
-}
getMonadDoSyntax :: MonadInstance -> DoSyntax
getMonadDoSyntax = doSyntax

{-|
  This function provides the constants that were declared in the
  given monad instance.
-}
getMonadConstants :: MonadInstance -> [String]
getMonadConstants mon = 
    let ExplicitMonadConstants transl = monadConstants mon in
    Map.keys transl

{-|
  This function provides the monad instance of the monad
  that was declared to be lifted from by the given lift function
  name inside the given monad or @Nothing@ if there is no such 
  declaration.
-}
getMonadLift :: MonadInstance  -- ^The context monad.
             -> String -- ^The possible lift function.
             -> Maybe MonadInstance -- ^The monad that is lifted (if any).
getMonadLift MonadInstance{monadLifts = Right consts} name =
    Map.lookup name consts

{-|
  This function translates the given constant name using 
  the translation declaration given in the monad instance
  argument.
-}
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

{-|
  This function takes the root element of a configuration document
  and reads the configuration information in it.
-}
parseConfigDoc :: Element -> XMLReader Config
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

{-|
  This function processes the given customisations, i.e. it resolves all
  dependencies. Currently, this means that names of monads are replaced by
  the corresponding 'MonadInstance' data structures they point to. If a monad
  name is not found an error in the XMLReader monad is raised.
-}
processCustomisations :: Customisations -> XMLReader Customisations
processCustomisations custs = processCustThys custs >>= processLifts

{-|
  This function processes 'MonadLifts' data structures in the given 
  customisations by replacing the 'Left' of the 'Either' type into a 'Right'.
-}
processLifts :: Customisations -> XMLReader Customisations
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
{-|
  This function processes 'CustomTheory' data structures in the given
  customisations by replacing monad names by the actual 'MonadInstance'
  data structures.
-}
processCustThys :: Customisations -> XMLReader Customisations
processCustThys (Customisations thys mons) = 
    let thys' = Map.map lookup thys in
    case check of
      [] -> return $ Customisations thys' mons
      monName:_ -> fail $ "Monad instance " ++ monName ++ " not found in configuration!"
    where monNames CustomTheory{custThyMonads = (Left ns)} = ns
          lookup thy = thy{custThyMonads = Right $ map (fromJust . (flip Map.lookup mons)) (monNames thy)}
          check = filter (`Map.notMember` mons) $ concatMap monNames (Map.elems thys)


{-|
  This function turns all file paths in the given configuration into absolute
  paths using the given path as the current directory.
-}
makePathsAbsolute :: FilePath -> Config -> Config
makePathsAbsolute base = everywhere $ mkT alterPath
    where alterPath (FileLocation path) = FileLocation $ combine base path

-----------
-- Input --
-----------

{-|
  This function reads the input locations stored in the given
  @input@ XML element.
-}
parseInputElem :: Element -> XMLReader [InputLocation]
parseInputElem el =  mapM parseInputLocElem $ onlyElems $ elContent el

{-|
  This function reads a single input location stored in the given
  XML element being one of @file@, @dir@ and @path@.
-}
parseInputLocElem :: Element -> XMLReader InputLocation
parseInputLocElem el
    | elName el `elem`  map simpName ["file", "dir", "path"]
        = liftM FileLocation $ findSAttr "location" el
    | otherwise = fail $ "Unexpected element \"" ++ (show.qName.elName $ el) ++ "\"" ++ (showLine.elLine $ el) ++ "!"

------------                       
-- Output --
------------

{-|
  This function reads the output location stored in the given @output@
  XML element.
-}

parseOutputElem :: Element -> XMLReader OutputLocation
parseOutputElem  el = liftM FileLocation $ findSAttr "location" el

--------------------
-- Customisations --
--------------------

{-|
  This function partitions a list of customisation into two lists of replace
  and monad instance customisations respectively.
-}
partitionCustomisations :: [Customisation] -> ([Replace],[MonadInstance])
partitionCustomisations [] = ([],[])
partitionCustomisations (cust: custs) =
    let (repls,mons) = partitionCustomisations custs in
    case cust of
      CustReplace repl -> (repl:repls,mons)
      CustMonadInstance mon -> (repls, mon:mons)

{-|
  This function constructs a customisation data structure given a list of
  single customisation options.
-}
makeCustomisations :: [Customisation] -> Customisations
makeCustomisations custs = Customisations replsMap monsMap
    where (repls,mons) = partitionCustomisations custs
          monsMap = Map.fromList $ map (\mon -> (monadName mon,mon)) mons
          replsMap = Map.fromList $ map (\repl-> (moduleRepl repl, customTheoryRepl repl)) repls

{-|
  This function reads the customisations stored the given
  @customisations@ XML element.
-}
parseCustElem :: Element -> XMLReader Customisations
parseCustElem el =liftM makeCustomisations $ mapM parseCustOptElem $ onlyElems $ elContent el


{-|
  This function reads a single customisation option stored in the given
  XML element being either @replace@ or @monadInstance@.
-}
parseCustOptElem :: Element -> XMLReader Customisation
parseCustOptElem el
    | elName el == simpName "replace" = liftM CustReplace $ parseReplaceElem el
    | elName el == simpName "monadInstance" = liftM CustMonadInstance $ parseMonadInstanceElem el
    | otherwise = fail $ "Unexpected element \"" ++ (show.qName.elName $ el) ++ "\"" ++ (showLine.elLine $ el) ++ "!"

---------------------
-- Custom Theories --
---------------------

{-|
  This function reads a replace customisation option stored in the given
  @replace@ XML element
-}
parseReplaceElem :: Element -> XMLReader Replace
parseReplaceElem  el
    = do moduleEl <- findSingleSElem "module" el
         theoryEl <- findSingleSElem "theory" el
         mod <- parseModuleElem moduleEl
         custThy <- parseTheoryElem theoryEl
         return $  Replace mod custThy

{-|
  This function reads a custom theory stored in the given @theory@
  XML element.
-}
parseTheoryElem :: Element -> XMLReader CustomTheory
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

{-|
  This function reads a list of constant names stored in the given
  @constants@ XML element.
-}
parseThyConstantsElem :: Element -> XMLReader [String]
parseThyConstantsElem el = return . words . strContent $ el

{-|
  This function reads a list of type names stored in the given
  @types@ XML element.
-}
parseThyTypesElem :: Element -> XMLReader [String]
parseThyTypesElem el = return . words . strContent $ el

{-|
  This function reads a list of monad names stored in the given
  @monads@ XML element.
-}
parseThyMonadsElem :: Element -> XMLReader [String]
parseThyMonadsElem el = return .words . strContent $ el

{-|
  This function reads a module name stored in the given @module@
  XML element.
-}            
parseModuleElem :: Element -> XMLReader Module
parseModuleElem el = liftM Module $ findSAttr "name" el

---------------------
-- Monad Instances --
---------------------

{-|
  This function reads a monad instance declaration stored in the given
  @monadInstance@ XML element.
-}
parseMonadInstanceElem :: Element -> XMLReader MonadInstance
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

{-|
  This function reads a list of monad lift information stored in the 
  given @lifts@ XML element.
-}
parseLiftsElem :: Element -> XMLReader [(String,String)]
parseLiftsElem el = findSElems "lift" el >>= mapM parseLiftElem

{-|
  This function read a single piece of monad lift information stored
  in the given @lift@ XML element.
-}
parseLiftElem :: Element -> XMLReader (String,String)
parseLiftElem el = 
    do from <- findSAttr "from" el
       by <- findSAttr "by" el
       return (by, from)

{-|
  This function reads @do@ syntax information stored in the given 
  @doSyntax@ XML element.
-}
parseDoSyntaxElem :: Element -> XMLReader DoSyntax
parseDoSyntaxElem el =
    let [begin, end] = words . strContent $ el
    in return $ DoParen begin end

{-|
  This function reads monad constants information stored in the given
  @constants@ XML element
-}
parseMonConstantsElem :: Element -> XMLReader MonadConstants
parseMonConstantsElem = return . ExplicitMonadConstants . Map.fromList . pair . words . strContent
    where pair [] = []
          pair [_] = fail "Monad constants have to be defined in pairs!"
          pair (a:b:rest) = (a,b) : pair rest



-------------------
-- XML utilities -- 
-------------------

{-|
  This combinator provides the given default value if the given 
  @XMLReader@ monad fails.
-}
defaultVal :: XMLReader a -> a -> XMLReader a
defaultVal parse val = parse `catchError` const (return val)

{-|
  This function is similar to 'findSinlgeElem' but it takes a string as the basis for
  a name provided by 'simpName'.
-}
findSingleSElem :: String -> Element -> XMLReader Element
findSingleSElem name el = findSingleElem (simpName name) el

{-|
  This looks for a single element of the given name as the child of the 
  given element. If not /exactly one/ element is found an error is raised.
-}
findSingleElem :: QName -> Element -> XMLReader Element
findSingleElem name el = case findChildren name el of
                           [] -> failAt el $ "Required element \""++ (showName name) ++"\" not found"
                           _:_:_ -> failAt el $ "Only one element \""++ (showName name) ++"\" is allowed"
                           [e] -> return e

{-|
  This function is similar to 'findElems' but it takes a string as the basis
  for a name provided by 'simpName'.
-}
findSElems :: String -> Element -> XMLReader [Element]
findSElems name el = findElems (simpName name) el

{-|
  This function provides all children elements of the given
  element having the given name.
-}
findElems :: QName -> Element -> XMLReader [Element]
findElems name el = return $ findChildren name el

{-|
  This function provides an unqualified name having the given string
  as a name.
-}
simpName :: String -> QName
simpName name = QName {qName = name, qURI = Nothing, qPrefix = Nothing}

{-|
  This function is similar to 'checkName' but it takes a string as the basis 
  of a name provided by 'simpName'.
-}
checkSName :: Element -> String -> XMLReader ()
checkSName el sname = checkName el (simpName sname)

{-|
  This function checks whether the given element has the given name. If it has
  not an error is raised.
-}
checkName :: Element -> QName -> XMLReader ()
checkName el name 
    = let foundName = elName el in
      if foundName /= name
      then failAt el $ "Expected \""++ (showName name) ++"\" element but found \"" ++ (showName foundName)
      else return ()

{-|
  This function raises an error with the given message. The XML element is used
  to provide information where the error occurred.
-}
failAt :: Element -> String -> XMLReader a
failAt el msg = fail $ msg ++ (showLine $ elLine el) ++ "!"

{-|
  This function turns a line information of an XML element into a
  human readable string that can be used in an error message.
-}
showLine :: Maybe Line -> String
showLine Nothing = ""
showLine (Just line) = " at line " ++ (show line)

{-|
  This function provides a human readable string representation of the given
  qualified name.
-}
showName :: QName -> String
showName name = qName name

{-|
  This function is similar to 'findAttr' but instead of a qualified name it
  takes a string to construct one using 'simpName'
-}
findSAttr :: String -> Element -> XMLReader String
findSAttr name el = findAttr (simpName name) el

{-|
  This function provides the value of the attribute of the given name in the given 
  element. If there is no such attribute an error is raised.
-}
findAttr :: QName -> Element -> XMLReader String
findAttr name el = maybe
                     (fail $ "Expected attribute \"" ++ (showName name) ++ "\" not found" ++ (showLine $ elLine el) ++ "!")
                     return
                     (XML.findAttr name el)

