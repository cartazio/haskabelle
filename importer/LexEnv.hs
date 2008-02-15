
module Importer.LexEnv where

import Maybe

import Data.Generics.PlateData (universeBi, contextsBi)

import qualified Data.Map as Map
import Language.Haskell.Hsx

import qualified Importer.Msg as Msg
import qualified Importer.IsaSyntax as Isa

import Importer.Utilities.Hsk
import Importer.Utilities.Misc

--
-- LexEnv
--

data HskLexInfo = HskLexInfo { 
                              identifier :: HsQName,
                              typeOf     :: Maybe HsType,
                              moduleOf   :: Module
                             }
  deriving (Eq, Show)

data HskIdentifier = HskVariable HskLexInfo
                   | HskFunction HskLexInfo
                   | HskInfixOp  HskLexInfo HsAssoc Int
                   | HskData     HskLexInfo [HsQName] -- data constructors
                   | HskTypeAnnotation HsType
  deriving (Eq, Show)

isHskVariable, isHskFunction, isHskInfixOp, isHskTypeAnnotation :: HskIdentifier -> Bool

isHskVariable (HskVariable _) = True
isHskVariable _ = False

isHskFunction (HskFunction _) = True
isHskFunction _ = False

isHskInfixOp (HskInfixOp _ _ _) = True
isHskInfixOp _ = False

isHskTypeAnnotation (HskTypeAnnotation _) = True
isHskTypeAnnotation _ = False

isHskData (HskData _ _) = True
isHskData _ = False

identifier2name :: HskIdentifier -> HsQName
identifier2name hsxidentifier
    = identifier (extractLexInfo hsxidentifier)
    where extractLexInfo (HskVariable i)    = i
          extractLexInfo (HskFunction i)    = i
          extractLexInfo (HskInfixOp i _ _) = i
          extractLexInfo (HskData i _)      = i


makeUnqualified :: HskIdentifier -> HskIdentifier
makeUnqualified hsxidentifier
    = case identifier2name hsxidentifier of
        UnQual n -> hsxidentifier
        Qual _ n -> case hsxidentifier of
                      HskVariable lexinfo     -> HskVariable (lexinfo { identifier = UnQual n })
                      HskFunction lexinfo     -> HskFunction (lexinfo { identifier = UnQual n })
                      HskInfixOp  lexinfo a p -> HskInfixOp  (lexinfo { identifier = UnQual n }) a p
                      HskData     lexinfo cs  -> HskData     (lexinfo { identifier = UnQual n }) cs


data LexE = HskLexEnv (Map.Map HsQName HskIdentifier)
  deriving (Show)


emptyLexEnv_Hsk = HskLexEnv Map.empty

makeLexEnv_Hsk :: [(HsQName, HskIdentifier)] -> LexE
makeLexEnv_Hsk initbindings
    = HskLexEnv (Map.fromListWith mergeLexInfos initbindings)

mergeLexInfos :: HskIdentifier -> HskIdentifier -> HskIdentifier
mergeLexInfos ident1 ident2
    = case (ident1, ident2) of
        (HskVariable i,       HskTypeAnnotation t) -> HskVariable (updateLexInfo i t)
        (HskFunction i,       HskTypeAnnotation t) -> HskFunction (updateLexInfo i t)
        (HskInfixOp  i a p,   HskTypeAnnotation t) -> HskInfixOp  (updateLexInfo i t) a p
        (HskTypeAnnotation t, HskVariable i)       -> HskVariable (updateLexInfo i t)
        (HskTypeAnnotation t, HskFunction i)       -> HskFunction (updateLexInfo i t)
        (HskTypeAnnotation t, HskInfixOp  i a p)   -> HskInfixOp  (updateLexInfo i t) a p
        (_,_) 
            -> error ("Internal error (mergeLexInfo): Merge collision between `" ++ show ident1 ++ "'"
                      ++ " and `" ++ show ident2 ++ "'.")
    where updateLexInfo lexinfo@(HskLexInfo { typeOf = Nothing }) typ = lexinfo { typeOf = Just typ }
          updateLexInfo lexinfo typ
              = error ("Internal Error (mergeLexInfo): Type collision between `" ++ show lexinfo ++ "'" 
                       ++ " and `" ++ show typ ++ "'.")
        

--
-- ModuleEnv 
--

data ModuleE = HskModuleEnv Module [HsImportDecl] [HsExportSpec] LexE
  deriving (Show)

emptyModuleEnv = HskModuleEnv (Module "Main") [] [] emptyLexEnv_Hsk

makeModuleEnv :: HsModule -> ModuleE
makeModuleEnv (HsModule loc modul exports imports topdecls)
    = let lexenv   = makeLexEnv_Hsk (concatMap (extractLexInfos modul) topdecls)
          imports' = checkImports imports
          exports' = if isNothing exports then [HsEModuleContents modul] 
                                          else checkExports (fromJust exports) imports
      in HskModuleEnv modul imports' exports' lexenv
    where 
      checkImports imports 
          = checkForDuplicateImport (map checkImport imports)

      checkImport (HsImportDecl { importSpecs = Just _ }) 
          = error "Not supported yet: Explicit import specifications."
      checkImport etc = etc

      checkForDuplicateImport imports 
          = if hasDuplicates (modulesFromImports imports)
            then error ("Duplicates found in import list: " ++ show imports)
            else imports

      checkExports :: [HsExportSpec] -> [HsImportDecl] -> [HsExportSpec]
      checkExports exports imports 
          = do export <- checkForDuplicateExport (map checkExport exports)
               let [(qname, restoreExport)] = contextsBi export :: [(HsQName, HsQName -> HsExportSpec)]
               case qname of 
                 UnQual _ -> return (restoreExport qname)
                 Qual m _ 
                     -> if isImportedModule_aux m imports then return (restoreExport qname)
                        else error ("Module of `" ++ show qname ++ "'"
                                    ++ " is not in import list, but in export list.")

      checkExport e@(HsEVar _)            = e
      checkExport e@(HsEAbs _)            = e
      checkExport e@(HsEThingAll _)       = e
      checkExport e@(HsEModuleContents _) = e
      checkExport etc                     = error ("Not supported yet: " ++ show etc)

      checkForDuplicateExport :: [HsExportSpec] -> [HsExportSpec]
      checkForDuplicateExport exports 
          = if hasDuplicates (universeBi exports :: [HsName]) -- strip off qualifiers
            then error ("Duplicates found in export list: " ++ show exports)
            else exports

extractLexInfos :: Module -> HsDecl -> [(HsQName, HskIdentifier)]
extractLexInfos modul decl 
    = map (\name -> let defaultLexInfo = HskLexInfo { identifier=name, typeOf=Nothing, moduleOf=modul}
                    in (name, case decl of
                                HsPatBind _ _ _ _          -> HskVariable defaultLexInfo
                                HsFunBind _                -> HskFunction defaultLexInfo
                                HsInfixDecl _ assoc prio _ -> HskInfixOp  defaultLexInfo assoc prio
                                HsTypeSig _ _ typ          -> HskTypeAnnotation typ
                                HsDataDecl _ _ _ _ condecls _
                                    -> HskData (defaultLexInfo { typeOf = Just (HsTyCon name) })
                                               (map (qualify modul . UnQual . extractConstrName) condecls)
                                       where extractConstrName (HsQualConDecl _ _ _ (HsConDecl n _)) = n
                                             extractConstrName (HsQualConDecl _ _ _ (HsRecDecl n _)) = n
                       ))
      (fromJust $ namesFromHsDecl decl)


modulesFromImports :: [HsImportDecl] -> [Module]
modulesFromImports imports
    = map (\(HsImportDecl { importModule=m, importQualified=isQualified, importAs=nickname }) 
               -> if isQualified && isJust nickname then fromJust nickname 
                                                    else m)
          imports

isImportedModule_aux :: Module -> [HsImportDecl] -> Bool
isImportedModule_aux modul imports
    = let ms = modulesFromImports imports
      in case filter (== modul) ms of
           []     -> False
           [name] -> True
           etc    -> error ("Internal error (isImportedModule): Fall through. [" ++ show etc ++ "]")

isImportedModule modul (HskModuleEnv _ imports _ _)
    = isImportedModule_aux modul imports



--
-- GlobalEnv
--

data GlobalE = HskGlobalEnv (Map.Map Module ModuleE)
  deriving (Show)

emptyGlobalEnv = HskGlobalEnv (Map.empty)

makeGlobalEnv_Hsk :: [HsModule] -> GlobalE
makeGlobalEnv_Hsk ms 
    = HskGlobalEnv (Map.fromListWith failDups 
                     $ map (\m@(HsModule _ modul _ _ _) -> (modul, makeModuleEnv m)) ms)
    where failDups a b
              = error ("Duplicate modules: " ++ show a ++ ", " ++ show b)


findModuleEnv :: Module -> GlobalE -> Maybe ModuleE
findModuleEnv m (HskGlobalEnv globalmap) = Map.lookup m globalmap

findModuleEnvOrLose m globalEnv
    = case findModuleEnv m globalEnv of
        Just env -> env
        Nothing  -> error ("Couldn't find module `" ++ show m ++ "'.")


-- computeImportedModules :: Module -> GlobalE -> [Module]
-- computeImportedModules modul globalEnv
--     = let (HskModuleEnv _ imports _ _) = findModuleEnvOrLose modul globalEnv
--       in importedModules imports

computeExportedNames :: Module -> GlobalE -> [HsName]
computeExportedNames modul globalEnv
    = map (\qn -> case qn of { UnQual n -> n; Qual m n -> n }) 
       $ computeExportedQNames (findModuleEnvOrLose modul globalEnv) globalEnv
      where  
        computeExportedQNames (HskModuleEnv modul _ exports (HskLexEnv lexmap)) globalEnv
            = concatMap computeQNames exports
              where computeQNames (HsEVar qn) = [qn]
                    computeQNames (HsEAbs qn) = [qn]
                    computeQNames (HsEThingAll qn) 
                        = case Importer.LexEnv.lookup modul qn globalEnv of
                            Just (HskData _ constructors) 
                                -> constructors
                            etc -> error ("Internal error (computeExportedNames): " ++ show etc)
                    computeQNames (HsEModuleContents m)
                        = if m == modul then Map.keys lexmap -- export everything
                                        else computeExportedQNames (findModuleEnvOrLose m globalEnv) 
                                                                   globalEnv
isExported :: HskIdentifier -> Module -> GlobalE -> Bool
isExported identifier modul globalEnv
    = case identifier2name identifier of
        Qual m _  -> if  m == modul then isExported (makeUnqualified identifier) m globalEnv 
                                    else False
        UnQual n  -> n `elem` (computeExportedNames modul globalEnv)


lookup :: Module -> HsQName -> GlobalE -> Maybe HskIdentifier
lookup currentModule qname globalEnv = lookup' currentModule qname globalEnv -- ambiguous occurence `lookup'
    where                                                                    -- between LexEnv and Prelude
      lookup' currentModule qname globalEnv                              
          = do currentModuleEnv <- findModuleEnv currentModule globalEnv
               case qname of
                 Qual m n | m == currentModule || isImportedModule m currentModuleEnv
                          -> do hsxidentifier <- lookup' m (UnQual n) globalEnv
                                if isExported hsxidentifier m globalEnv then Just hsxidentifier
                                                                        else Nothing
                 Qual _ _ -> Nothing
                 UnQual n -> let (HskModuleEnv _ imports _ (HskLexEnv lexmap)) 
                                            = currentModuleEnv
                                 local_try  = Map.lookup (UnQual n) lexmap
                                 tries      = map (\(HsImportDecl { importModule = m }) 
                                                       -> lookup' currentModule (Qual m n) globalEnv) 
                                               $ filter (not . importQualified) imports
                             in case catMaybes (local_try : tries) of
                                  []   -> Nothing
                                  [x]  -> Just x
                                  x:xs -> error (Msg.identifier_collision_in_lookup currentModule qname (x:xs))
                 Special s -> Just (translateSpecialConstructor s)

-- FIXME: Kludge; what we actually need is an initial environment.
translateSpecialConstructor :: HsSpecialCon -> HskIdentifier
translateSpecialConstructor HsCons = HskInfixOp consLexInfo HsAssocRight 5
    where consLexInfo = HskLexInfo { identifier = Special HsCons,
                                     typeOf     = Just (HsTyFun (HsTyVar (HsIdent "a"))
                                                                (HsTyApp (HsTyCon (Special HsListCon))
                                                                         (HsTyCon (UnQual (HsIdent "a"))))),
                                     moduleOf   = Module "Prelude" }