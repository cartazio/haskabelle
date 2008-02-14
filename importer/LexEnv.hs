
module Importer.LexEnv where

import Maybe

import Data.Generics.PlateData (universeBi, contextsBi)

import qualified Data.Map as Map
import Language.Haskell.Hsx

import qualified Importer.Msg as Msg
import qualified Importer.IsaSyntax as Isa

import Importer.Utilities.Hsx
import Importer.Utilities.Misc

--
-- LexEnv
--

data HsxLexInfo = HsxLexInfo { 
                              identifier :: HsQName,
                              typeOf     :: Maybe HsType,
                              moduleOf   :: Module
                             }
  deriving (Eq, Show)

data HsxIdentifier = HsxVariable HsxLexInfo
                   | HsxFunction HsxLexInfo
                   | HsxInfixOp  HsxLexInfo HsAssoc Int
                   | HsxData     HsxLexInfo [HsQName] -- data constructors
                   | HsxTypeAnnotation HsType
  deriving (Eq, Show)

isHsxVariable, isHsxFunction, isHsxInfixOp, isHsxTypeAnnotation :: HsxIdentifier -> Bool

isHsxVariable (HsxVariable _) = True
isHsxVariable _ = False

isHsxFunction (HsxFunction _) = True
isHsxFunction _ = False

isHsxInfixOp (HsxInfixOp _ _ _) = True
isHsxInfixOp _ = False

isHsxTypeAnnotation (HsxTypeAnnotation _) = True
isHsxTypeAnnotation _ = False

isHsxData (HsxData _ _) = True
isHsxData _ = False

identifier2name :: HsxIdentifier -> HsQName
identifier2name hsxidentifier
    = identifier (extractLexInfo hsxidentifier)
    where extractLexInfo (HsxVariable i)    = i
          extractLexInfo (HsxFunction i)    = i
          extractLexInfo (HsxInfixOp i _ _) = i
          extractLexInfo (HsxData i _)      = i


makeUnqualified :: HsxIdentifier -> HsxIdentifier
makeUnqualified hsxidentifier
    = case identifier2name hsxidentifier of
        UnQual n -> hsxidentifier
        Qual _ n -> case hsxidentifier of
                      HsxVariable lexinfo     -> HsxVariable (lexinfo { identifier = UnQual n })
                      HsxFunction lexinfo     -> HsxFunction (lexinfo { identifier = UnQual n })
                      HsxInfixOp  lexinfo a p -> HsxInfixOp  (lexinfo { identifier = UnQual n }) a p
                      HsxData     lexinfo cs  -> HsxData     (lexinfo { identifier = UnQual n }) cs


data LexE = HsxLexEnv (Map.Map HsQName HsxIdentifier)
  deriving (Show)


emptyLexEnv_Hsx = HsxLexEnv Map.empty

makeLexEnv_Hsx :: [(HsQName, HsxIdentifier)] -> LexE
makeLexEnv_Hsx initbindings
    = HsxLexEnv (Map.fromListWith mergeLexInfos initbindings)

mergeLexInfos :: HsxIdentifier -> HsxIdentifier -> HsxIdentifier
mergeLexInfos ident1 ident2
    = case (ident1, ident2) of
        (HsxVariable i,       HsxTypeAnnotation t) -> HsxVariable (updateLexInfo i t)
        (HsxFunction i,       HsxTypeAnnotation t) -> HsxFunction (updateLexInfo i t)
        (HsxInfixOp  i a p,   HsxTypeAnnotation t) -> HsxInfixOp  (updateLexInfo i t) a p
        (HsxTypeAnnotation t, HsxVariable i)       -> HsxVariable (updateLexInfo i t)
        (HsxTypeAnnotation t, HsxFunction i)       -> HsxFunction (updateLexInfo i t)
        (HsxTypeAnnotation t, HsxInfixOp  i a p)   -> HsxInfixOp  (updateLexInfo i t) a p
        (_,_) 
            -> error ("Internal error (mergeLexInfo): Merge collision between `" ++ show ident1 ++ "'"
                      ++ " and `" ++ show ident2 ++ "'.")
    where updateLexInfo lexinfo@(HsxLexInfo { typeOf = Nothing }) typ = lexinfo { typeOf = Just typ }
          updateLexInfo lexinfo typ
              = error ("Internal Error (mergeLexInfo): Type collision between `" ++ show lexinfo ++ "'" 
                       ++ " and `" ++ show typ ++ "'.")
        

--
-- ModuleEnv 
--

data ModuleE = HsxModuleEnv Module [HsImportDecl] [HsExportSpec] LexE
  deriving (Show)

emptyModuleEnv = HsxModuleEnv (Module "Main") [] [] emptyLexEnv_Hsx

makeModuleEnv :: HsModule -> ModuleE
makeModuleEnv (HsModule loc modul exports imports topdecls)
    = let lexenv   = makeLexEnv_Hsx (concatMap (extractLexInfos modul) topdecls)
          imports' = checkImports imports
          exports' = if isNothing exports then [HsEModuleContents modul] 
                                          else checkExports (fromJust exports) imports
      in HsxModuleEnv modul imports' exports' lexenv
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

extractLexInfos :: Module -> HsDecl -> [(HsQName, HsxIdentifier)]
extractLexInfos modul decl 
    = map (\name -> let defaultLexInfo = HsxLexInfo { identifier=name, typeOf=Nothing, moduleOf=modul}
                    in (name, case decl of
                                HsPatBind _ _ _ _          -> HsxVariable defaultLexInfo
                                HsFunBind _                -> HsxFunction defaultLexInfo
                                HsInfixDecl _ assoc prio _ -> HsxInfixOp  defaultLexInfo assoc prio
                                HsTypeSig _ _ typ          -> HsxTypeAnnotation typ
                                HsDataDecl _ _ _ _ condecls _
                                    -> HsxData (defaultLexInfo { typeOf = Just (HsTyCon name) })
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

isImportedModule modul (HsxModuleEnv _ imports _ _)
    = isImportedModule_aux modul imports



--
-- GlobalEnv
--

data GlobalE = HsxGlobalEnv (Map.Map Module ModuleE)
  deriving (Show)

emptyGlobalEnv = HsxGlobalEnv (Map.empty)

makeGlobalEnv_Hsx :: [HsModule] -> GlobalE
makeGlobalEnv_Hsx ms 
    = HsxGlobalEnv (Map.fromListWith failDups 
                     $ map (\m@(HsModule _ modul _ _ _) -> (modul, makeModuleEnv m)) ms)
    where failDups a b
              = error ("Duplicate modules: " ++ show a ++ ", " ++ show b)


findModuleEnv :: Module -> GlobalE -> Maybe ModuleE
findModuleEnv m (HsxGlobalEnv globalmap) = Map.lookup m globalmap

findModuleEnvOrLose m globalEnv
    = case findModuleEnv m globalEnv of
        Just env -> env
        Nothing  -> error ("Couldn't find module `" ++ show m ++ "'.")


-- computeImportedModules :: Module -> GlobalE -> [Module]
-- computeImportedModules modul globalEnv
--     = let (HsxModuleEnv _ imports _ _) = findModuleEnvOrLose modul globalEnv
--       in importedModules imports

computeExportedNames :: Module -> GlobalE -> [HsName]
computeExportedNames modul globalEnv
    = map (\qn -> case qn of { UnQual n -> n; Qual m n -> n }) 
       $ computeExportedQNames (findModuleEnvOrLose modul globalEnv) globalEnv
      where  
        computeExportedQNames (HsxModuleEnv modul _ exports (HsxLexEnv lexmap)) globalEnv
            = concatMap computeQNames exports
              where computeQNames (HsEVar qn) = [qn]
                    computeQNames (HsEAbs qn) = [qn]
                    computeQNames (HsEThingAll qn) 
                        = case Importer.LexEnv.lookup modul qn globalEnv of
                            Just (HsxData _ constructors) 
                                -> constructors
                            etc -> error ("Internal error (computeExportedNames): " ++ show etc)
                    computeQNames (HsEModuleContents m)
                        = if m == modul then Map.keys lexmap -- export everything
                                        else computeExportedQNames (findModuleEnvOrLose m globalEnv) 
                                                                   globalEnv
isExported :: HsxIdentifier -> Module -> GlobalE -> Bool
isExported identifier modul globalEnv
    = case identifier2name identifier of
        Qual m _  -> if  m == modul then isExported (makeUnqualified identifier) m globalEnv 
                                    else False
        UnQual n  -> n `elem` (computeExportedNames modul globalEnv)


lookup :: Module -> HsQName -> GlobalE -> Maybe HsxIdentifier
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
                 UnQual n -> let (HsxModuleEnv _ imports _ (HsxLexEnv lexmap)) 
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
translateSpecialConstructor :: HsSpecialCon -> HsxIdentifier
translateSpecialConstructor HsCons = HsxInfixOp consLexInfo HsAssocRight 5
    where consLexInfo = HsxLexInfo { identifier = Special HsCons,
                                     typeOf     = Just (HsTyFun (HsTyVar (HsIdent "a"))
                                                                (HsTyApp (HsTyCon (Special HsListCon))
                                                                         (HsTyCon (UnQual (HsIdent "a"))))),
                                     moduleOf   = Module "Prelude" }