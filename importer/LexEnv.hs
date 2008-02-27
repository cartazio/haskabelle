
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
-- Identifier information
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
    = let name = identifier (extractLexInfo hsxidentifier)
      in assert (not $ isQualifiedName name) name

extractLexInfo (HskVariable i)    = i
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



data IsaLexInfo = IsaLexInfo { 
                              _identifier :: Isa.Name,
                              _typeOf     :: Isa.Type,
                              _theoryOf   :: Isa.Theory
                             }
  deriving (Eq, Show)

data IsaIdentifier = IsaVariable IsaLexInfo
                   | IsaFunction IsaLexInfo
                   | IsaInfixOp  IsaLexInfo Isa.Assoc Int
  deriving (Eq, Show)

isaIdentifier2name (IsaVariable i)     = _identifier i
isaIdentifier2name (IsaFunction i)     = _identifier i
isaIdentifier2name (IsaInfixOp  i _ _) = _identifier i

extractLexInfo_isa (IsaVariable i)    = i
extractLexInfo_isa (IsaFunction i)    = i
extractLexInfo_isa (IsaInfixOp i _ _) = i

--
-- LexEnv
--

-- We must use HsQName as key (and not just HsName) because HsQName
-- does additionally contain special constructor names. We, however,
-- guarantee that a LexE does _not_ contain any qualified names, only
-- UnQual and Special constructors.
data LexE = HskLexEnv (Map.Map HsQName HskIdentifier)
          | IsaLexEnv (Map.Map Isa.Name IsaIdentifier)
  deriving (Show)


emptyLexEnv_Hsk = HskLexEnv Map.empty

makeLexEnv_Hsk :: [(HsQName, HskIdentifier)] -> LexE
makeLexEnv_Hsk initbindings
    = assert (all (not . isQualifiedName) $ map fst initbindings)
        $ HskLexEnv (Map.fromListWith mergeLexInfosOrFail initbindings)


mergeLexInfosOrFail :: HskIdentifier -> HskIdentifier -> HskIdentifier
mergeLexInfosOrFail ident1 ident2
    = case mergeLexInfos ident1 ident2 of
        Just result -> result
        Nothing     -> error ("Internal error (mergeLexInfo): Merge collision between `" 
                              ++ show ident1 ++ "'" ++ " and `" ++ show ident2 ++ "'.")

mergeLexInfos :: HskIdentifier -> HskIdentifier -> Maybe HskIdentifier
mergeLexInfos ident1 ident2
    = case (ident1, ident2) of
        (HskVariable i,       HskTypeAnnotation t) -> Just $ HskVariable (update i t)
        (HskFunction i,       HskTypeAnnotation t) -> Just $ HskFunction (update i t)
        (HskInfixOp  i a p,   HskTypeAnnotation t) -> Just $ HskInfixOp  (update i t) a p
        (HskTypeAnnotation t, HskVariable i)       -> Just $ HskVariable (update i t)
        (HskTypeAnnotation t, HskFunction i)       -> Just $ HskFunction (update i t)
        (HskTypeAnnotation t, HskInfixOp  i a p)   -> Just $ HskInfixOp  (update i t) a p
        (_,_) -> Nothing
    where update lexinfo@(HskLexInfo { typeOf = Nothing }) typ = lexinfo { typeOf = Just typ }
          update lexinfo typ
              = error ("Internal Error (mergeLexInfo): Type collision between `" ++ show lexinfo ++ "'" 
                       ++ " and `" ++ show typ ++ "'.")

mergeLexEnvs (HskLexEnv map1) (HskLexEnv map2)
    = HskLexEnv
        $ Map.unionWithKey
              (\n identifier1 identifier2
                   -> let id1 = if Map.member n map1 then identifier1 else identifier1
                          id2 = if Map.member n map1 then identifier2 else identifier2
                      in -- id1 is identifier that belongs to `map1'.
                        case mergeLexInfos id1 id2 of
                          Nothing     -> id2  -- favoritize second argument.
                          Just result -> result)
              map1 map2

--
-- ModuleEnv 
--

data ModuleE = HskModuleEnv Module [HsImportDecl] [HsExportSpec] LexE
             | IsaTheoryEnv Isa.Theory LexE
  deriving (Show)

emptyModuleEnv = HskModuleEnv (Module "Main") [] [] emptyLexEnv_Hsk

defaultImports = [HsImportDecl { importLoc       = srcloc,
                                 importModule    = Module "Prelude",
                                 importQualified = False,
                                 importAs        = Nothing,
                                 importSpecs     = Nothing
                               }
                 ]
    where srcloc = SrcLoc { srcFilename = "Importer/LexEnv.hs",
                            srcLine = 135, srcColumn = 0 }

makeModuleEnv :: HsModule -> ModuleE
makeModuleEnv (HsModule loc modul exports imports topdecls)
    = let lexenv   = makeLexEnv_Hsk (concatMap (extractLexInfos modul) topdecls)
          imports' = checkImports imports ++ defaultImports
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
    = map (\name -> let name' = unqualify name
                        defaultLexInfo = HskLexInfo { identifier=name, typeOf=Nothing, moduleOf=modul}
                    in (name', case decl of
                                 HsPatBind _ _ _ _          -> HskVariable defaultLexInfo
                                 HsFunBind _                -> HskFunction defaultLexInfo
                                 HsInfixDecl _ assoc prio _ -> HskInfixOp  defaultLexInfo assoc prio
                                 HsTypeSig _ _ typ          -> HskTypeAnnotation typ
                                 HsDataDecl _ _ _ _ condecls _
                                     -> HskData (defaultLexInfo { typeOf = Just (HsTyCon name') })
                                           $ map (UnQual . extractConstrName) condecls
                                        where extractConstrName (HsQualConDecl _ _ _ (HsConDecl n _)) = n
                                              extractConstrName (HsQualConDecl _ _ _ (HsRecDecl n _)) = n
                       ))
      (fromJust $ namesFromHsDecl decl)


mergeModuleEnvs (HskModuleEnv m1 is1 es1 lex1) (HskModuleEnv m2 is2 es2 lex2)
    = assert (m1 == m2)
        $ HskModuleEnv m1 (is1 ++ is2) (es1 ++ es2) (mergeLexEnvs lex1 lex2)


-- returns module name as can be found in source code, i.e.
-- returns qualified nicknames if any.
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
             | IsaGlobalEnv (Map.Map Isa.Theory ModuleE)
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

mergeGlobalEnvs :: GlobalE -> GlobalE -> GlobalE
mergeGlobalEnvs (HskGlobalEnv map1) (HskGlobalEnv map2)
    = HskGlobalEnv 
        $ Map.unionWithKey
              (\m moduleEnv1 moduleEnv2
                   -> let env1 = if Map.member m map1 then moduleEnv1 else moduleEnv2
                          env2 = if Map.member m map1 then moduleEnv2 else moduleEnv1
                      in -- env1 contains ModuleE that belongs to `map1'.
                        mergeModuleEnvs env1 env2)
              map1 map2
                  

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
        Qual m _  -> error ("Internal Error: All identifiers should be unqualified: " 
                            ++ prettyShow' "identifier" identifier ++ "\n" 
                            ++ prettyShow' "globalEnv" globalEnv)
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
                 Special s -> lookup' currentModule (translateSpecialConstructor s) globalEnv

translateSpecialConstructor :: HsSpecialCon -> HsQName
translateSpecialConstructor HsCons = Qual (Module "Prelude") (HsIdent "cons")

lookup_isa :: Isa.Theory -> Isa.Name -> GlobalE -> Maybe IsaIdentifier
lookup_isa theory name globalEnv
    = case lookup' theory name globalEnv of
        Nothing  -> lookup' (Isa.Theory "Prelude") name globalEnv
        Just foo -> Just foo
    where lookup' theory (Isa.QName thy string) globalEnv
              = if theory == thy then lookup' theory (Isa.Name string) globalEnv
                                 else Nothing
          lookup' theory name@(Isa.Name _) (IsaGlobalEnv globalmap)
              = do (IsaTheoryEnv _ (IsaLexEnv lexmap)) <- Map.lookup theory globalmap
                   Map.lookup name lexmap