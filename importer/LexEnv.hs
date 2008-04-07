{-  ID:         $Id: Isa.hs 431 2007-08-14 09:07:17Z haftmann $
    Author:     Tobias C. Rittweiler, TU Muenchen
-}

module Importer.LexEnv where

import Maybe
import List (groupBy, sortBy)
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

type ModuleID = String
type IdentifierID = String

data EnvName = EnvQualName ModuleID IdentifierID
             | EnvUnqualName IdentifierID
  deriving (Eq, Show)

data EnvType = EnvTyVar EnvName
             | EnvTyCon EnvName [EnvType]
             | EnvTyFun EnvType EnvType
             | EnvTyTuple [EnvType]
  deriving (Eq, Show)

data EnvAssoc = EnvAssocRight | EnvAssocLeft | EnvAssocNone
  deriving (Eq, Show)

data LexInfo = LexInfo { 
                        nameOf   :: IdentifierID,
                        typeOf   :: Maybe EnvType,
                        moduleOf :: ModuleID
                       }
  deriving (Eq, Show)

data Identifier = Variable LexInfo
                | Function LexInfo
                | InfixOp  LexInfo EnvAssoc Int
                | TypeAnnotation LexInfo EnvType
                | Type LexInfo [IdentifierID] -- Type lexinfo [constructorNs]
  deriving (Eq, Show)

makeLexInfo :: ModuleID -> IdentifierID -> EnvType -> LexInfo
makeLexInfo moduleID identifierID t
    = LexInfo { nameOf   = identifierID,
                typeOf   = Just t,
                moduleOf = moduleID }

isVariable, isFunction, isInfixOp, isTypeAnnotation :: Identifier -> Bool

isVariable (Variable _)   = True
isVariable _              = False

isFunction (Function _)   = True
isFunction _              = False

isInfixOp (InfixOp _ _ _) = True
isInfixOp _               = False

isTypeAnnotation (TypeAnnotation _ _) = True
isTypeAnnotation _                    = False

isType (Type _ _) = True
isType _          = False


lexInfoOf (Variable i)         = i
lexInfoOf (Function i)         = i
lexInfoOf (InfixOp i _ _)      = i
lexInfoOf (Type i _)           = i
lexInfoOf (TypeAnnotation i _) = i

identifier2name :: Identifier -> EnvName
identifier2name identifier
    = let lexinfo  = lexInfoOf identifier
          name     = nameOf lexinfo
          modul    = moduleOf lexinfo
      in if (modul == "") then EnvUnqualName name
                          else EnvQualName modul name

-- makeUnqualified :: HskIdentifier -> HskIdentifier
-- makeUnqualified hsxidentifier
--     = case identifier2name hsxidentifier of
--         UnQual n -> hsxidentifier
--         Qual _ n -> case hsxidentifier of
--                       HskVariable lexinfo     -> HskVariable (lexinfo { identifier = UnQual n })
--                       HskFunction lexinfo     -> HskFunction (lexinfo { identifier = UnQual n })
--                       HskInfixOp  lexinfo a p -> HskInfixOp  (lexinfo { identifier = UnQual n }) a p
--                       HskType     lexinfo cs  -> HskType     (lexinfo { identifier = UnQual n }) cs


class Hsk2Env a b where
    fromHsk :: (Show a, Hsk2Env a b) => a -> b
    toHsk   :: (Show b, Hsk2Env a b) => b -> a
    toHsk b = error ("(toHsk) Internal Error: Don't know how to lift " ++ show b)

instance Hsk2Env Module ModuleID where
    fromHsk (Module id) = id
    toHsk id            = Module id

instance Hsk2Env HsQName IdentifierID where
    fromHsk (Qual _ n)  = fromHsk n
    fromHsk (UnQual n)  = fromHsk n
    fromHsk (Special s) = fromHsk (translateSpecialCon DataCon s)
    
    toHsk junk = error ("toHsk IdentifierID -> HsName: " ++ show junk)

    
instance Hsk2Env HsName IdentifierID where
    fromHsk (HsIdent s)  = s
    fromHsk (HsSymbol s) = s
    toHsk id             = string2HsName id

data ConKind = DataCon | TypeCon

translateSpecialCon :: ConKind -> HsSpecialCon -> HsQName
translateSpecialCon DataCon HsCons    = Qual (Module "Prelude") (HsSymbol ":")
translateSpecialCon TypeCon HsListCon = Qual (Module "Prelude") (HsIdent "list")

retranslateSpecialCon :: ConKind -> HsQName -> Maybe HsSpecialCon
retranslateSpecialCon DataCon (Qual (Module "Prelude") (HsSymbol ":"))   = Just HsCons
retranslateSpecialCon TypeCon (Qual (Module "Prelude") (HsIdent "list")) = Just HsListCon
retranslateSpecialCon _ _ = Nothing


instance Hsk2Env HsQName EnvName where
    fromHsk (Qual m n)  = EnvQualName (fromHsk m) (fromHsk n)
    fromHsk (UnQual n)  = EnvUnqualName (fromHsk n)
    fromHsk (Special s) = fromHsk (translateSpecialCon DataCon s)

    toHsk (EnvQualName moduleId id) = let qname = Qual (toHsk moduleId) (toHsk id)
                                      in case retranslateSpecialCon DataCon qname of
                                           Just s  -> Special s
                                           Nothing -> qname                                         
    toHsk (EnvUnqualName id)        = UnQual (toHsk id)

instance Hsk2Env HsName EnvName where
    fromHsk hsname           = EnvUnqualName (fromHsk hsname)
    toHsk (EnvUnqualName id) = toHsk id
    toHsk junk = error ("toHsk EnvName -> HsName: " ++ show junk)

instance Hsk2Env HsAssoc EnvAssoc where
    fromHsk HsAssocRight = EnvAssocRight
    fromHsk HsAssocLeft  = EnvAssocLeft
    fromHsk HsAssocNone  = EnvAssocNone

    toHsk EnvAssocRight  = HsAssocRight
    toHsk EnvAssocLeft   = HsAssocLeft
    toHsk EnvAssocNone   = HsAssocNone


instance Hsk2Env HsType EnvType where
    fromHsk (HsTyVar name)  = EnvTyVar (fromHsk name)
    fromHsk (HsTyCon qname) = EnvTyCon (fromHsk (translate qname)) []
                            where translate (Special s) = translateSpecialCon TypeCon s
                                  translate etc = etc

    fromHsk (HsTyTuple Boxed types) = EnvTyTuple (map fromHsk types)

    fromHsk (HsTyFun type1 type2) = let type1' = fromHsk type1
                                        type2' = fromHsk type2
                                    in EnvTyFun type1' type2'

    -- Types aren't curried or partially appliable in HOL, so we must pull a nested
    -- chain of type application inside out:
    --
    --  T a b ==> HsTyApp (HsTyApp (HsTyCon T) (HsTyVar a)) (HsTyVar b)
    --       
    --        ==> EnvTyCon T [(EnvTyVar a), (EnvTyVar b)]   
    --
    fromHsk tyapp@(HsTyApp _ _) 
        = let tycon:tyvars = unfoldl1 split tyapp
              tycon'       = fromHsk tycon
              tyvars'      = map fromHsk tyvars
          in case tycon' of EnvTyCon n [] -> EnvTyCon n tyvars'
          where split (HsTyApp tyapp x) = Just (x, tyapp)
                split (HsTyCon _)       = Nothing         -- Note that this HsTyCon will become
                split junk                                --  the head of the returned list.
                    = error ("HsType -> EnvType (split HsTyApp): " ++ (show junk))

    fromHsk junk = error ("HsType -> EnvType: Fall Through: " ++ show junk)

    toHsk (EnvTyVar n)       = HsTyVar (toHsk n)
    toHsk (EnvTyTuple types) = HsTyTuple Boxed (map toHsk types)
    toHsk (EnvTyFun t1 t2)   = HsTyFun (toHsk t1) (toHsk t2)
    toHsk (EnvTyCon qn [])   = HsTyCon (toHsk qn)
    toHsk (EnvTyCon qn tyvars)
        = let tycon'         = toHsk (EnvTyCon qn [])
              tyvar':tyvars' = map toHsk tyvars
          in foldl HsTyApp (HsTyApp tycon' tyvar') tyvars'


class Isa2Env a b where
    fromIsa :: (Show a, Isa2Env a b) => a -> b
    toIsa   :: (Show b, Isa2Env a b) => b -> a
    toIsa b = error ("(toIsa) Internal Error: Don't know how to lift " ++ show b)

instance Isa2Env Isa.Theory ModuleID where
    fromIsa (Isa.Theory thyN) = thyN
    toIsa moduleID            = Isa.Theory moduleID

instance Isa2Env Isa.Name EnvName where
    fromIsa (Isa.QName thy n)       = EnvQualName (fromIsa thy) n
    fromIsa (Isa.Name n)            = EnvUnqualName n

    toIsa (EnvQualName moduleId id) = Isa.QName (toIsa moduleId) id
    toIsa (EnvUnqualName id)        = Isa.Name id

instance Isa2Env Isa.Assoc EnvAssoc where
    fromIsa Isa.AssocRight = EnvAssocRight
    fromIsa Isa.AssocLeft  = EnvAssocLeft
    fromIsa Isa.AssocNone  = EnvAssocNone

    toIsa EnvAssocRight    = Isa.AssocRight
    toIsa EnvAssocLeft     = Isa.AssocLeft
    toIsa EnvAssocNone     = Isa.AssocNone

instance Isa2Env Isa.Type EnvType where
    fromIsa (Isa.TyVar n)         = EnvTyVar (fromIsa n)
    fromIsa (Isa.TyTuple types)   = EnvTyTuple (map fromIsa types)
    fromIsa (Isa.TyFun t1 t2)     = EnvTyFun (fromIsa t1) (fromIsa t2)
    fromIsa (Isa.TyCon qn tyvars) = EnvTyCon (fromIsa qn) (map fromIsa tyvars)

    toIsa (EnvTyVar n)            = Isa.TyVar (toIsa n)
    toIsa (EnvTyTuple types)      = Isa.TyTuple (map toIsa types)
    toIsa (EnvTyFun t1 t2)        = Isa.TyFun (toIsa t1) (toIsa t2)
    toIsa (EnvTyCon qn tyvars)    = Isa.TyCon (toIsa qn) (map toIsa tyvars)


-- data IsaLexInfo = IsaLexInfo { 
--                               _identifier :: Isa.Name,
--                               _typeOf     :: Isa.Type,
--                               _theoryOf   :: Isa.Theory
--                              }
--   deriving (Eq, Show)

-- data IsaIdentifier = IsaVariable IsaLexInfo
--                    | IsaFunction IsaLexInfo
--                    | IsaInfixOp  IsaLexInfo Isa.Assoc Int
--                    | IsaType     IsaLexInfo
--   deriving (Eq, Show)

-- isaIdentifier2name id  = _identifier (extractLexInfo_isa id)

-- extractLexInfo_isa (IsaVariable i)    = i
-- extractLexInfo_isa (IsaFunction i)    = i
-- extractLexInfo_isa (IsaInfixOp i _ _) = i
-- extractLexInfo_isa (IsaType i)        = i


--
-- LexEnv
--

data LexE = LexEnv (Map.Map IdentifierID Identifier)
  deriving (Show)

emptyLexEnv = LexEnv Map.empty

makeLexEnv :: [Identifier] -> LexE
makeLexEnv identifiers
    = let initbindings = zip (map (nameOf . lexInfoOf) identifiers) identifiers
      in LexEnv (Map.fromListWith mergeIdentifiers_OrFail initbindings)

mergeIdentifiers_OrFail :: Identifier -> Identifier -> Identifier
mergeIdentifiers_OrFail ident1 ident2
    = case mergeIdentifiers ident1 ident2 of
        Just result -> result
        Nothing     -> error ("Internal error (mergeLexInfo): Merge collision between `" 
                              ++ show ident1 ++ "'" ++ " and `" ++ show ident2 ++ "'.")
mergeIdentifiers :: Identifier -> Identifier -> Maybe Identifier
mergeIdentifiers ident1 ident2
    = assert (identifier2name ident1 == identifier2name ident2)
      $ case (ident1, ident2) of
          (Variable i,       TypeAnnotation _ t) -> Just $ Variable (update i t)
          (Function i,       TypeAnnotation _ t) -> Just $ Function (update i t)
          (InfixOp  i a p,   TypeAnnotation _ t) -> Just $ InfixOp  (update i t) a p
          (TypeAnnotation _ t, Variable i)       -> Just $ Variable (update i t)
          (TypeAnnotation _ t, Function i)       -> Just $ Function (update i t)
          (TypeAnnotation _ t, InfixOp  i a p)   -> Just $ InfixOp  (update i t) a p
          (_,_) -> Nothing
    where update lexinfo@(LexInfo { typeOf = Nothing }) typ 
              = lexinfo { typeOf = Just typ }
          update lexinfo typ    -- Cannot merge + internal inconsistency.
              = error ("Internal Error (mergeLexInfo): Type collision between `" ++ show lexinfo ++ "'" 
                       ++ " and `" ++ show typ ++ "'.")

mergeLexEnvs (LexEnv map1) (LexEnv map2)
    = LexEnv
        $ Map.unionWithKey
              (\n identifier1 identifier2
                   -> let id1 = if Map.member n map1 then identifier1 else identifier1
                          id2 = if Map.member n map1 then identifier2 else identifier2
                      in -- id1 is identifier that belongs to `map1'.
                        case mergeIdentifiers id1 id2 of
                          Nothing     -> id2  -- favorize second argument.
                          Just result -> result)
              map1 map2

mapLexEnv :: (Identifier -> Maybe Identifier) -> LexE -> LexE
mapLexEnv update (LexEnv lexmap)
    = LexEnv (Map.mapMaybe update lexmap)

--
-- ModuleEnv 
--

data ModuleE = ModuleEnv ModuleID [HsImportDecl] [HsExportSpec] LexE
  deriving (Show)


emptyModuleEnv = ModuleEnv "Main" [] [] emptyLexEnv

defaultImports = [HsImportDecl { importLoc       = srcloc,
                                 importModule    = Module "Prelude",
                                 importQualified = False,
                                 importAs        = Nothing,
                                 importSpecs     = Nothing
                               }
                 ]
    where srcloc = SrcLoc { srcFilename = "Importer/LexEnv.hs",
                            srcLine = 135, srcColumn = 0 }

makeModuleEnv :: (Identifier -> Bool) -> [Identifier] -> ModuleE
makeModuleEnv shall_export_p identifiers
    = let m = moduleOf (lexInfoOf (head identifiers))
      in assert (all (== m) $ map (moduleOf . lexInfoOf) (tail identifiers))
           $ ModuleEnv m [] (exportAll (filter shall_export_p identifiers))
                            (makeLexEnv identifiers)
    where exportAll :: [Identifier] -> [HsExportSpec]
          exportAll identifiers = map (HsEVar . toHsk . identifier2name) identifiers

mapModuleEnv :: (Identifier -> Maybe Identifier) -> ModuleE -> ModuleE
mapModuleEnv update (ModuleEnv mId imps exps lexenv)
    = ModuleEnv mId imps exps (mapLexEnv update lexenv)

makeModuleEnv_fromHsModule :: HsModule -> ModuleE
makeModuleEnv_fromHsModule (HsModule loc modul exports imports topdecls)
    = let lexenv   = makeLexEnv (concatMap (computeIdentifierMappings modul) topdecls)
          imports' = checkImports imports ++ defaultImports
          exports' = if isNothing exports then [HsEModuleContents modul] 
                                          else checkExports (fromJust exports) imports
      in ModuleEnv (fromHsk modul) imports' exports' lexenv
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
                   | isImportedModule_aux (fromHsk m) imports  
                       -> return (restoreExport qname)
                   | otherwise 
                       -> error ("Module of `" ++ show qname ++ "'"
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

computeIdentifierMappings :: Module -> HsDecl -> [Identifier]
computeIdentifierMappings modul decl 
    = do name <- fromJust (namesFromHsDecl decl)
         let nameID         = fromHsk name
         let moduleID       = fromHsk modul
         let defaultLexInfo = LexInfo { nameOf=nameID, typeOf=Nothing, moduleOf=moduleID}
         return $ case decl of
                    HsPatBind _ _ _ _   -> Variable defaultLexInfo
                    HsFunBind _         -> Function defaultLexInfo
                    HsInfixDecl _ a p _ -> InfixOp  defaultLexInfo (fromHsk a) p
                    HsTypeSig _ _ typ   -> TypeAnnotation defaultLexInfo (fromHsk typ)
                    HsDataDecl _ _ conN tyvarNs condecls _
                        -> assert (fromHsk conN == nameID)
                             $ Type (defaultLexInfo { typeOf = Just (mkTyCon nameID tyvarNs) })
                                    (map (fromHsk . extractConN) condecls)
                        where mkTyCon nameID tyvarNs = EnvTyCon (fromHsk name) 
                                                         $ map (EnvTyVar . fromHsk) tyvarNs
                              extractConN (HsQualConDecl _ _ _ (HsConDecl n _)) = n
                              extractConN (HsQualConDecl _ _ _ (HsRecDecl n _)) = n
      

mergeModuleEnvs (ModuleEnv m1 is1 es1 lex1) (ModuleEnv m2 is2 es2 lex2)
    = assert (m1 == m2)
        $ ModuleEnv m1 (is1 ++ is2) (es1 ++ es2) (mergeLexEnvs lex1 lex2)


-- returns module name as can be found in source code, i.e.
-- returns qualified nicknames if any.
modulesFromImports :: [HsImportDecl] -> [Module]
modulesFromImports imports
    = concatMap (\(imp@(HsImportDecl { importModule=m, 
                                       importQualified=isQualified, 
                                       importAs=nickname }))
                     -> case (isQualified, isJust nickname) of
                          -- Notice: Module names can _always_ be explicitly qualified.
                          (False, False) -> [m] 
                          (True,  False) -> [m]
                          (True,  True)  -> [m, fromJust nickname]
                          (False, True)  
                              -> error ("<modulesFromImports> Internal Error: " ++
                                        "bogus import:" ++ show imp))
          imports

isImportedModule_aux :: ModuleID -> [HsImportDecl] -> Bool
isImportedModule_aux moduleID imports
    = let ms = map fromHsk (modulesFromImports imports)
      in case filter (== moduleID) ms of
           []     -> False
           [name] -> True
           etc    -> error ("Internal error (isImportedModule): Fall through. [" ++ show etc ++ "]")

isImportedModule moduleID (ModuleEnv _ imports _ _)
    = isImportedModule_aux moduleID imports



--
-- GlobalEnv
--

data GlobalE = GlobalEnv (Map.Map ModuleID ModuleE)
  deriving (Show)

emptyGlobalEnv = GlobalEnv (Map.empty)

makeGlobalEnv :: (Identifier -> Bool) -> [Identifier] -> GlobalE
makeGlobalEnv shall_export_p identifiers
     = GlobalEnv
         $ Map.fromListWith failDups
             (do (moduleId, ids) <- groupIdentifiers identifiers
                 return (moduleId, makeModuleEnv shall_export_p ids))
    where failDups a b = error ("Duplicate modules: " ++ show a ++ ", " ++ show b)

groupIdentifiers :: [Identifier] -> [(ModuleID, [Identifier])]
groupIdentifiers identifiers
    = map (\(m:_, ids) -> (m, ids)) 
      $ map unzip 
         $ groupBy (\(m1,_) (m2,_) -> m1 == m2) 
             $ sortBy (\(m1,_) (m2,_) -> m1 `compare` m2) entries
    where entries :: [(ModuleID, Identifier)]
          entries = map (\id -> (moduleOf (lexInfoOf id), id)) identifiers

makeGlobalEnv_fromHsModules :: [HsModule] -> GlobalE
makeGlobalEnv_fromHsModules ms 
    = GlobalEnv 
        $ Map.fromListWith failDups 
              [ (fromHsk modul, makeModuleEnv_fromHsModule m) 
                    | m@(HsModule _ modul _ _ _) <- ms ]
    where failDups a b = error ("Duplicate modules: " ++ show a ++ ", " ++ show b)

findModuleEnv :: ModuleID -> GlobalE -> Maybe ModuleE
findModuleEnv mID (GlobalEnv globalmap) = Map.lookup mID globalmap

findModuleEnv_OrLose m globalEnv
    = case findModuleEnv m globalEnv of
        Just env -> env
        Nothing  -> error ("Couldn't find module `" ++ show m ++ "'.")

mergeGlobalEnvs :: GlobalE -> GlobalE -> GlobalE
mergeGlobalEnvs (GlobalEnv map1) (GlobalEnv map2)
    = GlobalEnv 
        $ Map.unionWithKey
              (\m moduleEnv1 moduleEnv2
                   -> let env1 = if Map.member m map1 then moduleEnv1 else moduleEnv2
                          env2 = if Map.member m map1 then moduleEnv2 else moduleEnv1
                      in -- `env1' contains ModuleE that belongs to `map1'.
                         mergeModuleEnvs env1 env2)
              map1 map2
          
mapGlobalEnv :: (Identifier -> Maybe Identifier) -> GlobalE -> GlobalE
mapGlobalEnv update (GlobalEnv modulemap)
    = GlobalEnv $ Map.map (\moduleEnv -> mapModuleEnv update moduleEnv) modulemap        

-- computeImportedModules :: Module -> GlobalE -> [Module]
-- computeImportedModules modul globalEnv
--     = let (HskModuleEnv _ imports _ _) = findModuleEnvOrLose modul globalEnv
--       in importedModules imports

computeExportedNames :: ModuleID -> GlobalE -> [IdentifierID]
computeExportedNames moduleID globalEnv
    = do let ModuleEnv moduleID _ exports (LexEnv lexmap)
                 = findModuleEnv_OrLose moduleID globalEnv
         export <- exports
         case export of         -- List Monad concats implicitly for us.
           HsEVar qn -> [fromHsk qn]
           HsEAbs qn -> [fromHsk qn]
           HsEThingAll qn 
             -> case Importer.LexEnv.lookup moduleID (fromHsk qn) globalEnv of
                  Just (Type _ constructorNs) 
                      -> constructorNs
                  etc -> error ("Internal error (computeExportedNames): " ++ show etc)
           HsEModuleContents m
             | fromHsk m == moduleID -> Map.keys lexmap -- export everything
             | otherwise             -> computeExportedNames (fromHsk m) globalEnv

isExported :: Identifier -> ModuleID -> GlobalE -> Bool
isExported identifier moduleID globalEnv
    = nameOf (lexInfoOf identifier) `elem` (computeExportedNames moduleID globalEnv)

-- module Imp1 (alpha) where 
--   alpha = 1
--   beta  = 2

-- module Imp2 (Thing(ThingA, ThingB)) where 
--   data Thing = ThingA | ThingB | ThingC deriving (Show)

-- module Imp3 (Stuff(..)) where 
--   data Stuff = StuffA | StuffB | StuffC deriving (Show)

-- module Foo (b) where
--
-- import Imp1
-- import qualified Imp2
-- import qualified Imp3 as Quux
-- 
-- a = "a"
-- b = "b"

-- lookup "Foo" "a"             => Just ...
-- lookup "Foo" "Foo.a"         => Just ...
-- lookup "Foo" "Foo.b"         => Just ...

-- lookup "Foo" "alpha"         => Just ...
-- lookup "Foo" "Imp1.alpha"    => Just ...
-- lookup "Foo" "Imp1.beta"     => Nothing

-- lookup "Foo" "ThingA"        => Nothing
-- lookup "Foo" "Imp2.ThingA"   => Just ...
-- lookup "Foo" "Imp2.ThingC"   => Nothing

-- lookup "Foo" "Quux.StuffA"   => Just ...
-- lookup "Foo" "Imp3.StuffA"   => Just ...
-- lookup "Foo" "Imp3.StuffC"   => Just ...
-- lookup "Foo" "Imp1.beta"     => Nothing

lookup :: ModuleID -> EnvName -> GlobalE -> Maybe Identifier
lookup currentModule qname globalEnv = lookup' currentModule qname globalEnv -- ambiguous occurence `lookup'
    where                                                                    -- between LexEnv and Prelude
      lookup' currentModule qname globalEnv                            
          = do currentModuleEnv <- findModuleEnv currentModule globalEnv
               case qname of
                 EnvQualName m n 
                     | m == currentModule  
                         -> lookup' m (EnvUnqualName n) globalEnv
                     | isImportedModule m currentModuleEnv
                         -> do identifier <- lookup' m (EnvUnqualName n) globalEnv
                               if isExported identifier m globalEnv then Just identifier
                                                                    else Nothing
                     | otherwise -> Nothing
                 EnvUnqualName n 
                     -> let (ModuleEnv _ imports _ (LexEnv lexmap)) 
                                       = currentModuleEnv
                            local_try  = Map.lookup n lexmap
                            tries      = map (\(HsImportDecl { importModule = m }) 
                                                  -> lookup' currentModule 
                                                             (EnvQualName (fromHsk m) n) 
                                                             globalEnv) 
                                          $ filter (not . importQualified) imports
                        in case catMaybes (local_try : tries) of
                             []   -> Nothing
                             [x]  -> Just x
                             x:xs -> error (Msg.identifier_collision_in_lookup 
                                               currentModule qname (x:xs))

-- lookup_isa :: Isa.Theory -> Isa.Name -> GlobalE -> Maybe IsaIdentifier
-- lookup_isa theory name globalEnv
--     = case lookup' theory name globalEnv of
--         Nothing  -> lookup' (Isa.Theory "Prelude") name globalEnv
--         Just foo -> Just foo
--     where lookup' theory (Isa.QName thy string) globalEnv
--               = if theory == thy then lookup' theory (Isa.Name string) globalEnv
--                                  else Nothing
--           lookup' theory name@(Isa.Name _) (IsaGlobalEnv globalmap)
--               = do (IsaTheoryEnv _ (IsaLexEnv lexmap)) <- Map.lookup theory globalmap
--                    Map.lookup name lexmap
