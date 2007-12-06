
module Importer.LexEnv where

import Maybe

import qualified Data.Map as Map
import Language.Haskell.Hsx

import qualified Importer.Msg as Msg
import qualified Importer.IsaSyntax as Isa

import Importer.Utilities.Hsx
import Importer.Utilities.Misc


data LexE = HsxLexEnv (Map.Map HsQName HsxIdentifier)
  deriving (Show)


data HsxLexInfo = HsxLexInfo { 
                              identifier :: HsQName,
                              exported   :: Bool,
                              typeOf     :: Maybe HsType,
                              moduleOf   :: Module
                             }
  deriving (Show)

data HsxIdentifier = HsxVariable HsxLexInfo
                   | HsxFunction HsxLexInfo
                   | HsxInfixOp  HsxLexInfo HsAssoc Int
                   | HsxData     HsxLexInfo [HsQName] -- data constructors
                   | HsxTypeAnnotation HsType
  deriving (Show)

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



emptyLexEnv_Hsx = HsxLexEnv Map.empty

makeLexEnv_Hsx :: [(HsQName, HsxIdentifier)] -> LexE
makeLexEnv_Hsx initbindings
    = HsxLexEnv (Map.fromListWith mergeLexInfos initbindings)


mergeLexInfos (HsxVariable lexinfo@(HsxLexInfo { typeOf=Nothing })) (HsxTypeAnnotation typ) 
    = HsxVariable (lexinfo { typeOf = Just typ })

mergeLexInfos (HsxFunction lexinfo@(HsxLexInfo { typeOf=Nothing })) (HsxTypeAnnotation typ) 
    = HsxFunction (lexinfo { typeOf = Just typ })

mergeLexInfos (HsxInfixOp lexinfo@(HsxLexInfo { typeOf=Nothing }) a p) (HsxTypeAnnotation typ) 
    = HsxInfixOp (lexinfo { typeOf = Just typ }) a p

mergeLexInfos (HsxTypeAnnotation typ) (HsxVariable lexinfo@(HsxLexInfo { typeOf=Nothing })) 
    = HsxVariable (lexinfo { typeOf = Just typ })

mergeLexInfos (HsxTypeAnnotation typ) (HsxFunction lexinfo@(HsxLexInfo { typeOf=Nothing })) 
    = HsxFunction (lexinfo { typeOf = Just typ })

mergeLexInfos (HsxTypeAnnotation typ) (HsxInfixOp lexinfo@(HsxLexInfo { typeOf=Nothing }) a p) 
    = HsxInfixOp (lexinfo { typeOf = Just typ }) a p

isExported :: HsxIdentifier -> Bool
isExported (HsxVariable lexinfo)     = exported lexinfo
isExported (HsxFunction lexinfo)     = exported lexinfo
isExported (HsxInfixOp  lexinfo _ _) = exported lexinfo
isExported (HsxTypeAnnotation _)     = False


data ModuleE = HsxModuleEnv Module [HsxImportInfo] LexE
  deriving (Show)

data HsxImportInfo = HsxImportInfo (Module, Maybe Module) -- (importedModule, qualifiedName)
  deriving (Show)

isQualifiedImport, isUnqualifiedImport :: HsxImportInfo -> Bool
isQualifiedImport (HsxImportInfo (_, Just _)) = True
isQualifiedImport _                           = False
isUnqualifiedImport = not . isQualifiedImport


emptyModuleEnv = HsxModuleEnv (Module "Main") [] emptyLexEnv_Hsx

makeModuleEnv :: HsModule -> ModuleE
makeModuleEnv (HsModule loc modul exports imports topdecls)
    = let lexenv   = makeLexEnv_Hsx (concatMap (extractLexInfos modul) topdecls)
          lexenv'  = exportIdentifiers exports lexenv
          imports' = map normalizeImport imports
      in HsxModuleEnv modul imports' lexenv'

extractLexInfos :: Module -> HsDecl -> [(HsQName, HsxIdentifier)]
extractLexInfos modul decl 
    = map (\name -> let defaultLexInfo = HsxLexInfo { identifier=name, exported=False, 
                                                      typeOf=Nothing, moduleOf=modul}
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

normalizeImport :: HsImportDecl -> HsxImportInfo
normalizeImport (HsImportDecl { importModule=modul, importQualified=isQual, importAs=nickname })
    = case (isQual, nickname) of
        (True, Nothing)   -> HsxImportInfo (modul, Just modul)
        (True, Just nick) -> HsxImportInfo (modul, Just nick)
        (False, _)        -> HsxImportInfo (modul, Nothing)

exportIdentifiers :: Maybe [HsExportSpec] -> LexE -> LexE
exportIdentifiers Nothing lexenv = lexenv
exportIdentifiers (Just exportspecs) lexenv
    = foldl export lexenv exportspecs
      where export (HsxLexEnv lexmap) (HsEVar qname) 
                = HsxLexEnv (Map.update (updateHsxIdentifier [Var, Fun, Op, Ann]) qname lexmap)
            export (HsxLexEnv lexmap) (HsEAbs qname)
                = HsxLexEnv (Map.update (updateHsxIdentifier [Data]) qname lexmap)
            export env etc = error ("Not supported: " ++ show etc)

data AllowedIdentifier = Var | Fun | Op | Ann | Data
  deriving (Show)

updateHsxIdentifier :: [AllowedIdentifier] -> HsxIdentifier -> Maybe HsxIdentifier

updateHsxIdentifier allowedIdents hsxidentifier
    = assert (isAllowed allowedIdents hsxidentifier)
        $ update hsxidentifier
      where 
        update (HsxVariable lexinfo)     = Just $ HsxVariable (lexinfo { exported = True })
        update (HsxFunction lexinfo)     = Just $ HsxFunction (lexinfo { exported = True })
        update (HsxInfixOp  lexinfo a p) = Just $ HsxInfixOp  (lexinfo { exported = True }) a p
        update (HsxTypeAnnotation _)     = Nothing

isAllowed :: [AllowedIdentifier] -> HsxIdentifier -> Bool
isAllowed allowedIdents hsxidentifier
    = or (map ($ hsxidentifier) (map toPredicate allowedIdents))
    where toPredicate Var  = isHsxVariable
          toPredicate Fun  = isHsxFunction
          toPredicate Op   = isHsxInfixOp
          toPredicate Ann  = isHsxTypeAnnotation
          toPredicate Data = isHsxData

findModule :: Module -> [HsxImportInfo] -> Maybe Module
findModule modul imports
    = let ms = map (\i@(HsxImportInfo (m,n)) 
                         -> if isUnqualifiedImport i then m else fromJust n)
                   imports
      in case filter (== modul) ms of
           [name] -> Just name
           _ -> Nothing



data GlobalE = HsxGlobalEnv (Map.Map Module ModuleE)
  deriving (Show)

emptyGlobalEnv = HsxGlobalEnv (Map.empty)

makeGlobalEnv_Hsx :: [HsModule] -> GlobalE
makeGlobalEnv_Hsx ms 
    = HsxGlobalEnv (Map.fromListWith failDups 
                              $ map (\m@(HsModule _ modul _ _ _) -> (modul, makeModuleEnv m)) ms)
    where failDups a b
              = error ("Duplicate modules: " ++ show a ++ ", " ++ show b)


lookup :: Module -> HsQName -> GlobalE -> Maybe HsxIdentifier
lookup currentModule qname globalenv = lookup' currentModule qname globalenv
    where lookup' currentModule qname globalenv@(HsxGlobalEnv globalmap)
              = do (HsxModuleEnv _ importedMs (HsxLexEnv lexmap)) <- Map.lookup currentModule globalmap
                   case qname of
                     Qual m n -> do m' <- findModule m importedMs
                                    hsxidentifier <- lookup' m' (UnQual n) globalenv
                                    if isExported hsxidentifier then Just hsxidentifier
                                                                else Nothing
                     UnQual n -> let first_try = Map.lookup (UnQual n) lexmap
                                     tries     = map (\(HsxImportInfo (m, _)) 
                                                          -> lookup' currentModule (Qual m n) globalenv) 
                                                     (filter isUnqualifiedImport importedMs)
                          in case catMaybes (first_try : tries) of
                               []   -> Nothing
                               [x]  -> Just x
                               x:xs -> error (Msg.ambiguous_occurences currentModule qname (x:xs))



