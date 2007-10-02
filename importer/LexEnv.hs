
module Importer.LexEnv where

import Maybe

import qualified Data.Map as Map
import Language.Haskell.Hsx

import qualified Importer.IsaSyntax as Isa
import Importer.Utilities.Hsx


data LexE = HsxLexEnv (Map.Map HsQName  HsxLexInfo)
          | IsaLexEnv (Map.Map Isa.Name IsaLexInfo)
  deriving (Show)

data HsxLexInfo = HsxVariable (Maybe HsType)
                | HsxFunction (Maybe HsType)
                | HsxInfixOp  (Maybe HsType) HsAssoc Int
                | HsxTypeAnnotation HsType
  deriving (Show)

data IsaLexInfo = IsaVariable | IsaFunction
 deriving (Show)

emptyLexEnv_Hsx = HsxLexEnv Map.empty

makeLexEnv_Hsx :: [(HsQName, HsxLexInfo)] -> LexE
makeLexEnv_Hsx initbindings
    = HsxLexEnv (Map.fromListWith mergeLexInfos initbindings)

mergeLexInfos (HsxVariable Nothing)    (HsxTypeAnnotation typ) = HsxVariable (Just typ)
mergeLexInfos (HsxFunction Nothing)    (HsxTypeAnnotation typ) = HsxFunction (Just typ)
mergeLexInfos (HsxInfixOp Nothing a p) (HsxTypeAnnotation typ) = HsxInfixOp  (Just typ) a p
mergeLexInfos (HsxTypeAnnotation typ) (HsxVariable Nothing)    = HsxVariable (Just typ)
mergeLexInfos (HsxTypeAnnotation typ) (HsxFunction Nothing)    = HsxFunction (Just typ)
mergeLexInfos (HsxTypeAnnotation typ) (HsxInfixOp Nothing a p) = HsxInfixOp  (Just typ) a p


data ModuleE = HsxModuleEnv Module [(Module, Maybe Module)] LexE
  deriving (Show)

emptyModuleEnv = HsxModuleEnv (Module "Main") [] emptyLexEnv_Hsx

makeModuleEnv :: HsModule -> ModuleE
makeModuleEnv (HsModule loc modul _exports imports topdecls)
    = HsxModuleEnv modul (map normalizeImport imports) 
        $ makeLexEnv_Hsx (concatMap extractLexInfos topdecls)
    where 
      extractLexInfos decl 
          = map (\name -> (name, case decl of
                                   HsPatBind _ _ _ _          -> HsxVariable Nothing
                                   HsFunBind _                -> HsxFunction Nothing
                                   HsInfixDecl _ assoc prio _ -> HsxInfixOp  Nothing assoc prio
                                   HsTypeSig _ _ typ          -> HsxTypeAnnotation typ))
            (fromJust $ namesFromHsDecl decl)

      normalizeImport (HsImportDecl { importModule=modul, importQualified=isQual, importAs=nickname })
          = case (isQual, nickname) of
              (True, Nothing)   -> (modul, Just modul)
              (True, Just nick) -> (modul, Just nick)
              (False, _)        -> (modul, Nothing)

findModule :: Module -> [(Module, Maybe Module)] -> Maybe Module
findModule m ms
    = let (names, nicknames) = unzip ms 
      in case filter (== m) (catMaybes nicknames) of
        [name] -> Just name
        _ -> Nothing

unqualifiedModules :: [(Module, Maybe Module)] -> [Module]
unqualifiedModules ms
    = map fst (filter (isNothing . snd) ms)

data GlobalE = HsxGlobalEnv (Map.Map Module ModuleE)
  deriving (Show)

makeGlobalEnv_Hsx :: [HsModule] -> GlobalE
makeGlobalEnv_Hsx ms 
    = HsxGlobalEnv (Map.fromListWith failDups 
                              $ map (\m@(HsModule _ modul _ _ _) -> (modul, makeModuleEnv m)) ms)
    where failDups a b
              = error ("Duplicate modules: " ++ show a ++ ", " ++ show b)


lookup :: Module -> HsQName -> GlobalE -> Maybe HsxLexInfo
lookup currentModule qname globalenv@(HsxGlobalEnv globalmap)
    = do (HsxModuleEnv _ importedMs (HsxLexEnv lexmap)) <- Map.lookup currentModule globalmap
         case qname of
           Qual m n -> do m' <- findModule m importedMs
                          Importer.LexEnv.lookup m' (UnQual n) globalenv
           n -> Map.lookup n lexmap


emptyGlobalEnv = HsxGlobalEnv (Map.empty)