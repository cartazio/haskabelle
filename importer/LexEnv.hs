
module Importer.LexEnv where

import Maybe

import qualified Data.Map as Map
import Language.Haskell.Hsx

import qualified Importer.IsaSyntax as Isa
import Importer.Utilities.Hsx


data LexEnv = HsxLexEnv (Map.Map HsQName HsxLexInfo)
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

makeLexEnv_Hsx :: [(HsQName, HsxLexInfo)] -> LexEnv
makeLexEnv_Hsx initbindings
    = HsxLexEnv (Map.fromListWith mergeLexInfos initbindings)

makeModuleEnv_Hsx :: HsModule -> LexEnv
makeModuleEnv_Hsx (HsModule loc modul _exports _imports topdecls)
    = makeLexEnv_Hsx (concatMap extractLexInfos topdecls)
    where 
      extractLexInfos decl 
          = map (\name -> (name,
                           case decl of
                             HsPatBind _ _ _ _          -> HsxVariable Nothing
                             HsFunBind _                -> HsxFunction Nothing
                             HsInfixDecl _ assoc prio _ -> HsxInfixOp  Nothing assoc prio
                             HsTypeSig _ _ typ          -> HsxTypeAnnotation typ))
            (fromJust $ namesFromHsDecl decl)

mergeLexInfos (HsxVariable Nothing)    (HsxTypeAnnotation typ) = HsxVariable (Just typ)
mergeLexInfos (HsxFunction Nothing)    (HsxTypeAnnotation typ) = HsxFunction (Just typ)
mergeLexInfos (HsxInfixOp Nothing a p) (HsxTypeAnnotation typ) = HsxInfixOp  (Just typ) a p
mergeLexInfos (HsxTypeAnnotation typ) (HsxVariable Nothing)    = HsxVariable (Just typ)
mergeLexInfos (HsxTypeAnnotation typ) (HsxFunction Nothing)    = HsxFunction (Just typ)
mergeLexInfos (HsxTypeAnnotation typ) (HsxInfixOp Nothing a p) = HsxInfixOp  (Just typ) a p


lookup :: HsQName -> LexEnv -> Maybe HsxLexInfo
lookup k (HsxLexEnv map) = Map.lookup k map


data GlobalLexEnv = HsxGlobalLexEnv (Map.Map Module LexEnv)
  deriving (Show)

makeGlobalEnv_Hsx :: [HsModule] -> GlobalLexEnv
makeGlobalEnv_Hsx ms 
    = HsxGlobalLexEnv (Map.fromListWith failDups 
                              $ map (\m@(HsModule _ modul _ _ _) -> (modul, makeModuleEnv_Hsx m)) ms)
    where failDups a b
              = error ("Duplicate modules: " ++ show a ++ ", " ++ show b)


lookupGlobally :: Module -> HsQName -> GlobalLexEnv -> Maybe HsxLexInfo
lookupGlobally m n (HsxGlobalLexEnv globalmap)
    = Map.lookup m globalmap >>= (\(HsxLexEnv lexmap) -> Map.lookup n lexmap)


emptyGlobalLexEnv = HsxGlobalLexEnv Map.empty