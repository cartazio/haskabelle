{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen
-}

module Importer.LexEnv where

import Maybe
import List (nub, partition)

import Control.Monad.State
import qualified Data.Map as Map

import Language.Haskell.Exts

import qualified Importer.Msg as Msg
import qualified Importer.IsaSyntax as Isa

import Importer.Utilities.Hsk
import Importer.Utilities.Misc

import Importer.Adapt.Common (primitive_tycon_table, primitive_datacon_table)

--
-- Identifier information
--

type ModuleID     = String
type IdentifierID = String

data EnvType = EnvTyVar EnvName
             | EnvTyCon EnvName [EnvType]
             | EnvTyFun EnvType EnvType
             | EnvTyTuple [EnvType]
             | EnvTyScheme [(EnvName, [EnvName])] EnvType
             | EnvTyNone
  deriving (Eq, Ord, Show)

data EnvAssoc = EnvAssocRight | EnvAssocLeft | EnvAssocNone
  deriving (Eq, Ord, Show)

data EnvName = EnvQualName ModuleID IdentifierID
             | EnvUnqualName IdentifierID
  deriving (Eq, Ord, Show)

isQualified :: EnvName -> Bool
isQualified (EnvQualName _ _) = True
isQualified (EnvUnqualName _) = False

qualifyEnvName :: ModuleID -> EnvName -> EnvName
qualifyEnvName mID qn@(EnvQualName mID' _) = qn
qualifyEnvName mID (EnvUnqualName n)       = EnvQualName mID n

unqualifyEnvName :: ModuleID -> EnvName -> EnvName
unqualifyEnvName mID (EnvQualName mID' id) = assert (mID == mID') $ EnvUnqualName id
unqualifyEnvName mID n@(EnvUnqualName _)   = n

substituteTyVars :: [(EnvType, EnvType)] -> EnvType -> EnvType
substituteTyVars alist typ
    = let lookup' = Prelude.lookup in
      case typ of
        t@(EnvTyVar _)     -> case lookup' t alist of { Just t' -> t'; Nothing -> t }
        t@(EnvTyCon cN ts) -> case lookup' t alist of
                                Just t' -> t'
                                Nothing -> EnvTyCon cN (map (substituteTyVars alist) ts)
        t@(EnvTyFun t1 t2) -> case lookup' t alist of
                                Just t' -> t'
                                Nothing -> EnvTyFun (substituteTyVars alist t1)
                                                    (substituteTyVars alist t2)
        t@(EnvTyTuple ts)  -> case lookup' t alist of
                                Just t' -> t'
                                Nothing -> EnvTyTuple (map (substituteTyVars alist) ts)
        t@(EnvTyNone)      -> case lookup' t alist of { Just t' -> t'; Nothing -> t }


data LexInfo = LexInfo { 
                        nameOf   :: IdentifierID,
                        typeOf   :: EnvType,
                        moduleOf :: ModuleID
                       }
  deriving (Eq, Ord, Show)

data ClassInfo = ClassInfo {
                            superclassesOf :: [EnvName],
                            methodsOf      :: [Identifier],
                            classVarOf     :: EnvName
                           }
  deriving (Eq, Ord, Show)

data Constant = Variable LexInfo
              | Function LexInfo
              | UnaryOp  LexInfo Int
              | InfixOp  LexInfo EnvAssoc Int
              | Class    LexInfo ClassInfo
              | TypeAnnotation LexInfo 
  deriving (Eq, Ord, Show)

data Type = Data LexInfo [Constant] -- Type lexinfo [constructors]
  deriving (Eq, Ord, Show)

data Identifier = Constant Constant
                | Type Type
  deriving (Eq, Ord, Show)

makeLexInfo :: ModuleID -> IdentifierID -> EnvType -> LexInfo
makeLexInfo moduleID identifierID t
    = let mID = (if moduleID == "" then prelude else moduleID)
      in 
        LexInfo { nameOf   = identifierID,
                  typeOf   = t,
                  moduleOf = mID }

makeClassInfo :: [EnvName] -> [Identifier] -> EnvName -> ClassInfo
makeClassInfo superclasses methods classVarName
    = assert (all isTypeAnnotation methods)
        $ ClassInfo { superclassesOf = superclasses,
                      methodsOf      = methods,
                      classVarOf     = classVarName }

isVariable, isFunction, isUnaryOp, isInfixOp  :: Identifier -> Bool
isTypeAnnotation, isClass, isData :: Identifier -> Bool

isVariable (Constant (Variable _))   = True
isVariable _                         = False

isFunction (Constant (Function _))   = True
isFunction _                         = False

isUnaryOp (Constant (UnaryOp _ _))   = True
isUnaryOp _                          = False

isInfixOp (Constant (InfixOp _ _ _)) = True
isInfixOp _                          = False

isTypeAnnotation (Constant (TypeAnnotation _)) = True
isTypeAnnotation _                             = False

isClass (Constant (Class _ _))       = True
isClass _                            = False

isData (Type (Data _ _)) = True
isData _                 = False


lexInfoOf :: Identifier -> LexInfo
lexInfoOf identifier
    = case identifier of
        Constant c -> lexInfoOf_con c
        Type t     -> lexInfoOf_typ t
    where
      lexInfoOf_con (Variable i)       = i
      lexInfoOf_con (Function i)       = i
      lexInfoOf_con (UnaryOp i _)      = i
      lexInfoOf_con (InfixOp i _ _)    = i
      lexInfoOf_con (Class i _)        = i
      lexInfoOf_con (TypeAnnotation i) = i

      lexInfoOf_typ (Data i _)         = i

updateIdentifier :: Identifier -> LexInfo -> Identifier
updateIdentifier identifier lexinfo
    = case identifier of
        Constant c -> Constant (updateConstant c lexinfo)
        Type t     -> Type     (updateType t lexinfo)
    where 
      updateConstant (Variable _) lexinfo        = Variable lexinfo
      updateConstant (Function _) lexinfo        = Function lexinfo
      updateConstant (UnaryOp _ p) lexinfo       = UnaryOp lexinfo p
      updateConstant (InfixOp _ a p) lexinfo     = InfixOp lexinfo a p
      updateConstant (TypeAnnotation _) lexinfo  = TypeAnnotation lexinfo
      updateConstant (Class _ classinfo) lexinfo = Class lexinfo classinfo

      updateType (Data _ conNs) lexinfo = Data lexinfo conNs

identifier2name :: Identifier -> EnvName
identifier2name identifier
    = let lexinfo  = lexInfoOf identifier
          name     = nameOf lexinfo
          modul    = moduleOf lexinfo
      in assert (modul /= "") $ EnvQualName modul name

constant2name :: Constant -> EnvName
type2name     :: Type     -> EnvName
constant2name c = identifier2name (Constant c)
type2name t     = identifier2name (Type t)

splitIdentifiers :: [Identifier] -> ([Constant], [Type])
splitIdentifiers ids
    = let (c_ids, t_ids) 
              = partition (\i -> case i of {Constant _ -> True; _ -> False}) ids
      in 
        ([ c | Constant c <- c_ids ], [ t | Type t <- t_ids ])



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
    
    toHsk junk = error ("toHsk ConstantID -> HsName: " ++ show junk)

instance Hsk2Env HsName IdentifierID where
    fromHsk (HsIdent s)  = s
    fromHsk (HsSymbol s) = s
    toHsk id             = string2HsName id


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

    fromHsk (HsTyForall _ [] typ)  = fromHsk typ
    fromHsk (HsTyForall _ ctx typ) = EnvTyScheme (frobContext ctx) (fromHsk typ)
        where frobContext [] = []
              frobContext (HsClassA classqN tys : rest_ctx)
                  = assert (all isTyVar tys) $
                    groupAlist [ (fromHsk tyvarN, fromHsk classqN) | HsTyVar tyvarN <- tys ]
                    ++ frobContext rest_ctx
              isTyVar (HsTyVar _) = True
              isTyVar _           = False

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

    fromHsk junk = error ("HsType -> EnvType: Fall Through: " ++ prettyShow' "thing" junk)

    toHsk (EnvTyVar n)          = HsTyVar (toHsk n)
    toHsk (EnvTyTuple types)    = HsTyTuple Boxed (map toHsk types)
    toHsk (EnvTyFun t1 t2)      = HsTyFun (toHsk t1) (toHsk t2)
    toHsk (EnvTyCon qn [])      = HsTyCon (toHsk qn)
    toHsk (EnvTyCon qn tyvars)
        = let tycon'            = toHsk (EnvTyCon qn [])
              tyvar':tyvars'    = map toHsk tyvars
          in foldl HsTyApp (HsTyApp tycon' tyvar') tyvars'
    toHsk (EnvTyScheme alist t) = HsTyForall Nothing ctx (toHsk t)
        where
          revalist = groupAlist 
                       $ concat [ map (flip (,) tyvarN) classNs | (tyvarN, classNs) <- alist ]
          ctx      = [ HsClassA (toHsk classN) (map (HsTyVar . toHsk) tyvarNs) 
                           | (classN, tyvarNs) <- revalist ]

    toHsk junk = error ("EnvType -> HsType: Fall Through: " ++ prettyShow' "thing" junk)

instance Hsk2Env HsExportSpec EnvExport where
    fromHsk (HsEVar qname)        = EnvExportVar   (fromHsk qname)
    fromHsk (HsEAbs qname)        = EnvExportAbstr (fromHsk qname)
    fromHsk (HsEThingAll qname)   = EnvExportAll   (fromHsk qname)
    fromHsk (HsEModuleContents m) = EnvExportMod   (fromHsk m)
    fromHsk etc = error ("Not supported yet: " ++ show etc)

instance Hsk2Env HsImportDecl EnvImport where
    fromHsk (HsImportDecl { importModule=m,
                            importQualified=qual,
                            importAs=nick,
                            importSpecs=Nothing })
        = EnvImport (fromHsk m) qual 
                    (if isNothing nick then Nothing 
                                       else Just (fromHsk (fromJust nick)))
    fromHsk etc = error ("Not supported yet: " ++ show etc)


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
    fromIsa (Isa.TyNone)          = EnvTyNone
    fromIsa (Isa.TyVar n)         = EnvTyVar (fromIsa n)
    fromIsa (Isa.TyTuple types)   = EnvTyTuple (map fromIsa types)
    fromIsa (Isa.TyFun t1 t2)     = EnvTyFun (fromIsa t1) (fromIsa t2)
    fromIsa (Isa.TyCon qn tyvars) = EnvTyCon (fromIsa qn) (map fromIsa tyvars)
    fromIsa (Isa.TyScheme ctx t)  = EnvTyScheme ctx' (fromIsa t)
        where ctx' = [ (fromIsa vN, map fromIsa cNs) | (vN, cNs) <- ctx ]
    
    toIsa (EnvTyNone)             = Isa.TyNone
    toIsa (EnvTyVar n)            = Isa.TyVar (toIsa n)
    toIsa (EnvTyTuple types)      = Isa.TyTuple (map toIsa types)
    toIsa (EnvTyFun t1 t2)        = Isa.TyFun (toIsa t1) (toIsa t2)
    toIsa (EnvTyCon qn tyvars)    = Isa.TyCon (toIsa qn) (map toIsa tyvars)
    toIsa (EnvTyScheme ctx t)     = Isa.TyScheme ctx' (toIsa t)
        where ctx' = [ (toIsa vN, map toIsa cNs) | (vN, cNs) <- ctx ]

data ConKind = DataCon | TypeCon deriving Show

translateSpecialCon :: ConKind -> HsSpecialCon -> HsQName
translateSpecialCon DataCon con = fromJust $ Prelude.lookup con primitive_datacon_table
translateSpecialCon TypeCon con = fromJust $ Prelude.lookup con primitive_tycon_table

retranslateSpecialCon :: ConKind -> HsQName -> Maybe HsSpecialCon
retranslateSpecialCon DataCon qname 
    = Prelude.lookup qname [ (y,x) | (x,y) <- primitive_datacon_table ]
retranslateSpecialCon TypeCon qname 
    = Prelude.lookup qname [ (y,x) | (x,y) <- primitive_tycon_table ]



--
-- LexEnv
--

data LexE = LexEnv (Map.Map IdentifierID Constant) (Map.Map IdentifierID Type)
  deriving (Show)

makeLexEnv :: [Identifier] -> LexE
makeLexEnv identifiers
    = let (constants, types) = splitIdentifiers identifiers
          constant_bindings  = zip (map (nameOf . lexInfoOf . Constant) constants) constants
          type_bindings      = zip (map (nameOf . lexInfoOf . Type) types) types
          constants_map      = Map.fromListWith mergeConstants_OrFail constant_bindings
          types_map          = Map.fromListWith mergeTypes_OrFail type_bindings
      in 
        LexEnv constants_map types_map

mergeConstants_OrFail :: Constant -> Constant -> Constant
mergeConstants_OrFail c1 c2
    = case mergeConstants c1 c2 of
        Just result -> result
        Nothing     -> error (Msg.merge_collision "mergeConstants_OrFail" c1 c2)

mergeTypes_OrFail :: Type -> Type -> Type
mergeTypes_OrFail t1 t2
    | t1 == t2  = t1
    | otherwise = error (Msg.merge_collision "mergeTypes_OrFail" t1 t2)

mergeConstants :: Constant -> Constant -> Maybe Constant
mergeConstants c1 c2
    = assert (constant2name c1 == constant2name c2)
      $ let merge c1 c2 
                = case (c1, c2) of
                    -- Update saved types from explicit type annotations:
                    (Variable i,            TypeAnnotation ann)   -> Just $ Variable (update i ann)
                    (Function i,            TypeAnnotation ann)   -> Just $ Function (update i ann)
                    (UnaryOp  i p,          TypeAnnotation ann)   -> Just $ UnaryOp  (update i ann) p
                    (InfixOp  i a p,        TypeAnnotation ann)   -> Just $ InfixOp  (update i ann) a p
                    (_,_) -> Nothing
        in case merge c1 c2 of { Just c' -> Just c'; Nothing -> merge c2 c1 }
    where 
      update lexinfo@(LexInfo { typeOf = EnvTyNone }) (LexInfo { typeOf = typ })
          = lexinfo { typeOf = typ }
      update lexinfo typ    -- Cannot merge + internal inconsistency.
          = error ("Internal Error (mergeLexInfo): Type collision between `" ++ show lexinfo ++ "'" 
                   ++ " and `" ++ show typ ++ "'.")


mergeLexEnvs (LexEnv cmap1 tmap1) (LexEnv cmap2 tmap2)
    = LexEnv (Map.unionWith constant_merger cmap1 cmap2)
             (Map.union tmap1 tmap2)
    where 
      constant_merger c1 c2 = case mergeConstants c1 c2 of
                                Nothing  -> c2  -- favorize second argument.
                                Just res -> res

--
-- ModuleEnv 
--

data ModuleE = ModuleEnv ModuleID [EnvImport] [EnvExport] LexE
  deriving (Show)


data EnvImport = EnvImport ModuleID Bool (Maybe ModuleID)
  deriving (Show, Eq)

defaultImports = [EnvImport prelude False Nothing]

isQualifiedImport :: EnvImport -> Bool
isQualifiedImport (EnvImport _ isQual _) = isQual

data EnvExport = EnvExportVar   EnvName
               | EnvExportAbstr EnvName
               | EnvExportAll   EnvName
               | EnvExportMod   ModuleID
  deriving (Show, Eq)
                 

makeModuleEnv :: [EnvImport] -> (Identifier -> Bool) -> [Identifier] -> ModuleE
makeModuleEnv imports shall_export_p identifiers
    = let m = moduleOf (lexInfoOf (head identifiers))
      in assert (all (== m) $ map (moduleOf . lexInfoOf) (tail identifiers))
           $ ModuleEnv m imports exports (makeLexEnv identifiers)
    where
      exports = map export (filter shall_export_p identifiers)
      export id@(Type (Data _ _)) = EnvExportAll (identifier2name id) 
      export id                   = EnvExportVar (identifier2name id)

makeModuleEnv_fromHsModule :: HsModule -> ModuleE
makeModuleEnv_fromHsModule (HsModule loc modul exports imports topdecls)
    = let lexenv   = makeLexEnv (concatMap (computeConstantMappings modul) topdecls)
          imports' = map fromHsk imports ++ defaultImports
          exports' = if isNothing exports then [EnvExportMod (fromHsk modul)] 
                                          else map fromHsk (fromJust exports)
      in ModuleEnv (fromHsk modul) imports' exports' lexenv

computeConstantMappings :: Module -> HsDecl -> [Identifier]
computeConstantMappings modul decl 
    = do name <- fromJust (namesFromHsDecl decl)
         let nameID         = fromHsk name
         let moduleID       = fromHsk modul
         let defaultLexInfo = LexInfo { nameOf=nameID, typeOf=EnvTyNone, moduleOf=moduleID}
         let con c          = Constant c
         let typ t          = Type t
         case decl of
           HsPatBind _ _ _ _           -> [con (Variable defaultLexInfo)]
           HsFunBind _                 -> [con (Function defaultLexInfo)]
           HsInfixDecl _ a p _         -> [con (InfixOp  defaultLexInfo (fromHsk a) p)]
           HsTypeSig _ _ typ           -> [con (TypeAnnotation (defaultLexInfo { typeOf = fromHsk typ}))]
           HsClassDecl _ ctx _ ns _ ds -> let sups      = map fromHsk (extractSuperclassNs ctx)
                                              typesigs  = extractMethodSigs ds
                                              m         = modul
                                              methods   = concatMap (computeConstantMappings m) typesigs
                                              -- If length ns > 1, we will die later in Convert.hs anyway.
                                              classInfo = makeClassInfo sups methods (fromHsk (head ns))
                                          in [con (Class defaultLexInfo classInfo)]
           HsInstDecl  _ _ _ _ _       -> []
           HsDataDecl _ _ _ conN tyvarNs condecls _
               -> assert (fromHsk conN == nameID) $
                  let tycon = mkTyCon (fromHsk name) tyvarNs
                      constructors  = map (mkDataCon tycon) condecls
                      constructors' = map Constant constructors
                  in [typ (Data (defaultLexInfo { typeOf = tycon }) constructors)] ++ constructors'
               where 
                 mkTyCon name tyvarNs 
                   = EnvTyCon name $ map (EnvTyVar . fromHsk) tyvarNs
                 mkDataCon tycon (HsQualConDecl _ _ _ (HsConDecl n args))
                   = let typ = foldr EnvTyFun tycon (map (\(HsUnBangedTy t) -> fromHsk t) args)
                     in Function (makeLexInfo moduleID (fromHsk n) typ)
                 mkDataCon nameID etc
                   = error ("mkDataCon: " ++ show nameID ++ "; " ++ show etc)
      

mergeModuleEnvs (ModuleEnv m1 is1 es1 lex1) (ModuleEnv m2 is2 es2 lex2)
    = assert (m1 == m2)
        $ ModuleEnv m1 (nub $ is1 ++ is2) (nub $ es1 ++ es2) (mergeLexEnvs lex1 lex2)

importedModuleIDs :: ModuleE -> [ModuleID]
importedModuleIDs (ModuleEnv _ imports _ _)
    = map (\(imp@(EnvImport m isQualified nickname ))
               -> case (isQualified, isJust nickname) of
                    -- Notice: Module names can _always_ be explicitly qualified.
                    (False, False) -> m 
                    (True,  False) -> m
                    (True,  True)  -> m
                    (False, True)  
                        -> error ("<importedModules> Internal Error: bogus import:" ++ show imp))
          imports

-- isImportedModule_aux :: ModuleID -> [EnvImport] -> Bool
-- isImportedModule_aux moduleID imports
--     = case filter (== moduleID) (importedModules imports) of
--         []     -> False
--         [name] -> True
--         etc    -> error ("Internal error (isImportedModule): Fall through. [" ++ show etc ++ "]")

isImportedModule :: ModuleID -> ModuleE -> Bool
isImportedModule moduleID moduleEnv
    = -- trace ("isImportedModule " ++ moduleID ++ " " ++ prettyShow' "moduleEnv" moduleEnv) $
      case filter (== moduleID) (importedModuleIDs moduleEnv) of
        []     -> False
        [name] -> True
        etc    -> error ("Internal error (isImportedModule): Fall through. [" ++ show etc ++ "]")



--
-- GlobalEnv
--

data GlobalE = GlobalEnv (Map.Map ModuleID ModuleE)
  deriving (Show)

prelude = "Prelude"

initialGlobalEnv = GlobalEnv 
                     $ Map.singleton prelude 
                           (ModuleEnv prelude [] [] (LexEnv (Map.empty) (Map.empty)))

makeGlobalEnv :: (ModuleID -> [EnvImport]) -> (Identifier -> Bool) -> [Identifier] -> GlobalE
makeGlobalEnv compute_imports shall_export_p identifiers
     = GlobalEnv
         $ Map.fromListWith failDups
               (do (moduleID, ids) <- groupIdentifiers identifiers
                   return (moduleID, makeModuleEnv (compute_imports moduleID) shall_export_p ids))
    where failDups a b = error ("Duplicate modules: " ++ show a ++ ", " ++ show b)

groupIdentifiers :: [Identifier] -> [(ModuleID, [Identifier])]
groupIdentifiers identifiers
    = groupAlist [ (moduleOf (lexInfoOf id), id) | id <- identifiers ]

makeGlobalEnv_fromHsModules :: [HsModule] -> GlobalE
makeGlobalEnv_fromHsModules ms 
    = GlobalEnv 
        $ Map.fromListWith failDups 
              [ (fromHsk modul, makeModuleEnv_fromHsModule m) 
                    | m@(HsModule _ modul _ _ _) <- ms ]
    where failDups a b = error ("Duplicate modules: " ++ show a ++ ", " ++ show b)

-- Left-prioritized union of Global Environments.
--
unionGlobalEnvs :: GlobalE -> GlobalE -> GlobalE
unionGlobalEnvs (GlobalEnv map1) (GlobalEnv map2)
    = GlobalEnv 
        $ Map.unionWithKey
              (\m moduleEnv1 moduleEnv2
                   -> let env1 = if Map.member m map1 then moduleEnv1 else moduleEnv2
                          env2 = if Map.member m map1 then moduleEnv2 else moduleEnv1
                      in -- `env1' contains ModuleE that belongs to `map1'.
                         mergeModuleEnvs env1 env2)
              map1 map2

findModuleEnv :: ModuleID -> GlobalE -> Maybe ModuleE
findModuleEnv mID (GlobalEnv globalmap)
    = Map.lookup mID globalmap

findModuleEnv_OrLose m globalEnv
    = case findModuleEnv m globalEnv of
        Just env -> env
        Nothing  -> error ("Couldn't find module `" ++ show m ++ "'.")
          
computeExportedNames :: ModuleID -> GlobalE -> [IdentifierID]
computeExportedNames moduleID globalEnv
    = do let ModuleEnv moduleID' _ exports (LexEnv constants_map types_map)
                 = findModuleEnv_OrLose moduleID globalEnv
         assert (moduleID == moduleID') $ return ()
         export <- exports   -- List Monad concats implicitly for us.
         case export of         
           EnvExportVar   qn -> [idOf (unqualifyEnvName moduleID qn)]
           EnvExportAbstr qn -> [idOf (unqualifyEnvName moduleID qn)]
           EnvExportAll qn 
             -> case Importer.LexEnv.lookupType moduleID qn globalEnv of
                  Just t@(Type (Data _ constructors))
                      -> let id_of i = nameOf (lexInfoOf i)
                         in id_of t : map (id_of . Constant) constructors
                  etc -> error ("Internal error (computeExportedNames): " ++ show etc)
           EnvExportMod m
             | m == moduleID -> Map.keys constants_map ++ Map.keys types_map -- export everything
             | otherwise     -> computeExportedNames m globalEnv
    where idOf :: EnvName -> IdentifierID
          idOf (EnvUnqualName id) = id

isExported :: Identifier -> ModuleID -> GlobalE -> Bool
isExported identifier moduleID globalEnv
    = nameOf (lexInfoOf identifier) `elem` (computeExportedNames moduleID globalEnv)

-- If the given ModuleID is a mere nickname of the ModuleE,
-- return the actual name.
resolveModuleID :: ModuleID -> ModuleE -> ModuleID
resolveModuleID moduleID (ModuleEnv _ imps _ _)
    = fromMaybe moduleID (lookfor moduleID imps)
    where 
      lookfor _ [] = Nothing
      lookfor mID (EnvImport mID' _ nick:imports)
              = case nick of
                  Just nickID | mID == nickID -> Just mID'
                  _ -> lookfor mID imports
         
         

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

lookup :: ModuleID -> EnvName -> GlobalE -> (Maybe Constant, Maybe Type)
lookup currentModule qname globalEnv 
    = case lookup' currentModule qname globalEnv of
        Nothing  -> (Nothing, Nothing)
        Just ids -> let (cs, ts) = splitIdentifiers ids in (listToMaybe cs, listToMaybe ts)
    where
      lookup' :: ModuleID -> EnvName -> GlobalE -> Maybe [Identifier]
      lookup' currentModule qname globalEnv                            
          = do currentModuleEnv <- findModuleEnv currentModule globalEnv
               case qname of
                 EnvQualName m n 
                     | m == currentModule  
                         -> lookup' m (EnvUnqualName n) globalEnv
                     | isImportedModule (resolveModuleID m currentModuleEnv) currentModuleEnv
                         -> do identifiers <- lookup' m (EnvUnqualName n) globalEnv
                               return (filter (\id -> isExported id m globalEnv) identifiers)
                     | otherwise 
                         -> Nothing
                 EnvUnqualName n 
                     -> let (ModuleEnv _ imports _ (LexEnv cmap tmap)) 
                                       = currentModuleEnv
                            local_con  = Map.lookup n cmap
                            local_typ  = Map.lookup n tmap
                            
                            others     = concatMap (\(EnvImport m _ _) 
                                                        -> fromMaybe [] $
                                                           lookup' currentModule
                                                                   (EnvQualName m n)
                                                                   globalEnv)
                                          $ filter (not . isQualifiedImport) imports
                            (other_cs, other_ts) 
                                       = splitIdentifiers others
                        in Just $
                           map Constant (consider local_con other_cs) ++ 
                           map Type (consider local_typ other_ts)
                     where
                       consider Nothing  []  = []
                       consider (Just x) []  = [x]
                       consider Nothing  [x] = [x]
                       consider Nothing  xs  
                           = error (Msg.identifier_collision_in_lookup currentModule qname xs)
                       consider (Just x) xs  
                           = error (Msg.identifier_collision_in_lookup currentModule qname (x:xs))

lookupIdentifiers_OrLose :: ModuleID -> EnvName -> GlobalE -> [Identifier]
lookupIdentifiers_OrLose mID n globalEnv
    = case Importer.LexEnv.lookup mID n globalEnv of
         (Just c, Nothing)  -> [Constant c]
         (Nothing, Just t)  -> [Type t]
         (Just c, Just t)   -> [Constant c, Type t]
         (Nothing, Nothing) -> error (Msg.failed_lookup "Identifier" mID n globalEnv)

lookupConstant :: ModuleID -> EnvName -> GlobalE -> Maybe Identifier
lookupConstant m n env
    = case Importer.LexEnv.lookup m n env of
        (Just c, _) -> Just (Constant c)
        _           -> Nothing

lookupConstant_OrLose :: ModuleID -> EnvName -> GlobalE -> Identifier
lookupConstant_OrLose m n env
    = case lookupConstant m n env of
        Just c -> c
        _      -> error (Msg.failed_lookup "Constant" m n env)

lookupType :: ModuleID -> EnvName -> GlobalE -> Maybe Identifier
lookupType m n env
    = case Importer.LexEnv.lookup m n env of
        (_, Just t) -> Just (Type t)
        _           -> Nothing

lookupType_OrLose :: ModuleID -> EnvName -> GlobalE -> Identifier
lookupType_OrLose m n env
    = case lookupType m n env of
        Just t -> t
        _      -> error (Msg.failed_lookup "Type" m n env)

lookupImports_OrLose :: ModuleID -> GlobalE -> [EnvImport]
lookupImports_OrLose moduleID globalEnv
    = let (ModuleEnv _ imps _ _) = findModuleEnv_OrLose moduleID globalEnv 
      in imps

-- 
resolveEnvName_OrLose :: GlobalE -> ModuleID -> EnvName -> EnvName
resolveEnvName_OrLose globalEnv mID name
    = case Importer.LexEnv.lookup mID name globalEnv of
        (Just c, Nothing)  -> constant2name c
        (Nothing, Just t)  -> type2name t
        (Nothing, Nothing) -> error (Msg.failed_lookup "Constant or Type" mID name globalEnv)
        (Just c, Just t)   -> assert (constant2name c == type2name t) 
                                $ constant2name c

resolveConstantName :: GlobalE -> ModuleID -> EnvName -> Maybe EnvName
resolveConstantName globalEnv mID name
    = case lookupConstant mID name globalEnv of
        Nothing -> Nothing
        Just c  -> Just (identifier2name c)


resolveTypeName :: GlobalE -> ModuleID -> EnvName -> Maybe EnvName
resolveTypeName globalEnv mID name
    = case lookupType mID name globalEnv of
        Nothing -> Nothing
        Just c  -> Just (identifier2name c)

allIdentifiers :: GlobalE -> [Identifier]
allIdentifiers (GlobalEnv modulemap)
    = concatMap (\(ModuleEnv _ _ _ (LexEnv cmap tmap)) 
                     -> map Constant (Map.elems cmap) ++
                        map Type (Map.elems tmap))
        $ Map.elems modulemap

updateGlobalEnv :: (EnvName -> [Identifier]) -> GlobalE -> GlobalE
updateGlobalEnv update globalEnv@(GlobalEnv modulemaps)
    = let all_ids     = allIdentifiers globalEnv
          id_alist    = groupAlist $ concatMap (\id -> case update (identifier2name id) of 
                                                         []      -> [(id, id)]
                                                         new_ids -> [ (new, id) | new <- new_ids ])
                                         all_ids
          mod_alist   = nub (concat [ [ (moduleOf (lexInfoOf n), (moduleOf (lexInfoOf o))) | o <- os ] 
                                          | (n, os) <- id_alist ])
          id_tbl      = Map.fromListWith (failDups "id_tbl")  id_alist   -- Map from new_id  to [old_id]
          mod_tbl     = Map.fromListWith (failDups "mod_tbl") mod_alist  -- Map from new_mID to old_mID
          rev_mod_tbl = Map.fromListWith (failDups "rev_mod_tbl")        -- Map from old_mID to [new_mID]
                          (groupAlist [ (o,n) | (n,o) <- mod_alist ]) 

          -- The new ModuleE gets the same imports as the old ModuleE, but we
          -- have to account for old imports being possibly updated themselves.
          -- E.g. if `Foo' imported `Prelude', and `Prelude` was split into `List', 
          -- and `Datatype`, then 'Foo' now has to import 'Prelude', 'List', 
          -- and 'Datatype'.
          recompute_imports new_mID
              = let old_mID         = fromJust (Map.lookup new_mID mod_tbl)
                    old_mEnv        = findModuleEnv_OrLose old_mID globalEnv
                    old_imports     = (let (ModuleEnv _ imps _ _) = old_mEnv in imps)
                    old_import_mIDs = importedModuleIDs old_mEnv
                in  
                  do (old_imported_mID, old_import) <- zip old_import_mIDs old_imports
                     case fromJust (Map.lookup old_imported_mID rev_mod_tbl) of
                       []       -> return old_import
                       mIDs     -> let new_imports = map (\mID -> EnvImport mID False Nothing) mIDs
                                   in if old_imported_mID `elem` mIDs then new_imports
                                                                      else old_import : new_imports

          -- The new ModuleE must export all those identifiers that are the same
          -- as the exported identifiers in the old ModuleE, and all those that
          -- resulted from updating any such identifier.
          recompute_exports new_id
              = or (do old_id  <- fromJust (Map.lookup new_id id_tbl)
                       old_mID <- (let oldm = moduleOf (lexInfoOf old_id)
                                       newm = moduleOf (lexInfoOf new_id)
                                   in assert (oldm == fromJust (Map.lookup newm mod_tbl))
                                      $ return oldm)
                       return (isExported old_id old_mID globalEnv))

       in 
         makeGlobalEnv recompute_imports recompute_exports (map fst id_alist)

    where failDups str a b = error (Msg.found_duplicates ("computing " ++ str) a b)

augmentGlobalEnv :: GlobalE -> [Identifier] -> GlobalE
augmentGlobalEnv globalEnv new_identifiers
    = let all_identifiers        = allIdentifiers globalEnv
          tmp                    = partition (`elem` all_identifiers) new_identifiers
          updated_identifiers    = fst tmp
          really_new_identifiers = snd tmp
          env1 = makeGlobalEnv (const []) (const True) really_new_identifiers
          env2 = updateGlobalEnv (\qn@(EnvQualName mID _) 
                                      -> let old_ids = lookupIdentifiers_OrLose mID qn globalEnv
                                             new_ids = filter (\id -> qn == identifier2name id)
                                                              updated_identifiers
                                         in if null new_ids
                                            then old_ids 
                                            else old_ids ++ new_ids)
                      globalEnv
      in unionGlobalEnvs env2 env1



-- check_GlobalEnv_Consistency

--       check_duplicates :: Eq a => ([a] -> String) -> [a] -> [a]
--       check_duplicates failure_str xs 
--           | hasDuplicates xs = error (failure_str xs)
--           | otherwise = xs 

--              (check_duplicates Msg.duplicate_import (importedModules imports'))
--              (check_duplicates Msg.export (importedModules exports')) 

--     where 

--       checkExports :: [HsExportSpec] -> [HsImportDecl] -> [HsExportSpec]
--       checkExports exports imports 
--           = do export <- checkForDuplicateExport exports
--                let [(qname, restoreExport)] = contextsBi export :: [(HsQName, HsQName -> HsExportSpec)]
--                case qname of 
--                  UnQual _ -> return (restoreExport qname)
--                  Qual m _ 
--                    | isImportedModule_aux (fromHsk m) imports  
--                        -> return (restoreExport qname)
--                    | otherwise 
--                        -> error ("Module of `" ++ show qname ++ "'"
--                                  ++ " is not in import list, but in export list.")

--       checkForDuplicateExport :: [HsExportSpec] -> [HsExportSpec]
--       checkForDuplicateExport exports 
--           = if hasDuplicates (universeBi exports :: [HsName]) -- strip off qualifiers
--             then error ("Duplicates found in export list: " ++ show exports)
--             else exports
