{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, TypeSynonymInstances, GeneralizedNewtypeDeriving #-}

{-| Author: Tobias C. Rittweiler, TU Muenchen

Definition of a Global Environment for identifier resolution and information
retrieval.
-}

module Importer.Ident_Env
    ( GlobalE,
      Assoc(..),
      Identifier(..),
      Constant(..),
      Type(..),
      TypeDecl(..),
      Name(..),
      LexInfo(..),
      Import(..),
      Constructor(..),
      RecordField(..),
      ModuleID,
      IdentifierID,
      identifier2name,
      getDepDataType,
      fromHsk,
      toHsk,
      fromIsa,
      toIsa,
      typscheme_of_hsk_typ,
      hsk_typ_of_typscheme,
      isa_of_sort,
      resolveName_OrLose,
      makeLexInfo,
      makeClassInfo,
      initialGlobalEnv,
      isInfixOp,
      isUnaryOp,
      isClass,
      isType,
      isInstance,
      isFunction,
      isData,
      isTypeAnnotation,
      qualifyName,
      resolveConstantName,
      resolveTypeName,
      unionGlobalEnvs,
      augmentGlobalEnv,
      updateGlobalEnv,
      updateIdentifier,
      renameHsModuleNames,
      environmentOf,
      makeGlobalEnv,
      lookupConstant, lookupConstant_OrLose,
      lookupType, lookupType_OrLose,
      substituteTyVars,
      lookupIdentifiers_OrLose,
      lookupImports_OrLose,
      lexInfoOf,
      methodsOf,
      classVarOf,
      prelude
    ) where

import Importer.Library
import qualified Importer.AList as AList
import Maybe
import List (partition, nub)
import qualified Data.Map as Map

import Control.Monad.Reader

import qualified Importer.Msg as Msg
import Importer.Configuration hiding (getCustomTheory)
import qualified Importer.Configuration as Conf (getCustomTheory)

import qualified Language.Haskell.Exts as Hsx
import qualified Importer.Hsx as Hsx
import qualified Importer.Isa as Isa


newtype LexM a = LexM (Reader Customisations a)
    deriving (Functor, Monad, MonadReader Customisations)

runLexM :: Customisations -> LexM a -> a
runLexM c (LexM m) = runReader m c 

{-|
  This function returns the custom theory for given module name if there is one.
-}
getCustomTheory :: Hsx.ModuleName -> LexM (Maybe CustomTheory)
getCustomTheory mod
    = do custs <- ask
         return $ Conf.getCustomTheory custs mod


---
--- Identifier information
--
--    This is used for information retrieval about an identifier.
--    E.g. if an identifier represents a function, or a class, etc.
--

type ModuleID     = String
type IdentifierID = String


{-|
  This data structure represents types. NB: It also contains an 'EnvTyNone' type to
  indicate that no type information is present.
-}
data Type = TyVar Name
             | TyCon Name [Type]
             | TyFun Type Type
             | TyNone
  deriving (Eq, Ord, Show)

{-|
  This data structure represents the associativity declaration of binary operators.
-}
data Assoc = AssocRight | AssocLeft | AssocNone
  deriving (Eq, Ord, Show)

{-|
  This data structure represents identifier name in either unqualified or qualified form.
-}
data Name = QualName ModuleID IdentifierID
             | UnqualName IdentifierID
  deriving (Eq, Ord, Show)

{-|
  Checks whether an environment name is qualified by a module.
-}

isQualified :: Name -> Bool
isQualified (QualName _ _) = True
isQualified (UnqualName _) = False

{-|
  Qualifies an existing environment name with a module.
  If the name is already qualified nothing is changed.
-}

qualifyName :: ModuleID -> Name -> Name
qualifyName mID qn@(QualName mID' _) = qn
qualifyName mID (UnqualName n)       = QualName mID n

{-|
  If the given environment name is qualified with the given
  module the qualification is removed and the corresponding
  unqualified name is returned. If the modules do not match an exception
  is thrown.
  Unqualified environment names are left untouched.
-}

unqualifyName :: ModuleID -> Name -> Name
unqualifyName mID (QualName mID' id) = assert (mID == mID') $ UnqualName id
unqualifyName mID n@(UnqualName _)   = n


{-|
  This function substitutes type variables by types
  as given by the substitution argument.
  E.g.: 
  	@substituteTyVars [(a, Quux)] (Foo a -> Foobar a b -> Bar a b)@
   			==>
  	@Foo Quux -> Foobar Quux b -> Bar Quux b@
-}
substituteTyVars :: [(Type, Type)] -- ^the substitution to use
                 -> Type -- ^the type to apply the substitution to
                 -> Type -- ^the resulting type
substituteTyVars alist typ
    = let lookup' = Prelude.lookup in
      case typ of
        t@(TyVar _)     -> case lookup' t alist of
                               Just t' -> t'
                               Nothing -> t
        t@(TyCon cN ts) -> case lookup' t alist of
                               Just t' -> t'
                               Nothing -> TyCon cN (map (substituteTyVars alist) ts)
        t@(TyFun t1 t2) -> case lookup' t alist of
                               Just t' -> t'
                               Nothing -> TyFun (substituteTyVars alist t1)
                                                    (substituteTyVars alist t2)
        t@(TyNone)      -> case lookup' t alist of { Just t' -> t'; Nothing -> t }

{-|
  This data type collects identifier information attached to
  an identifier
-}

data LexInfo = LexInfo {
  nameOf :: IdentifierID,
  typschemeOf :: ([(Name, [Name])], Type),
  moduleOf :: ModuleID
} deriving (Eq, Ord, Show)


{-| 
  This data type collects information that is
  attached to a class.
-}
data ClassInfo = ClassInfo {
                            superclassesOf :: [Name],
                            methodsOf      :: [Identifier],
                            classVarOf     :: Name,
                            instancesOf    :: [InstanceInfo]
                           }
  deriving (Eq, Ord, Show)

{-|
  This data type collects information about 
-}

data InstanceInfo = InstanceInfo { specializedTypeOf :: Type }
  deriving (Eq, Ord, Show)

{-|
  This data structure represents identifier information for
  different kinds of constants.
-}

data Constant = Variable LexInfo
              | Constructor Constructor
              | Field LexInfo [Constructor]
              | Function LexInfo
              | UnaryOp  LexInfo Int
              | InfixOp  LexInfo Assoc Int
              | TypeAnnotation LexInfo 
  deriving (Eq, Ord, Show)

data Constructor = SimpleConstr {constrTypeName :: Name, constrLexInfo :: LexInfo}
                 | RecordConstr {constrTypeName :: Name, constrLexInfo :: LexInfo, constrFields :: [RecordField]}
  deriving (Eq, Ord, Show)

data RecordField = RecordField IdentifierID Type
  deriving (Eq, Ord, Show)

{-|
  This data structure represents identifier information for 
  different kinds of type declaration.
-}
data TypeDecl = Data LexInfo [Constructor]
          | TypeDef LexInfo
          | Class LexInfo ClassInfo
          | Instance LexInfo [InstanceInfo]
  deriving (Eq, Ord, Show)

{-| 
  Identifier forms the union of the 'Type' and 'Constant' type. The reasong for this
  is that types and constants live in different namespaces.
-}
data Identifier = Constant Constant
                | TypeDecl TypeDecl
  deriving (Eq, Ord, Show)

{-| 
  This function constructs a identifier information structure, given a module
  the identifier and the type of the identifier.
-}
makeLexInfo :: ModuleID -> IdentifierID -> ([(Name, [Name])], Type) -> LexInfo
makeLexInfo moduleID identifierID t = LexInfo {
  nameOf   = identifierID,
  typschemeOf = t,
  moduleOf = if moduleID == "" then prelude else moduleID
}

{-|
  This function constructs a class information structure, given a list of its
  super classes, a list of the methods defined in the class and the variable 
  that is declared to be in the class.
-}
makeClassInfo :: [Name] -> [Identifier] -> Name -> ClassInfo
makeClassInfo superclasses methods classVarName
    = assert (all isTypeAnnotation methods)
        $ ClassInfo { superclassesOf = superclasses,
                      methodsOf      = methods,
                      classVarOf     = classVarName,
                      instancesOf    = [] }
{-|
 ???
-}
makeInstanceInfo :: Type -> InstanceInfo
makeInstanceInfo t 
    = InstanceInfo { specializedTypeOf = t }

{-|
  Returns true for identifiers being a constant.
-}
isConstant :: Identifier -> Bool
isConstant (Constant _)              = True
isConstant _                         = False

{-|
  Returns true for identifiers being a type.
-}
isType :: Identifier -> Bool
isType (TypeDecl _)                      = True
isType _                             = False

{-|
  Returns true for identifiers being a variable.
-}
isVariable :: Identifier -> Bool
isVariable (Constant (Variable _))   = True
isVariable _                         = False

{-|
  Returns true for identifiers being a function.
-}
isFunction :: Identifier -> Bool
isFunction (Constant (Function _))   = True
isFunction _                         = False

{-|
  Returns true for identifiers being unary operators.
-}
isUnaryOp :: Identifier -> Bool
isUnaryOp (Constant (UnaryOp _ _))   = True
isUnaryOp _                          = False

{-|
  Returns true for identifiers being infix operators.
-}
isInfixOp :: Identifier -> Bool
isInfixOp (Constant (InfixOp _ _ _)) = True
isInfixOp _                          = False

{-|
  Returns true for identifiers being type annotations.
-}
isTypeAnnotation :: Identifier -> Bool
isTypeAnnotation (Constant (TypeAnnotation _)) = True
isTypeAnnotation _                             = False


{-|
  Returns true for identifiers being classes.
-}
isClass :: Identifier -> Bool
isClass (TypeDecl (Class _ _))           = True
isClass _                            = False

{-|
  Returns true for identifiers being instance declarations.
-}
isInstance :: Identifier -> Bool
isInstance (TypeDecl (Instance _ _))     = True
isInstance _                         = False

{-|
  Returns true for identifiers being data types.
-}
isData :: Identifier -> Bool
isData (TypeDecl (Data _ _)) = True
isData _                 = False

{-|
  This function provides the information attached to the
  given identifier.
-}
lexInfoOf :: Identifier -> LexInfo
lexInfoOf identifier
    = case identifier of
        Constant c -> lexInfoOf_con c
        TypeDecl t     -> lexInfoOf_typ t
    where
      lexInfoOf_con (Variable i)       = i
      lexInfoOf_con (Field i _)       = i
      lexInfoOf_con (Function i)       = i
      lexInfoOf_con (UnaryOp i _)      = i
      lexInfoOf_con (InfixOp i _ _)    = i
      lexInfoOf_con (TypeAnnotation i) = i
      lexInfoOf_con (Constructor con)  = 
          case con of
            SimpleConstr _ i -> i
            RecordConstr _ i _ -> i

      lexInfoOf_typ (Class i _)        = i
      lexInfoOf_typ (Instance i _)     = i
      lexInfoOf_typ (Data i _)         = i
      lexInfoOf_typ (TypeDef i )         = i



getDepDataType :: GlobalE -> ModuleID -> Name -> Maybe Name
getDepDataType env mod  name = 
    case lookupConstant mod name env of
      Nothing -> Nothing
      Just (Constant c) ->
          case c of
            Field _ (constr:_) -> Just $ constrTypeName constr
            Constructor constr -> Just $ constrTypeName constr
            _ -> Nothing


{-|
  This function updates the identifier information attached to the
  given identifier.
-}
updateIdentifier :: Identifier -> LexInfo -> Identifier
updateIdentifier identifier lexinfo
    = case identifier of
        Constant c -> Constant (updateConstant c lexinfo)
        TypeDecl t     -> TypeDecl     (updateType t lexinfo)
    where 
      updateConstant (Variable _) lexinfo        = Variable lexinfo
      updateConstant (Field _ constr) lexinfo        = Field lexinfo constr
      updateConstant (Constructor c) lexinfo
          = Constructor $
            case c of
              SimpleConstr dataTy _ -> SimpleConstr dataTy lexinfo
              RecordConstr dataTy _ fs -> RecordConstr dataTy lexinfo fs
      updateConstant (Function _) lexinfo        = Function lexinfo
      updateConstant (UnaryOp _ p) lexinfo       = UnaryOp lexinfo p
      updateConstant (InfixOp _ a p) lexinfo     = InfixOp lexinfo a p
      updateConstant (TypeAnnotation _) lexinfo  = TypeAnnotation lexinfo

      updateType (Data _ conNs) lexinfo          = Data lexinfo conNs
      updateType (Class _ classinfo) lexinfo     = Class lexinfo classinfo
      updateType (Instance _ instinfo) lexinfo   = Instance lexinfo instinfo
      updateType (TypeDef _) lexinfo             = TypeDef lexinfo
{-|
  This function provides the environment name for the given identifier
-}
identifier2name :: Identifier -> Name
identifier2name identifier
    = let lexinfo  = lexInfoOf identifier
          name     = nameOf lexinfo
          modul    = moduleOf lexinfo
      in assert (modul /= "") $ QualName modul name

{-|
  This function provides the environment name for the given constant.
-}
constant2name :: Constant -> Name
constant2name c = identifier2name (Constant c)

{-|
  This function provides the environment name for the given type.
-}
type2name     :: TypeDecl -> Name
type2name t     = identifier2name (TypeDecl t)

{-|
  This function splits the given list into a list of constants and
  a list of types.
-}
splitIdentifiers :: [Identifier] -> ([Constant], [TypeDecl])
splitIdentifiers ids
    = let (c_ids, t_ids) 
              = partition (\i -> case i of {Constant _ -> True; _ -> False}) ids
      in 
        ([ c | Constant c <- c_ids ], [ t | TypeDecl t <- t_ids ])


{-|
  Instances of this class are pairs of at the one hand a Haskell entity and on the
  other and an environment entity that can be translated into each other.
-}
class Hsk2Env a b where
    fromHsk :: Show a => a -> b
    toHsk   :: Show b => b -> a
    toHsk b = error ("(toHsk) Internal Error: Don't know how to convert: " ++ show b)


instance Hsk2Env Hsx.ModuleName ModuleID where
    fromHsk (Hsx.ModuleName id) = id
    toHsk id            = Hsx.ModuleName id

instance Hsk2Env Hsx.QName IdentifierID where
    fromHsk (Hsx.Qual _ n)  = fromHsk n
    fromHsk (Hsx.UnQual n)  = fromHsk n
    fromHsk (Hsx.Special s) = fromHsk (translateSpecialCon DataCon s)
    
    toHsk junk = error ("toHsk ConstantID -> Hsx.Name: " ++ show junk)

instance Hsk2Env Hsx.Name IdentifierID where
    fromHsk (Hsx.Ident s)  = s
    fromHsk (Hsx.Symbol s) = s
    toHsk id = Hsx.string2Name id


instance Hsk2Env Hsx.QName Name where
    fromHsk (Hsx.Qual m n)  = QualName (fromHsk m) (fromHsk n)
    fromHsk (Hsx.UnQual n)  = UnqualName (fromHsk n)
    fromHsk (Hsx.Special s) = fromHsk (translateSpecialCon DataCon s)

    toHsk (QualName moduleId id) = let qname = Hsx.Qual (toHsk moduleId) (toHsk id)
                                      in case retranslateSpecialCon DataCon qname of
                                           Just s  -> Hsx.Special s
                                           Nothing -> qname                                         
    toHsk (UnqualName id)        = Hsx.UnQual (toHsk id)

instance Hsk2Env Hsx.Name Name where
    fromHsk hsname           = UnqualName (fromHsk hsname)
    toHsk (UnqualName id) = toHsk id
    toHsk junk = error ("toHsk Ident_Env.Name -> Hsx.Name: " ++ show junk)

instance Hsk2Env Hsx.Assoc Assoc where
    fromHsk Hsx.AssocRight = AssocRight
    fromHsk Hsx.AssocLeft  = AssocLeft
    fromHsk Hsx.AssocNone  = AssocNone

    toHsk AssocRight  = Hsx.AssocRight
    toHsk AssocLeft   = Hsx.AssocLeft
    toHsk AssocNone   = Hsx.AssocNone

instance Hsk2Env Hsx.Type Type where
    fromHsk (Hsx.TyVar name)  = TyVar (fromHsk name)
    fromHsk (Hsx.TyCon qname) = TyCon (fromHsk (translate qname)) []
                            where translate (Hsx.Special s) = translateSpecialCon TypeCon s
                                  translate etc = etc

    fromHsk (Hsx.TyTuple Hsx.Boxed []) = TyCon (fromHsk unit_tyco) []
    fromHsk (Hsx.TyTuple Hsx.Boxed [typ]) = fromHsk typ
    fromHsk (Hsx.TyTuple Hsx.Boxed (typ1 : typ2 : typs)) = combl
      (\typ1 -> \typ2 -> TyCon (fromHsk pair_tyco) [typ1, fromHsk typ2])
      (TyCon (fromHsk pair_tyco) [fromHsk typ1, fromHsk typ2]) typs

    fromHsk (Hsx.TyFun type1 type2) = let
        type1' = fromHsk type1
        type2' = fromHsk type2
      in TyFun type1' type2'

    -- Types aren't curried or partially appliable in HOL, so we must pull a nested
    -- chain of type application inside out:
    --
    --  T a b ==> Hsx.TyApp (Hsx.TyApp (Hsx.Type T) (Hsx.TyVar a)) (Hsx.TyVar b)
    --       
    --        ==> Type T [(TyVar a), (TyVar b)]   
    --
    fromHsk tyapp@(Hsx.TyApp _ _) 
        = let (tycon, tyvars) = uncombl dest tyapp
              tycon'       = fromHsk tycon
              tyvars'      = map fromHsk tyvars
          in case tycon' of TyCon n [] -> TyCon n tyvars'
          where dest (Hsx.TyApp typ1 typ2) = Just (typ1, typ2)
                dest (Hsx.TyCon _) = Nothing
                dest junk = error ("Hsx.Type -> Ident_Env.Type (dest Hsx.TyApp): " ++ show junk)

    fromHsk junk = error ("Hsx.Type -> Ident_Env.Type: Fall Through: " ++ Msg.prettyShow' "thing" junk)

    toHsk (TyVar n)          = Hsx.TyVar (toHsk n)
    toHsk (TyFun t1 t2)      = Hsx.TyFun (toHsk t1) (toHsk t2)
    toHsk (TyCon qn [])      = Hsx.TyCon (toHsk qn)
    toHsk (TyCon qn tyvars)
        = let tycon'            = toHsk (TyCon qn [])
              tyvar':tyvars'    = map toHsk tyvars
          in foldl Hsx.TyApp (Hsx.TyApp tycon' tyvar') tyvars'

typscheme_of_hsk_typ :: Hsx.Type -> ([(Name, [Name])], Type)
typscheme_of_hsk_typ (Hsx.TyForall _ ctx typ) =
  (map (map_pair fromHsk (map fromHsk)) (Hsx.dest_typcontext ctx), fromHsk typ)
typscheme_of_hsk_typ typ = ([], fromHsk typ)

hsk_typ_of_typscheme :: ([(Name, [Name])], Type) -> Hsx.Type
hsk_typ_of_typscheme (vs, typ) = Hsx.TyForall Nothing ctx (toHsk typ) where
  aux = AList.group $ concat [ map (flip (,) tyvarN) classNs | (tyvarN, classNs) <- vs ]
  ctx = [ Hsx.ClassA (toHsk classN) (map (Hsx.TyVar . toHsk) tyvarNs) | (classN, tyvarNs) <- aux ]

{-    toHsk (TyScheme alist t) = Hsx.TyForall Nothing ctx (toHsk t)
        where
          revalist = AList.group 
                       $ concat [ map (flip (,) tyvarN) classNs | (tyvarN, classNs) <- alist ]
          ctx      = [ Hsx.ClassA (toHsk classN) (map (Hsx.TyVar . toHsk) tyvarNs) 
                           | (classN, tyvarNs) <- revalist ]

    toHsk junk = error ("Type -> Hsx.Type: Fall Through: " ++ Msg.prettyShow' "thing" junk) -}
instance Hsk2Env Hsx.ExportSpec Export where
    fromHsk (Hsx.EVar qname)        = ExportVar   (fromHsk qname)
    fromHsk (Hsx.EAbs qname)        = ExportAbstr (fromHsk qname)
    fromHsk (Hsx.EThingAll qname)   = ExportAll   (fromHsk qname)
    fromHsk (Hsx.EModuleContents m) = ExportMod   (fromHsk m)
    fromHsk etc = error ("Not supported yet: " ++ show etc)

instance Hsk2Env Hsx.ImportDecl Import where
    fromHsk (Hsx.ImportDecl { Hsx.importModule=m,
                            Hsx.importQualified=qual,
                            Hsx.importAs=nick})
        = Import (fromHsk m) qual 
                    (case nick of
                       Nothing -> Nothing 
                       Just nick' -> Just $ fromHsk nick')

{-|
  Instances of this class are two types, on the one hand side Isabelle entities and on the other
  hand side environment entities, that can be converted into each other.
-}
class Isa2Env a b where
    fromIsa :: Show a => a -> b
    toIsa   :: Show b => b -> a
    toIsa b = error ("(toIsa) Internal Error: Don't know how to lift " ++ show b)

instance Isa2Env Isa.ThyName ModuleID where
    fromIsa (Isa.ThyName thyN) = thyN
    toIsa moduleID            = Isa.ThyName moduleID

instance Isa2Env Isa.Name Name where
    fromIsa (Isa.QName thy n)       = QualName (fromIsa thy) n
    fromIsa (Isa.Name n)            = UnqualName n

    toIsa (QualName moduleId id) = Isa.QName (toIsa moduleId) id
    toIsa (UnqualName id)        = Isa.Name id

instance Isa2Env Assoc Assoc where
    fromIsa AssocRight = AssocRight
    fromIsa AssocLeft  = AssocLeft
    fromIsa AssocNone  = AssocNone

    toIsa AssocRight    = AssocRight
    toIsa AssocLeft     = AssocLeft
    toIsa AssocNone     = AssocNone

instance Isa2Env Isa.Type Type where
    fromIsa Isa.NoType = TyNone
    fromIsa (Isa.TVar n) = TyVar (fromIsa n)
    fromIsa (Isa.Func t1 t2) = TyFun (fromIsa t1) (fromIsa t2)
    fromIsa (Isa.Type qn tyvars) = TyCon (fromIsa qn) (map fromIsa tyvars)
    
    toIsa TyNone = Isa.NoType
    toIsa (TyVar n) = Isa.TVar (toIsa n)
    toIsa (TyFun t1 t2) = Isa.Func (toIsa t1) (toIsa t2)
    toIsa (TyCon qn tyvars) = Isa.Type (toIsa qn) (map toIsa tyvars)

isa_of_sort :: [Name] -> [Isa.Name]
isa_of_sort = map toIsa

{-|
  This data type represents which kind a particular constructor is of. 
  I.e. a data or a type constructor. We have to translate those to names,
  because they're not special in Isabelle, and hence not in our Global Environment.
-} 

data ConKind = DataCon | TypeCon deriving Show

{-|
  This function translates special constructors to primitive qualified names.
-}
translateSpecialCon :: ConKind -- ^the kind of the constructor
                    -> Hsx.SpecialCon -- ^the constructor to translate
                    -> Hsx.QName -- ^the translated constructor
translateSpecialCon DataCon con = case Prelude.lookup con primitive_datacon_table of
                                    Just name -> name
                                    Nothing -> error $ "Internal error: Special data constructor " ++ show con ++ " not found!"
translateSpecialCon TypeCon con = case Prelude.lookup con primitive_tycon_table of
                                    Just name -> name
                                    Nothing -> error $ "Internal error: Special type constructor " ++ show con ++ " not found!"

{-|
  This is the \"reverse\" of 'translateSpecialCon'. It translates qualified names into
  special syntax constructors if possible.
-}
retranslateSpecialCon :: ConKind -> Hsx.QName -> Maybe Hsx.SpecialCon
retranslateSpecialCon DataCon qname 
    = Prelude.lookup qname [ (y,x) | (x,y) <- primitive_datacon_table ]
retranslateSpecialCon TypeCon qname 
    = Prelude.lookup qname [ (y,x) | (x,y) <- primitive_tycon_table ]

unit_tyco = Hsx.Ident "UnitTyCon"
pair_tyco = Hsx.Ident "PairTyCon"

primitive_tycon_table, primitive_datacon_table :: [(Hsx.SpecialCon, Hsx.QName)]

primitive_tycon_table 
    = [(Hsx.ListCon,    Hsx.Qual (Hsx.ModuleName "Prelude") (Hsx.Ident "ListTyCon")),
       (Hsx.UnitCon,    Hsx.Qual (Hsx.ModuleName "Prelude") unit_tyco),
       (Hsx.TupleCon 2, Hsx.Qual (Hsx.ModuleName "Prelude") pair_tyco)
      ]

primitive_datacon_table 
    = [(Hsx.Cons,       Hsx.Qual (Hsx.ModuleName "Prelude") (Hsx.Ident ":")),
       (Hsx.ListCon,    Hsx.Qual (Hsx.ModuleName "Prelude") (Hsx.Ident "[]")),
       (Hsx.UnitCon,    Hsx.Qual (Hsx.ModuleName "Prelude") (Hsx.Ident "()")),
       (Hsx.TupleCon 2, Hsx.Qual (Hsx.ModuleName "Prelude") (Hsx.Ident "PairDataCon"))
      ]


--
--  Mappings between identifier's name and the Identifier data type.
--

{-|
  This data structure provides identifier information for constants and types.
-}
data ConstTypes = ConstTypes (Map.Map IdentifierID Constant) (Map.Map IdentifierID TypeDecl)
  deriving Show

{-|
  This function takes a list of identifiers (that contain identifier information) and collects the
  identifier information in a lexical environment. The identifiers are normalized, i.e. possibly merged.
-}
makeEnvConstTypes :: [Identifier] -> ConstTypes
makeEnvConstTypes identifiers
    = let (constants, types) = splitIdentifiers identifiers
          constant_bindings  = zip (map (nameOf . lexInfoOf . Constant) constants) constants
          type_bindings      = zip (map (nameOf . lexInfoOf . TypeDecl) types) types
          constants_map      = Map.fromListWith mergeConstants_OrFail constant_bindings
          types_map          = Map.fromListWith mergeTypes_OrFail type_bindings
      in 
        ConstTypes constants_map types_map
                 
{-|
  Same as 'mergeConstants' but throws an exception if it was not successful.

  There are some declarations which affect the same identifier even though the declarations
  are apart from each other. We merge the information comming from such declarations.

  E.g. explicit type annotations affect function-binding declarations,
       instance declarations affect the class defined by some class declaration.
-}

mergeConstants_OrFail :: Constant -> Constant -> Constant
mergeConstants_OrFail c1 c2
    = case mergeConstants c1 c2 of
        Just result -> result
        Nothing     -> error (Msg.merge_collision "mergeConstants_OrFail" c1 c2)

{-|
  Same as 'mergeTypes' but throws an exception if it was not successful.
-}
mergeTypes_OrFail :: TypeDecl -> TypeDecl -> TypeDecl
mergeTypes_OrFail t1 t2
    = case mergeTypes t1 t2 of
        Just result -> result
        Nothing     -> error (Msg.merge_collision "mergeTypes_OrFail" t1 t2)

{-|
  This function merges two identifier information blocks involving classes (i.e., also instance declarations for
  a particular class). It throws an exception if the arguments have different names.
  It merges instances into the instancesOf slot of the corresponding class's ClassInfo
  structure.
-}
mergeTypes :: TypeDecl -> TypeDecl -> Maybe TypeDecl
mergeTypes t1 t2
    = assert (nameOf (lexInfoOf (TypeDecl t1)) == nameOf (lexInfoOf (TypeDecl t2)))
      $ case (t1, t2) of
          (Class lexinfo classinfo@(ClassInfo { instancesOf = old_insts }), Instance _ instinfos)
              -> Just $ Class lexinfo (classinfo { instancesOf = instinfos ++ old_insts})
          (Instance _ instinfos, Class lexinfo classinfo@(ClassInfo { instancesOf = old_insts }))
              -> Just $ Class lexinfo (classinfo { instancesOf = instinfos ++ old_insts})
          (Instance lexinfo instinfos1, Instance _ instinfos2)
              -> Just $ Instance lexinfo (instinfos1 ++ instinfos2)
          (_,_) | t1 == t2  -> Just t1
                | otherwise -> Nothing

{-|
  This function merges type annotations with identifier information for constants.
-}
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
      update lexinfo@(LexInfo { typschemeOf = ([], TyNone) }) (LexInfo { typschemeOf = typ })
          = lexinfo { typschemeOf = typ }
      update lexinfo typ    -- Cannot merge + internal inconsistency.
          = error ("Internal Error (mergeLexInfo): Type collision between `" ++ show lexinfo ++ "'" 
                   ++ " and `" ++ show typ ++ "'.")

{-|
  This function merges two lexical environments by merging constants and types
  separately. If two identifiers cannot be merged the identifier from the first
  environment is discarded!
-}
mergeEnvConstTypess (ConstTypes cmap1 tmap1) (ConstTypes cmap2 tmap2)
    = ConstTypes (Map.unionWith constant_merger cmap1 cmap2)
             (Map.unionWith type_merger tmap1 tmap2)
    where 
      constant_merger c1 c2 = case mergeConstants c1 c2 of
                                Nothing  -> c2  -- favorize second argument.
                                Just res -> res
      type_merger t1 t2     = case mergeTypes t1 t2 of
                                Nothing  -> t2
                                Just res -> res

{-|
  This data structure represents export declarations.
-}
data Export = ExportVar   Name -- ^exporting a variable
               | ExportAbstr Name -- ^exporting a class or data type abstractly
               | ExportAll   Name -- ^exporting a class or data type completely
               | ExportMod   ModuleID -- ^re-exporting a module
  deriving (Show, Eq)

{-|
  This data structure represents import declarations.
  This includes

    * the name of the imported module,

    * a flag indicating whether the import is qualified, and

    * possibly an alias name.
-}
data Import = Import ModuleID Bool (Maybe ModuleID)
                 deriving (Show, Eq)


{-|
  This data structure represents the environment of a complete module.
  This includes the name of the module, a list of its imports, a list of its exports
  and its lexical environment.
-}
data Module = Module { moduleEName :: ModuleID, moduleEImports :: [Import],
    moduleEExports :: [Export], moduleELex :: ConstTypes }
  deriving (Show)

{-|
  The default import.
-}
defaultImports = [Import prelude False Nothing]


{-|
  This function checks whether the import is declared to be
  qualified.
-}
isQualifiedImport :: Import -> Bool
isQualifiedImport (Import _ isQual _) = isQual
                 
{-|
  This function constructs a module environment from a list of imports, a predicate
  indicating which identifier to export and a list of declared identifiers.
-}
makeEnvModule :: [Import] -- ^import declarations
              -> (Identifier -> Bool) -- ^predicate indicating which identifiers to export
              -> [Identifier] -- ^declared identifiers
              -> Module -- ^constructed environment
makeEnvModule imports shall_export_p identifiers
    = let m = moduleOf (lexInfoOf (head identifiers))
      in assert (all (== m) $ map (moduleOf . lexInfoOf) (tail identifiers))
           $ Module m imports exports (makeEnvConstTypes identifiers)
    where
      exports = map export (filter shall_export_p identifiers)
      export id@(TypeDecl (Data _ _)) = ExportAll (identifier2name id) 
      export id                   = ExportVar (identifier2name id)

{-|
  This function constructs a module environment from a Haskell module.
-}
makeEnvModule_FromModule :: Hsx.Module ->  LexM Module
makeEnvModule_FromModule (Hsx.Module loc modul pragmas warning exports imports topdecls)
    = let env = makeEnvConstTypes (concatMap (computeConstantMappings modul) topdecls)
          imports' = map fromHsk imports ++ defaultImports
          exports' = case exports of
                       Nothing -> [ExportMod (fromHsk modul)] 
                       Just jexports -> map fromHsk jexports
          mod = fromHsk modul
      in return $ Module mod imports' exports' env

customExportList :: ModuleID -> CustomTheory -> [Export]
customExportList mod custThy
    = let constants = getCustomConstants custThy 
          constants' = map (ExportVar . QualName mod) constants
          types = getCustomTypes custThy
          types' = map (ExportAll . QualName mod) types
      in constants' ++ types'

customEnvConstTypes :: ModuleID -> CustomTheory -> ConstTypes
customEnvConstTypes mod custThy
    = let constants = getCustomConstants custThy 
          types = getCustomTypes custThy
      in ConstTypes (env Variable constants) (env (`Data` []) types)
            where env ctr exps = Map.fromListWith (\a b -> a) $ 
                                    map (\a -> (a,ctr $ LexInfo {nameOf = a, typschemeOf = ([], TyNone), moduleOf = mod})) exps

{-|
  This function infers identifier information for the identifiers mentioned in the given Haskell 
  declaration.
-}
computeConstantMappings :: Hsx.ModuleName -> Hsx.Decl -> [Identifier]
computeConstantMappings modul decl 
    = do name <- Hsx.namesFromDecl decl
         let nameID         = fromHsk name
         let moduleID       = fromHsk modul
         let defaultLexInfo = LexInfo { nameOf=nameID, typschemeOf=([], TyNone), moduleOf=moduleID}
         case decl of
           Hsx.PatBind _ _ _ _ _         -> [Constant (Variable defaultLexInfo)]
           Hsx.FunBind _                 -> [Constant (Function defaultLexInfo)]
           Hsx.InfixDecl _ a p _         -> [Constant (InfixOp  defaultLexInfo (fromHsk a) p)]
           Hsx.TypeSig _ _ typ           -> [Constant (TypeAnnotation (defaultLexInfo { typschemeOf = typscheme_of_hsk_typ typ }))]
           Hsx.ClassDecl _ ctx _ ns _ ds -> let
               sups      = map fromHsk (Hsx.extractSuperclassNs ctx)
               typesigs  = Hsx.extractMethodSigs ds
               m         = modul
               methods   = concatMap (computeConstantMappings m) typesigs
               -- If length ns > 1, we will die later in Convert.hs anyway.
               classInfo = makeClassInfo sups methods (fromHsk (head ns))
             in [TypeDecl (Class defaultLexInfo classInfo)]
             -- If length ts > 1, we will die later in Convert.hs anyway.
           Hsx.InstDecl _ _ _ ts _       -> [TypeDecl (Instance defaultLexInfo $ [makeInstanceInfo (fromHsk (head ts))])]
           Hsx.DataDecl _ _ _ conN tyvarNs condecls _
               -> assert (fromHsk conN == nameID) $
                  let tycon = mkType (fromHsk name) tyvarNs
                      constructors = map (mkDataCon tycon) condecls
                      constructors' = map (Constant . Constructor) constructors
                      fields = concatMap mkRecordFields constructors
                      fields' = mergeFields fields
                  in [TypeDecl (Data (defaultLexInfo { typschemeOf = ([], tycon) }) constructors)] ++ constructors'
                         ++ fields'
               where
                 mergeFields fields = Map.elems $ Map.fromListWith mergePair fields
                 mergePair (Constant (Field lex constrs)) (Constant (Field lex' constrs'))
                     = (Constant (Field lex (constrs ++ constrs')))
                 mkRecordFields (SimpleConstr _ _) = []
                 mkRecordFields constr@(RecordConstr _ _ fields) = 
                     let mkField (RecordField id ty) = (id,Constant (Field (LexInfo id ([], ty) moduleID) [constr]))
                     in map mkField fields
                 mkType name tyvarNs 
                   = TyCon name $ map (TyVar . fromHsk) tyvarNs
                 conNe = case fromHsk conN of
                           UnqualName name -> QualName moduleID name
                 mkDataCon :: Type -> Hsx.QualConDecl -> Constructor
                 mkDataCon tycon (Hsx.QualConDecl _ _ _ (Hsx.ConDecl n args))
                     = let typ = foldr TyFun tycon (map (fromHsk . Hsx.unBang) args)
                       in SimpleConstr conNe (makeLexInfo moduleID (fromHsk n) ([], typ))
                 mkDataCon tycon (Hsx.QualConDecl _ _ _ (Hsx.RecDecl name fields))
                     = let fields' = Hsx.flattenRecFields fields
                           typ = foldr TyFun tycon (map (fromHsk. snd) fields')
                           mkField (n,ty) = RecordField (fromHsk n) (fromHsk ty)
                           recFields = map mkField fields'
                       in RecordConstr conNe (makeLexInfo moduleID (fromHsk name) ([], typ)) recFields
           Hsx.TypeDecl _ typeName _ _ -> [TypeDecl (TypeDef defaultLexInfo)]

{-|
  This function merges two module environments provided they have the same name (otherwise,
  an exception is thrown). Duplicates in the resulting imports and exports are removed, and 
  the lexical environment is merged by 'mergeEnvConstTypess'.
-}

mergeEnvModules (Module m1 is1 es1 lex1) (Module m2 is2 es2 lex2)
    = assert (m1 == m2)
        $ Module m1 (nub $ is1 ++ is2) (nub $ es1 ++ es2) (mergeEnvConstTypess lex1 lex2)


{-|
  This function provides a list of all module names that are imported in fully qualified form.
-}

importedModuleIDs :: Module -> [ModuleID]
importedModuleIDs (Module _ imports _ _)
    = map (\(imp@(Import m isQualified nickname ))
               -> case (isQualified, isJust nickname) of
                    -- Notice: Hsx.ModuleName names can _always_ be explicitly qualified.
                    (False, False) -> m 
                    (True,  False) -> m
                    (True,  True)  -> m
                    (False, True)  
                        -> error ("<importedModules> Internal Error: bogus import:" ++ show imp))
          imports
{-|
  This function checks whether the module identified by the given name is imported in the 
  given module environment.
-}
isImportedModule :: ModuleID -> Module -> Bool
isImportedModule moduleID moduleEnv
    = case filter (== moduleID) (importedModuleIDs moduleEnv) of
        []     -> False
        [name] -> True
        etc    -> error ("Internal error (isImportedModule): Fall through. [" ++ show etc ++ "]")



--
-- GlobalEnv
--

{-|
  This data structure represents a global environment.
-}
data GlobalE = GlobalEnv (Map.Map ModuleID Module)
  deriving Show

{-|
  Name of the prelude module.
-}
prelude :: ModuleID
prelude = "Prelude"

{-|
  The initial global environment.
-}
initialGlobalEnv :: GlobalE
initialGlobalEnv = GlobalEnv 
                     $ Map.singleton prelude 
                           (Module prelude [] [] (ConstTypes (Map.empty) (Map.empty)))

renameHsModuleNames :: (ModuleID -> Maybe ModuleID) -> GlobalE -> GlobalE
renameHsModuleNames ren (GlobalEnv env) = GlobalEnv . Map.fromList . map rename . Map.toList $ env
    where rename orig@(name, mod) = case ren name of
                                 Nothing -> orig
                                 Just newName -> (newName, mod{moduleEName = newName})

{-|
  This function constructs a global environment from a function generating the imports for a
  module name, a predicate identifying identifiers that should be exported, and a list of
  identifiers.

  This list of Identifiers is normalized, i.e. Instances and Classes are possibly
  merged, and Identifiers may get annotated by the type information
  of explicit TypeAnnotations.
-}

makeGlobalEnv :: (ModuleID -> [Import]) -> (Identifier -> Bool) -> [Identifier] -> GlobalE
makeGlobalEnv compute_imports shall_export_p identifiers
    = GlobalEnv
      $ Map.fromListWith failDups
            $ do let (constants, types) = splitIdentifiers identifiers
                 let types'             = mergeInstancesWithClasses types
                 (moduleID, ids) <- groupIdentifiers (map Constant constants ++ map TypeDecl types')
                 return (moduleID, makeEnvModule (compute_imports moduleID) shall_export_p ids)
    where 
      failDups a b = error ("Duplicate modules: " ++ show a ++ ", " ++ show b)

{-|
  Merges instance and corresponding class declarations using 'mergeTypes_OrFail'.
-}
mergeInstancesWithClasses :: [TypeDecl] -> [TypeDecl]
mergeInstancesWithClasses ts
    = let type_map  = Map.fromListWith (++) [ (nameOf (lexInfoOf (TypeDecl t)), [t]) | t <- ts ]
          instances = filter (isInstance . TypeDecl) ts
          type_map' = foldl (\map i -> Map.adjust (\ts -> case ts of
                                                            [t] -> [t]
                                                            ts  -> [foldl1 mergeTypes_OrFail ts])
                                                  (nameOf (lexInfoOf (TypeDecl i)))
                                                  type_map)
                        type_map
                        instances
      in concat $ Map.elems type_map'

{-|
  This function groups the given identifier by the respective module they are declared in.
-}
groupIdentifiers :: [Identifier] -> [(ModuleID, [Identifier])]
groupIdentifiers identifiers
    = AList.group [ (moduleOf (lexInfoOf id), id) | id <- identifiers ]

environmentOf :: Customisations -> [Hsx.Module] -> CustomTranslations -> GlobalE
environmentOf custs ms custMods = runLexM custs $ makeGlobalEnv_FromModule ms custMods

{-|
  This function constructs a global environment given a list of Haskell modules.
-}
makeGlobalEnv_FromModule :: [Hsx.Module] -> CustomTranslations -> LexM GlobalE
makeGlobalEnv_FromModule ms  custMods
    = do mapping <- mapM (\ m@(Hsx.Module _ modul _ _ _ _ _) ->
                         do env <- makeEnvModule_FromModule m
                            return (fromHsk modul,env) ) ms
         let custMapping = map (\(m, ct) -> let mid = fromHsk m in (mid, makeEnvModule_FromCustThy mid ct)) (Map.toList custMods)
         return $ GlobalEnv $ Map.fromListWith failDups (mapping ++ custMapping)
    where failDups a b = error ("Duplicate modules: " ++ show a ++ ", " ++ show b)

makeEnvModule_FromCustThy :: ModuleID -> CustomTheory -> Module
makeEnvModule_FromCustThy mod custThy = 
    Module mod [] (customExportList mod custThy) (customEnvConstTypes mod custThy)

{-|
  This method builds the union of two global environments, prioritising the first one.
  Instance declarations are merged with class declaration of the two environments.
-}
unionGlobalEnvs :: GlobalE -> GlobalE -> GlobalE
unionGlobalEnvs globalEnv1 globalEnv2
    = let compute_old_imports mID 
              = let get_imports (Module _ is _ _) = is
                in case mapMaybe (findEnvModule mID) [globalEnv1, globalEnv2] of
                     []      -> error ("unionGlobalEnvs: Internal error during computation of imports.")
                     [m]     -> get_imports m
                     [m1,m2] -> get_imports m1 ++ get_imports m2
          was_exported_p id
              = isExported id (moduleOf (lexInfoOf id)) globalEnv1 ||
                isExported id (moduleOf (lexInfoOf id)) globalEnv2
      in
        -- We explicitly recreate a GlobalE from new to merge Instances with Classes
        -- across all modules.
        makeGlobalEnv compute_old_imports was_exported_p
           $ allIdentifiers (simple_union globalEnv1 globalEnv2)
    where 
      -- This will merge the two envs module-wise; it'll especially merge Instances
      -- with Classes within the boundaries of one module only.
      simple_union (GlobalEnv map1) (GlobalEnv map2)
          = GlobalEnv 
              $ Map.unionWithKey
                    (\m moduleEnv1 moduleEnv2
                         -> let env1 = if Map.member m map1 then moduleEnv1 else moduleEnv2
                                env2 = if Map.member m map1 then moduleEnv2 else moduleEnv1
                            in
                               mergeEnvModules env1 env2)
                    map1 map2


{-|
  This method looks up the module environment in the given global environment using
  the given module name.
-}
findEnvModule :: ModuleID -> GlobalE -> Maybe Module
findEnvModule mID (GlobalEnv globalmap)
    = Map.lookup mID globalmap
{-|
  Same as 'findEnvModule' but throws an exception on failure.
-}
findEnvModule_OrLose m globalEnv
    = case findEnvModule m globalEnv of
        Just env -> env
        Nothing  -> error ("Couldn't find module `" ++ show m ++ "'.")

{-|
  This function provides a list of all identifier names that are exported by the
  module identified by the given module name in the given global environment.
-}
computeExportedNames :: ModuleID -> GlobalE -> [IdentifierID]
computeExportedNames moduleID globalEnv
    = case findEnvModule moduleID globalEnv of
        Nothing -> []
        Just (Module moduleID' _ exports (ConstTypes constants_map types_map))
            -> assert (moduleID == moduleID') $ do
                  export <- exports   -- List Monad concats implicitly for us.
                  case export of         
                    ExportVar   qn -> [idOf (unqualifyName moduleID qn)]
                    ExportAbstr qn -> [idOf (unqualifyName moduleID qn)]
                    ExportAll qn 
                        -> case lookupType moduleID qn globalEnv of
                             Just t@(TypeDecl (Data _ constructors))
                                 -> let id_of = nameOf . lexInfoOf
                                    in id_of t : map (id_of . Constant . Constructor) constructors
                             etc -> error ("Internal error (computeExportedNames): " ++ show etc)
                    ExportMod m
                                           -- export everything:
                        | m == moduleID -> Map.keys constants_map ++ Map.keys types_map 
                        | otherwise     -> computeExportedNames m globalEnv
    where idOf :: Name -> IdentifierID
          idOf (UnqualName id) = id

{-|
  This is a predicate deciding whether the given identifier is exported by the 
  module, given by the module name, in the given global environment
-}
isExported :: Identifier -> ModuleID -> GlobalE -> Bool
isExported identifier moduleID globalEnv
    = nameOf (lexInfoOf identifier) `elem` (computeExportedNames moduleID globalEnv)

{-|
  This function looks up the given module name in the imports of the
  given module environment and provides the full-qualified name of it.
  In case the module name cannot be found the input name is just returned.
  This function is supposed to be used to get the full-qualified name for a alias of
  a module name.
-}
resolveModuleID :: ModuleID -> Module -> ModuleID
resolveModuleID moduleID (Module _ imps _ _)
    = fromMaybe moduleID (lookfor moduleID imps)
    where 
      lookfor _ [] = Nothing
      lookfor mID (Import mID' _ nick:imports)
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

{-|
  This function looks up the given name in the import list of the given module.
  Note that types and constants have different namespaces. Hence the result can be a type
  and a constant.
-}
lookupName :: ModuleID -> Name -> GlobalE -> (Maybe Constant, Maybe TypeDecl)
lookupName currentModule qname globalEnv 
    = let (cs, ts) = splitIdentifiers (lookup' currentModule qname globalEnv)
      in (listToMaybe cs, listToMaybe ts)
    where
      lookup' :: ModuleID -> Name -> GlobalE -> [Identifier]
      lookup' currentModule qname globalEnv                            
          = case findEnvModule currentModule globalEnv of
              Nothing -> []
              Just currentEnvModule ->
                  case qname of
                    QualName m n 
                        | m == currentModule
                            -> lookup' m (UnqualName n) globalEnv
                        | isImportedModule (resolveModuleID m currentEnvModule) currentEnvModule
                            -> let identifiers = lookup' m (UnqualName n) globalEnv
                              in (filter (\id -> isExported id m globalEnv) identifiers)
                        | otherwise 
                            -> []
                    UnqualName n ->
                        let (Module _ imports _ (ConstTypes cmap tmap)) = currentEnvModule
                            local_con = Map.lookup n cmap
                            local_typ = Map.lookup n tmap      
                            others    = concatMap (\(Import m _ _) -> lookup' currentModule (QualName m n) globalEnv)
                                                       $ filter (not . isQualifiedImport) imports
                            (other_cs, other_ts) = splitIdentifiers others
                          in map Constant (consider local_con other_cs) ++ map TypeDecl (consider local_typ other_ts)
            where consider Nothing  []  = []
                  consider (Just x) []  = [x]
                  consider Nothing  [x] = [x]
                  consider Nothing  xs 
                      = error (Msg.identifier_collision_in_lookup currentModule qname xs)
                  consider (Just x) xs  
                      = error (Msg.identifier_collision_in_lookup currentModule qname (x:xs))

{-|
  Looks up the given identifier name in the given module's import list.
  Note that types and constants have different namespaces hence the result can
  be a list of length two (at most), containing a type and a constructor with
  the same name.
-}
lookupIdentifiers_OrLose :: ModuleID -> Name -> GlobalE -> [Identifier]
lookupIdentifiers_OrLose mID n globalEnv
    = case lookupName mID n globalEnv of
         (Just c, Nothing)  -> [Constant c]
         (Nothing, Just t)  -> [TypeDecl t]
         (Just c, Just t)   -> [Constant c, TypeDecl t]
         (Nothing, Nothing) -> error (Msg.failed_lookup "Identifier" mID n globalEnv)

{-|
  This function looks up the given identifier name, which is supposed to identify a constant, in the
  import list of the given module.
-}
lookupConstant :: ModuleID -> Name -> GlobalE -> Maybe Identifier
lookupConstant m n env
    = case lookupName m n env of
          (Just c, _) -> Just (Constant c)
          _           -> Nothing

{-|
  Same as 'lookupConstant' but throws an exception on failure.
-}
lookupConstant_OrLose :: ModuleID -> Name -> GlobalE -> Identifier
lookupConstant_OrLose m n env
    = case lookupConstant m n env of
        Just c -> c
        _      -> error (Msg.failed_lookup "Constant" m n env)

{-|
  This function looks up the given identifier name, which is supposed to identify a type, in the
  import list of the given module.
-}
lookupType :: ModuleID -> Name -> GlobalE -> Maybe Identifier
lookupType m n env
    = case lookupName m n env of
        (_, Just t) -> Just (TypeDecl t)
        _           -> Nothing

{-|
  Same as 'lookupType' but throws an exception on failure.
-}
lookupType_OrLose :: ModuleID -> Name -> GlobalE -> Identifier
lookupType_OrLose m n env
    = case lookupType m n env of
        Just t -> t
        _      -> error (Msg.failed_lookup "Type" m n env)
{-|
  This function looks up the import list of the given module.
-}
lookupImports_OrLose :: ModuleID -> GlobalE -> [Import]
lookupImports_OrLose moduleID globalEnv
    = let (Module _ imps _ _) = findEnvModule_OrLose moduleID globalEnv 
      in imps

{-|
  This function looks up the given name in the given module's import list to get
  a qualified name.
-}
resolveName_OrLose :: GlobalE -> ModuleID -> Name -> Name
resolveName_OrLose globalEnv mID name
    = case lookupName mID name globalEnv of
        (Just c, Nothing)  -> constant2name c
        (Nothing, Just t)  -> type2name t
        (Nothing, Nothing) -> error (Msg.failed_lookup "Constant or Type" mID name globalEnv)
        (Just c, Just t)   -> assert (constant2name c == type2name t) 
                                $ constant2name c

{-|
  This function looks up the given name, which is supposed to identify a constant, in the
  given module's import list to get a qualified name.
-}
resolveConstantName :: GlobalE -> ModuleID -> Name -> Maybe Name
resolveConstantName globalEnv mID name
    = case lookupConstant mID name globalEnv of
        Nothing -> Nothing
        Just c  -> Just (identifier2name c)

{-|
  This function looks up the given name, which is supposed to identify a type, in the given
  module's import list to get a qualified name.
-}
resolveTypeName :: GlobalE -> ModuleID -> Name -> Maybe Name
resolveTypeName globalEnv mID name
    = case lookupType mID name globalEnv of
        Nothing -> Nothing
        Just c  -> Just (identifier2name c)

{-|
  This function provides a list of all identifiers declared in the given global environment.
-}
allIdentifiers :: GlobalE -> [Identifier]
allIdentifiers (GlobalEnv modulemap)
    = concatMap (\(Module _ _ _ (ConstTypes cmap tmap)) 
                     -> map Constant (Map.elems cmap) ++
                        map TypeDecl (Map.elems tmap))
        $ Map.elems modulemap

{-|
  ???
-}
updateGlobalEnv :: (Name -> [Identifier]) -> GlobalE -> GlobalE
updateGlobalEnv update globalEnv@(GlobalEnv modulemaps)
    = let all_ids     = allIdentifiers globalEnv
          id_alist    = AList.group $ concatMap (\id -> case update (identifier2name id) of 
                                                         []      -> [(id, id)]
                                                         new_ids -> [ (new, id) | new <- new_ids ])
                                         all_ids
          mod_alist   = nub (concat [ [ (moduleOf (lexInfoOf n), (moduleOf (lexInfoOf o))) | o <- os ] 
                                          | (n, os) <- id_alist ])
          id_tbl      = Map.fromListWith (failDups "id_tbl")  id_alist   -- Map from new_id  to [old_id]
          mod_tbl     = Map.fromListWith (failDups "mod_tbl") mod_alist  -- Map from new_mID to old_mID
          rev_mod_tbl = Map.fromListWith (failDups "rev_mod_tbl")        -- Map from old_mID to [new_mID]
                          (AList.group [ (o,n) | (n,o) <- mod_alist ]) 

          -- The new Module gets the same imports as the old Module, but we
          -- have to account for old imports being possibly updated themselves.
          -- E.g. if `Foo' imported `Prelude', and `Prelude` was split into `List', 
          -- and `Datatype`, then 'Foo' now has to import 'Prelude', 'List', 
          -- and 'Datatype'.
          recompute_imports new_mID
              = let old_mID         = fromMaybe (error $ "Internal error: New module " ++ new_mID ++ " not found during update of global environment!")
                                      (Map.lookup new_mID mod_tbl)
                    old_mEnv        = findEnvModule_OrLose old_mID globalEnv
                    old_imports     = (let (Module _ imps _ _) = old_mEnv in imps)
                    old_import_mIDs = importedModuleIDs old_mEnv
                in  
                  do (old_imported_mID, old_import) <- zip old_import_mIDs old_imports
                     let res = fromMaybe  (error $ "Internal error: Old module " ++ new_mID ++ " not found during update of global environment!")
                               (Map.lookup old_imported_mID rev_mod_tbl)
                     case res of
                       []       -> return old_import
                       mIDs     -> let new_imports = map (\mID -> Import mID False Nothing) mIDs
                                   in if old_imported_mID `elem` mIDs then new_imports
                                                                      else old_import : new_imports

          -- The new Module must export all those identifiers that are the same
          -- as the exported identifiers in the old Module, and all those that
          -- resulted from updating any such identifier.
          recompute_exports new_id
              = or (do old_id  <- fromMaybe (error $ "Internal error: New identifier " ++ show new_id ++ " not found during update of global environment!")
                                 (Map.lookup new_id id_tbl)
                       old_mID <- (let oldm = moduleOf (lexInfoOf old_id)
                                       newm = moduleOf (lexInfoOf new_id)
                                   in assert (oldm == fromMaybe (error $ "Internal error: New module " ++ show newm ++ " not found during assertion in update of global environment") (Map.lookup newm mod_tbl))
                                      $ return oldm)
                       return (isExported old_id old_mID globalEnv))

       in 
         makeGlobalEnv recompute_imports recompute_exports (map fst id_alist)

    where failDups str a b = error (Msg.found_duplicates ("computing " ++ str) a b)
{-|
  ???
-}
augmentGlobalEnv :: GlobalE -> [Identifier] -> GlobalE
augmentGlobalEnv globalEnv new_identifiers
    = let all_identifiers        = allIdentifiers globalEnv
          tmp                    = partition (`elem` all_identifiers) new_identifiers
          updated_identifiers    = fst tmp
          really_new_identifiers = snd tmp
          env1 = makeGlobalEnv (const []) (const True) really_new_identifiers
          env2 = updateGlobalEnv (\qn@(QualName mID _) 
                                      -> let old_ids = lookupIdentifiers_OrLose mID qn globalEnv
                                             new_ids = filter (\id -> qn == identifier2name id)
                                                              updated_identifiers
                                         in if null new_ids
                                            then old_ids 
                                            else old_ids ++ new_ids)
                      globalEnv
      in unionGlobalEnvs env2 env1
