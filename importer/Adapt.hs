{-  Author: Tobias C. Rittweiler and Florian Haftmann, TU Muenchen

Adaption tables and their application
-}

module Importer.Adapt(Adaption(..), AdaptionTable(AdaptionTable),
  readAdapt, makeAdaptionTable_FromHsModule, extractHskEntries,
  adaptGlobalEnv, adaptIsaUnit
) where

import Importer.Library
import Data.Maybe (mapMaybe, fromMaybe, catMaybes, isJust)
import List (partition, sort, group, intersperse)
import Control.Monad.State
import System.FilePath (combine)

import qualified Importer.Msg as Msg

import qualified Language.Haskell.Exts as Hsx
import Importer.Utilities.Hsk (extractBindingNs)
import qualified Importer.Isa as Isa
import qualified Importer.Utilities.Isa as Isa (nameOfTypeSign, prettyShow')
import qualified Importer.LexEnv as Env
import Importer.ConversionUnit (IsaUnit(IsaUnit))


{- Fundamental data structures -}

data RawClassInfo = RawClassInfo 
    { superclasses :: [String],
      methods      :: [(String, String)],
      classVar     :: String
    }

data OpKind = Type 
            | Variable 
            | Function
            | RawHskOp          -- placeholder
            | UnaryOp Int 
            | InfixOp Assoc Int
            | Class RawClassInfo

data Assoc = RightAssoc | LeftAssoc | NoneAssoc

data AdaptionEntry = Haskell String OpKind
                   | Isabelle String OpKind

data Adaption = Adaption {
  rawAdaptionTable :: [(AdaptionEntry, AdaptionEntry)],
  reservedKeywords :: [String],
  usedConstNames :: [String],
  usedThyNames :: [String],
  preludeFile :: FilePath
}

data AdaptionTable = AdaptionTable [(Env.Identifier, Env.Identifier)]


{- Haskell Prelude data -}

hsk_infix_ops :: [(String, OpKind)]
hsk_infix_ops = [
  ("Prelude.(.)",  InfixOp RightAssoc 9),
  ("Prelude.(&&)", InfixOp LeftAssoc 3),
  ("Prelude.(||)", InfixOp LeftAssoc 2),
  ("Prelude.(:)",  InfixOp RightAssoc 5),
  ("Prelude.(++)", InfixOp RightAssoc 5),
  ("Prelude.(+)",  InfixOp LeftAssoc 6),
  ("Prelude.(*)",  InfixOp LeftAssoc 7),
  ("Prelude.(-)",  InfixOp LeftAssoc 6),
  ("Prelude.(==)", InfixOp NoneAssoc 4),
  ("Prelude.(<=)", InfixOp NoneAssoc 4),
  ("Prelude.(>=)", InfixOp NoneAssoc 4),
  ("Prelude.(<)",  InfixOp NoneAssoc 4),
  ("Prelude.(>)",  InfixOp NoneAssoc 4),
  ("Prelude.(!!)", InfixOp LeftAssoc 9)
  ]


{- Reading adaption file -}

readError :: forall a. FilePath -> String -> a
readError file msg =
  error ("An error occurred while reading adaption file \"" ++ file ++ "\": " ++ msg)

parseAdapt :: FilePath -> IO [Hsx.Decl]
parseAdapt file = do
  result <- Hsx.parseFile file
    `catch` (\ ioError -> readError file (show ioError))
  case result of
    Hsx.ParseFailed loc msg ->
      readError file (Msg.failed_parsing loc msg)
    Hsx.ParseOk (Hsx.Module _ _ _ _ _ _ decls) ->
      return decls

indexify :: [Hsx.Decl] -> [(String, Hsx.Exp)]
indexify decls = fold idxify decls [] where
  idxify (Hsx.PatBind _ (Hsx.PVar (Hsx.Ident name)) (Hsx.UnGuardedRhs rhs) _) xs =
      (name, rhs) : xs
  idxify _ xs = xs

evaluateString :: Hsx.Exp -> String
evaluateString (Hsx.Lit (Hsx.String s)) = s

evaluateList :: (Hsx.Exp -> a) -> Hsx.Exp -> [a]
evaluateList eval (Hsx.List ts) = map eval ts

evaluatePair :: (Hsx.Exp -> a) -> (Hsx.Exp -> b) -> Hsx.Exp -> (a, b)
evaluatePair eval1 eval2 (Hsx.Tuple [t1, t2]) = (eval1 t1, eval2 t2)

evaluateEntryClass :: Hsx.Exp -> RawClassInfo
evaluateEntryClass (Hsx.Paren (Hsx.RecConstr (Hsx.UnQual (Hsx.Ident "RawClassInfo"))
  [Hsx.FieldUpdate (Hsx.UnQual (Hsx.Ident "superclasses")) superclasses,
    Hsx.FieldUpdate (Hsx.UnQual (Hsx.Ident "classVar")) classVar,
      Hsx.FieldUpdate (Hsx.UnQual (Hsx.Ident "methods")) methods])) =
  RawClassInfo {
    superclasses = evaluateList evaluateString superclasses,
    classVar = evaluateString classVar,
    methods = evaluateList (evaluatePair evaluateString evaluateString) methods }

evaluateEntryKind :: Hsx.Exp -> OpKind
evaluateEntryKind (Hsx.Paren (Hsx.App (Hsx.Con (Hsx.UnQual (Hsx.Ident "Class"))) cls)) =
  Class (evaluateEntryClass cls)
evaluateEntryKind (Hsx.Con (Hsx.UnQual (Hsx.Ident "Type"))) = Type
evaluateEntryKind (Hsx.Con (Hsx.UnQual (Hsx.Ident "Function"))) = Function
evaluateEntryKind (Hsx.Paren (Hsx.App (Hsx.App (Hsx.Con (Hsx.UnQual (Hsx.Ident "InfixOp")))
  (Hsx.Con (Hsx.UnQual (Hsx.Ident assc)))) (Hsx.Lit (Hsx.Int pri)))) =
    InfixOp assoc (fromInteger pri) where
    assoc = case assc of
      "LeftAssoc" -> LeftAssoc
      "RightAssoc" -> RightAssoc
      "NoneAssoc" -> NoneAssoc

evaluateEntry :: Hsx.Exp -> AdaptionEntry
evaluateEntry (Hsx.App (Hsx.App (Hsx.Con (Hsx.UnQual (Hsx.Ident kind))) (Hsx.Lit (Hsx.String name))) entry)
  | (kind == "Haskell") = Haskell name (evaluateEntryKind entry)
  | (kind == "Isabelle") = Isabelle name (evaluateEntryKind entry)

evaluate dir decls = Adaption {
  rawAdaptionTable = evaluateList (evaluatePair evaluateEntry evaluateEntry)
    (lookupFunbind "raw_adaption_table"),
  reservedKeywords = lookupStringList "reserved_keywords",
  usedConstNames = lookupStringList "used_const_names",
  usedThyNames = lookupStringList "used_thy_names",
  preludeFile = combine dir "Prelude.thy" } where
    lookupFunbind name = case lookup name decls of
      Nothing -> error ("No entry for " ++ name ++ " in adaption file")
      Just rhs -> rhs
    lookupStringList name = evaluateList evaluateString (lookupFunbind name)

readAdapt :: FilePath -> IO Adaption
readAdapt dir = do
  decls <- parseAdapt (combine dir "Raw.hs")
  return (evaluate dir (indexify decls))


{- Building adaption table -}

mkAdaptionTable :: Adaption -> AdaptionTable
mkAdaptionTable adapt = AdaptionTable 
  $ map (\(hEntry, iEntry) -> (parseEntry hEntry, parseEntry iEntry))
      (check_raw_adaption_table (rawAdaptionTable adapt))

extractHskEntries (AdaptionTable mapping) = map fst mapping
extractIsaEntries (AdaptionTable mapping) = map snd mapping

-- Our predefined `adaptionTable' contains entries for all things that
-- may possibly get adapted; a haskell source file may, however, define
-- their own variants of the Prelude stuff (e.g. define its own `map'.)
-- 
-- Hence, we have to remove entries from `adaptionTable' which are
-- defined in one of the source files.
makeAdaptionTable_FromHsModule :: Adaption -> Env.GlobalE -> [Hsx.Module] -> AdaptionTable
makeAdaptionTable_FromHsModule adapt env hsmodules = let
  adaptionTable = mkAdaptionTable adapt
  initial_class_env = makeGlobalEnv_FromAdaptionTable
    (filterAdaptionTable (Env.isClass . fst) adaptionTable)
  tmp_env = Env.unionGlobalEnvs initial_class_env env
  defined_names = concatMap (extractDefNames tmp_env) hsmodules
  extractDefNames :: Env.GlobalE -> Hsx.Module -> [String]
  extractDefNames globalEnv (Hsx.Module _ m _ _ _ _ decls) =
    mapMaybe (\n -> let m'   = Env.fromHsk m
                        n'   = Env.fromHsk n
                        ids  = Env.lookupIdentifiers_OrLose m' n' globalEnv
                        name = Env.nameOf . Env.lexInfoOf
                    in  case filter Env.isType ids of
                                []                       -> Just $ name (head ids)
                                [id] | Env.isInstance id -> Just $ name id
                                     | otherwise         -> Nothing)
              $ concatMap extractBindingNs decls
  in filterAdaptionTable (\(from, to) -> let
    fromN = Env.nameOf (Env.lexInfoOf from)
    toN = Env.nameOf (Env.lexInfoOf to)
    in fromN `notElem` defined_names && toN `notElem` defined_names) adaptionTable
  
makeGlobalEnv_FromAdaptionTable :: AdaptionTable -> Env.GlobalE
makeGlobalEnv_FromAdaptionTable adaptionTable
    = Env.makeGlobalEnv importNothing exportAll (extractHskEntries adaptionTable)
    where importNothing = const []
          exportAll     = const True

filterAdaptionTable :: ((Env.Identifier, Env.Identifier) -> Bool) -> AdaptionTable -> AdaptionTable
filterAdaptionTable predicate (AdaptionTable entries)
    = AdaptionTable (filter predicate entries)


-- Check the Raw Adaption Table for consistency; prohibit duplicate
-- entries, and ensure that class methods have their own entry as
-- function or op.
--
check_raw_adaption_table :: [(AdaptionEntry, AdaptionEntry)] -> [(AdaptionEntry, AdaptionEntry)]
check_raw_adaption_table tbl
    = let (hsk_entries, _)   = unzip tbl
          names              = [ n | Haskell n _ <- hsk_entries ]
          methods            = concatMap (\(Haskell _ (Class (RawClassInfo { methods = m }))) -> fst (unzip m))
                                 $ filter isClassEntry hsk_entries
          functions          = extract_functionoid_names hsk_entries
          missing_fn_entries = filter (`notElem` functions) methods
      in 
        if (has_duplicates names)
        then error ("Duplicates in Raw Adaption Table found: "
                    ++ show (filter (flip (>) 1 . length) (group (sort names))))
        else if not (null missing_fn_entries)
             then error ("Inconsistency in Raw Adaption Table: The following methods\n" 
                         ++ "don't have a Function entry: " ++ show missing_fn_entries)
             else tbl
                 
    where
      extract_functionoid_names [] = []
      extract_functionoid_names (e:rest_entries)
          = case e of
              Haskell n Function      -> n : extract_functionoid_names rest_entries
              Haskell n RawHskOp      -> n : extract_functionoid_names rest_entries
              Haskell n (UnaryOp _)   -> n : extract_functionoid_names rest_entries
              Haskell n (InfixOp _ _) -> n : extract_functionoid_names rest_entries
              _                       -> extract_functionoid_names rest_entries

      isClassEntry (Haskell _ (Class _))   = True
      isClassEntry _                       = False

parseEntry :: AdaptionEntry -> Env.Identifier

parseEntry (Haskell raw_identifier op)
    = let (moduleID, identifierID) = parseRawIdentifier raw_identifier
          op' = (case op of Function -> fromMaybe Function (lookup raw_identifier hsk_infix_ops)
                            etc      -> etc)
      in makeIdentifier op' moduleID identifierID Env.EnvTyNone
parseEntry (Isabelle raw_identifier op)
    -- the raw identifier may look like "Datatype.option.None", where
    -- "Datatype" is the ModuleID, and "None" is the real identifier,
    -- and "option" basically noisy garbage.
    = let (moduleID, identifierID) = parseRawIdentifier raw_identifier
          moduleID'                = (case wordsBy (== '.') moduleID of 
                                        []  -> moduleID
                                        m:_ -> m)
      in makeIdentifier op moduleID' identifierID Env.EnvTyNone

parseRawIdentifier :: String -> (String, String)
parseRawIdentifier string
    = if '(' `elem` string 
      then let (modul, identifier) = break (== '(') string -- "Prelude.(:)"
           in assert (last modul == '.' && 
                      last identifier == ')') 
                 $ (init modul, tail (init identifier))
      else let parts      = wordsBy (== '.') string
               identifier = last parts
               modul      = concat $ intersperse "." (init parts)
           in (modul, identifier)

makeIdentifier :: OpKind -> Env.ModuleID -> Env.IdentifierID -> Env.EnvType -> Env.Identifier
makeIdentifier Variable m identifier t
    = Env.Constant $ Env.Variable $ Env.makeLexInfo m identifier t
makeIdentifier Function m identifier t
    = Env.Constant $ Env.Function $ Env.makeLexInfo m identifier t
makeIdentifier (UnaryOp prio) m identifier t
    = Env.Constant $ Env.UnaryOp (Env.makeLexInfo m identifier t) prio
makeIdentifier (InfixOp assoc prio) m identifier t
    = Env.Constant $ Env.InfixOp (Env.makeLexInfo m identifier t) (transformAssoc assoc) prio
makeIdentifier (Class classinfo) m identifier t
    = let supers  = map (Env.EnvUnqualName . snd . parseRawIdentifier) (superclasses classinfo)
          meths   = map (\(n, tstr) -> let t = Env.fromHsk (parseType tstr)
                                       in makeTypeAnnot (Env.makeLexInfo m n t))
                        (methods classinfo)
          classV  = Env.EnvUnqualName (classVar classinfo)
      in 
        Env.Type $ Env.Class (Env.makeLexInfo m identifier t)
                             (Env.makeClassInfo supers meths classV)
makeIdentifier Type m identifier t
    = Env.Type $ Env.Data (Env.makeLexInfo m identifier t) []

makeTypeAnnot :: Env.LexInfo -> Env.Identifier
makeTypeAnnot lexinfo = Env.Constant (Env.TypeAnnotation lexinfo)

parseType :: String -> Hsx.Type
parseType string
    = let (Hsx.ParseOk (Hsx.Module _ _ _ _ _ _ [Hsx.TypeSig _ _ t])) 
              = Hsx.parseFileContents ("__foo__ :: " ++ string)
      in t

transformAssoc :: Assoc -> Env.EnvAssoc
transformAssoc RightAssoc = Env.EnvAssocRight
transformAssoc LeftAssoc  = Env.EnvAssocLeft
transformAssoc NoneAssoc  = Env.EnvAssocNone


{- Applying adaptions -}

data AdptState = AdptState { oldGlobalEnv     :: Env.GlobalE,
                             adaptedGlobalEnv :: Env.GlobalE,
                             adaptionTable    :: AdaptionTable,
                             currentModuleID  :: Maybe Env.ModuleID
                           }

type AdaptM v = State AdptState v

getAdptState :: AdaptM AdptState
getAdptState = do s <- get; return s

query :: (AdptState -> x) -> AdaptM x
query slot = do s <- getAdptState; return (slot s)

set :: (AdptState -> AdptState) -> AdaptM ()
set update = do s <- getAdptState; put (update s); return ()

shadow :: [Env.EnvName] -> AdaptM ()
shadow names
    = set (\state 
               -> let (AdaptionTable mappings) = adaptionTable state 
                      -- Functions (especially data constructors, like []) can't
                      -- be locally bound, so we must not shadow them.
                      (fun_mappings, rest_mappings)
                          = partition (\(id,_) -> Env.isInfixOp id || Env.isFunction id ) 
                              mappings
                  in state { adaptionTable 
                                 = AdaptionTable $ 
                                     fun_mappings ++
                                     filter ((`notElem` names) . Env.identifier2name . fst) 
                                        rest_mappings
                           })
   
-- shadowing [a, b, c] $ body
--   with appropriate a, b, c.      
--
-- Inside `body', do not adapt names `a', `b', and `c'.
--
shadowing :: [Isa.Name] -> AdaptM v -> AdaptM v
shadowing names body
    = do old_tbl <- query adaptionTable
         shadow (map Env.fromIsa names)
         r <- body
         set (\state -> state { adaptionTable = old_tbl })
         return r

-- nested_binding [(a, computeA), (b, computeB), (c, computeC)] $
--   \([a', b', c']) -> body
--
--     with appropriate a, b, c 
-- and with a', b', c' being the results of computeA, computeB, computeC.
--
-- LET like binding construct: while computing `computeB', `a' is shadowed,
-- while computing `computeC', `a' and `b' are shadowed, and so on.
--
-- Inside `body', the identifiers `a', `b' and `c' won't be adapted..
-- 
nested_binding :: [([Isa.Name], AdaptM b)] -> ([b] -> AdaptM v) -> AdaptM v
nested_binding [] continuation = continuation []
nested_binding bindings continuation
    = do old_tbl <- query adaptionTable
         rs      <- foldM (\result (ns,thunk) -> let ns' = map Env.fromIsa ns in
                                                 do shadow ns' ; t <- thunk
                                                    return (result ++ [t])) 
                    [] bindings
         r       <- continuation rs
         set (\state -> state { adaptionTable = old_tbl })
         return r
                         

runAdaptionWith :: AdaptM v -> AdptState -> v
runAdaptionWith adaption state
    = evalState adaption state

runAdaption :: Env.GlobalE -> Env.GlobalE -> AdaptionTable -> AdaptM v -> v
runAdaption oldEnv newEnv tbl adaption 
    = runAdaptionWith adaption (AdptState { oldGlobalEnv     = oldEnv,
                                            adaptedGlobalEnv = newEnv,
                                            adaptionTable    = tbl,
                                            currentModuleID  = Nothing 
                                          })


qualifyConstantName :: Env.GlobalE -> Env.ModuleID -> Env.EnvName -> Env.EnvName
qualifyConstantName globalEnv mID name
    = fromMaybe (Env.qualifyEnvName mID name)
        $ Env.resolveConstantName globalEnv mID name

qualifyTypeName :: Env.GlobalE -> Env.ModuleID -> Env.EnvName -> Env.EnvName
qualifyTypeName globalEnv mID name
    = fromMaybe (Env.qualifyEnvName mID name)
        $ Env.resolveTypeName globalEnv mID name


adaptGlobalEnv :: AdaptionTable -> Env.GlobalE -> Env.GlobalE
adaptGlobalEnv tbl env
    = Env.updateGlobalEnv 
        (\n -> case translateName tbl n of 
                 Just new_id -> [new_id]
                 Nothing     -> adapt_type_in_identifier env tbl n)
        env

translateName :: AdaptionTable -> Env.EnvName -> Maybe Env.Identifier
translateName (AdaptionTable mappings) name =
  lookupBy (\n1 id2 -> n1 == Env.identifier2name id2) name mappings where
    lookupBy                :: (a -> b -> Bool) -> a -> [(b, c)] -> Maybe c
    lookupBy eq key []      =  Nothing
    lookupBy eq key ((x,y):xys)
        | key `eq` x        =  Just y
        | otherwise         =  lookupBy eq key xys


translateIdentifier :: AdaptionTable -> Env.Identifier -> Env.Identifier
translateIdentifier tbl id
    = case translateName tbl (Env.identifier2name id) of
        Nothing     -> id
        Just new_id -> new_id

adapt_type_in_identifier :: Env.GlobalE -> AdaptionTable -> Env.EnvName -> [Env.Identifier]
adapt_type_in_identifier globalEnv tbl n@(Env.EnvQualName mID _)
    = let old_ids      = Env.lookupIdentifiers_OrLose mID n globalEnv
          old_lexinfos = map Env.lexInfoOf old_ids
          old_types    = map Env.typeOf old_lexinfos
          new_types    = catMaybes (zipWith translate old_types old_lexinfos)
          new_lexinfos = zipWith (\t lxinf -> lxinf {Env.typeOf = t}) new_types old_lexinfos
      in 
        zipWith Env.updateIdentifier old_ids new_lexinfos
    where 
      translate typ lexinfo
          = translateEnvType tbl (qualifyTypeName globalEnv (Env.moduleOf lexinfo)) typ

translateEnvType :: AdaptionTable -> (Env.EnvName -> Env.EnvName) -> Env.EnvType -> Maybe Env.EnvType
translateEnvType (AdaptionTable mappings) qualify typ
    = let type_renams   = filter (Env.isData . fst) mappings
          type_renams'  = assert (all (Env.isData . snd) type_renams) 
                            $ map (\(t1,t2) -> (Env.identifier2name t1, Env.identifier2name t2)) 
                                  type_renams
          class_renams  = filter (Env.isClass . fst) mappings
          class_renams' = assert (all (Env.isClass . snd) class_renams)
                            $ map (\(c1,c2) -> (Env.identifier2name c1, Env.identifier2name c2))
                                  class_renams
          renamings     = type_renams' ++ class_renams'
      in 
        case runState (translate renamings typ) False of
          (_, False)       -> Nothing        -- no match found in AdaptionTable. 
          (new_type, True) -> Just new_type
    where 
      translate :: [(Env.EnvName, Env.EnvName)] -> Env.EnvType -> State Bool Env.EnvType
      translate alist typ
          = let transl n = case lookup (qualify n) alist of
                             Nothing -> return n
                             Just n' -> do put True; return n'
                in case typ of 
                     Env.EnvTyNone      -> return Env.EnvTyNone
                     Env.EnvTyVar n     -> transl n >>= (return . Env.EnvTyVar)
                     Env.EnvTyCon n ts  -> do n'  <- transl n
                                              ts' <- mapM (translate alist) ts
                                              return (Env.EnvTyCon n' ts')
                     Env.EnvTyFun t1 t2 -> do t1' <- translate alist t1
                                              t2' <- translate alist t2
                                              return (Env.EnvTyFun t1' t2')
                     Env.EnvTyTuple ts  -> do ts' <- mapM (translate alist) ts
                                              return (Env.EnvTyTuple ts')
                     Env.EnvTyScheme ctx t
                        -> do let (tyvarNs, classNss) = unzip ctx
                              tyvarNs'  <- mapM transl tyvarNs
                              classNss' <- mapM (mapM transl) classNss
                              t'        <- translate alist t
                              let ctx'   = zip tyvarNs' classNss'
                              return (Env.EnvTyScheme ctx' t')

adaptEnvName :: Env.EnvName -> AdaptM Env.EnvName
adaptEnvName n 
    = do Just mID <- query currentModuleID
         tbl      <- query adaptionTable
         oldEnv   <- query oldGlobalEnv
         newEnv   <- query adaptedGlobalEnv
         case Env.lookupConstant mID n oldEnv of
           Nothing -> return n
           Just id -> let new_id       = translateIdentifier tbl id
                          new_id_name  = Env.identifier2name new_id
                      in assert (isJust (Env.lookupConstant mID new_id_name newEnv))
                           $ return new_id_name

adaptEnvType :: Env.EnvType -> AdaptM Env.EnvType
adaptEnvType t
    = do Just mID <- query currentModuleID
         tbl      <- query adaptionTable
         oldEnv   <- query oldGlobalEnv
         let qualify n = qualifyTypeName oldEnv mID n
         return (fromMaybe t (translateEnvType tbl qualify t))

adaptName :: Isa.Name -> AdaptM Isa.Name
adaptName n = do
  n' <- adaptEnvName (Env.fromIsa n)
  return (Env.toIsa n')

adaptType :: Isa.Type -> AdaptM Isa.Type
adaptType t = do t' <- adaptEnvType (Env.fromIsa t); return (Env.toIsa t')

adaptClass :: Isa.Name -> AdaptM Isa.Name
adaptClass classN = do let ignore = Isa.Name "_"
                       t <- adaptType (Isa.TyScheme [(ignore, [classN])] Isa.NoType)
                       let (Isa.TyScheme [(_, [classN'])] _) = t
                       return classN'

adaptModules ::  AdaptionTable  -> Env.GlobalE -> Env.GlobalE -> [Isa.Module] -> [Isa.Module]
adaptModules adaptionTable adaptedGlobalEnv globalEnv modules =
  runAdaption globalEnv adaptedGlobalEnv adaptionTable (mapM adapt modules)

adaptIsaUnit :: AdaptionTable -> Env.GlobalE -> IsaUnit -> IsaUnit
adaptIsaUnit adaptionTable globalEnv (IsaUnit modules custThys adaptedGlobalEnv) =
  IsaUnit (adaptModules adaptionTable adaptedGlobalEnv globalEnv modules) custThys adaptedGlobalEnv


not_implemented x = error ("Adaption not implemented yet for\n  " ++ Isa.prettyShow' "thing" x) 

class Adapt a where
    adapt  :: a -> AdaptM a

instance Adapt Isa.Module where

    adapt (Isa.Module thy imps cmds)
        = do old_mID <- query currentModuleID
             set (setModuleID $ Just (Env.fromIsa thy))
             cmds' <- mapM adapt cmds
             set (setModuleID old_mID)
             return (Isa.Module thy imps cmds')
        where setModuleID v state
                  = state { currentModuleID = v }

instance Adapt Isa.Stmt where

    adapt (Isa.TypeSynonym aliases) = liftM Isa.TypeSynonym (mapM adpt aliases)
        where adpt (spec,typ) = liftM2 (,) (return spec) (adaptType typ)
    adapt c@(Isa.Record _ _)      = not_implemented c
    adapt c@(Isa.Comment _)          = return c

    adapt (Isa.Datatype decls) = liftM Isa.Datatype $ mapM adaptDecls decls where
      adaptDecls ((sig @ (Isa.TypeSpec tyvarNs tycoN), constrs)) = shadowing (tycoN : tyvarNs) $
        do constrs' <- mapM adaptConstr constrs
           return (sig, constrs')
      adaptConstr (name, types) =
        do types' <- mapM adaptType types
           return (name, types')

    adapt (Isa.Fun typesigs permissive defs)
        = do typesigs' <- mapM adapt typesigs
             let funNs = map Isa.nameOfTypeSign (typesigs ++ typesigs')
             shadowing (map Isa.nameOfTypeSign typesigs) $
               do defs' <- mapM (\(funN, pats, body)
                                     -> do funN' <- adaptName funN
                                           assert (funN `elem` funNs) $ return ()
                                           pats' <- mapM adapt pats
                                           shadowing (concatMap extractNames pats') $
                                             do body' <- adapt body ; return (funN', pats', body'))
                                defs
                  return (Isa.Fun typesigs' permissive defs')
         
    adapt (Isa.Primrec typesigs defs)
        = do typesigs' <- mapM adapt typesigs
             let funNs = map Isa.nameOfTypeSign (typesigs ++ typesigs')
             shadowing (map Isa.nameOfTypeSign typesigs) $
               do defs' <- mapM (\(funN, pats, body)
                                     -> do funN' <- adaptName funN
                                           assert (funN `elem` funNs) $ return ()
                                           pats' <- mapM adapt pats
                                           shadowing (concatMap extractNames pats') $
                                             do body' <- adapt body ; return (funN', pats', body'))
                                defs
                  return (Isa.Primrec typesigs' defs')

    adapt (Isa.Definition typesig (pat, term))
        = do typesig' <- adapt typesig
             shadowing (extractNames pat) $
               do term' <- adapt term ; return (Isa.Definition typesig' (pat, term'))

    adapt (Isa.Class classN supclassNs typesigs)
        = do classN'     <- adaptClass classN
             supclassNs' <- mapM adaptClass supclassNs
             typesigs'   <- mapM adapt typesigs
             return (Isa.Class classN' supclassNs' typesigs')

    adapt (Isa.Instance classN typ cmds)
        = do classN' <- adaptClass classN
             shadowing [classN'] $ do typ'  <- adaptType typ
                                      cmds' <- mapM adapt cmds
                                      return (Isa.Instance classN' typ' cmds')

instance Adapt Isa.TypeSpec where
    adapt (Isa.TypeSpec tyvarNs tycoN)
        = do (Isa.Type tycoN' tyvars') <- adaptType (Isa.Type tycoN (map Isa.TVar tyvarNs))
             return $ Isa.TypeSpec (map (\(Isa.TVar n) -> n) tyvars') tycoN'

instance Adapt Isa.TypeSign where
    adapt (Isa.TypeSign n t) = do
      n' <- adaptName n
      t' <- adaptType t
      return (Isa.TypeSign n' t')

instance Adapt Isa.Term where
    adapt (Isa.Literal lit)     = return (Isa.Literal lit)

    adapt (Isa.Const n)           = adaptConst n >>= (return . Isa.Const)
      where
        adaptConst n = do
          n' <- adaptEnvName (Env.fromIsa n)
          return (Env.toIsa n')

    adapt (Isa.Parenthesized t) = adapt t     >>= (return . Isa.Parenthesized)

    adapt (Isa.App t1 t2)       = do Just mID <- query currentModuleID
                                     oldEnv   <- query oldGlobalEnv
                                     newEnv   <- query adaptedGlobalEnv
                                     t1'      <- adapt t1 
                                     t2'      <- adapt t2
                                     -- t1 may have been an InfixOp and was adapted to
                                     -- a function. In this case, we have to make sure that
                                     -- all the arguments passed to this function are 
                                     -- parenthesized.
                                     let n1   = find_applied_op t1
                                     let n1'  = find_applied_op t1'
                                     case (n1, n1') of 
                                       (Just n1, Just n1')
                                           -> if isInfixOp mID n1 oldEnv && not (isInfixOp mID n1' newEnv)
                                              then return $ Isa.App t1' (Isa.Parenthesized t2')
                                              else return $ Isa.App t1' t2'
                                       _   -> return (Isa.App t1' t2')
        where isInfixOp mID n env
                  = case Env.lookupConstant mID (Env.fromIsa n) env of
                      Nothing -> False
                      Just c  -> Env.isInfixOp c
              find_applied_op :: Isa.Term -> Maybe Isa.Name
              find_applied_op t 
                  = case t of
                      Isa.Const n            -> Just n
                      Isa.App t1 t2        -> find_applied_op t1
                      Isa.Parenthesized t' -> find_applied_op t'
                      _                    -> Nothing -- the remaining cases are 
                                                      -- too complicated, so we give up.

    adapt (Isa.If c t e)        = do c' <- adapt c ; t' <- adapt t ; e' <- adapt e
                                     return (Isa.If c' t' e')

    adapt (Isa.Abs boundN body)
        = shadowing [boundN] $
            adapt body >>= (return . Isa.Abs boundN)

    adapt (Isa.Let bindings body)
        = do pats' <- mapM adapt (map fst bindings)
             nested_binding (zipWith (\p' t -> (extractNames p', adapt t))
                                     pats' (map snd bindings)) $
               \terms' -> do body' <- adapt body
                             return (Isa.Let (zip pats' terms') body')

    adapt (Isa.Case term patterns)
        = do term'     <- adapt term
             patterns' <- mapM (\(pat, body) 
                                    -> do pat' <- adapt pat
                                          shadowing (extractNames pat') $
                                            do body' <- adapt body
                                               return (pat', body'))
                               patterns
             return (Isa.Case term' patterns')

    adapt (Isa.ListCompr body stmts) = adpt body stmts []
      where 
        adpt e [] stmts' = do e' <- adapt e; return (Isa.ListCompr e' (reverse stmts'))
        adpt e (Isa.Guard b : rest) stmts'
            = adapt b >>= (\b' -> adpt e rest (Isa.Guard b':stmts'))
        adpt e (Isa.Generator (pat, exp) : rest) stmts'
            = do pat' <- adapt pat
                 exp' <- adapt exp
                 shadowing (extractNames pat') $ 
                   adpt e rest (Isa.Generator (pat', exp') : stmts')
    adapt (Isa.DoBlock pre stmts post) = 
        do stmts' <- mapM adapt stmts
           return $ Isa.DoBlock pre stmts' post

instance Adapt Isa.DoBlockFragment where
    adapt (Isa.DoGenerator pat exp) = liftM2 Isa.DoGenerator (adapt pat) (adapt exp)
    adapt (Isa.DoQualifier exp) = liftM Isa.DoQualifier $ adapt exp

               
extractNames :: Isa.Term -> [Isa.Name]
extractNames (Isa.Const n)                   = [n]
extractNames (Isa.App t1 t2)               = extractNames t1 ++ extractNames t2
extractNames etc = []
