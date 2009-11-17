{-# LANGUAGE 
  MultiParamTypeClasses,
  FunctionalDependencies,
  FlexibleContexts,
  FlexibleInstances,
  TypeSynonymInstances,
  GeneralizedNewtypeDeriving #-}

{-| Author: Tobias C. Rittweiler, TU Muenchen

Conversion from abstract Haskell code to abstract Isar/HOL theory.
-}

module Importer.Convert (convertHskUnit) where

import Data.List (nub, unzip4, partition)
import Maybe
import qualified Data.Map as Map

import Control.Monad
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State

import Importer.Library
import qualified Importer.AList as AList

import Importer.Utilities.Hsk
import Importer.Utilities.Gensym
import Importer.Preprocess
import Importer.ConversionUnit (HskUnit(..), IsaUnit(..))
import Importer.DeclDependencyGraph

import Importer.Adapt (makeAdaptionTable_FromHsModule, extractHskEntries,
  AdaptionTable, adaptGlobalEnv, adaptIsaUnit, Adaption(..))

import qualified Language.Haskell.Exts as Hsx

import qualified Importer.Isa as Isa
import qualified Importer.Utilities.Isa as Isa (nameOfTypeSign, prettyShow, prettyShow')

import qualified Importer.Msg as Msg
import qualified Importer.Env as Env

import Importer.Configuration hiding (getMonadInstance)
import qualified Importer.Configuration as Config (getMonadInstance)


{-|
  This is the main function of the conversion process; converts a Unit of Haskell
  ASTs into a Unit of Isar/HOL ASTs.
-}
convertHskUnit :: Customisations -> Adaption -> HskUnit -> (AdaptionTable, IsaUnit)
convertHskUnit custs adapt (HskUnit hsmodules custMods initialGlobalEnv)
    = let pragmass       = map (accumulate (fold add_pragmas) . decls_of) hsmodules
          hsmodules'     = map (preprocessModule (usedConstNames adapt)) hsmodules
          env            = Env.environmentOf custs hsmodules' custMods
          adaptionTable  = makeAdaptionTable_FromHsModule adapt env hsmodules'
          initial_env    = Env.augmentGlobalEnv initialGlobalEnv $ extractHskEntries adaptionTable
          global_env_hsk = Env.unionGlobalEnvs env initial_env
                             
          hskmodules = map (toHskModule global_env_hsk) hsmodules'
          
          isathys = fst $ runConversion custs adapt global_env_hsk $
            mapM convertModule (zip pragmass hskmodules)
          custThys = Map.elems custMods
          adaptedEnv = adaptGlobalEnv adaptionTable global_env_hsk
          isaunit = IsaUnit isathys custThys adaptedEnv
      in
        (adaptionTable, adaptIsaUnit adaptionTable global_env_hsk isaunit)
    where 
      decls_of :: Hsx.Module -> [Hsx.Decl]
      decls_of (Hsx.Module _ _ _ _ _ _ decls) = decls
      toHskModule :: Env.GlobalE -> Hsx.Module -> HskModule
      toHskModule globalEnv (Hsx.Module loc modul _ _ _ _ decls) =
        HskModule loc modul ((map HskDependentDecls . arrangeDecls globalEnv modul) decls)

type Pragma = (String, [String])

permissive_pragma = "permissive"

pragmas :: [String]
pragmas = [permissive_pragma]

add_pragmas :: Hsx.Decl -> [Pragma] -> [Pragma]
add_pragmas (Hsx.UnknownDeclPragma src "HASKABELLE" pragma) =
  if null pragma then error ("empty pragma encountered at " ++ srcloc2string src)
  else let
    directive : args = words pragma
  in if directive `elem` pragmas
  then AList.map_default (directive, []) (fold insert args)
  else error ("unknown pragma " ++ directive ++ " encountered at " ++ srcloc2string src)
add_pragmas _ = id


-- The naming scheme "HsFoo" is treated as being owned by the parser
-- libary Language.Haskell.Exts. We use "HskFoo" instead to
-- differentiate between what's defined by us and by that library. 
--
-- (Ok, this might sound somewhat confusing, at least we're consistent
-- about it.)

data HskModule = HskModule Hsx.SrcLoc Hsx.ModuleName [HskDependentDecls]
  deriving Show

{-|
  This data structure is supposed to collect function declarations
  that depend mutually recursive on each other.
-}
newtype HskDependentDecls = HskDependentDecls [Hsx.Decl]
  deriving Show

{-|
  ???
-}
data Context = Context {
  _theory :: Isa.ThyName,
  _globalEnv :: Env.GlobalE,
  _warnings :: [Warning],
  _backtrace :: [String],
  _adapt :: Adaption,
  _monad :: Maybe MonadInstance }

initContext adapt env = Context {
  _theory = Isa.ThyName "Scratch", {- FIXME: Default Hsx.ModuleName in Haskell
    is called `Main'; clashes with Isabelle. -}
  _globalEnv = env,
  _warnings = [],
  _backtrace = [],
  _adapt = adapt,
  _monad = Nothing }

{-|
  Instead of accessing a record directly by their `_foo' slots, we
  use the respective `foo' surrogate which consists of an appropriate
  getter and setter -- which allows functions to both query and
  update a record by slot name.
-}
type FieldSurrogate field = (Context -> field, Context -> field -> Context) 

theory :: FieldSurrogate Isa.ThyName
theory      = (_theory,      \c f -> c { _theory      = f })
globalEnv :: FieldSurrogate Env.GlobalE
globalEnv   = (_globalEnv,   \c f -> c { _globalEnv   = f })
warnings :: FieldSurrogate [Warning]
warnings    = (_warnings,    \c f -> c { _warnings    = f })
backtrace :: FieldSurrogate [String]
backtrace   = (_backtrace,   \c f -> c { _backtrace   = f })
adapt :: FieldSurrogate Adaption
adapt       = (_adapt,       \c f -> c { _adapt       = f })
monad     :: FieldSurrogate (Maybe MonadInstance)
monad       = (_monad,       \c f -> c { _monad       = f })

currentModule :: FieldSurrogate Hsx.ModuleName
currentModule = (\c -> let (Isa.ThyName n) = _theory c in Hsx.ModuleName n, \c f -> c)

getMonadInstance :: String -> ContextM (Maybe MonadInstance)
getMonadInstance name = ask >>= (return . flip Config.getMonadInstance name)

getMonadInstance' :: Hsx.Type -> ContextM (Maybe MonadInstance)
getMonadInstance' ty =
    case typeConName . returnType $ ty of
      Nothing -> return Nothing
      Just name -> getMonadInstance name

withFunctionType :: Hsx.Type -> ContextM a -> ContextM a
withFunctionType ty contextm = 
    do mbMon <- getMonadInstance' ty
       withUpdatedContext monad (const mbMon) contextm

withFunctionType' :: Maybe Hsx.Type -> ContextM a -> ContextM a
withFunctionType' mbTy contextm = 
    case mbTy of
      Nothing -> contextm
      Just ty -> withFunctionType ty contextm

withPossibleLift :: Hsx.Exp -> ContextM a -> ContextM a
withPossibleLift name contextm = 
    do mbMon <- queryContext monad
       case mbMon of
         Nothing -> contextm
         Just mon -> 
             case varName name >>= getMonadLift mon of
               Nothing -> contextm
               newMon@(Just _) ->
                   withUpdatedContext monad (const newMon) contextm
    where uname (Hsx.Qual _ n) = n
          uname (Hsx.UnQual n) = n
          sname (Hsx.Ident n) = n
          sname (Hsx.Symbol n) = n
          qname (Hsx.Var n) = Just n
          qname _ = Nothing
          varName = liftM sname . liftM uname . qname

getCurrentMonadFunction :: Hsx.QName -> ContextM Hsx.QName
getCurrentMonadFunction name =
    do mbMon <- queryContext monad
       case mbMon of
         Nothing -> return name
         Just mon -> 
             case name of
               Hsx.Qual mod uName -> return $ Hsx.Qual mod (lookup mon uName)
               Hsx.UnQual uName -> return $ Hsx.UnQual (lookup mon uName)
               def -> return def
       where lookup mon (Hsx.Ident name) = Hsx.Ident $ getMonadConstant mon name
             lookup mon (Hsx.Symbol name) = Hsx.Symbol $ getMonadConstant mon name

getCurrentMonadDoSyntax :: ContextM (Maybe DoSyntax)
getCurrentMonadDoSyntax =
    do mbMon <- queryContext monad
       case mbMon of 
         Nothing -> return Nothing
         Just mon -> return . Just $ getMonadDoSyntax mon
         

{-|
  The conversion process is done in this monad.
-}
newtype ContextM v = ContextM (ReaderT Customisations (StateT Context GensymM) v)
    deriving (Monad, MonadState Context, Functor, MonadReader Customisations)

queryCustomisations = ask

{-|
  This function lifts a gensym computation to a context computation
-}
liftGensym :: GensymM a -> ContextM a
liftGensym = ContextM . lift . lift

{-|
  This function executes the given conversion with the given environment as
  the context.
-}
runConversion :: Customisations -> Adaption -> Env.GlobalE -> ContextM v -> (v, Context)
runConversion custs adapt env (ContextM m) =
  evalGensym 0 $ runStateT (runReaderT m custs) (initContext adapt env)

{-|
  This function queries the given field in the context monad
-}
queryContext :: (FieldSurrogate field) -> ContextM field
queryContext (query, _)
    = do context <- get; return (query context) 

{-|
  This function updates the given field in the context monad using the given function.
-}
updateContext :: (FieldSurrogate field) -> (field -> field) -> ContextM ()
updateContext (query, update) updateField
    = do context <- get
         put (update context (updateField (query context)))
         return ()

{-|
  This function changes the given field in the given context monad using the given
  function. The original context is restored afterwards.
-}
withUpdatedContext :: (FieldSurrogate field) -> (field -> field) -> ContextM a -> ContextM a
withUpdatedContext surrogate updateField body
     = do oldval <- queryContext surrogate
          updateContext surrogate updateField
          result <- body
          updateContext surrogate (\_ -> oldval)
          return result

{-|
  This data structure is supposed to contain warning messages
-}
newtype Warning = Warning String
  deriving (Show, Eq, Ord)

{-|
  This function issues a warning in the current conversion monad.
-}
warn :: String -> ContextM ()
warn msg = updateContext warnings (\warnings -> warnings ++ [(Warning msg)])
     
{-|
  This function quits the conversion with an error providing the given error
  message.
-}
die :: String -> ContextM t
die msg 
    = do backtrace <- queryContext backtrace
         error $ msg ++ "\n\n"
                   ++ "Backtrace:\n"
                   ++ concat (map (++ "\n\n") (reverse backtrace))

{-|
  This function quits the conversion with an error providing the given error
  message and source location.
-}
dieWithLoc :: Hsx.SrcLoc -> String -> ContextM t
dieWithLoc loc msg 
    = do backtrace <- queryContext backtrace
         error $ srcloc2string loc ++ ": " ++ msg ++ "\n\n"
                   ++ "Backtrace:\n"
                   ++ concat (map (++ "\n\n") (reverse backtrace))
{-|
  This function quits the conversion with an error that is due to a
  pattern matching case that was observed but not anticipated. The object
  causing this and an a string describing the context has to be provided.
-}
pattern_match_exhausted :: (Show a) => String -> a -> ContextM t
pattern_match_exhausted str obj 
    = die (str ++ ": Pattern match exhausted for\n" ++ Isa.prettyShow obj)


          
{-|
  This function generates the auxiliary functions for the given Haskell
  data type declaration. This includes accessor functions and update functions
-}
generateRecordAux :: [Pragma] -> Hsx.Decl -> ContextM [Isa.Stmt]
generateRecordAux pragmas (Hsx.DataDecl _loc _kind _context tyconN tyvarNs condecls _deriving)
        = let strip (Hsx.QualConDecl _loc _FIXME _context decl) = decl
              decls = map strip condecls
          in do tyvars <- mapM (convert pragmas) tyvarNs
                let vs = map (rpair []) tyvars
                tycon <- convert pragmas tyconN
                let dataTy = Isa.Type tycon (map Isa.TVar tyvars)
                let fieldNames = concatMap extrFieldNames decls
                fields <- mapM (liftM fromJust . lookupIdentifier_Constant . Hsx.UnQual) (nub fieldNames)
                let funBinds = map (mkAFunBinds (length decls) vs dataTy) fields
                      ++ map (mkUFunBinds (length decls) vs dataTy) fields
                return funBinds
              where extrFieldNames (Hsx.RecDecl conName fields) = map fst $ flattenRecFields fields
                    extrFieldNames _ = []
                    mkAFunBinds numCon vs dty (Env.Constant (Env.Field Env.LexInfo{Env.nameOf=fname, Env.typschemeOf=(_, fty)} constrs)) =
                        let binds = map (mkAFunBind fname) constrs
                            fname' = Isa.Name fname
                            funTy = Isa.Func dty (Env.toIsa fty)
                        in Isa.Primrec [Isa.TypeSign fname' vs funTy] binds
                    mkAFunBind fname (Env.RecordConstr _ Env.LexInfo{Env.nameOf=cname} fields) =
                        let fname' = Isa.Name fname
                            con = Isa.Const $ Isa.Name cname
                            genArg (Env.RecordField n _)
                                | n == fname = Isa.Const (Isa.Name "x")
                                | otherwise = Isa.Const (Isa.Name "_")
                            conArgs = map genArg fields
                            pat = Isa.Parenthesized $ foldl Isa.App con conArgs
                            term = Isa.Const (Isa.Name "x")
                        in (fname', [pat], term)
                    mkUFunBinds numCon vs dty (Env.Constant (Env.Field Env.LexInfo{Env.nameOf=fname, Env.typschemeOf=(_, fty)} constrs)) =
                        let uname = "update_" ++ fname
                            binds = map (mkUFunBind fname uname) constrs
                            uname' = Isa.Name uname
                            funTy = Isa.Func (Env.toIsa fty) (Isa.Func dty dty)
                        in Isa.Primrec [Isa.TypeSign uname' vs funTy] binds
                    mkUFunBind fname uname (Env.RecordConstr _ Env.LexInfo{Env.nameOf=cname} fields) =
                        let uname' = Isa.Name uname
                            con = Isa.Const $ Isa.Name cname
                            genPatArg (i,(Env.RecordField n _))
                                | n == fname = Isa.Const (Isa.Name "_")
                                | otherwise = Isa.Const (Isa.Name ("f" ++ show i))
                            genTermArg (i,(Env.RecordField n _))
                                | n == fname = Isa.Const (Isa.Name "x")
                                | otherwise = Isa.Const (Isa.Name ("f" ++ show i))
                            patArgs = map genPatArg (zip [1..] fields)
                            termArgs = map genTermArg (zip [1..] fields)
                            pat = Isa.Parenthesized $ foldl Isa.App con patArgs
                            term = Isa.Parenthesized $ foldl Isa.App con termArgs
                            arg = Isa.Const (Isa.Name "x")
                        in (uname', [arg,pat], term)


{-|
  This function converts a Haskell data type declaration into a
  Isabelle data type definition .
-}
convertDataDecl :: [Pragma] -> Hsx.Decl -> ContextM (Isa.TypeSpec, [(Isa.Name, [Isa.Type])])
convertDataDecl pragmas (Hsx.DataDecl _loc _kind _context tyconN tyvarNs condecls _deriving)
    = let strip (Hsx.QualConDecl _loc _FIXME _context decl) = decl
          decls = map strip condecls
      in do tyvars <- mapM (convert pragmas) tyvarNs
            tycon  <- convert pragmas tyconN
            decls' <- mapM cnvt decls
            return $ (Isa.TypeSpec tyvars tycon, decls')
              where cnvt (Hsx.ConDecl name types)
                        = do name'  <- convert pragmas name
                             tyvars <- mapM (convert pragmas) types
                             return $ (name', tyvars)
                    cnvt (Hsx.RecDecl name fields) = 
                        let types = map snd (flattenRecFields fields)
                        in do name'  <- convert pragmas name
                              tyvars <- mapM (convert pragmas) types
                              return $ (name', tyvars)

{-|
  Instances of this class constitute pairs of types s.t. the first one
  (a Haskell entity) can be converted into the last one (an Isabelle entity).
  
  Instance declarations are supposed to implement 'convert'' instead of 
  'convert'. The latter uses the first by adding further boilerplate code.
-}
class Show a => Convert a b | a -> b where
    convert' :: [Pragma] -> Convert a b => a -> ContextM b
    convert  :: [Pragma] -> Convert a b => a -> ContextM b
    convert pragmas hsexpr = withUpdatedContext backtrace 
                       (\bt -> let frameName = "frame" ++ show (length bt)
                               in Isa.prettyShow' frameName hsexpr : bt)
                     $ convert' pragmas hsexpr

convertModule :: ([Pragma], HskModule) -> ContextM Isa.Module
convertModule (pragmas, HskModule _loc modul dependentDecls) =
  do
    thy <- convert pragmas modul
    env <- queryContext globalEnv
    adaption <- queryContext adapt
    custs <- queryCustomisations
    let imps = filter (not . isStandardTheory (usedThyNames adaption)) (lookupImports thy env custs)
    withUpdatedContext theory (\t -> assert (t == Isa.ThyName "Scratch") thy)
      $ do
          stmts <- mapsM (convertDependentDecls pragmas) dependentDecls
          return (Isa.retopologize (Isa.Module thy imps stmts))
  where isStandardTheory usedThyNames (Isa.ThyName n) = n `elem` usedThyNames

lookupImports :: Isa.ThyName -> Env.GlobalE -> Customisations -> [Isa.ThyName]
lookupImports thy globalEnv custs
    = map (rename .(\(Env.EnvImport name _ _) ->  Env.toIsa name))
        $ Env.lookupImports_OrLose (Env.fromIsa thy) globalEnv
    where rename orig@(Isa.ThyName name) = case getCustomTheory custs (Hsx.ModuleName name) of
                                   Nothing -> orig
                                   Just ct -> getCustomTheoryName ct

convertDependentDecls :: [Pragma] -> HskDependentDecls -> ContextM [Isa.Stmt]
convertDependentDecls pragmas (HskDependentDecls [])  =
  return []
convertDependentDecls pragmas (HskDependentDecls [d]) = do
  d <- convertDecl pragmas d
  return d
convertDependentDecls pragmas (HskDependentDecls decls@(decl:_))
  | isFunBind decl = assert (all isFunBind decls)
      $ do funcmds <- mapsM (convertDecl pragmas) decls
           let (sigs, permissive, eqs) = unzip3 (map splitFunCmd funcmds)
           return [Isa.Fun sigs (or permissive) (flat eqs)]
  | isDataDecl decl = assert (all isDataDecl decls)
      $ do dataDefs <- mapM (convertDataDecl pragmas) decls
           auxCmds <- mapM (generateRecordAux pragmas) decls
           return (Isa.Datatype dataDefs : concat auxCmds)
  where 
    isFunBind (Hsx.FunBind _) = True
    isFunBind _ = False
    isDataDecl (Hsx.DataDecl _ _ _ _ _ _ _) = True
    isDataDecl _ = False
    splitFunCmd (Isa.Fun [sig] permissive eqs) = (sig, permissive, eqs)

instance Convert Hsx.Module Isa.Stmt where
    convert' pragmas (Hsx.Module loc modul _ _ _exports _imports decls)
        = dieWithLoc loc "Internal Error: Each Hsx.Module should have been pre-converted to HskModule."


--- Trivially convertable stuff.

instance Convert Hsx.ModuleName Isa.ThyName where
    convert' pragmas m = return (Env.toIsa (Env.fromHsk m :: Env.ModuleID))

instance Convert Hsx.Name Isa.Name where
    convert' pragmas n = return (Env.toIsa (Env.fromHsk n :: Env.EnvName))

instance Convert Hsx.QName Isa.Name where
    convert' pragmas qn = return (Env.toIsa (Env.fromHsk qn :: Env.EnvName))

instance Convert Hsx.Type Isa.Type where
    convert' pragmas t @ (Hsx.TyForall _ _ _) = pattern_match_exhausted "Hsx.Type -> Isa.Type" t
    convert' pragmas t = return (Env.toIsa (Env.fromHsk t :: Env.EnvType))

convert_type_sign :: Hsx.Name -> Hsx.Type -> Isa.TypeSign
convert_type_sign n typ =
  let
    n' = Env.toIsa (Env.fromHsk n :: Env.EnvName)
    (e_vs, e_typ) = Env.typscheme_of_hsk_typ typ
    vs' = map (\(v, sort) -> (Env.toIsa v, Env.isa_of_sort sort)) e_vs
    typ' = Env.toIsa e_typ
  in Isa.TypeSign n' vs' typ'

instance Convert Hsx.BangType Isa.Type where
    convert' pragmas t@(Hsx.BangedTy _)   = pattern_match_exhausted "Hsx.BangType -> Isa.Type" t
    convert' pragmas (Hsx.UnBangedTy typ) = convert pragmas typ

instance Convert Hsx.QOp Isa.Term where
    convert' pragmas (Hsx.QVarOp qname) = do qname' <- convert pragmas qname; return (Isa.Const qname')
    convert' pragmas (Hsx.QConOp qname) = do qname' <- convert pragmas qname; return (Isa.Const qname')
    -- convert' junk = pattern_match_exhausted "Hsx.QOp -> Isa.Term" junk

instance Convert Hsx.Op Isa.Name where
    convert' pragmas (Hsx.VarOp qname) = convert pragmas qname
    convert' pragmas (Hsx.ConOp qname) = convert pragmas qname
    -- convert' junk = pattern_match_exhausted "HsOp -> Isa.Name" junk

instance Convert Hsx.Literal Isa.Literal where
    convert' pragmas (Hsx.Int i)      = return (Isa.Int i)
    convert' pragmas (Hsx.Char ch)    = return (Isa.Char ch)
    convert' pragmas (Hsx.String str) = return (Isa.String str)
    convert' pragmas junk           = pattern_match_exhausted "HsLiteral -> Isa.Literal" junk


--- Not so trivially convertable stuff.

convertDecl :: [Pragma] -> Hsx.Decl -> ContextM [Isa.Stmt]
convertDecl pragmas (Hsx.TypeDecl _loc tyconN tyvarNs typ)
        = do tyvars <- mapM (convert pragmas) tyvarNs
             tycon  <- convert pragmas tyconN
             typ'   <- convert pragmas typ
             return [Isa.TypeSynonym [(Isa.TypeSpec tyvars tycon, typ')]]
                                
convertDecl pragmas decl@(Hsx.DataDecl _ _ _ _ _ _ _) = 
        do dataDef <- convertDataDecl pragmas decl
           accCmds <- generateRecordAux pragmas decl
           return (Isa.Datatype [dataDef] : accCmds)

convertDecl pragmas (Hsx.InfixDecl _loc assoc prio ops)
        = do (assocs, prios) <- mapAndUnzipM (lookupInfixOp . toQOp) ops 
             assert (all (== assoc) assocs && all (== prio) prios) 
               $ return []
        where toQOp (Hsx.VarOp n) = Hsx.QVarOp (Hsx.UnQual n)
              toQOp (Hsx.ConOp n) = Hsx.QConOp (Hsx.UnQual n)

convertDecl pragmas (Hsx.TypeSig _loc names typ)
        = do globalEnv <- queryContext globalEnv
             modul     <- queryContext currentModule
             types     <- liftM catMaybes $ mapM (lookupType . Hsx.UnQual) names
             assert (all (== typ) types) 
               $ return []
                         
    -- Remember that at this stage there are _no_ local declarations in the Hsx
    -- AST anymore, as we made those global during the preprocessing stage.
    -- 
    --   E.g.                                                       fun g0 :: "Int => Int"    
    --                                    g0 :: Int -> Int          where                      
    --    f :: Int -> Int                 g0 0 = 0                    "g0 0 = 0"              
    --    f x = g x                       g0 n = n + g0 (n-1)       | "g0 n = n + g0 (n - 1)"
    --      where g :: Int -> Int   ==>                        ==>                            
    --            g 0 = 0                 f :: Int -> Int           fun f :: "Int => Int"     
    --            g n = n + g (n-1)       f x = g0 x                where                     
    --                                                                "f x = g0 x"            
    --
convertDecl pragmas (Hsx.FunBind matchs)
        = do let (names, patterns, bodies, wbinds) = unzip4 (map splitMatch matchs)
             assert (all (== head names) (tail names)) (return ())
             assert (all isEmpty wbinds) (return ()) -- all decls are global at this point.
             ftype <- lookupType (Hsx.UnQual (names !! 0)) -- as all names are equal, pick first one.
             let name = names !! 0
             name' <- convert' pragmas name
             let n = name_of name
             let permissive = n `elem` these (lookup permissive_pragma pragmas)
             let fsig' = case ftype of { 
               Nothing -> Isa.TypeSign name' [] Isa.NoType;
               Just typ -> convert_type_sign name typ }
             patsNames  <- mapM (mapM (convert pragmas)) patterns
             let patsNames' = map unzip patsNames
                 patterns'  = map fst patsNames'
                 aliases    = map (concat.snd) patsNames'
             bodies'    <- withFunctionType' ftype $
                                mapM (convert pragmas) bodies
             let bodies'' = zipWith mkSimpleLet aliases bodies'
             thy        <- queryContext theory
             return [Isa.Fun [fsig'] permissive (zip3 (repeat (Isa.nameOfTypeSign fsig')) patterns' bodies'')]
       where splitMatch (Hsx.Match _loc name patterns (Hsx.UnGuardedRhs body) wherebind)
                 = (name, patterns, body, wherebind)
             isEmpty wherebind = case wherebind of Hsx.BDecls [] -> True; _ -> False
             name_of (Hsx.Ident n) = n
             name_of _ = ""

convertDecl pragmas (Hsx.PatBind loc pattern rhs _wherebinds)
        = case pattern of
            pat@(Hsx.PVar name) 
                -> do name' <- convert pragmas name
                      (pat', aliases)  <- convert pragmas pat
                      rhs'  <- convert pragmas rhs
                      let rhs'' = mkSimpleLet aliases rhs'
                      ftype <- lookupType (Hsx.UnQual name)
                      let sig' = case ftype of { 
                        Nothing -> Isa.TypeSign name' [] Isa.NoType;
                        Just typ -> convert_type_sign name typ }
                      return [Isa.Definition sig' (name', rhs'')]
            _   -> dieWithLoc loc (Msg.complex_toplevel_patbinding)
    
convertDecl pragmas decl@(Hsx.ClassDecl _ ctx classN _ _ class_decls)
        = check_class_decl decl
            $ do let superclassNs   = extractSuperclassNs ctx
                 superclassNs' <- mapM (convert pragmas) superclassNs
                 classN'       <- convert pragmas classN
                 typesigs'     <- mapsM convertToTypeSig class_decls
                 return [Isa.Class classN' superclassNs' typesigs']
        where
          check_class_decl (Hsx.ClassDecl loc ctx classN varNs fundeps decls) cont
              | length varNs /= 1          = dieWithLoc loc (Msg.only_one_tyvar_in_class_decl)
              | not (null fundeps)         = dieWithLoc loc (Msg.no_fundeps_in_class_decl)
              | not (all isTypeSig decls)  = dieWithLoc loc (Msg.no_default_methods_in_class_decl)
              | otherwise                  = cont
          isTypeSig decl = case decl of 
                             Hsx.ClsDecl (Hsx.TypeSig _ _ _) -> True
                             _                           -> False
          convertToTypeSig (Hsx.ClsDecl (Hsx.TypeSig _ names typ))
                  = do names' <- mapM (convert pragmas) names
                       typ'   <- convert pragmas typ {-FIXME-}
                       return (map (\name' -> Isa.TypeSign name' [] typ') names')

convertDecl pragmas (Hsx.InstDecl loc ctx classqN tys inst_decls)
        | length tys /= 1 = dieWithLoc loc (Msg.only_one_tyvar_in_class_decl)
        | not (isType (head tys)) = dieWithLoc loc (Msg.only_specializing_on_tycon_allowed)
        | otherwise
            = do classqN'   <- convert pragmas classqN
                 type'      <- convert pragmas (head tys)
                 let (tyco', _) = Isa.dest_Type type'
                 identifier <- lookupIdentifier_Type classqN
                 let classinfo
                                   = case fromJust identifier of
                                       Env.Type (Env.Class _ classinfo) -> classinfo
                                       t -> error $ "found:\n" ++ show t
                 let methods       = Env.methodsOf classinfo
                 let classVarN     = Env.classVarOf classinfo
                 let inst_envtype  = Env.fromHsk (head tys)
                 let tyannots = map (mk_method_annotation classVarN inst_envtype) methods
                 withUpdatedContext globalEnv (\e -> Env.augmentGlobalEnv e tyannots) $
                   do decls' <- mapsM (convertDecl pragmas) (map toHsDecl inst_decls)
                      return [Isa.Instance classqN' tyco' [] decls'] {- FIXME -}
        where 
          isType t = case t of { Hsx.TyCon _ -> True; _ -> False }
          toHsDecl (Hsx.InsDecl decl) = decl

          mk_method_annotation :: Env.EnvName -> Env.EnvType -> Env.Identifier -> Env.Identifier
          mk_method_annotation tyvarN tycon class_method_annot
              = assert (Env.isTypeAnnotation class_method_annot)
                  $ let lexinfo = Env.lexInfoOf class_method_annot
                        (_, typ)     = Env.typschemeOf lexinfo
                        typ'    = Env.substituteTyVars [(Env.EnvTyVar tyvarN, tycon)] typ
                    in Env.Constant (Env.TypeAnnotation (lexinfo { Env.typschemeOf = ([], typ') }))

convertDecl pragmas junk = pattern_match_exhausted "Hsx.Decl -> Isa.Stmt" junk


instance Convert Hsx.Binds [Isa.Stmt] where
    convert' pragmas (Hsx.BDecls decls) = mapsM (convertDecl pragmas) decls
    convert' pragmas junk = pattern_match_exhausted "Hsx.Binds -> Isa.Stmt" junk

mkList :: [Isa.Term] -> Isa.Term
mkList = foldr
         (\x xs -> Isa.App (Isa.App (Isa.Const (Isa.Name "List.Cons")) x) xs)
         (Isa.Const (Isa.Name "List.Nil"))

mkSimpleLet :: [(Isa.Name, Isa.Term)] -> Isa.Term -> Isa.Term
mkSimpleLet [] body = body
mkSimpleLet binds body = Isa.Let binds' body
    where binds' = map (\(a,b) -> (Isa.Const a, b)) binds

type PatternE = Bool
type PatternO = [(Isa.Name,Isa.Term)]

newtype PatternM a = PatternM ((ReaderT PatternE (WriterT PatternO ContextM)) a)
    deriving (Monad, MonadReader PatternE, MonadWriter PatternO, Functor)

runPatternM :: PatternM a -> ContextM (a,PatternO)
runPatternM (PatternM pm) =  (runWriterT (runReaderT pm False))

liftConvert :: ContextM a -> PatternM a
liftConvert = PatternM . lift . lift

withAsPattern :: PatternM a -> PatternM a
withAsPattern = local (const True)

isInsideAsPattern :: PatternM Bool
isInsideAsPattern = ask

addAlias :: (Isa.Name, Isa.Term) -> PatternM ()
addAlias = tell . (:[])

convertPat :: [Pragma] -> Hsx.Pat -> PatternM Isa.Pat
convertPat pragmas (Hsx.PVar name) = 
    do name' <- liftConvert $ convert pragmas name
       return (Isa.Const name')
convertPat pragmas (Hsx.PLit lit) = 
    do lit' <- liftConvert $ convert pragmas lit
       return (Isa.Literal lit')
              
convertPat pragmas infixapp@Hsx.PInfixApp{} = 
    do (Hsx.PInfixApp p1 qname p2) <- liftConvert $ fixOperatorFixities' infixapp
       p1' <- convertPat pragmas p1 
       qname'   <- liftConvert $ convert pragmas qname
       p2' <- convertPat pragmas p2
       return (Isa.App (Isa.App (Isa.Const qname') p1') p2')

convertPat pragmas (Hsx.PApp qname pats) = 
    do qname' <- liftConvert $ convert pragmas qname
       pats' <- mapM (convertPat pragmas) pats
       return $ foldl Isa.App (Isa.Const qname') pats'
       
convertPat pragmas (Hsx.PTuple comps) = 
    convertPat pragmas (foldr hskPPair (Hsx.PParen (last comps)) (init comps))

convertPat pragmas (Hsx.PList []) =
    do list_datacon_name <- liftConvert $ convert pragmas (Hsx.Special Hsx.ListCon)
       return (Isa.Const list_datacon_name)

convertPat pragmas (Hsx.PList els) =
    convertPat pragmas $ foldr hskPCons hskPNil els

convertPat pragmas (Hsx.PParen pat) = 
    do pat' <- convertPat pragmas pat
       return (Isa.Parenthesized pat')

convertPat pragmas (Hsx.PRec qname fields) = 
    do mbConstr <- liftConvert $ lookupIdentifier_Constant qname
       case mbConstr of
         Just (Env.Constant (Env.Constructor (Env.RecordConstr _ _ recFields))) -> 
             do isAs <- isInsideAsPattern
                let fields' = map (\(Hsx.PFieldPat name pat) -> (Env.fromHsk name, pat)) fields
                    toSimplePat (Env.RecordField iden _) = 
                        case lookup iden fields' of
                          Nothing -> if isAs
                                     then liftConvert . liftGensym . liftM Isa.Const . liftM Isa.Name $
                                          gensym "a"
                                     else return (Isa.Const (Isa.Name "_"))
                          Just pat -> convertPat pragmas pat
                recArgs <- mapM toSimplePat recFields
                qname' <- liftConvert $ convert pragmas qname
                return $ Isa.Parenthesized (foldl Isa.App (Isa.Const qname') recArgs)
         _ -> liftConvert . die $ "Record constructor " ++ Msg.quote qname ++ " is not declared in environment!"

convertPat pragmas (Hsx.PAsPat name pat) = 
    do name' <- liftConvert $ convert pragmas name
       pat' <- withAsPattern $ convertPat pragmas pat
       addAlias (name', pat')
       return pat'
convertPat pragmas (Hsx.PWildCard) = 
    do isAs <- isInsideAsPattern
       if isAs
         then liftConvert . liftGensym . liftM Isa.Const . liftM Isa.Name $
              gensym "a"
         else return (Isa.Const (Isa.Name "_"))

convertPat pragmas junk = liftConvert $ pattern_match_exhausted 
                  "Hsx.Pat -> Isa.Term" 
                  junk
instance Convert Hsx.Pat (Isa.Pat, [(Isa.Name, Isa.Term)]) where
    convert' pragmas  = runPatternM . convertPat pragmas 

instance Convert Hsx.Rhs Isa.Term where
    convert' pragmas (Hsx.UnGuardedRhs exp) = convert pragmas exp
    -- convert (Hsx.GuardedRhss rhss) ; FIXME
    convert' pragmas junk = pattern_match_exhausted "Hsx.Rhs -> Isa.Term" junk

instance Convert Hsx.FieldUpdate (Isa.Name, Isa.Term) where
    convert' pragmas (Hsx.FieldUpdate qname exp)
        = do qname' <- convert pragmas qname
             exp'   <- convert pragmas exp
             return (qname', exp')

instance Convert Hsx.Alt (Isa.Term, Isa.Term) where
    convert' pragmas (Hsx.Alt _loc pat (Hsx.UnGuardedAlt exp) _wherebinds)
        = do (pat',aliases) <- convert pragmas pat
             exp' <- convert pragmas exp
             let exp'' = mkSimpleLet aliases exp'
             return (pat', exp'')
    convert' pragmas junk 
        = pattern_match_exhausted "Hsx.Alt -> (Isa.Term, Isa.Term)" junk


instance Convert Hsx.Exp Isa.Term where
    convert' pragmas (Hsx.Lit lit)       = convert pragmas lit   >>= (\l -> return (Isa.Literal l))
    convert' pragmas (Hsx.Var qname)     =
        do qname' <- getCurrentMonadFunction qname
           convert pragmas qname' >>= (\n -> return (Isa.Const n))
    convert' pragmas (Hsx.Con qname)     = convert pragmas qname >>= (\n -> return (Isa.Const n))
    convert' pragmas (Hsx.Paren exp)     = convert pragmas exp   >>= (\e -> return (Isa.Parenthesized e))
    -- convert' (Hsx.WildCard)      = return (Isa.Const (Isa.Name "_"))
    convert' pragmas (Hsx.NegApp exp)    = convert pragmas (hsk_negate exp)

    convert' pragmas (Hsx.List [])       = do
      list_datacon_name <- convert pragmas (Hsx.Special Hsx.ListCon)
      return (Isa.Const list_datacon_name)
    convert' pragmas (Hsx.List exps)
        = convert pragmas $ foldr hsk_cons hsk_nil exps

    -- We have to wrap the last expression in an explicit HsParen as that last
    -- expression may itself be a pair. If we didn't, we couldn't distinguish
    -- between "((1,2), (3,4))" and "((1,2), 3, 4)" afterwards anymore.
    convert' pragmas (Hsx.Tuple exps)    = convert pragmas (foldr hsk_pair (Hsx.Paren (last exps)) (init exps))

    convert' pragmas (Hsx.App exp1 exp2)
        = do exp1' <- convert pragmas exp1
             exp2' <- withPossibleLift exp1 $ convert pragmas exp2
             return (Isa.App exp1' exp2')

    convert' pragmas infixapp@(Hsx.InfixApp _ _ _)
        = do (Hsx.InfixApp exp1 op exp2) <- fixOperatorFixities infixapp
             exp1' <- convert pragmas exp1 
             op'   <- convert pragmas op
             exp2' <- if isApp op
                       then withPossibleLift exp1 $ convert pragmas exp2
                       else convert pragmas exp2
             return (mkInfixApp exp1' op' exp2')
        where 
          uname (Hsx.Qual _ n) = n
          uname (Hsx.UnQual n) = n
          isApp (Hsx.QVarOp qname) =
              case uname qname of
                Hsx.Ident _ -> False
                Hsx.Symbol sym -> sym == "$"
          isApp _ = False
          mkInfixApp t1 op t2 = Isa.App (Isa.App op t1) t2

    convert' pragmas (Hsx.LeftSection e qop)
        = do e'   <- convert pragmas e
             qop' <- convert pragmas qop
             g    <- liftGensym (genIsaName (Isa.Name "arg"))
             return (makeAbs [g] $ Isa.App (Isa.App qop' e') (Isa.Const g))

    convert' pragmas (Hsx.RightSection qop e)
        = do e'   <- convert pragmas e
             qop' <- convert pragmas qop
             g <- liftGensym (genIsaName (Isa.Name "arg"))
             return (makeAbs [g] $ Isa.App (Isa.App qop' (Isa.Const g)) e')

    convert' pragmas (Hsx.RecConstr qname updates) = 
        do mbConstr <- lookupIdentifier_Constant qname
           case mbConstr of
             Just (Env.Constant (Env.Constructor (Env.RecordConstr _ _ recFields))) -> 
                 let updates' = map (\(Hsx.FieldUpdate name exp) -> (Env.fromHsk name, exp)) updates
                     toSimplePat (Env.RecordField iden _) = 
                         case lookup iden updates' of
                           Nothing -> Hsx.Var (Hsx.UnQual (Hsx.Ident "undefined"))
                           Just exp -> exp
                     recArgs = map toSimplePat recFields
                 in convert' pragmas $ foldl Hsx.App (Hsx.Con qname) recArgs
             _ -> die $ "Record constructor " ++ Msg.quote qname ++ " is not declared in environment!"

    convert' pragmas (Hsx.RecUpdate exp updates) = 
        do exp' <- convert pragmas exp
           fstupd:upds <- mapM convUpd updates
           let updateFunction = Isa.Parenthesized (foldr comp fstupd upds)
           return $ Isa.App updateFunction exp'
       where comp a b = Isa.App (Isa.App (Isa.Const (Isa.Name "o")) a) b
             convUpd (Hsx.FieldUpdate fname fexp) =
                                do fexp' <- convert pragmas fexp
                                   let ufun = Isa.Const (Isa.Name ("update_" ++ unqual fname))
                                   return $ Isa.App ufun fexp'
             unqual (Hsx.Qual _ n) = uname n
             unqual (Hsx.UnQual n) = uname n
             uname (Hsx.Ident n) = n
             uname (Hsx.Symbol n) = n

    convert' pragmas (Hsx.If t1 t2 t3)
        = do t1' <- convert pragmas t1; t2' <- convert pragmas t2; t3' <- convert pragmas t3
             return (Isa.If t1' t2' t3')

    convert' pragmas (Hsx.Case exp alts)
        = do exp'  <- convert pragmas exp
             alts' <- mapM (convert pragmas) alts
             return $ Isa.Case exp' alts'

    convert' pragmas x@(Hsx.Lambda _loc pats body)
        = do patsNames  <- mapM (convert pragmas) pats
             let (pats', aliases) = unzip patsNames
                 aliases' = concat aliases
             body'  <- convert pragmas body
             let body'' = mkSimpleLet aliases' body'
             if all isConst pats' then return $ makeAbs [n | Isa.Const n <- pats'] body''
                                else makePatternMatchingAbs pats' body''
          where isConst (Isa.Const _)   = True
                isConst _             = False

    convert' pragmas expr@(Hsx.Let (Hsx.BDecls bindings) body)
        = let (_, patbindings) = partition isTypeSig bindings
          in assert (all isPatBinding patbindings)
             $ do let (pats, rhss) = unzip (map (\(Hsx.PatBind _ pat rhs _) -> (pat, rhs)) patbindings)
                  patsNames <- mapM (convert pragmas) pats
                  let (pats', aliases) = unzip patsNames
                  rhss' <- mapM (convert pragmas) rhss
                  let rhss'' = zipWith mkSimpleLet aliases rhss'
                  body' <- convert pragmas body
                  return (Isa.Let (zip pats' rhss'') body')
          where isTypeSig (Hsx.TypeSig _ _ _)      = True
                isTypeSig _                      = False
                isPatBinding (Hsx.PatBind _ _ _ (Hsx.BDecls [])) = True
                isPatBinding _                   = False
                
    convert' pragmas (Hsx.ListComp e stmts) 
        = do e'     <- convert pragmas e
             stmts' <- liftM concat $ mapM convertListCompStmt stmts
             return (Isa.ListCompr e' stmts')
        where convertListCompStmt (Hsx.Qualifier b)     = convert pragmas  b >>= (return . (:[]) . Isa.Guard)
              convertListCompStmt (Hsx.Generator _ p e) = do
                (p',as) <- convert pragmas p
                let gens = mkSimpleGens as
                e' <- convert pragmas e
                return $ [Isa.Generator (p', e')] ++ gens
              convertListCompStmt (Hsx.LetStmt _)
                  = die "Let statements not supported in List Comprehensions."
              mkSimpleGens = map (\(n,t) -> Isa.Generator (Isa.Const n, mkList [t]))
    convert' pragmas (Hsx.Do stmts)
        = do isaStmts <- liftM concat $ mapM (convert pragmas) stmts
             mbDo <- getCurrentMonadDoSyntax
             case mbDo of
               Nothing -> die "Do syntax is used without sufficient type information!"
               Just (DoParen pre post) -> 
                   return $ Isa.DoBlock pre isaStmts post

    convert' pragmas junk = pattern_match_exhausted "Hsx.Exp -> Isa.Term" junk

instance Convert Hsx.Stmt [Isa.DoBlockFragment] where

    convert' pragmas (Hsx.Generator _ pat exp) = 
        do exp' <- convert pragmas exp
           (pat', aliases) <- convert pragmas pat
           aliases' <- mkDoLet pragmas aliases
           return (Isa.DoGenerator pat' exp' : aliases')
    convert' pragmas (Hsx.Qualifier exp) = liftM ( (:[]) . Isa.DoQualifier) (convert pragmas exp)
    convert' pragmas (Hsx.LetStmt binds) =
        case binds of
          Hsx.BDecls [Hsx.PatBind _ pat (Hsx.UnGuardedRhs exp) _] ->
              do exp' <- convert pragmas exp
                 (pat', aliases) <- convert pragmas pat
                 aliases' <- mkDoLet pragmas aliases
                 ret <- mkReturn pragmas
                 return (Isa.DoGenerator pat' (Isa.App ret exp') : aliases')
             -- liftM2 Isa.DoGenerator (convert pat) (convert (Hsx.App (Hsx.Var (Hsx.UnQual (Hsx.Ident "return"))) exp))
          def -> pattern_match_exhausted "Hsx.Stmt -> Isa.DoBlockFragment" def

mkReturn :: [Pragma] -> ContextM Isa.Term
mkReturn pragmas = convert pragmas . Hsx.Var . Hsx.UnQual .Hsx.Ident $ "return"

mkDoLet :: [Pragma] -> [(Isa.Name, Isa.Term)] -> ContextM [Isa.DoBlockFragment]
mkDoLet pragmas aliases = 
    do ret <- mkReturn pragmas
       let mkSingle (name, term) = Isa.DoGenerator (Isa.Const name) (Isa.App ret term)
       return $ map mkSingle aliases

{-|
  We desugare lambda expressions to true unary functions, i.e. to
  lambda expressions binding only one argument.
 -}
makeAbs :: [Isa.Name] -> Isa.Term -> Isa.Term
makeAbs varNs body
    = assert (not (null varNs)) $ foldr Isa.Abs body varNs

{-|
  Since HOL doesn't have true n-tuple constructors (it uses nested
  pairs to represent n-tuples), we simply return a lambda expression
  that takes n parameters and constructs the nested pairs within its
  body.
 -}

makeTupleDataCon :: [Pragma] -> Int -> ContextM Isa.Term
makeTupleDataCon pragmas n     -- n < 2  cannot happen (cf. Language.Haskell.Exts.Hsx.TupleCon)
    = assert (n > 2) $ -- n == 2, i.e. pairs, can and are dealt with by usual conversion.
      do argNs  <- mapM (liftGensym . genHsQName) (replicate n (Hsx.UnQual (Hsx.Ident "arg")))
         args   <- return (map Hsx.Var argNs)
         argNs' <- mapM (convert pragmas) argNs
         args'  <- convert pragmas (Hsx.Tuple args)
         return $ Isa.Parenthesized (makeAbs argNs' args')
    where pair x y = Hsx.App (Hsx.App (Hsx.Con (Hsx.Special (Hsx.TupleCon 2))) x) y

{-|
  HOL does not support pattern matching directly within a lambda
  expression, so we transform a @Hsx.Abs pat1 pat2 .. patn -> body@ to
  
  @
  Isa.Abs g1 .
     Isa.Case g1 of pat1' =>
       Isa.Abs g2 .
         Isa.Case g2 of pat2' => ... => Isa.Abs gn .
                                          Isa.Case gn of patn' => body'
  @
  where @g1@, ..., @gn@ are fresh identifiers.
-}
makePatternMatchingAbs :: [Isa.Pat] -> Isa.Term -> ContextM Isa.Term
makePatternMatchingAbs patterns theBody
    = foldM mkMatchingAbs theBody (reverse patterns) -- foldM is a left fold.
      where mkMatchingAbs body pat
                = do g <- liftGensym (genIsaName (Isa.Name "arg"))
                     return $ Isa.Abs g (Isa.Case (Isa.Const g) [(pat, body)])


makeRecordCmd :: [Pragma] -> Hsx.Name  -- ^type constructor
              -> [Hsx.Name] -- ^type variable arguments to the constructor
              -> [Hsx.ConDecl] -- ^a singleton list containing a record declaration
              -> ContextM Isa.Stmt   -- ^the resulting record declaration
makeRecordCmd pragmas tyconN tyvarNs [Hsx.RecDecl name slots] -- cf. `isRecDecls'
    = do tycon  <- convert pragmas tyconN
         tyvars <- mapM (convert pragmas) tyvarNs
         slots' <- mapsM cnvSlot slots
         return $ Isa.Record (Isa.TypeSpec tyvars tycon) slots'
    where cnvSlot (names, typ)
              = do names' <- mapM (convert pragmas) names
                   typ'   <- convert pragmas typ
                   return (zip names' (cycle [typ']))
 

{-|
  Hsx parses every infix application simply from left to right without
  taking operator associativity or binding priority into account. So
  we gotta fix that up ourselves. (We also properly consider infix
  declarations to get user defined operator right.)
-}
fixOperatorFixities :: Hsx.Exp -> ContextM Hsx.Exp

-- Notice that `1 * 2 + 3 / 4' is parsed as `((1 * 2) + 3) / 4', i.e.
-- 
--    Hsx.InfixApp (Hsx.InfixApp (Hsx.InfixApp 1 * 2) + 3) / 4
--
-- whereas `1 * 2 + (3 / 4)' is parsed as
--
--    Hsx.InfixApp (Hsx.InfixApp 1 * 2) + (HsParen (Hsx.InfixApp 3 / 4))
--
-- and `1 * (2 + 3) / 4' is parsed as
--
--    Hsx.InfixApp (Hsx.InfixApp 1 (HsParen (Hsx.InfixApp 2 + 3))) / 4
--
-- Thus we _know_ that the second operand of an infix application,
-- i.e. the e2 in `Hsx.InfixApp e1 op e2', can _never_ be a bare infix
-- application that we might have to consider during fixup.
--  
fixOperatorFixities app@(Hsx.InfixApp (Hsx.InfixApp e1 op1 e2) op2 e3)
    -- We assume that `(e1, op1, e2)' is correct already
    -- and from above, we also know that `e3' cannot possibly
    -- interfere, so we just have to find the proper place of `op2'.
    = do (assoc1', prio1)  <- lookupInfixOp op1
         (assoc2', prio2)  <- lookupInfixOp op2
         let assoc1 = normalizeAssociativity assoc1'
         let assoc2 = normalizeAssociativity assoc2'
         case prio1 `compare` prio2 of
           GT -> return app
           LT -> liftM (Hsx.InfixApp e1 op1) (fixOperatorFixities (Hsx.InfixApp e2 op2 e3))
           EQ -> if assoc2 /= assoc1 then
                     die (Msg.assoc_mismatch op1 assoc1 op2 assoc2)
                 else case assoc2 of
                        Hsx.AssocLeft  -> return app
                        Hsx.AssocRight -> return (Hsx.InfixApp e1 op1 (Hsx.InfixApp e2 op2 e3))
                        Hsx.AssocNone  -> die ("fixupOperatorFixities: Internal error " ++
                                               "(AssocNone should have already been normalized away.)")
fixOperatorFixities nonNestedInfixApp = return nonNestedInfixApp


{-|
  Hsx parses every infix application simply from left to right without
  taking operator associativity or binding priority into account. So
  we gotta fix that up ourselves. (We also properly consider infix
  declarations to get user defined operator right.)
-}
fixOperatorFixities' :: Hsx.Pat -> ContextM Hsx.Pat
fixOperatorFixities' app@(Hsx.PInfixApp (Hsx.PInfixApp e1 op1 e2) op2 e3)
    = do (assoc1', prio1)  <- lookupInfixOpName op1
         (assoc2', prio2)  <- lookupInfixOpName op2
         let assoc1 = normalizeAssociativity assoc1'
         let assoc2 = normalizeAssociativity assoc2'
         case prio1 `compare` prio2 of
           GT -> return app
           LT -> liftM (Hsx.PInfixApp e1 op1) (fixOperatorFixities' (Hsx.PInfixApp e2 op2 e3))
           EQ -> if assoc2 /= assoc1 then
                     die (Msg.assoc_mismatch op1 assoc1 op2 assoc2)
                 else case assoc2 of
                        Hsx.AssocLeft  -> return app
                        Hsx.AssocRight -> return (Hsx.PInfixApp e1 op1 (Hsx.PInfixApp e2 op2 e3))
                        Hsx.AssocNone  -> die ("fixupOperatorFixities: Internal error " ++
                                               "(AssocNone should have already been normalized away.)")
fixOperatorFixities' nonNestedInfixApp = return nonNestedInfixApp


{-|
  Enforces left associativity as default.
-}
normalizeAssociativity :: Hsx.Assoc -> Hsx.Assoc
normalizeAssociativity (Hsx.AssocNone) = Hsx.AssocLeft -- as specified in Haskell98.
normalizeAssociativity etc = etc

{-|
  This function looks up the lexical information for the
  given constant identifier.
-}
lookupIdentifier_Constant :: Hsx.QName -> ContextM (Maybe Env.Identifier)
lookupIdentifier_Constant qname
    = do globalEnv <- queryContext globalEnv
         modul     <- queryContext currentModule
         return (Env.lookupConstant (Env.fromHsk modul) (Env.fromHsk qname) globalEnv)

{-|
  This function looks up the lexical information for the given
  type identifier.
-}
lookupIdentifier_Type' :: Env.EnvName -> ContextM (Maybe Env.Identifier)
lookupIdentifier_Type' envName
    = do globalEnv <- queryContext globalEnv
         modul     <- queryContext currentModule
         return (Env.lookupType (Env.fromHsk modul) envName globalEnv)
{-|
  This function looks up the lexical information for the given
  type identifier.
-}
lookupIdentifier_Type :: Hsx.QName -> ContextM (Maybe Env.Identifier)
lookupIdentifier_Type qname
    = do globalEnv <- queryContext globalEnv
         modul     <- queryContext currentModule
         return (Env.lookupType (Env.fromHsk modul) (Env.fromHsk qname) globalEnv)

{-|
  This function looks up the fixity declaration for the given
  infix operator.
-}
lookupInfixOp :: Hsx.QOp -> ContextM (Hsx.Assoc, Int)
lookupInfixOp = lookupInfixOpName . qop2name
    where qop2name (Hsx.QVarOp n) = n
          qop2name (Hsx.QConOp n) = n
{-|
  This function looks up the fixity declaration for the given
  infix operator.
-}
lookupInfixOpName :: Hsx.QName -> ContextM (Hsx.Assoc, Int)
lookupInfixOpName qname
    = do identifier <- lookupIdentifier_Constant (qname)
         case identifier of
           Just (Env.Constant (Env.InfixOp _ envassoc prio)) 
                   -> return (Env.toHsk envassoc, prio)
           Nothing -> do globalEnv <- queryContext globalEnv;
                         warn (Msg.missing_infix_decl qname globalEnv)
                         return (Hsx.AssocLeft, 9) -- default values in Haskell98
    where qop2name (Hsx.QVarOp n) = n
          qop2name (Hsx.QConOp n) = n


{-|
  This function looks up the type for the given identifier.
-}
lookupType :: Hsx.QName -> ContextM (Maybe Hsx.Type)
lookupType fname = do
  identifier <- lookupIdentifier_Constant fname
  case identifier of
    Nothing -> return Nothing
    Just id -> let typscheme = Env.typschemeOf (Env.lexInfoOf id) 
               in if snd typscheme == Env.EnvTyNone
                  then return Nothing else return $ Just (Env.hsk_typ_of_typscheme typscheme)
