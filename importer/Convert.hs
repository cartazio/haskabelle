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

module Importer.Convert (
  convertHskUnit
) where

import qualified Language.Haskell.Exts as Hs

import Data.List
import Maybe

import Control.Monad
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State

import Importer.Utilities.Misc
import Importer.Utilities.Hsk
import Importer.Utilities.Gensym
import Importer.Preprocess
import Importer.ConversionUnit (HskUnit(..), IsaUnit(..))
import Importer.DeclDependencyGraph

import Importer.Adapt.Mapping (makeAdaptionTable_FromHsModule, extractHskEntries)
import Importer.Adapt.Adaption (adaptGlobalEnv, adaptIsaUnit)
import Importer.Adapt.Raw (used_thy_names)

import qualified Importer.IsaSyntax as Isa
import qualified Importer.Msg as Msg

import qualified Importer.LexEnv as Env

import qualified Data.Map as Map
import Importer.Configuration hiding (getMonadInstance)
import qualified Importer.Configuration as Config (getMonadInstance)

{-|
  This is the main function of the conversion process; converts a Unit of Haskell
  ASTs into a Unit of Isar/HOL ASTs.
-}
convertHskUnit :: Customisations -> HskUnit -> IsaUnit
convertHskUnit custs (HskUnit hsmodules custMods initialGlobalEnv)
    = let hsmodules'     = map preprocessModule hsmodules
          env            = Env.environmentOf custs hsmodules' custMods
          adaptionTable  = makeAdaptionTable_FromHsModule env hsmodules'
          initial_env    = Env.augmentGlobalEnv initialGlobalEnv $ extractHskEntries adaptionTable
          global_env_hsk = Env.unionGlobalEnvs env initial_env
                             
          hskmodules     = map (toHskModule global_env_hsk) hsmodules'
          
          isathys = fst $ runConversion custs global_env_hsk $ mapM convert hskmodules 
          custThys = Map.elems custMods
          adaptedEnv = adaptGlobalEnv global_env_hsk adaptionTable
          isaunit = IsaUnit isathys custThys adaptedEnv
      in
        adaptIsaUnit global_env_hsk adaptionTable isaunit
    where 
      toHskModule :: Env.GlobalE -> Hs.Module -> HskModule
      toHskModule globalEnv (Hs.Module loc modul _ _ _exports _imports decls)
          = let declDepGraph = makeDeclDepGraph globalEnv modul decls 
            in HskModule loc modul
                $ map HskDependentDecls (flattenDeclDepGraph declDepGraph)


-- The naming scheme "HsFoo" is treated as being owned by the parser
-- libary Language.Haskell.Exts. We use "HskFoo" instead to
-- differentiate between what's defined by us and by that library. 
--
-- (Ok, this might sound somewhat confusing, at least we're consistent
-- about it.)

data HskModule = HskModule Hs.SrcLoc Hs.ModuleName [HskDependentDecls]
  deriving (Show)

{-|
  This data structure is supposed to collect function declarations
  that depend mutually recursive on each other.
-}
newtype HskDependentDecls = HskDependentDecls [Hs.Decl]
  deriving (Show)

{-|
  ???
-}
data Context    = Context
    {     
      _theory      :: Isa.Theory
    , _globalEnv   :: Env.GlobalE
    , _warnings    :: [Warning]
    , _backtrace   :: [String]
    , _monad       :: Maybe MonadInstance
    }

emptyContext = Context { _theory      = Isa.Theory "Scratch", -- FIXME: Default Hs.ModuleName in Haskell
                         _globalEnv   = Env.initialGlobalEnv,  --  is called `Main'; clashes with Isabelle.
                         _warnings    = [],
                         _backtrace   = [],
                         _monad = Nothing }

{-|
  Instead of accessing a record directly by their `_foo' slots, we
  use the respective `foo' surrogate which consists of an appropriate
  getter and setter -- which allows functions to both query and
  update a record by slot name.
-}
type FieldSurrogate field = (Context -> field, Context -> field -> Context) 

theory :: FieldSurrogate Isa.Theory
theory      = (_theory,      \c f -> c { _theory      = f })
globalEnv :: FieldSurrogate Env.GlobalE
globalEnv   = (_globalEnv,   \c f -> c { _globalEnv   = f })
warnings :: FieldSurrogate [Warning]
warnings    = (_warnings,    \c f -> c { _warnings    = f })
backtrace :: FieldSurrogate [String]
backtrace   = (_backtrace,   \c f -> c { _backtrace   = f })
monad     :: FieldSurrogate (Maybe MonadInstance)
monad       = (_monad,       \c f -> c { _monad       = f })

currentModule :: FieldSurrogate Hs.ModuleName
currentModule = (\c -> let (Isa.Theory n) = _theory c in Hs.ModuleName n, \c f -> c)

getMonadInstance :: String -> ContextM (Maybe MonadInstance)
getMonadInstance name = ask >>= (return . flip Config.getMonadInstance name)

getMonadInstance' :: Hs.Type -> ContextM (Maybe MonadInstance)
getMonadInstance' ty =
    case typeConName . returnType $ ty of
      Nothing -> return Nothing
      Just name -> getMonadInstance name

withFunctionType :: Hs.Type -> ContextM a -> ContextM a
withFunctionType ty contextm = 
    do mbMon <- getMonadInstance' ty
       withUpdatedContext monad (const mbMon) contextm

withFunctionType' :: Maybe Hs.Type -> ContextM a -> ContextM a
withFunctionType' mbTy contextm = 
    case mbTy of
      Nothing -> contextm
      Just ty -> withFunctionType ty contextm

withPossibleLift :: Hs.Exp -> ContextM a -> ContextM a
withPossibleLift name contextm = 
    do mbMon <- queryContext monad
       case mbMon of
         Nothing -> contextm
         Just mon -> 
             case varName name >>= getMonadLift mon of
               Nothing -> contextm
               newMon@(Just _) ->
                   withUpdatedContext monad (const newMon) contextm
    where uname (Hs.Qual _ n) = n
          uname (Hs.UnQual n) = n
          sname (Hs.Ident n) = n
          sname (Hs.Symbol n) = n
          qname (Hs.Var n) = Just n
          qname _ = Nothing
          varName = liftM sname . liftM uname . qname

getCurrentMonadFunction :: Hs.QName -> ContextM Hs.QName
getCurrentMonadFunction name =
    do mbMon <- queryContext monad
       case mbMon of
         Nothing -> return name
         Just mon -> 
             case name of
               Hs.Qual mod uName -> return $ Hs.Qual mod (lookup mon uName)
               Hs.UnQual uName -> return $ Hs.UnQual (lookup mon uName)
               def -> return def
       where lookup mon (Hs.Ident name) = Hs.Ident $ getMonadConstant mon name
             lookup mon (Hs.Symbol name) = Hs.Symbol $ getMonadConstant mon name

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
runConversion :: Customisations -> Env.GlobalE -> ContextM v -> (v, Context)
runConversion custs env (ContextM m) = evalGensym 0 $ runStateT (runReaderT m custs) (emptyContext { _globalEnv = env })

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
                   ++ foldr1 (++) (map (++"\n\n") (reverse backtrace))

{-|
  This function quits the conversion with an error providing the given error
  message and source location.
-}
dieWithLoc :: Hs.SrcLoc -> String -> ContextM t
dieWithLoc loc msg 
    = do backtrace <- queryContext backtrace
         error $ srcloc2string loc ++ ": " ++ msg ++ "\n\n"
                   ++ "Backtrace:\n"
                   ++ foldr1 (++) (map (++"\n\n") (reverse backtrace))
{-|
  This function quits the conversion with an error that is due to a
  pattern matching case that was observed but not anticipated. The object
  causing this and an a string describing the context has to be provided.
-}
pattern_match_exhausted :: (Show a) => String -> a -> ContextM t
pattern_match_exhausted str obj 
    = die (str ++ ": Pattern match exhausted for\n" ++ prettyShow obj)


          
{-|
  This function generates the auxiliary functions for the given Haskell
  data type declaration. This includes accessor functions and update functions
-}
generateRecordAux :: Hs.Decl -> ContextM [Isa.Cmd]
generateRecordAux (Hs.DataDecl _loc _kind _context tyconN tyvarNs condecls _deriving)
        = let strip (Hs.QualConDecl _loc _FIXME _context decl) = decl
              decls = map strip condecls
          in do tyvars <- mapM convert tyvarNs
                tycon  <- convert tyconN
                let dataTy = Isa.TyCon tycon (map Isa.TyVar tyvars)
                let fieldNames = concatMap extrFieldNames decls
                fields <-  mapM (liftM fromJust . lookupIdentifier_Constant . Hs.UnQual) (nub fieldNames)
                let funBinds = map (mkAFunBinds (length decls) dataTy) fields
                               ++ map (mkUFunBinds (length decls) dataTy) fields
                return funBinds
              where extrFieldNames (Hs.RecDecl conName fields) = map fst $ flattenRecFields fields
                    extrFieldNames _ = []
                    mkAFunBinds numCon dty (Env.Constant (Env.Field Env.LexInfo{Env.nameOf=fname, Env.typeOf=fty} constrs)) =
                        let binds = map (mkAFunBind fname) constrs
                            fname' = Isa.Name fname
                            funTy = Isa.TyFun dty (Env.toIsa fty)
                        in Isa.PrimrecCmd [fname'] [Isa.TypeSig fname' funTy] binds
                    mkAFunBind fname (Env.RecordConstr _ Env.LexInfo{Env.nameOf=cname} fields) =
                        let fname' = Isa.Name fname
                            con = Isa.Var $ Isa.Name cname
                            genArg (Env.RecordField n _)
                                | n == fname = Isa.Var (Isa.Name "x")
                                | otherwise = Isa.Var (Isa.Name "_")
                            conArgs = map genArg fields
                            pat = Isa.Parenthesized $ foldl Isa.App con conArgs
                            term = Isa.Var (Isa.Name "x")
                        in (fname', [pat], term)
                    mkUFunBinds numCon dty (Env.Constant (Env.Field Env.LexInfo{Env.nameOf=fname, Env.typeOf=fty} constrs)) =
                        let uname = "update_" ++ fname
                            binds = map (mkUFunBind fname uname) constrs
                            uname' = Isa.Name uname
                            funTy = Isa.TyFun (Env.toIsa fty) (Isa.TyFun dty dty)
                        in Isa.PrimrecCmd [uname'] [Isa.TypeSig uname' funTy] binds
                    mkUFunBind fname uname (Env.RecordConstr _ Env.LexInfo{Env.nameOf=cname} fields) =
                        let uname' = Isa.Name uname
                            con = Isa.Var $ Isa.Name cname
                            genPatArg (i,(Env.RecordField n _))
                                | n == fname = Isa.Var (Isa.Name "_")
                                | otherwise = Isa.Var (Isa.Name ("f" ++ show i))
                            genTermArg (i,(Env.RecordField n _))
                                | n == fname = Isa.Var (Isa.Name "x")
                                | otherwise = Isa.Var (Isa.Name ("f" ++ show i))
                            patArgs = map genPatArg (zip [1..] fields)
                            termArgs = map genTermArg (zip [1..] fields)
                            pat = Isa.Parenthesized $ foldl Isa.App con patArgs
                            term = Isa.Parenthesized $ foldl Isa.App con termArgs
                            arg = Isa.Var (Isa.Name "x")
                        in (uname', [arg,pat], term)


{-|
  This function converts a Haskell data type declaration into a
  Isabelle data type definition .
-}
convertDataDecl :: Hs.Decl -> ContextM Isa.DatatypeDef
convertDataDecl (Hs.DataDecl _loc _kind _context tyconN tyvarNs condecls _deriving)
    = let strip (Hs.QualConDecl _loc _FIXME _context decl) = decl
          decls = map strip condecls
      in do tyvars <- mapM convert tyvarNs
            tycon  <- convert tyconN
            decls' <- mapM cnvt decls
            return $ Isa.DatatypeDef (Isa.TypeSpec tyvars tycon) decls'
              where cnvt (Hs.ConDecl name types)
                        = do name'  <- convert name
                             tyvars <- mapM convert types
                             return $ Isa.Constructor name' tyvars
                    cnvt (Hs.RecDecl name fields) = 
                        let types = map snd (flattenRecFields fields)
                        in do name'  <- convert name
                              tyvars <- mapM convert types
                              return $ Isa.Constructor name' tyvars

{-|
  Instances of this class constitute pairs of types s.t. the first one
  (a Haskell entity) can be converted into the last one (an Isabelle entity).
  
  Instance declarations are supposed to implement 'convert'' instead of 
  'convert'. The latter uses the first by adding further boilerplate code.
-}
class Show a => Convert a b | a -> b where
    convert' :: (Convert a b) => a -> ContextM b
    convert  :: (Convert a b) => a -> ContextM b
    convert hsexpr = withUpdatedContext backtrace 
                       (\bt -> let frameName = "frame" ++ show (length bt)
                               in prettyShow' frameName hsexpr : bt)
                     $ convert' hsexpr

instance Convert HskModule Isa.Cmd where
    convert' (HskModule _loc modul dependentDecls)
        = do thy <- convert modul
             env <- queryContext globalEnv
             custs <- queryCustomisations
             let imps  = filter (not . isStandardTheory) (lookupImports thy env custs)
             withUpdatedContext theory (\t -> assert (t == Isa.Theory "Scratch") thy) 
               $ do cmds <- mapM convert dependentDecls
                    return (Isa.TheoryCmd thy imps cmds)
        where isStandardTheory (Isa.Theory n) = n `elem` used_thy_names


lookupImports :: Isa.Theory -> Env.GlobalE -> Customisations -> [Isa.Theory]
lookupImports thy globalEnv custs
    = map (rename .(\(Env.EnvImport name _ _) ->  Env.toIsa name))
        $ Env.lookupImports_OrLose (Env.fromIsa thy) globalEnv
    where rename orig@(Isa.Theory name) = case getCustomTheory custs (Hs.ModuleName name) of
                                   Nothing -> orig
                                   Just ct -> getCustomTheoryName ct

instance Convert HskDependentDecls Isa.Cmd where
    -- Mutual recursive function definitions must be specified specially
    -- in Isabelle/HOL (via an explicit "and" statement between the
    -- definitions that are dependent on each other.)
    convert' (HskDependentDecls [])  = return (Isa.Block [])
    convert' (HskDependentDecls [d]) = convert d
    convert' (HskDependentDecls decls@(decl:_))
        | isFunBind decl
            = assert (all isFunBind decls)
              $ do funcmds <- mapM convert decls
                   let (names, sigs, eqs) = unzip3 (map splitFunCmd funcmds)
                   return (Isa.FunCmd names sigs (concat eqs))
        | isDataDecl decl
            = assert (all isDataDecl decls)
              $ do dataDefs <- mapM convertDataDecl decls
                   auxCmds <- mapM generateRecordAux decls
                   return $ Isa.Block (Isa.DatatypeCmd dataDefs : concat auxCmds)

        where isFunBind (Hs.FunBind _) = True
              isFunBind _             = False
              isDataDecl (Hs.DataDecl _ _ _ _ _ _ _) = True
              isDataDecl _ = False
              splitFunCmd (Isa.FunCmd [n] [s] eqs) = (n, s, eqs)

instance Convert Hs.Module Isa.Cmd where
    convert' (Hs.Module loc modul _ _ _exports _imports decls)
        = dieWithLoc loc "Internal Error: Each Hs.Module should have been pre-converted to HskModule."


--- Trivially convertable stuff.

instance Convert Hs.ModuleName Isa.Theory where
    convert' m = return (Env.toIsa (Env.fromHsk m :: Env.ModuleID))

instance Convert Hs.Name Isa.Name where
    convert' n = return (Env.toIsa (Env.fromHsk n :: Env.EnvName))

instance Convert Hs.QName Isa.Name where
    convert' qn = return (Env.toIsa (Env.fromHsk qn :: Env.EnvName))

instance Convert Hs.Assoc Isa.Assoc where
    convert' a = return (Env.toIsa (Env.fromHsk a :: Env.EnvAssoc))

instance Convert Hs.Type Isa.Type where
    convert' t = return (Env.toIsa (Env.fromHsk t :: Env.EnvType))

instance Convert Hs.BangType Isa.Type where
    convert' t@(Hs.BangedTy _)   = pattern_match_exhausted "Hs.BangType -> Isa.Type" t
    convert' (Hs.UnBangedTy typ) = convert typ

instance Convert Hs.QOp Isa.Term where
    convert' (Hs.QVarOp qname) = do qname' <- convert qname; return (Isa.Var qname')
    convert' (Hs.QConOp qname) = do qname' <- convert qname; return (Isa.Var qname')
    -- convert' junk = pattern_match_exhausted "Hs.QOp -> Isa.Term" junk

instance Convert Hs.Op Isa.Name where
    convert' (Hs.VarOp qname) = convert qname
    convert' (Hs.ConOp qname) = convert qname
    -- convert' junk = pattern_match_exhausted "HsOp -> Isa.Name" junk

instance Convert Hs.Literal Isa.Literal where
    convert' (Hs.Int i)      = return (Isa.Int i)
    convert' (Hs.Char ch)    = return (Isa.Char ch)
    convert' (Hs.String str) = return (Isa.String str)
    convert' junk           = pattern_match_exhausted "HsLiteral -> Isa.Literal" junk


--- Not so trivially convertable stuff.

instance Convert Hs.Decl Isa.Cmd where
    convert' (Hs.TypeDecl _loc tyconN tyvarNs typ)
        = do tyvars <- mapM convert tyvarNs
             tycon  <- convert tyconN
             typ'   <- convert typ
             return (Isa.TypesCmd [(Isa.TypeSpec tyvars tycon, typ')])
                                
    convert' decl@(Hs.DataDecl _ _ _ _ _ _ _) = 
        do dataDef <- convertDataDecl decl
           accCmds <- generateRecordAux decl
           return $ Isa.Block (Isa.DatatypeCmd [dataDef] : accCmds)
    convert' (Hs.InfixDecl _loc assoc prio ops)
        = do (assocs, prios) <- mapAndUnzipM (lookupInfixOp . toQOp) ops 
             assert (all (== assoc) assocs && all (== prio) prios) 
               $ return (Isa.Block [])
        where toQOp (Hs.VarOp n) = Hs.QVarOp (Hs.UnQual n)
              toQOp (Hs.ConOp n) = Hs.QConOp (Hs.UnQual n)

    convert' (Hs.TypeSig _loc names typ)
        = do globalEnv <- queryContext globalEnv
             modul     <- queryContext currentModule
             types     <- liftM catMaybes $ mapM (lookupType . Hs.UnQual) names
             assert (all (== typ) types) 
               $ return (Isa.Block [])
                         
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
    convert' (Hs.FunBind matchs)
        = do let (names, patterns, bodies, wbinds) = unzip4 (map splitMatch matchs)
             assert (all (== head names) (tail names)) (return ())
             assert (all isEmpty wbinds) (return ())      -- all decls are global at this point.
             ftype      <- lookupType (Hs.UnQual (names!!0)) -- as all
                                                        -- names are
                                                        -- equal, pick
                                                        -- first one.
             name'      <- convert' (names!!0)
             fsig'      <- (case ftype of Nothing -> return Isa.TyNone
                                          Just t  -> convert' t) >>= (return . Isa.TypeSig name')
             fname'     <- convert (names!!0)          
             -- each pattern is itself a list of Hs.Pat. 
             patsNames  <- mapM (mapM convert) patterns
             let patsNames' = map unzip patsNames
                 patterns'  = map fst patsNames'
                 aliases    = map (concat.snd) patsNames'
             bodies'    <- withFunctionType' ftype $
                                mapM convert bodies
             let bodies'' = zipWith mkSimpleLet aliases bodies'
             thy        <- queryContext theory
             return $ Isa.FunCmd [fname'] [fsig'] (zip3 (repeat fname') patterns' bodies'')
       where splitMatch (Hs.Match _loc name patterns (Hs.UnGuardedRhs body) wherebind)
                 = (name, patterns, body, wherebind)
             isEmpty wherebind = case wherebind of Hs.BDecls [] -> True; _ -> False

    convert' (Hs.PatBind loc pattern rhs _wherebinds)
        = case pattern of
            pat@(Hs.PVar name) 
                -> do name' <- convert name
                      (pat', aliases)  <- convert pat
                      rhs'  <- convert rhs
                      let rhs'' = mkSimpleLet aliases rhs'
                      ftype <- lookupType (Hs.UnQual name)
                      sig'  <- -- trace (prettyShow' "ftype" ftype)$
                               (case ftype of 
                                  Nothing -> return Isa.TyNone
                                  Just t  -> convert' t) >>= (return . Isa.TypeSig name') 
                      return $ Isa.DefinitionCmd name' sig' (pat', rhs'')
            _   -> dieWithLoc loc (Msg.complex_toplevel_patbinding)
    
    convert' decl@(Hs.ClassDecl _ ctx classN _ _ class_decls)
        = check_class_decl decl
            $ do let superclassNs   = extractSuperclassNs ctx
                 superclassNs' <- mapM convert superclassNs
                 let superclassNs'' = if null superclassNs' then [Isa.Name "type"]
                                                            else superclassNs'
                 classN'       <- convert classN
                 typesigs'     <- concatMapM convertToTypeSig class_decls
                 return (Isa.ClassCmd classN' superclassNs'' typesigs')
        where
          check_class_decl (Hs.ClassDecl loc ctx classN varNs fundeps decls) cont
              | length varNs /= 1          = dieWithLoc loc (Msg.only_one_tyvar_in_class_decl)
              | not (null fundeps)         = dieWithLoc loc (Msg.no_fundeps_in_class_decl)
              | not (all isTypeSig decls)  = dieWithLoc loc (Msg.no_default_methods_in_class_decl)
              | otherwise                  = cont
          isTypeSig decl = case decl of 
                             Hs.ClsDecl (Hs.TypeSig _ _ _) -> True
                             _                           -> False
          convertToTypeSig (Hs.ClsDecl (Hs.TypeSig _ names typ))
                  = do names' <- mapM convert names
                       typ'   <- convert typ
                       return (map (flip Isa.TypeSig typ') names')

    convert' (Hs.InstDecl loc ctx classqN tys inst_decls)
        | length tys /= 1          = dieWithLoc loc (Msg.only_one_tyvar_in_class_decl)
        | not (isTyCon (head tys)) = dieWithLoc loc (Msg.only_specializing_on_tycon_allowed)
        | otherwise
            = do classqN'   <- convert classqN
                 type'      <- convert (head tys)
                 identifier <- lookupIdentifier_Type classqN
                 let classinfo
                                   = case fromJust identifier of
                                       Env.Type (Env.Class _ classinfo) -> classinfo
                                       t -> error $ "found:\n" ++ show t
                 let methods       = Env.methodsOf classinfo
                 let classVarN     = Env.classVarOf classinfo
                 let inst_envtype  = Env.fromHsk (head tys)
                 let tyannots = map (mk_method_annotation classVarN inst_envtype) methods
                 -- Methods must be explicitly annotated in Isar/HOL to keep
                 -- the ability to resolve the types in all cases.
                 withUpdatedContext globalEnv (\e -> Env.augmentGlobalEnv e tyannots) $
                   do decls' <- mapM convert (map toHsDecl inst_decls)
                      return (Isa.InstanceCmd classqN' type' decls')
        where 
          isTyCon t = case t of { Hs.TyCon _ -> True; _ -> False }
          toHsDecl (Hs.InsDecl decl) = decl

          mk_method_annotation :: Env.EnvName -> Env.EnvType -> Env.Identifier -> Env.Identifier
          mk_method_annotation tyvarN tycon class_method_annot
              = assert (Env.isTypeAnnotation class_method_annot)
                  $ let lexinfo = Env.lexInfoOf class_method_annot
                        typ     = Env.typeOf lexinfo
                        typ'    = Env.substituteTyVars [(Env.EnvTyVar tyvarN, tycon)] typ
                    in Env.Constant (Env.TypeAnnotation (lexinfo { Env.typeOf = typ' }))

    convert' junk = pattern_match_exhausted "Hs.Decl -> Isa.Cmd" junk


instance Convert Hs.Binds [Isa.Cmd] where
    convert' (Hs.BDecls decls) = mapM convert decls
    convert' junk = pattern_match_exhausted "Hs.Binds -> Isa.Cmd" junk

mkList :: [Isa.Term] -> Isa.Term
mkList = foldr
         (\x xs -> Isa.App (Isa.App (Isa.Var (Isa.Name "List.Cons")) x) xs)
         (Isa.Var (Isa.Name "List.Nil"))

mkSimpleLet :: [(Isa.Name, Isa.Term)] -> Isa.Term -> Isa.Term
mkSimpleLet [] body = body
mkSimpleLet binds body = Isa.Let binds' body
    where binds' = map (\(a,b) -> (Isa.Var a, b)) binds

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

convertPat :: Hs.Pat -> PatternM Isa.Pat
convertPat (Hs.PVar name) = 
    do name' <- liftConvert $ convert name
       return (Isa.Var name')
convertPat (Hs.PLit lit) = 
    do lit' <- liftConvert $ convert lit
       return (Isa.Literal lit')
              
convertPat infixapp@Hs.PInfixApp{} = 
    do (Hs.PInfixApp p1 qname p2) <- liftConvert $ fixOperatorFixities' infixapp
       p1' <- convertPat p1 
       qname'   <- liftConvert $ convert qname
       p2' <- convertPat p2
       return (Isa.App (Isa.App (Isa.Var qname') p1') p2')

convertPat (Hs.PApp qname pats) = 
    do qname' <- liftConvert $ convert qname
       pats' <- mapM convertPat pats
       return $ foldl Isa.App (Isa.Var qname') pats'
       
convertPat (Hs.PTuple comps) = 
    convertPat (foldr hskPPair (Hs.PParen (last comps)) (init comps))

convertPat (Hs.PList []) =
    do list_datacon_name <- liftConvert $ convert (Hs.Special Hs.ListCon)
       return (Isa.Var list_datacon_name)

convertPat (Hs.PList els) =
    convertPat $ foldr hskPCons hskPNil els

convertPat (Hs.PParen pat) = 
    do pat' <- convertPat pat
       return (Isa.Parenthesized pat')

convertPat (Hs.PRec qname fields) = 
    do mbConstr <- liftConvert $ lookupIdentifier_Constant qname
       case mbConstr of
         Just (Env.Constant (Env.Constructor (Env.RecordConstr _ _ recFields))) -> 
             do isAs <- isInsideAsPattern
                let fields' = map (\(Hs.PFieldPat name pat) -> (Env.fromHsk name, pat)) fields
                    toSimplePat (Env.RecordField iden _) = 
                        case lookup iden fields' of
                          Nothing -> if isAs
                                     then liftConvert . liftGensym . liftM Isa.Var . liftM Isa.Name $
                                          gensym "a"
                                     else return (Isa.Var (Isa.Name "_"))
                          Just pat -> convertPat pat
                recArgs <- mapM toSimplePat recFields
                qname' <- liftConvert $ convert qname
                return $ Isa.Parenthesized (foldl Isa.App (Isa.Var qname') recArgs)
         _ -> liftConvert . die $ "Record constructor " ++ Msg.quote qname ++ " is not declared in environment!"

convertPat (Hs.PAsPat name pat) = 
    do name' <- liftConvert $ convert name
       pat' <- withAsPattern $ convertPat pat
       addAlias (name', pat')
       return pat'
convertPat (Hs.PWildCard) = 
    do isAs <- isInsideAsPattern
       if isAs
         then liftConvert . liftGensym . liftM Isa.Var . liftM Isa.Name $
              gensym "a"
         else return (Isa.Var (Isa.Name "_"))

convertPat junk = liftConvert $ pattern_match_exhausted 
                  "Hs.Pat -> Isa.Term" 
                  junk
instance Convert Hs.Pat (Isa.Pat, [(Isa.Name, Isa.Term)]) where
    convert'  = runPatternM . convertPat

instance Convert Hs.Rhs Isa.Term where
    convert' (Hs.UnGuardedRhs exp) = convert exp
    -- convert (Hs.GuardedRhss rhss) ; FIXME
    convert' junk = pattern_match_exhausted "Hs.Rhs -> Isa.Term" junk

instance Convert Hs.FieldUpdate (Isa.Name, Isa.Term) where
    convert' (Hs.FieldUpdate qname exp)
        = do qname' <- convert qname
             exp'   <- convert exp
             return (qname', exp')

instance Convert Hs.Alt (Isa.Term, Isa.Term) where
    convert' (Hs.Alt _loc pat (Hs.UnGuardedAlt exp) _wherebinds)
        = do (pat',aliases) <- convert pat
             exp' <- convert exp
             let exp'' = mkSimpleLet aliases exp'
             return (pat', exp'')
    convert' junk 
        = pattern_match_exhausted "Hs.Alt -> (Isa.Term, Isa.Term)" junk


instance Convert Hs.Exp Isa.Term where
    convert' (Hs.Lit lit)       = convert lit   >>= (\l -> return (Isa.Literal l))
    convert' (Hs.Var qname)     =
        do qname' <- getCurrentMonadFunction qname
           convert qname' >>= (\n -> return (Isa.Var n))
    convert' (Hs.Con qname)     = convert qname >>= (\n -> return (Isa.Var n))
    convert' (Hs.Paren exp)     = convert exp   >>= (\e -> return (Isa.Parenthesized e))
    -- convert' (Hs.WildCard)      = return (Isa.Var (Isa.Name "_"))
    convert' (Hs.NegApp exp)    = convert (hsk_negate exp)

    convert' (Hs.List [])       = do list_datacon_name <- convert (Hs.Special Hs.ListCon)
                                     return (Isa.Var list_datacon_name)
    convert' (Hs.List exps)
        = convert $ foldr hsk_cons hsk_nil exps

    -- We have to wrap the last expression in an explicit HsParen as that last
    -- expression may itself be a pair. If we didn't, we couldn't distinguish
    -- between "((1,2), (3,4))" and "((1,2), 3, 4)" afterwards anymore.
    convert' (Hs.Tuple exps)    = convert (foldr hsk_pair (Hs.Paren (last exps)) (init exps))

    convert' (Hs.App exp1 exp2)
        = do exp1' <- convert exp1
             exp2' <- withPossibleLift exp1 $ convert exp2
             return (Isa.App exp1' exp2')

    convert' infixapp@(Hs.InfixApp _ _ _)
        = do (Hs.InfixApp exp1 op exp2) <- fixOperatorFixities infixapp
             exp1' <- convert exp1 
             op'   <- convert op
             exp2' <- if isApp op
                       then withPossibleLift exp1 $ convert exp2
                       else convert exp2
             return (mkInfixApp exp1' op' exp2')
        where 
          uname (Hs.Qual _ n) = n
          uname (Hs.UnQual n) = n
          isApp (Hs.QVarOp qname) =
              case uname qname of
                Hs.Ident _ -> False
                Hs.Symbol sym -> sym == "$"
          isApp _ = False
          mkInfixApp t1 op t2 = Isa.App (Isa.App op t1) t2

    convert' (Hs.LeftSection e qop)
        = do e'   <- convert e
             qop' <- convert qop
             g    <- liftGensym (genIsaName (Isa.Name "arg"))
             return (makeLambda [g] $ Isa.App (Isa.App qop' e') (Isa.Var g))

    convert' (Hs.RightSection qop e)
        = do e'   <- convert e
             qop' <- convert qop
             g <- liftGensym (genIsaName (Isa.Name "arg"))
             return (makeLambda [g] $ Isa.App (Isa.App qop' (Isa.Var g)) e')

    convert' (Hs.RecConstr qname updates) = 
        do mbConstr <- lookupIdentifier_Constant qname
           case mbConstr of
             Just (Env.Constant (Env.Constructor (Env.RecordConstr _ _ recFields))) -> 
                 let updates' = map (\(Hs.FieldUpdate name exp) -> (Env.fromHsk name, exp)) updates
                     toSimplePat (Env.RecordField iden _) = 
                         case lookup iden updates' of
                           Nothing -> Hs.Var (Hs.UnQual (Hs.Ident "arbitrary"))
                           Just exp -> exp
                     recArgs = map toSimplePat recFields
                 in convert' $ foldl Hs.App (Hs.Con qname) recArgs
             _ -> die $ "Record constructor " ++ Msg.quote qname ++ " is not declared in environment!"

    convert' (Hs.RecUpdate exp updates) = 
        do exp' <- convert exp
           fstupd:upds <- mapM convUpd updates
           let updateFunction = Isa.Parenthesized (foldr comp fstupd upds)
           return $ Isa.App updateFunction exp'
       where comp a b = Isa.App (Isa.App (Isa.Var (Isa.Name "o")) a) b
             convUpd (Hs.FieldUpdate fname fexp) =
                                do fexp' <- convert fexp
                                   let ufun = Isa.Var (Isa.Name ("update_" ++ unqual fname))
                                   return $ Isa.App ufun fexp'
             unqual (Hs.Qual _ n) = uname n
             unqual (Hs.UnQual n) = uname n
             uname (Hs.Ident n) = n
             uname (Hs.Symbol n) = n

    convert' (Hs.If t1 t2 t3)
        = do t1' <- convert t1; t2' <- convert t2; t3' <- convert t3
             return (Isa.If t1' t2' t3')

    convert' (Hs.Case exp alts)
        = do exp'  <- convert exp
             alts' <- mapM convert alts
             return $ Isa.Case exp' alts'

    convert' x@(Hs.Lambda _loc pats body)
        = do patsNames  <- mapM convert pats
             let (pats', aliases) = unzip patsNames
                 aliases' = concat aliases
             body'  <- convert body
             let body'' = mkSimpleLet aliases' body'
             if all isVar pats' then return $ makeLambda [n | Isa.Var n <- pats'] body''
                                else makePatternMatchingLambda pats' body''
          where isVar (Isa.Var _)   = True
                isVar _             = False

    convert' expr@(Hs.Let (Hs.BDecls bindings) body)
        = let (_, patbindings) = partition isTypeSig bindings
          in assert (all isPatBinding patbindings)
             $ do let (pats, rhss) = unzip (map (\(Hs.PatBind _ pat rhs _) -> (pat, rhs)) patbindings)
                  patsNames <- mapM convert pats
                  let (pats', aliases) = unzip patsNames
                  rhss' <- mapM convert rhss
                  let rhss'' = zipWith mkSimpleLet aliases rhss'
                  body' <- convert body
                  return (Isa.Let (zip pats' rhss'') body')
          where isTypeSig (Hs.TypeSig _ _ _)      = True
                isTypeSig _                      = False
                isPatBinding (Hs.PatBind _ _ _ (Hs.BDecls [])) = True
                isPatBinding _                   = False
                
    convert' (Hs.ListComp e stmts) 
        = do e'     <- convert e
             stmts' <- liftM concat $ mapM convertListCompStmt stmts
             return (Isa.ListComp e' stmts')
        where convertListCompStmt (Hs.Qualifier b)     = convert b >>= (return . (:[]) . Isa.Guard)
              convertListCompStmt (Hs.Generator _ p e) = do (p',as) <- convert p
                                                            let gens = mkSimpleGens as
                                                            e' <- convert e
                                                            return $ [Isa.Generator (p', e')] ++ gens
                                                                  
              convertListCompStmt (Hs.LetStmt _)
                  = die "Let statements not supported in List Comprehensions."
              mkSimpleGens = map (\(n,t) -> Isa.Generator (Isa.Var n, mkList [t]))
    convert' (Hs.Do stmts)
        = do isaStmts <- liftM concat $ mapM convert stmts
             mbDo <- getCurrentMonadDoSyntax
             case mbDo of
               Nothing -> die "Do syntax is used without sufficient type information!"
               Just (DoParen pre post) -> 
                   return $ Isa.DoBlock pre isaStmts post

    convert' junk = pattern_match_exhausted "Hs.Exp -> Isa.Term" junk

instance Convert Hs.Stmt [Isa.Stmt] where

    convert' (Hs.Generator _ pat exp) = 
        do exp' <- convert exp
           (pat', aliases) <- convert pat
           aliases' <- mkDoLet aliases
           return (Isa.DoGenerator pat' exp' : aliases')
    convert' (Hs.Qualifier exp) = liftM ( (:[]) . Isa.DoQualifier) (convert exp)
    convert' (Hs.LetStmt binds) =
        case binds of
          Hs.BDecls [Hs.PatBind _ pat (Hs.UnGuardedRhs exp) _] ->
              do exp' <- convert exp
                 (pat', aliases) <- convert pat
                 aliases' <- mkDoLet aliases
                 ret <- mkReturn
                 return (Isa.DoGenerator pat' (Isa.App ret exp') : aliases')
             -- liftM2 Isa.DoGenerator (convert pat) (convert (Hs.App (Hs.Var (Hs.UnQual (Hs.Ident "return"))) exp))
          def -> pattern_match_exhausted "Hs.Stmt -> Isa.Stmt" def

mkReturn :: ContextM Isa.Term
mkReturn = convert . Hs.Var . Hs.UnQual .Hs.Ident $ "return"

mkDoLet :: [(Isa.Name, Isa.Term)] -> ContextM [Isa.Stmt]
mkDoLet aliases = 
    do ret <- mkReturn
       let mkSingle (name, term) = Isa.DoGenerator (Isa.Var name) (Isa.App ret term)
       return $ map mkSingle aliases

{-|
  We desugare lambda expressions to true unary functions, i.e. to
  lambda expressions binding only one argument.
 -}
makeLambda :: [Isa.Name] -> Isa.Term -> Isa.Term
makeLambda varNs body
    = assert (not (null varNs)) $ foldr Isa.Lambda body varNs

{-|
  Since HOL doesn't have true n-tuple constructors (it uses nested
  pairs to represent n-tuples), we simply return a lambda expression
  that takes n parameters and constructs the nested pairs within its
  body.
 -}

makeTupleDataCon :: Int -> ContextM Isa.Term
makeTupleDataCon n     -- n < 2  cannot happen (cf. Language.Haskell.Exts.Hs.TupleCon)
    = assert (n > 2) $ -- n == 2, i.e. pairs, can and are dealt with by usual conversion.
      do argNs  <- mapM (liftGensym . genHsQName) (replicate n (Hs.UnQual (Hs.Ident "arg")))
         args   <- return (map Hs.Var argNs)
         argNs' <- mapM convert argNs
         args'  <- convert (Hs.Tuple args)
         return $ Isa.Parenthesized (makeLambda argNs' args')
    where pair x y = Hs.App (Hs.App (Hs.Con (Hs.Special (Hs.TupleCon 2))) x) y

{-|
  HOL does not support pattern matching directly within a lambda
  expression, so we transform a @Hs.Lambda pat1 pat2 .. patn -> body@ to
  
  @
  Isa.Lambda g1 .
     Isa.Case g1 of pat1' =>
       Isa.Lambda g2 .
         Isa.Case g2 of pat2' => ... => Isa.Lambda gn .
                                          Isa.Case gn of patn' => body'
  @
  where @g1@, ..., @gn@ are fresh identifiers.
-}
makePatternMatchingLambda :: [Isa.Pat] -> Isa.Term -> ContextM Isa.Term
makePatternMatchingLambda patterns theBody
    = foldM mkMatchingLambda theBody (reverse patterns) -- foldM is a left fold.
      where mkMatchingLambda body pat
                = do g <- liftGensym (genIsaName (Isa.Name "arg"))
                     return $ Isa.Lambda g (Isa.Case (Isa.Var g) [(pat, body)])


makeRecordCmd :: Hs.Name  -- ^type constructor
              -> [Hs.Name] -- ^type variable arguments to the constructor
              -> [Hs.ConDecl] -- ^a singleton list containing a record declaration
              -> ContextM Isa.Cmd   -- ^the resulting record declaration
makeRecordCmd tyconN tyvarNs [Hs.RecDecl name slots] -- cf. `isRecDecls'
    = do tycon  <- convert tyconN
         tyvars <- mapM convert tyvarNs
         slots' <- concatMapM cnvSlot slots
         return $ Isa.RecordCmd (Isa.TypeSpec tyvars tycon) slots'
    where cnvSlot (names, typ)
              = do names' <- mapM convert names
                   typ'   <- convert typ
                   return (zip names' (cycle [typ']))
 

{-|
  Hsx parses every infix application simply from left to right without
  taking operator associativity or binding priority into account. So
  we gotta fix that up ourselves. (We also properly consider infix
  declarations to get user defined operator right.)
-}
fixOperatorFixities :: Hs.Exp -> ContextM Hs.Exp

-- Notice that `1 * 2 + 3 / 4' is parsed as `((1 * 2) + 3) / 4', i.e.
-- 
--    Hs.InfixApp (Hs.InfixApp (Hs.InfixApp 1 * 2) + 3) / 4
--
-- whereas `1 * 2 + (3 / 4)' is parsed as
--
--    Hs.InfixApp (Hs.InfixApp 1 * 2) + (HsParen (Hs.InfixApp 3 / 4))
--
-- and `1 * (2 + 3) / 4' is parsed as
--
--    Hs.InfixApp (Hs.InfixApp 1 (HsParen (Hs.InfixApp 2 + 3))) / 4
--
-- Thus we _know_ that the second operand of an infix application,
-- i.e. the e2 in `Hs.InfixApp e1 op e2', can _never_ be a bare infix
-- application that we might have to consider during fixup.
--  
fixOperatorFixities app@(Hs.InfixApp (Hs.InfixApp e1 op1 e2) op2 e3)
    -- We assume that `(t1, op1, t2)' is correct already
    -- and from above, we also know that `t3' cannot possibly
    -- interfere, so we just have to find the proper place of `op2'.
    = do (assoc1', prio1)  <- lookupInfixOp op1
         (assoc2', prio2)  <- lookupInfixOp op2
         let assoc1 = normalizeAssociativity assoc1'
         let assoc2 = normalizeAssociativity assoc2'
         case prio1 `compare` prio2 of
           GT -> return app
           LT -> liftM (Hs.InfixApp e1 op1) (fixOperatorFixities (Hs.InfixApp e2 op2 e3))
           EQ -> if assoc2 /= assoc1 then
                     die (Msg.assoc_mismatch op1 assoc1 op2 assoc2)
                 else case assoc2 of
                        Hs.AssocLeft  -> return app
                        Hs.AssocRight -> return (Hs.InfixApp e1 op1 (Hs.InfixApp e2 op2 e3))
                        Hs.AssocNone  -> die ("fixupOperatorFixities: Internal error " ++
                                               "(AssocNone should have already been normalized away.)")
fixOperatorFixities nonNestedInfixApp = return nonNestedInfixApp


{-|
  Hsx parses every infix application simply from left to right without
  taking operator associativity or binding priority into account. So
  we gotta fix that up ourselves. (We also properly consider infix
  declarations to get user defined operator right.)
-}
fixOperatorFixities' :: Hs.Pat -> ContextM Hs.Pat
fixOperatorFixities' app@(Hs.PInfixApp (Hs.PInfixApp e1 op1 e2) op2 e3)
    = do (assoc1', prio1)  <- lookupInfixOpName op1
         (assoc2', prio2)  <- lookupInfixOpName op2
         let assoc1 = normalizeAssociativity assoc1'
         let assoc2 = normalizeAssociativity assoc2'
         case prio1 `compare` prio2 of
           GT -> return app
           LT -> liftM (Hs.PInfixApp e1 op1) (fixOperatorFixities' (Hs.PInfixApp e2 op2 e3))
           EQ -> if assoc2 /= assoc1 then
                     die (Msg.assoc_mismatch op1 assoc1 op2 assoc2)
                 else case assoc2 of
                        Hs.AssocLeft  -> return app
                        Hs.AssocRight -> return (Hs.PInfixApp e1 op1 (Hs.PInfixApp e2 op2 e3))
                        Hs.AssocNone  -> die ("fixupOperatorFixities: Internal error " ++
                                               "(AssocNone should have already been normalized away.)")
fixOperatorFixities' nonNestedInfixApp = return nonNestedInfixApp


{-|
  Enforces left associativity as default.
-}
normalizeAssociativity :: Hs.Assoc -> Hs.Assoc
normalizeAssociativity (Hs.AssocNone) = Hs.AssocLeft -- as specified in Haskell98.
normalizeAssociativity etc = etc

{-|
  This function looks up the lexical information for the
  given constant identifier.
-}
lookupIdentifier_Constant :: Hs.QName -> ContextM (Maybe Env.Identifier)
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
lookupIdentifier_Type :: Hs.QName -> ContextM (Maybe Env.Identifier)
lookupIdentifier_Type qname
    = do globalEnv <- queryContext globalEnv
         modul     <- queryContext currentModule
         return (Env.lookupType (Env.fromHsk modul) (Env.fromHsk qname) globalEnv)

{-|
  This function looks up the fixity declaration for the given
  infix operator.
-}
lookupInfixOp :: Hs.QOp -> ContextM (Hs.Assoc, Int)
lookupInfixOp = lookupInfixOpName . qop2name
    where qop2name (Hs.QVarOp n) = n
          qop2name (Hs.QConOp n) = n
{-|
  This function looks up the fixity declaration for the given
  infix operator.
-}
lookupInfixOpName :: Hs.QName -> ContextM (Hs.Assoc, Int)
lookupInfixOpName qname
    = do identifier <- lookupIdentifier_Constant (qname)
         case identifier of
           Just (Env.Constant (Env.InfixOp _ envassoc prio)) 
                   -> return (Env.toHsk envassoc, prio)
           Nothing -> do globalEnv <- queryContext globalEnv;
                         warn (Msg.missing_infix_decl qname globalEnv)
                         return (Hs.AssocLeft, 9) -- default values in Haskell98
    where qop2name (Hs.QVarOp n) = n
          qop2name (Hs.QConOp n) = n


{-|
  This function looks up the type for the given identifier.
-}
lookupType :: Hs.QName -> ContextM (Maybe Hs.Type)
lookupType fname
    -- We're interested in the type of a Constant.
    = do identifier <- lookupIdentifier_Constant fname
         case identifier of
           Nothing -> return Nothing
           Just id -> let typ = Env.typeOf (Env.lexInfoOf id) 
                      in if (typ == Env.EnvTyNone) then return Nothing
                                                    else return $ Just (Env.toHsk typ)


