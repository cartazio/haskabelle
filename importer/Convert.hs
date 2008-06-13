{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen

Conversion from abstract Haskell code to abstract Isar/HOL theory.
-}

module Importer.Convert (
  convertHskUnit
) where

import Language.Haskell.Hsx

import List (unzip4, partition)
import Monad
import Maybe

import Control.Monad.State

import Importer.Utilities.Misc
import Importer.Utilities.Gensym
import Importer.Preprocess
import Importer.ConversionUnit
import Importer.DeclDependencyGraph

import Importer.Mapping (initialGlobalEnv, adaptionTable)
import Importer.Adapt (adaptGlobalEnv, adaptIsaUnit)

import qualified Importer.IsaSyntax as Isa
import qualified Importer.Msg as Msg

import qualified Importer.LexEnv as Env

import qualified Data.Map as Map

convertHskUnit :: ConversionUnit -> ConversionUnit
convertHskUnit (HskUnit hsmodules _emptyEnv)
    = let hsmodules'     = map preprocessHsModule hsmodules
          globalenv_hsk  = Env.makeGlobalEnv_fromHsModules hsmodules'
          globalenv_hsk' = Env.mergeGlobalEnvs globalenv_hsk initialGlobalEnv
          globalenv_isa  = adaptGlobalEnv globalenv_hsk' adaptionTable
          hskmodules     = map (toHskModule globalenv_hsk') hsmodules'
          (isathys, _)   = runConversion globalenv_hsk' $ mapM convert hskmodules 
      in -- trace (prettyShow' "globalenv_isa" globalenv_isa) $ -- trace ("convertHskUnit") $
         let !r = adaptIsaUnit globalenv_hsk' adaptionTable 
                  $ IsaUnit isathys globalenv_isa 
         in -- trace (prettyShow' "adaptedIsaUnits" r) r
           r
    where toHskModule globalEnv (HsModule loc modul _exports _imports decls)
              = let declDepGraph = makeDeclDepGraph globalEnv modul decls 
                in -- trace (prettyShow' "declDepGraph" (flattenDeclDepGraph declDepGraph)) $
                   HskModule loc modul 
                     $ map HskDependentDecls (flattenDeclDepGraph declDepGraph)


-- The naming scheme "HsFoo" is treated as being owned by the parser
-- libary Language.Haskell.Hsx. We use "HskFoo" instead to
-- differentiate between what's defined by us and by that library. 
--
-- (Ok, this might sound somewhat confusing, at least we're consistent
-- about it.)

data HskModule = HskModule SrcLoc Module [HskDependentDecls]
  deriving (Show)

-- Contains all declarations that are dependent on each other,
-- i.e. all those functions that are mutually recursive.
data HskDependentDecls = HskDependentDecls [HsDecl]
  deriving (Show)


data Context    = Context
    {     
      _theory      :: Isa.Theory
    , _globalEnv   :: Env.GlobalE
    , _warnings    :: [Warning]
    , _backtrace   :: [String]
    , _gensymcount :: Int
    }

emptyContext = Context { _theory      = Isa.Theory "Scratch", -- FIXME: Default Module in Haskell
                         _globalEnv   = Env.emptyGlobalEnv,  --  is called `Main'; clashes with Isabelle.
                         _warnings    = [],
                         _backtrace   = [],
                         _gensymcount = 0 }

-- Instead of accessing a record directly by their `_foo' slots, we
-- use the respective `foo' surrogate which consists of an appropriate
-- getter and setter -- which allows functions to both query and
-- update a record by slot name.
type FieldSurrogate field = (Context -> field, Context -> field -> Context) 

theory      = (_theory,      \c f -> c { _theory      = f })
globalEnv   = (_globalEnv,   \c f -> c { _globalEnv   = f })
warnings    = (_warnings,    \c f -> c { _warnings    = f })
backtrace   = (_backtrace,   \c f -> c { _backtrace   = f })
gensymcount = (_gensymcount, \c f -> c { _gensymcount = f })

currentModule = (\c -> let (Isa.Theory n) = _theory c in Module n, \c f -> c)

type ContextM v = StateT Context (State GensymCount) v

runConversion :: Env.GlobalE -> ContextM v -> (v, Context)
runConversion env m = runGensym 0 (runStateT m (emptyContext { _globalEnv = env }))

queryContext :: (FieldSurrogate field) -> ContextM field
queryContext (query, _)
    = do context <- get; return (query context) 

updateContext :: (FieldSurrogate field) -> (field -> field) -> ContextM ()
updateContext (query, update) updateField
    = do context <- get
         put (update context (updateField (query context)))
         return ()

withUpdatedContext :: (FieldSurrogate field) -> (field -> field) -> ContextM a -> ContextM a
withUpdatedContext surrogate updateField body
     = do oldval <- queryContext surrogate
          updateContext surrogate updateField
          result <- body
          updateContext surrogate (\_ -> oldval)
          return result


newtype Warning = Warning String
  deriving (Show, Eq, Ord)

warn :: String -> ContextM ()
warn msg = updateContext warnings (\warnings -> warnings ++ [(Warning msg)])
     
die :: String -> ContextM t
die msg = do backtrace <- queryContext backtrace
             error $ msg ++ "\n\n"
                         ++ "Backtrace:\n"
                         ++ foldr1 (++) (map (++"\n\n") (reverse backtrace))

barf str obj = die (str ++ ": Pattern match exhausted for\n" ++ prettyShow obj)


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
             withUpdatedContext theory (\t -> assert (t == Isa.Theory "Scratch") thy) 
               $ do cmds <- mapM convert dependentDecls
                    return (Isa.TheoryCmd thy cmds)

instance Convert HskDependentDecls Isa.Cmd where
    -- Mutual recursive function definitions must be specified specially
    -- in Isabelle/HOL (via an explicit "and" statement between the
    -- definitions that are dependent on each other.)
    convert' (HskDependentDecls [])  = return (Isa.Block [])
    convert' (HskDependentDecls [d]) = convert d
    convert' (HskDependentDecls decls)
        = assert (all isFunBind decls)
            $ do funcmds <- mapM convert decls
                 let (names, sigs, eqs) = unzip3 (map splitFunCmd funcmds)
                 return (Isa.FunCmd names sigs (concat eqs))
        where isFunBind (HsFunBind _) = True
              isFunBind _             = False
              splitFunCmd (Isa.FunCmd [n] [s] eqs) = (n, s, eqs)

instance Convert HsModule Isa.Cmd where
    convert' (HsModule _loc modul _exports _imports decls)
        = die "Internal Error: Each HsModule should have been pre-converted to HskModule."


--- Trivially convertable stuff.

instance Convert Module Isa.Theory where
    convert' m = return (Env.toIsa (Env.fromHsk m :: Env.ModuleID))

instance Convert HsName Isa.Name where
    convert' n = return (Env.toIsa (Env.fromHsk n :: Env.EnvName))

instance Convert HsQName Isa.Name where
    convert' qn = return (Env.toIsa (Env.fromHsk qn :: Env.EnvName))

instance Convert HsAssoc Isa.Assoc where
    convert' a = return (Env.toIsa (Env.fromHsk a :: Env.EnvAssoc))

instance Convert HsType Isa.Type where
    convert' t = return (Env.toIsa (Env.fromHsk t :: Env.EnvType))

instance Convert HsBangType Isa.Type where
    convert' t@(HsBangedTy _)   = barf "HsBangType -> Isa.Type" t
    convert' (HsUnBangedTy typ) = convert typ

instance Convert HsQOp Isa.Term where
    convert' (HsQVarOp qname) = do qname' <- convert qname; return (Isa.Var qname')
    convert' (HsQConOp qname) = do qname' <- convert qname; return (Isa.Var qname')
    -- convert' junk = barf "HsQOp -> Isa.Term" junk

instance Convert HsOp Isa.Name where
    convert' (HsVarOp qname) = convert qname
    convert' (HsConOp qname) = convert qname
    -- convert' junk = barf "HsOp -> Isa.Name" junk

instance Convert HsLiteral Isa.Literal where
    convert' (HsInt i)      = return (Isa.Int i)
    convert' (HsString str) = return (Isa.String str)
    convert' junk           = barf "HsLiteral -> Isa.Literal" junk


--- Not so trivially convertable stuff.

instance Convert HsDecl Isa.Cmd where
    convert' (HsTypeDecl _loc tyconN tyvarNs typ)
        = do tyvars <- mapM convert tyvarNs
             tycon  <- convert tyconN
             typ'   <- convert typ
             return (Isa.TypesCmd [(Isa.TypeSpec tyvars tycon, typ')])

    convert' (HsDataDecl _loc _context tyconN tyvarNs condecls _deriving)
        = let strip (HsQualConDecl _loc _FIXME _context decl) = decl
              decls = map strip condecls
          in if isRecDecls decls then
                 makeRecordCmd tyconN tyvarNs decls
             else do tyvars <- mapM convert tyvarNs
                     tycon  <- convert tyconN
                     decls' <- mapM cnvt decls
                     return (Isa.DatatypeCmd (Isa.TypeSpec tyvars tycon) decls')
                 where cnvt (HsConDecl name types)
                           = do name'  <- convert name
                                tyvars <- mapM convert types
                                return $ Isa.Constructor name' tyvars
                       cnvt junk = barf ("Internal Error: " ++
                                         "HsRecDecl should have been dealt with elsewhere already.")
                                        junk

    convert' (HsInfixDecl _loc assoc prio ops)
        = do (assocs, prios) <- mapAndUnzipM (lookupInfixOp . toHsQOp) ops 
             assert (all (== assoc) assocs && all (== prio) prios) 
               $ return (Isa.Block [])
        where toHsQOp (HsVarOp n) = HsQVarOp (UnQual n)
              toHsQOp (HsConOp n) = HsQConOp (UnQual n)

    convert' (HsTypeSig _loc names typ)
        = do globalEnv <- queryContext globalEnv
             modul     <- queryContext currentModule
             types     <- liftM catMaybes $ mapM (lookupType . UnQual) names
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
    convert' (HsFunBind matchs)
        = do let (names, patterns, bodies, wbinds) = unzip4 (map splitMatch matchs)
             assert (all (== head names) (tail names)) (return ())
             assert (all isEmpty wbinds) (return ())      -- all decls are global at this point.
             ftype      <- lookupType (UnQual (names!!0)) -- as all names are equal, pick first one.
             name'      <- convert' (names!!0)
             fsig'      <- (case ftype of Nothing -> return Isa.TyNone
                                          Just t  -> convert' t) >>= (return . Isa.TypeSig name')
             fname'     <- convert (names!!0)           
             patterns'  <- mapM (mapM convert) patterns  -- each pattern is itself a list of HsPat.
             bodies'    <- mapM convert bodies
             thy        <- queryContext theory
             return $ Isa.FunCmd [fname'] [fsig'] (zip3 (cycle [fname']) patterns' bodies')
       where splitMatch (HsMatch _loc name patterns (HsUnGuardedRhs body) wherebind)
                 = (name, patterns, body, wherebind)
             isEmpty wherebind = case wherebind of HsBDecls [] -> True; _ -> False

    convert' (HsPatBind _loc pattern rhs _wherebinds)
        = case pattern of
            pat@(HsPVar name) 
                -> do name' <- convert name
                      pat'  <- convert pat
                      rhs'  <- convert rhs
                      ftype <- lookupType (UnQual name)
                      sig'  <- (case ftype of 
                                  Nothing -> return Isa.TyNone
                                  Just t  -> convert' t) >>= (return . Isa.TypeSig name') 
                      return $ Isa.DefinitionCmd name' sig' (pat', rhs')
            _   -> die "Complex pattern binding on toplevel is not supported by Isar/HOL."
    

    convert' junk = barf "HsDecl -> Isa.Cmd" junk


instance Convert HsBinds [Isa.Cmd] where
    convert' (HsBDecls decls) = mapM convert decls
    convert' junk = barf "HsBinds -> Isa.Cmd" junk


-- As we convert to Isa.Term anyway, we can translate each HsPat
-- type to a HsExp first, and then convert that in order to
-- reduce some code bloat. (Although it comes at cost of making
-- backtraces a bit confusing perhaps.)
--
instance Convert HsPat Isa.Term where
    convert' (HsPWildCard) = return $ Isa.Var (Isa.Name "_")
    convert' anything      = convertHsPat anything >>= convert

convertHsPat :: HsPat -> ContextM HsExp
convertHsPat (HsPLit literal) = return $ HsLit literal
convertHsPat (HsPVar name)    = return $ HsVar (UnQual name)
convertHsPat (HsPList pats)   = liftM HsList  $ mapM convertHsPat pats
convertHsPat (HsPTuple pats)  = liftM HsTuple $ mapM convertHsPat pats
convertHsPat (HsPParen pat)   = liftM HsParen $ convertHsPat pat
convertHsPat (HsPWildCard)    = return HsWildCard

convertHsPat (HsPInfixApp pat1 qname pat2)
    = do pat1' <- convertHsPat pat1
         pat2' <- convertHsPat pat2
         return $ HsInfixApp pat1' (HsQConOp qname) pat2'

convertHsPat (HsPApp qname pats)
    = do pats' <- mapM convertHsPat pats
         return $ foldl HsApp (HsCon qname) pats'

convertHsPat junk = barf "HsPat -> Isa.Term (convertHsPat: HsPat -> HsExp)" junk


instance Convert HsRhs Isa.Term where
    convert' (HsUnGuardedRhs exp) = convert exp
    -- convert (HsGuardedRhss rhss) ; FIXME
    convert' junk = barf "HsRhs -> Isa.Term" junk

instance Convert HsFieldUpdate (Isa.Name, Isa.Term) where
    convert' (HsFieldUpdate qname exp)
        = do qname' <- convert qname
             exp'   <- convert exp
             return (qname', exp')

instance Convert HsAlt (Isa.Term, Isa.Term) where
    convert' (HsAlt _loc pat (HsUnGuardedAlt exp) _wherebinds)
        = do pat' <- convert pat; exp' <- convert exp; return (pat', exp')
    convert' junk 
        = barf "HsAlt -> (Isa.Term, Isa.Term)" junk


instance Convert HsExp Isa.Term where
    convert' (HsLit lit)       = convert lit   >>= (\l -> return (Isa.Literal l))
    convert' (HsVar qname)     = convert qname >>= (\n -> return (Isa.Var n))
    convert' (HsCon qname)     = convert qname >>= (\n -> return (Isa.Var n))
    convert' (HsParen exp)     = convert exp   >>= (\e -> return (Isa.Parenthesized e))
    convert' (HsWildCard)      = return (Isa.Var (Isa.Name "_"))

    convert' (HsList [])       = do list_datacon_name <- convert (Special HsListCon)
                                    return (Isa.Var list_datacon_name)
    convert' (HsList exps)
        = convert $ foldr cons nil exps
          where cons x y = HsApp (HsApp (HsCon (Special HsCons)) x) y
                nil = HsList []

    convert' (HsTuple exps)    = convert (foldr1 pair exps)
        where pair x y 
                  = HsApp (HsApp (HsCon (Special (HsTupleCon 2))) x) y

    convert' (HsApp exp1 exp2)
        = do exp1' <- cnv exp1 ; exp2' <- cnv exp2
             return (Isa.App exp1' exp2')
          where cnv app@(HsCon (Special (HsTupleCon n))) 
                    | n < 2  = die ("Internal Error, (HsTupleCon " ++ show n ++ ")")
                    | n == 2 = convert app         -- pairs can be dealt with the usual way. 
                    | n > 2  = makeTupleDataCon n
                cnv etc = convert etc

    convert' infixapp@(HsInfixApp _ _ _)
        = do (HsInfixApp exp1 op exp2) <- fixOperatorFixities infixapp
             exp1' <- convert exp1 
             op'   <- convert op
             exp2' <- convert exp2
             return (mkInfixApp exp1' op' exp2')
        where 
          mkInfixApp t1 op t2 = Isa.App (Isa.App op t1) t2


    convert' (HsRecConstr qname updates)
        = do qname'   <- convert qname
             updates' <- mapM convert updates
             return $ Isa.RecConstr qname' updates'

    convert' (HsRecUpdate exp updates)
        = do exp'     <- convert exp
             updates' <- mapM convert updates
             return $ Isa.RecUpdate exp' updates'

    convert' (HsIf t1 t2 t3)
        = do t1' <- convert t1; t2' <- convert t2; t3' <- convert t3
             return (Isa.If t1' t2' t3')

    convert' (HsCase exp alts)
        = do exp'  <- convert exp
             alts' <- mapM convert alts
             return $ Isa.Case exp' alts'

    convert' (HsLambda _loc pats body)
        = do pats'  <- mapM convert pats
             body'  <- convert body
             if all isVar pats' then return $ Isa.Lambda [n | Isa.Var n <- pats'] body'
                                else makePatternMatchingLambda pats' body'
          where isVar (Isa.Var _)   = True
                isVar _             = False

    convert' expr@(HsLet (HsBDecls bindings) body)
        = let (_, patbindings) = partition isTypeSig bindings
          in assert (all isPatBinding patbindings)
             $ do let (pats, rhss) = unzip (map (\(HsPatBind _ pat rhs _) -> (pat, rhs)) patbindings)
                  pats' <- mapM convert pats
                  rhss' <- mapM convert rhss
                  body' <- convert body
                  return (Isa.Let (zip pats' rhss') body')
          where isTypeSig (HsTypeSig _ _ _)      = True
                isTypeSig _                      = False
                isPatBinding (HsPatBind _ _ _ (HsBDecls [])) = True
                isPatBinding _                   = False
                
    convert' junk = barf "HsExp -> Isa.Term" junk


-- Since HOL doesn't have true n-tuple constructors (it uses nested
-- pairs to represent n-tuples), we simply return a lambda expression
-- that takes n parameters and constructs the nested pairs within its
-- body.
makeTupleDataCon :: Int -> ContextM Isa.Term
makeTupleDataCon n     -- n < 2  cannot happen (cf. Language.Haskell.Hsx.HsTupleCon)
    = assert (n > 2) $ -- n == 2, i.e. pairs, can and are dealt with by usual conversion.
      do argNs  <- mapM (lift . genHsQName) (replicate n (UnQual (HsIdent "arg")))
         args   <- return (map HsVar argNs)
         argNs' <- mapM convert argNs
         args'  <- convert (HsTuple args)
         return $ Isa.Parenthesized (Isa.Lambda argNs' args')
    where pair x y = HsApp (HsApp (HsCon (Special (HsTupleCon 2))) x) y

-- HOL does not support pattern matching directly within a lambda
-- expression, so we transform a `HsLambda pat1 pat2 .. patn -> body' to
--
--   Isa.Lambda g1 .
--     Isa.Case g1 of pat1' =>
--       Isa.Lambda g2 .
--         Isa.Case g2 of pat2' => ... => Isa.Lambda gn .
--                                          Isa.Case gn of patn' => body'
--
--   where g1, ..., gn are fresh identifiers.
--
makePatternMatchingLambda :: [Isa.Term] -> Isa.Term -> ContextM Isa.Term
makePatternMatchingLambda patterns theBody
    = foldM mkMatchingLambda theBody (reverse patterns) -- foldM is a left fold.
      where mkMatchingLambda body pat
                = do g <- lift (genIsaName (Isa.Name "arg"))
                     return $ Isa.Lambda [g] (Isa.Case (Isa.Var g) [(pat, body)])


isRecDecls :: [HsConDecl] -> Bool
isRecDecls decls
    = case decls of
        -- Haskell allows that a data declaration may be mixed up arbitrarily
        -- by normal data constructor declarations and record declarations.
        -- As HOL does not support that kind of mishmash, we require that a
        -- data declaration either consists of exactly one record definition,
        -- or arbitrarily many data constructor definitions.
        (HsRecDecl _ _):rest -> assert (null rest) True
        decls                -> assert (all (not.isRecDecl) decls) False
    where isRecDecl (HsRecDecl _ _) = True
          isRecDecl _               = False

makeRecordCmd :: HsName -> [HsName] -> [HsConDecl] -> ContextM Isa.Cmd
makeRecordCmd tyconN tyvarNs [HsRecDecl name slots] -- cf. `isRecDecls'
    = do tycon  <- convert tyconN
         tyvars <- mapM convert tyvarNs
         slots' <- concatMapM cnvSlot slots
         return $ Isa.RecordCmd (Isa.TypeSpec tyvars tycon) slots'
    where cnvSlot (names, typ)
              = do names' <- mapM convert names
                   typ'   <- convert typ
                   return (zip names' (cycle [typ']))
 


-- Hsx parses every infix application simply from left to right without
-- taking operator associativity or binding priority into account. So
-- we gotta fix that up ourselves. (We also properly consider infix
-- declarations to get user defined operator right.)

fixOperatorFixities :: HsExp -> ContextM HsExp

-- Notice that `1 * 2 + 3 / 4' is parsed as `((1 * 2) + 3) / 4', i.e.
-- 
--    HsInfixApp (HsInfixApp (HsInfixApp 1 * 2) + 3) / 4
--
-- whereas `1 * 2 + (3 / 4)' is parsed as
--
--    HsInfixApp (HsInfixApp 1 * 2) + (HsParen (HsInfixApp 3 / 4))
--
-- and `1 * (2 + 3) / 4' is parsed as
--
--    HsInfixApp (HsInfixApp 1 (HsParen (HsInfixApp 2 + 3))) / 4
--
-- Thus we _know_ that the second operand of an infix application,
-- i.e. the e2 in `HsInfixApp e1 op e2', can _never_ be a bare infix
-- application that we might have to consider during fixup.
--  
fixOperatorFixities app@(HsInfixApp (HsInfixApp e1 op1 e2) op2 e3)
    -- We assume that `(t1, op1, t2)' is correct already
    -- and from above, we also know that `t3' cannot possibly
    -- interfere, so we just have to find the proper place of `op2'.
    = do (assoc1', prio1)  <- lookupInfixOp op1
         (assoc2', prio2)  <- lookupInfixOp op2
         let assoc1 = normalizeAssociativity assoc1'
         let assoc2 = normalizeAssociativity assoc2'
         case prio1 `compare` prio2 of
           GT -> return app
           LT -> liftM (HsInfixApp e1 op1) (fixOperatorFixities (HsInfixApp e2 op2 e3))
           EQ -> if assoc2 /= assoc1 then
                     die (Msg.assoc_mismatch op1 assoc1 op2 assoc2)
                 else case assoc2 of
                        HsAssocLeft  -> return app
                        HsAssocRight -> return (HsInfixApp e1 op1 (HsInfixApp e2 op2 e3))
                        HsAssocNone  -> die ("fixupOperatorFixities: Internal error " ++
                                               "(AssocNone should have already been normalized away.)")
fixOperatorFixities nonNestedInfixApp = return nonNestedInfixApp

normalizeAssociativity (HsAssocNone) = HsAssocLeft -- as specified in Haskell98.
normalizeAssociativity etc = etc


lookupIdentifier :: HsQName -> ContextM (Maybe Env.Identifier)
lookupIdentifier qname
    = do globalEnv <- queryContext globalEnv
         modul     <- queryContext currentModule
         return (Env.lookup (Env.fromHsk modul) (Env.fromHsk qname) globalEnv)

lookupInfixOp :: HsQOp -> ContextM (HsAssoc, Int)
lookupInfixOp qop
    = do identifier <- lookupIdentifier (qop2name qop)
         case identifier of
           Just (Env.InfixOp _ envassoc prio) -> return (Env.toHsk envassoc, prio)
           Nothing -> do globalEnv <- queryContext globalEnv;
                         warn (Msg.missing_infix_decl qop globalEnv)
                         return (HsAssocLeft, 9) -- default values in Haskell98
    where qop2name (HsQVarOp n) = n
          qop2name (HsQConOp n) = n

lookupType :: HsQName -> ContextM (Maybe HsType)
lookupType fname
    = do identifier <- lookupIdentifier fname
         case identifier of
           Nothing -> return Nothing
           Just id -> let typ = Env.typeOf (Env.lexInfoOf id) 
                      in if (typ == Env.EnvTyNone) then return Nothing
                                                   else return $ Just (Env.toHsk typ)


