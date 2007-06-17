
module Hsimp.Convert (Convertion(..), convertFileContents, cnvFileContents) where

import Control.Exception (assert) -- FIXME
import Debug.Trace (trace)        -- FIXME

import Monad
import Language.Haskell.Hsx

import qualified Hsimp.IsaSyntax as Isa

convertFile fp = readFile fp >>= (return . convertFileContents)

cnvFile fp = readFile fp >>= cnvFileContents

data Context    = Context 
    {
      -- alist of (function name, its type signature) 
      _fsignatures :: [(Isa.Name, Isa.TypeSig)]   

      -- alist of (operator name, (its association kind, binding priority)
    , _optable     :: [(Isa.Name, (Isa.Assoc, Isa.Prio))]  
    , _warnings    :: [Warning]
    , _backtrace   :: [String]
    }

emptyContext = Context { _fsignatures = [], 
                         _optable     = [], 
                         _warnings    = [],
                         _backtrace   = [] }


type FieldSurrogate field = (Context -> field, Context -> field -> Context)

fsignatures = (_fsignatures, \c f -> c { _fsignatures = f })
optable     = (_optable,     \c f -> c { _optable     = f })
warnings    = (_warnings,    \c f -> c { _warnings    = f })
backtrace   = (_backtrace,   \c f -> c { _backtrace   = f })


data ContextM v = ContextM (Context -> (v, Context)) 

instance Monad ContextM where
    return value 
        = ContextM (\context -> (value, context))
    ContextM cf0 >>= f
        = ContextM $ \c0 -> let (v1, c1)     = cf0 c0
                                ContextM cf1 = f v1
                                (v2, c2)     = cf1 c1 in (v2, c2)

-- getContext :: ContextM Context
-- getContext = ContextM (\c -> (c, c))

-- setContext :: Context -> ContextM ()
-- setContext newContext = ContextM (\c -> ((), newContext))  

queryContext :: (FieldSurrogate field) -> ContextM field
queryContext (query, _)
    = ContextM $ \c -> (query c, c)

updateContext :: (FieldSurrogate field) -> (field -> field) -> ContextM ()
updateContext (query, update) updateField 
    = ContextM $ \c -> ((), update c (updateField (query c)))

withUpdatedContext :: (FieldSurrogate field) -> (field -> field) -> ContextM a -> ContextM a
withUpdatedContext surrogate updateField result
     = do oldval <- queryContext surrogate
          updateContext surrogate updateField
          evaledResult <- result
          updateContext surrogate (\_ -> oldval)
          return evaledResult


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


prettyShow' prefix obj = let str = prefix ++ " = " ++ show obj
                             (ParseOk foo) = parseModule str
                         in (prettyPrint foo)

prettyShow obj = prettyShow' "foo" obj



class Show a => Convert a b | a -> b where
    convert' :: (Convert a b) => a -> ContextM b
    convert  :: (Convert a b) => a -> ContextM b
    convert hsexpr = withUpdatedContext backtrace (\bt -> let frameName = "frame" ++ show (length bt)
                                                          in prettyShow' frameName hsexpr : bt)
                          $ convert' hsexpr

data Convertion a = ConvSuccess a [Warning] | ConvFailed String
  deriving (Eq, Ord, Show)

converter                        :: ParseResult HsModule -> Convertion Isa.Cmd
converter (ParseFailed loc msg)  = ConvFailed (show loc ++ " -- " ++ msg)
converter (ParseOk parseRes)     = let ContextM cf        = convert parseRes
                                       (result, context)  = cf emptyContext
                                   in ConvSuccess result (_warnings context)

cnvFileContents str 
    = let (ConvSuccess res warnings) = converter (parseModule str)
	  str2 = "warnings = " ++ show warnings ++ "\n" ++ "convResult = " ++ show res
	  (ParseOk foo) = parseModule str2
      in do putStrLn (prettyPrint foo)

convertFileContents str 
    = converter (parseModule str)





instance Convert HsModule Isa.Cmd where
    convert' (HsModule _loc modul _exports _imports decls)
        = do theory <- convert modul
             cmds   <- mapM convert decls
             return (Isa.TheoryCmd theory cmds)

instance Convert Module Isa.Theory where
    convert' (Module name) = return (Isa.Theory name)


instance Convert HsName Isa.Name where
    convert' (HsIdent  str) = return (Isa.Name str)
    convert' (HsSymbol str) = return (Isa.Name str)

instance Convert HsQName Isa.Name where
    convert' (UnQual name)     = (convert name)
    convert' (Qual modul name) = do theory <- convert modul
                                    return (Isa.QName theory (case name of
                                                                HsIdent str  -> str
                                                                HsSymbol str -> str))
    convert' (Special spcon)   = convert spcon 

instance Convert HsSpecialCon Isa.Name where
    convert' (HsListCon)    = return Isa.nil
    convert' (HsCons)       = return Isa.cons
    convert' junk           = barf "HsSpecialCon -> Isa.Name" junk

instance Convert HsAssoc Isa.Assoc where
    convert' (HsAssocNone)  = return Isa.AssocNone
    convert' (HsAssocLeft)  = return Isa.AssocLeft
    convert' (HsAssocRight) = return Isa.AssocRight


instance Convert HsDecl Isa.Cmd where
    convert' (HsTypeDecl _loc tyconN tyvarNs typ)
        = do tyvars <- (mapM convert tyvarNs) 
             tycon  <- (convert tyconN)
             typ'   <- (convert typ)
             return (Isa.TypesCmd [(Isa.TypeSpec tyvars tycon, typ')])

    convert' (HsDataDecl _loc _context tyconN tyvarNs condecls _deriving)
        = let unstrip (HsQualConDecl _loc _FIXME _context decl) = decl
              decls = map unstrip condecls
          in if isRecDecls decls then
                 createRecordCmd tyconN tyvarNs decls
             else do tyvars <- mapM convert tyvarNs
                     tycon  <- convert tyconN
                     decls' <- mapM cnvt decls
                     return (Isa.DatatypeCmd (Isa.TypeSpec tyvars tycon) decls')
                 where cnvt (HsConDecl name types) 
                           = do name'  <- convert name
                                tyvars <- mapM convert types
                                return $ Isa.Constructor name' tyvars
                       cnvt junk = barf ("Internal Error: " ++
                                         "HsRecDecl should be dealt with elsewhere already.") 
                                        junk

    convert' (HsInfixDecl _loc assoc prio ops)
        = do assoc' <- convert assoc
             ops'   <- mapM convert ops
             updateContext optable (\optable -> zip ops' (cycle [(assoc', prio)]) ++ optable)
             return (Isa.Block (map (\op' -> Isa.InfixDeclCmd op' assoc' prio) ops'))

    convert' (HsTypeSig _loc names typ)
        = do names' <- mapM convert names
             typ'   <- convert typ
             sigs   <- queryContext fsignatures
             let newsigs = map (\n -> Isa.TypeSig n typ') names'
             updateContext fsignatures (\sigs -> (zip names' newsigs) ++ sigs)
             return (Isa.Comment (prettyShow' "typeSigs" newsigs)) -- show type sigs in comment; FIXME

    convert' (HsFunBind matchs)
        = let (names, patterns, rhss) = unzip3 (map splitMatch matchs)
          in do assert (all (== head names) (tail names)) (return ()) 
                fname'    <- convert (names!!0)            -- as all names are equal, pick first one.
                patterns' <- mapM (mapM convert) patterns  -- each pattern is a list of HsPat.
                rhss'     <- mapM convert rhss
                fsig      <- lookupSig fname'
                return (Isa.FunCmd fname' fsig (zip patterns' rhss'))
            where splitMatch (HsMatch _loc name patterns rhs _wherebinds)
                      = (name, patterns, rhs)

    convert' (HsPatBind _loc pat@(HsPVar name) rhs _wherebinds)
        = do name' <- convert name
             pat'  <- convert pat
             rhs'  <- convert rhs
             sig   <- lookupSig name'
             return $ Isa.DefinitionCmd name' sig ([pat'], rhs')
 
    convert' junk = barf "HsDecl -> Isa.Cmd" junk


isRecDecls :: [HsConDecl] -> Bool
isRecDecls decls 
    = case decls of
        -- We only support data decls with exactly one record
        -- definition within it.
        (HsRecDecl _ _):rest -> assert (null rest) True
        decls                -> assert (all (not.isRecDecl) decls) False
    where isRecDecl (HsRecDecl _ _) = True
          isRecDecl _               = False

createRecordCmd :: HsName -> [HsName] -> [HsConDecl] -> ContextM Isa.Cmd
createRecordCmd tyconN tyvarNs [HsRecDecl name slots]
    = do tycon  <- convert tyconN
         tyvars <- mapM convert tyvarNs
         slots' <- liftM concat (mapM cnvtSlot slots)
         return $ Isa.RecordCmd (Isa.TypeSpec tyvars tycon) slots'
    where cnvtSlot (names, typ)
              = do names' <- mapM convert names
                   typ'   <- convert typ
                   return (zip names' (cycle [typ']))
         

instance Convert HsType Isa.Type where
    convert' (HsTyVar name)        = (convert name)  >>= (\n -> return (Isa.TyVar n))
    convert' (HsTyCon qname)       = (cnv qname)     >>= (\n -> return (Isa.TyCon n []))
                                     where cnv (Special HsListCon) = return Isa.list
                                           cnv (Special HsCons)    = return Isa.cons
                                           cnv etc  = (convert etc)

    convert' (HsTyFun type1 type2) = do type1' <- convert type1
                                        type2' <- convert type2
                                        return (Isa.TyFun type1' type2')
    --
    -- Types aren't curried or partially appliable in HOL, so we must pull a nested
    -- chain of type application inside out:
    --
    --  T a b ==> HsTyApp (HsTyApp (HsTyCon T) (HsTyVar a)) (HsTyVar b)
    --        
    --        ==> Isa.TyCon T [(Isa.TyVar a), (Isa.TyVar b)]    
    --
    convert' tyapp@(HsTyApp _ _) = grovel tyapp [] -- flattens chain of type application.
        where grovel :: HsType -> [HsType] -> ContextM Isa.Type
              grovel (HsTyApp tyapp@(HsTyApp _ _) tyarg) tyargs
                  -- Innermost type argument in a chain of type application
                  -- was the first/leftmost type argument given in the original
                  -- textual representation. So we _gotta_ append onto the end:
                  = grovel tyapp (tyargs ++ [tyarg])
              grovel (HsTyApp tycon@(HsTyCon _) tyarg) tyargs
                  = do tycon'  <- convert tycon 
                       tyargs' <- mapM convert (tyargs ++ [tyarg])
                       case tycon' of 
                         Isa.TyCon con [] -> return $ Isa.TyCon con tyargs' 
              grovel junk _ = barf "HsType -> Isa.Type (grovel HsTyApp)" junk

    convert' junk = barf "HsType -> Isa.Type" junk

instance Convert HsBangType Isa.Type where
    convert' (HsBangedTy typ)   = convert typ
    convert' (HsUnBangedTy typ) = convert typ



-- As we convert to Isa.Term anyway, we can translate each HsPat
-- type to a HsExp first, and then convert that on in order to
-- reduce some code bloat. 
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

convertHsPat (HsPInfixApp pat1 qname pat2)
    = do pat1' <- convertHsPat pat1
         pat2' <- convertHsPat pat2
         return $ HsInfixApp pat1' (HsQConOp qname) pat2'

convertHsPat (HsPApp qname (pat1:pats))
    = do pat1' <- convertHsPat pat1
         pats' <- mapM convertHsPat pats
         return $ foldl HsApp (HsApp (HsCon qname) pat1') pats'

convertHsPat junk = barf "HsPat -> Isa.Term (convertHsPat: HsPat -> HsExp)" junk


instance Convert HsRhs Isa.Term where
    convert' (HsUnGuardedRhs exp) = convert exp
    -- convert (HsGuardedRhss rhss) ; FIXME
    convert' junk = barf "HsRhs -> Isa.Term" junk


-- Language.Haskell.Hsx.Syntax calls an an operator `HsQOp' when it's
-- used within an expression, but `HsOp' when used within an infix
-- declaration. A bit confusing, unfortunately.

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


instance Convert HsExp Isa.Term where
    convert' (HsLit lit)       = (convert lit)   >>= (\l -> return (Isa.Literal l))
    convert' (HsVar qname)     = (convert qname) >>= (\n -> return (Isa.Var n))
    convert' (HsCon qname)     = (convert qname) >>= (\n -> return (Isa.Con n))
    convert' (HsParen exp)     = (convert exp)   >>= (\e -> return (Isa.Parenthesized e))
    convert' (HsList exps)     = cnvList exps
                                 where cnvList [] = return $ Isa.Var Isa.nil
                                       cnvList (exp:exps) = do
                                         exp'  <- convert exp
                                         exps' <- cnvList exps
                                         return $ Isa.App (Isa.App (Isa.Var Isa.cons) exp') exps'

    convert' (HsRecConstr qname updates)
        = do qname'   <- convert qname
             updates' <- mapM convert updates
             return $ Isa.RecConstr qname' updates'

    convert' (HsRecUpdate exp updates)
        = do exp'     <- convert exp
             updates' <- mapM convert updates
             return $ Isa.RecUpdate exp' updates'

    convert' (HsLambda _loc pats exp)
        = do pats'  <- mapM convert pats
             exp'   <- convert exp
             return $ Isa.Lambda pats' exp' 


    -- convert' (HsList [])       = return (Isa.Var (Isa.Name "[]"))
    -- convert' (HsList exps)     = do exps' <- mapM convert exps
    --                                 let exp1'  = head exps'
    --                                 let exps'  = tail exps'
    --                                 let listOp = (Isa.Var (Isa.Name "[]"))
    --                                 return (foldl Isa.App (Isa.App listOp exp1') exps')
                                    
    convert' (HsApp exp1 exp2) 
        = do exp1' <- convert exp1; exp2' <- convert exp2
             return (Isa.App exp1' exp2')

    convert' orig@(HsInfixApp exp1 op exp2) 
        = do exp1' <- convert exp1
             exp2' <- convert exp2
3             op'   <- convert op
             fixup (Isa.InfixApp exp1' op' exp2')

    convert' (HsIf t1 t2 t3)
        = do t1' <- convert t1; t2' <- convert t2; t3' <- convert t3
             return (Isa.If t1' t2' t3')
                    
    convert' junk = barf "HsExp -> Isa.Term" junk


fixup :: Isa.Term -> ContextM Isa.Term

fixup origExpr@(Isa.InfixApp (Isa.InfixApp e1 op1 e2) op2 e3)
    -- (e1 `op1` e2) `op2` e3,  where we assume that (e1 `op1` e2) is correct
    -- already; so we have just to find the proper place for (`op2` e3).
    = do (assoc1, prio1) <- lookupOp op1
         (assoc2, prio2) <- lookupOp op2
         case prio2 `compare` prio1 of
           LT -> return origExpr
           GT -> liftM (Isa.InfixApp e1 op1) $ fixup (Isa.InfixApp e2 op2 e3)
           EQ -> if assoc2 /= assoc1 then
                     die ("Associativity mismatch: " ++ (show op2) ++ " has " ++ (show assoc2)
                            ++ ", whereas " ++ (show op1) ++ " has " ++ (show assoc1) ++ ".")
                 else case assoc2 of
                        Isa.AssocLeft  -> return (Isa.InfixApp (Isa.InfixApp e1 op1 e2) op2 e3) -- i.e. origExpr
                        Isa.AssocRight -> return (Isa.InfixApp e1 op1 (Isa.InfixApp e2 op2 e3))
                        Isa.AssocNone  -> die ("No associativity for " ++ (show op2) ++ ", " ++ (show op1))
fixup expr@(Isa.InfixApp _ _ _) = return expr

lookupOp :: Isa.Term -> ContextM (Isa.Assoc, Int)
lookupOp (Isa.Var name)
    = do optable <- queryContext optable
         case lookup name optable of
           Just (assoc, prio) -> return (assoc, prio)
           Nothing            -> do warn ("Missing infix declaration for `" ++ (show name) ++ "'"
                                          ++ ", assuming left associativity and a fixity of 9.")
                                    return (Isa.AssocLeft, 9) -- default values in Haskell98
lookupOp junk = barf "lookupOp" junk

lookupSig :: Isa.Name -> ContextM Isa.TypeSig
lookupSig fname 
    = do seensigs  <- queryContext fsignatures
         case (lookup fname seensigs) of
           Nothing        -> die ("Missing function signature for " ++ (show fname) ++ " (FIXME)")
           Just signature -> return signature


instance Convert HsFieldUpdate (Isa.Name, Isa.Term) where
    convert' (HsFieldUpdate qname exp)
        = do qname' <- convert qname
             exp'   <- convert exp
             return (qname', exp')