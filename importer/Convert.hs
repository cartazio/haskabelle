{-  ID:         $Id$
    Author:     Tobias Christian Rittweiler <tcr@freebits.de>, TU Munich

Conversion from abstract Haskell code to abstract Isar/HOL theory.
-}

module Importer.Convert (
  Convertion(..), convertParseResult, cnvFileContents
) where

import Language.Haskell.Hsx

import List (unzip4)
import Monad
import Maybe

import Importer.Utilities
import qualified Importer.IsaSyntax as Isa
import qualified Importer.Msg as Msg

data Context    = Context
    {
      _theory      :: Maybe Isa.Theory
      -- alist of (function name, its type signature)
    , _fsignatures :: [(Isa.Name, Isa.TypeSig)]  

      -- alist of (operator name, (its association kind, binding priority)
    , _optable     :: [(Isa.Name, (Isa.Assoc, Isa.Prio))]
    , _warnings    :: [Warning]
    , _backtrace   :: [String]
    , _gensymcount :: Int
    }

emptyContext = Context { _theory = Nothing,
                         _fsignatures = [],
                         _optable     = [],
                         _warnings    = [],
                         _backtrace   = [],
                         _gensymcount = 0 }

-- Instead of accessing a record directly by their `_foo' slots, we
-- use the respective `foo' surrogate which consists of an appropriate
-- getter and setter -- which allows functions to both query and
-- update a record (almost) by slot name.
type FieldSurrogate field = (Context -> field, Context -> field -> Context) 

theory      = (_theory,      \c f -> c { _theory      = f })
fsignatures = (_fsignatures, \c f -> c { _fsignatures = f })
optable     = (_optable,     \c f -> c { _optable     = f })
warnings    = (_warnings,    \c f -> c { _warnings    = f })
backtrace   = (_backtrace,   \c f -> c { _backtrace   = f })
gensymcount = (_gensymcount, \c f -> c { _gensymcount = f })


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


class Show a => Convert a b | a -> b where
    convert' :: (Convert a b) => a -> ContextM b
    convert  :: (Convert a b) => a -> ContextM b
    convert hsexpr = withUpdatedContext backtrace 
                       (\bt -> let frameName = "frame" ++ show (length bt)
                               in prettyShow' frameName hsexpr : bt)
                     $ convert' hsexpr

data Convertion a = ConvSuccess a [Warning] | ConvFailed String -- FIXME: s/convertion/conversion
  deriving (Eq, Ord, Show)

convertParseResult :: ParseResult HsModule -> Convertion Isa.Cmd

convertParseResult (ParseOk parseRes) 
    = let ContextM cf       = convert parseRes
          (result, context) = cf emptyContext
      in ConvSuccess result (_warnings context)
convertParseResult (ParseFailed loc msg) 
    = ConvFailed (show loc ++ " -- " ++ msg)

convertFileContents = convertParseResult . parseModule -- FIXME: remove

cnvFileContents str = let
    (ConvSuccess res warnings) = convertFileContents str
    str2 = "warnings = " ++ show warnings ++ "\n" ++ "convResult = " ++ show res
    (ParseOk foo) = parseModule str2
  in prettyHsx foo



instance Convert HsModule Isa.Cmd where
    convert' (HsModule _loc modul _exports _imports decls)
        = do thy <- convert modul
             withUpdatedContext theory (\t -> assert (isNothing t) $ Just thy) 
               $ do cmds <- mapM convert decls
                    return (Isa.TheoryCmd thy cmds)

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
    convert' HsListCon      = return Isa.cnameNil
    convert' HsCons         = return Isa.cnameCons
    -- HOL only got pairs, and tuples are representated as nested pairs.
    -- Thus we have no general n-tuple type or data constructor; we fetch
    -- occurences of those earlier, and transform them into something
    -- we can handle instead.
    convert' (HsTupleCon 2) = return Isa.cnamePair
    convert' junk           = barf "HsSpecialCon -> Isa.Name" junk

instance Convert HsAssoc Isa.Assoc where
    convert' (HsAssocNone)  = return Isa.AssocNone
    convert' (HsAssocLeft)  = return Isa.AssocLeft
    convert' (HsAssocRight) = return Isa.AssocRight


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
                                         "HsRecDecl should have been dealt with elsewhere already.")
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

    -- There are no local functions in Isar/HOL, so local "where" declarations
    -- are pulled out and are made global. To avoid name capture, the names
    -- of these local functions are renamed to fresh identifiers (with the
    -- bodies of the local functions, and the body of the actual HsFunBind 
    -- being properly alpha converted.)
    --
    -- E.g.                                
    --                                     fun g0 :: "Int => Int"
    --    f :: Int -> Int                  where
    --    f x = g x                          "g0 x = x * x"
    --      where g :: Int -> Int   ==>    
    --            g x = x * x              fun f :: "Int => Int"
    --                                     where
    --                                       "f x = g0 x"
    convert' (HsFunBind matchs)
        = let (names, patterns, rhss, wbinds) = unzip4 (map splitMatch matchs)
          in do assert (all (== head names) (tail names)) (return ())
                fname'    <- convert (names!!0)            -- as all names are equal, pick first one.
                patterns' <- mapM (mapM convert) patterns  -- each pattern is itself a list of HsPat.
                rhss'     <- mapM convert rhss             
                locdecls  <- concatMapM convert wbinds     -- local declarations
                fsig      <- lookupSig fname'              
                thy       <- lookupThy                     
                locdeclNs <- case concatMapM extractBindNames wbinds of
                               Nothing    -> die "Illegal where bind" -- FIXME
                               Just names -> mapM convert names
                genNs     <- mapM genIsaName locdeclNs
                -- Note that we do the alpha-conversion on the Isar/HOL AST,
                -- as it's way easier to do it properly there than on full Haskell.
                let renamings  = zip locdeclNs genNs
                let locdecls'  = map (alphaConvertCmd thy renamings) locdecls
                let rhss''     = map (alphaConvertTerm thy renamings) rhss'
                return $ Isa.Block (locdecls' ++ [Isa.FunCmd fname' fsig (zip patterns' rhss'')])
            where splitMatch (HsMatch _loc name patterns rhs wherebind)
                      = (name, patterns, rhs, wherebind)
                  

    convert' (HsPatBind _loc pat@(HsPVar name) rhs _wherebinds)
        = do name' <- convert name
             pat'  <- convert pat
             rhs'  <- convert rhs
             sig   <- lookupSig name'
             return $ Isa.DefinitionCmd name' sig ([pat'], rhs')

    convert' junk = barf "HsDecl -> Isa.Cmd" junk


instance Convert HsBinds [Isa.Cmd] where
    convert' (HsBDecls decls) = mapM convert decls
    convert' junk = barf "HsBinds -> Isa.Cmd" junk

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
                                     -- Type constructors may be differently named than
                                     -- their respective data constructors.
                                     where cnv (Special HsListCon) = return Isa.tnameList
                                           cnv etc  = convert etc

    convert' (HsTyFun type1 type2) = do type1' <- convert type1
                                        type2' <- convert type2
                                        return (Isa.TyFun type1' type2')

    -- Types aren't curried or partially appliable in HOL, so we must pull a nested
    -- chain of type application inside out:
    --
    --  T a b ==> HsTyApp (HsTyApp (HsTyCon T) (HsTyVar a)) (HsTyVar b)
    --       
    --        ==> Isa.TyCon T [(Isa.TyVar a), (Isa.TyVar b)]   
    --
    convert' tyapp@(HsTyApp _ _) 
        = do let tycon:tyvars = unfoldl1 split tyapp
             tycon'  <- convert tycon
             tyvars' <- mapM convert tyvars
             return $ case tycon' of Isa.TyCon n [] -> Isa.TyCon n tyvars'
          where split (HsTyApp tyapp x) = Just (x, tyapp)
                split (HsTyCon _)       = Nothing         -- Note that this HsTyCon will become
                split junk                                --  the head of the returned list.
                    = error ("HsType -> Isa.Type (split HsTyApp): " ++ (show junk))

    convert' (HsTyTuple Boxed types)
        = do types' <- mapM convert types
             return $ Isa.TyTuple types'

    -- convert' (HsTyTuple Boxed types)
    --     = do types' <- mapM convert types
    --          return $ foldr1 Isa.mkPairType types'

    convert' junk = barf "HsType -> Isa.Type" junk

instance Convert HsBangType Isa.Type where
    convert' (HsBangedTy typ)   = convert typ
    convert' (HsUnBangedTy typ) = convert typ



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


instance Convert HsFieldUpdate (Isa.Name, Isa.Term) where
    convert' (HsFieldUpdate qname exp)
        = do qname' <- convert qname
             exp'   <- convert exp
             return (qname', exp')


instance Convert HsAlt (Isa.Term, Isa.Term) where
    convert' (HsAlt _loc pat (HsUnGuardedAlt exp) _wherebinds)
        = do pat' <- convert pat; exp' <- convert exp; return (pat', exp')


instance Convert HsExp Isa.Term where
    convert' (HsLit lit)       = convert lit   >>= (\l -> return (Isa.Literal l))
    convert' (HsVar qname)     = convert qname >>= (\n -> return (Isa.Var n))
    convert' (HsCon qname)     = convert qname >>= (\n -> return (Isa.Var n))
    convert' (HsParen exp)     = convert exp   >>= (\e -> return (Isa.Parenthesized e))

    convert' (HsApp exp1 exp2)
        = do exp1' <- cnv exp1 ; exp2' <- cnv exp2
             return (Isa.App exp1' exp2')
          where cnv (HsCon (Special (HsTupleCon n))) = makeTupleDataCon n
                cnv etc = convert etc

    convert' app@(HsInfixApp exp1 op exp2)
        = fixInfixApp app >>= (return . infix2prefix)
          where infix2prefix (Isa.InfixApp exp1 op exp2)
                    = Isa.App (Isa.App op (infix2prefix exp1)) (infix2prefix exp2)
                infix2prefix etc = etc

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
             if all isVar pats' then return $ Isa.Lambda (map getName pats') exp'
                                else makePatternMatchingLambda pats' exp'
          where isVar (Isa.Var _)   = True
                isVar _             = False
                getName (Isa.Var n) = n

    convert' (HsList []) = return (Isa.Var Isa.cnameNil)
    convert' (HsList exps)
        = do exps' <- mapM convert exps
             return $ foldr Isa.mkcons Isa.mknil exps' 

    convert' (HsTuple exps)
        = do exps' <- mapM convert exps
             return $ foldr1 Isa.mkpair exps'

    convert' (HsIf t1 t2 t3)
        = do t1' <- convert t1; t2' <- convert t2; t3' <- convert t3
             return (Isa.If t1' t2' t3')

    convert' (HsCase exp alts)
        = do exp'  <- convert exp
             alts' <- mapM convert alts
             return $ Isa.Case exp' alts'

    convert' junk = barf "HsExp -> Isa.Term" junk



gensym :: String -> ContextM String
gensym prefix = do count <- queryContext gensymcount
                   updateContext gensymcount (\count -> count + 1)
                   return $ prefix ++ (show count)

genIsaName :: Isa.Name -> ContextM Isa.Name
genIsaName (Isa.QName t prefix) 
    = gensym prefix >>= (\sym -> return (Isa.QName t sym))
genIsaName (Isa.Name prefix)
    = gensym prefix >>= (\sym -> return (Isa.Name sym))


-- Since HOL doesn't have true n-tuple constructors (it uses nested
-- pairs to represent n-tuples), we simply return a lambda expression
-- that takes n parameters and constructs the nested pairs within its
-- body.
makeTupleDataCon :: Int -> ContextM Isa.Term
makeTupleDataCon n
    = do args <- mapM genIsaName (replicate n (Isa.Name "_arg"))
         return $ Isa.Parenthesized (Isa.Lambda args (foldr1 Isa.mkpair (map Isa.Var args)))

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
                = do g <- genIsaName (Isa.Name "_arg")
                     return $ Isa.Lambda [g] (Isa.Case (Isa.Var g) [(pat, body)])


-- Hsx parses every infix application simply from left to right without
-- taking operator associativity or binding priority into account. So
-- we gotta fix that up ourselves. (We also properly consider infix
-- declarations to get user defined operator right.)
fixInfixApp :: HsExp -> ContextM Isa.Term

fixInfixApp (HsInfixApp exp1 op exp2)
    = do exp1' <- fixInfixApp exp1
         exp2' <- fixInfixApp exp2
         op'   <- convert op
         fixup (Isa.InfixApp exp1' op' exp2')
        
fixInfixApp expr = convert expr

-- Notice that `1 * 2 + 3 / 4' is parsed as `((1 * 2) + 3) / 4', i.e.
-- 
--    InfixApp (InfixApp (InfixApp 1 * 2) + 3) / 4
--
-- whereas `1 * 2 + (3 / 4)' is parsed as
--
--    InfixApp (InfixApp 1 * 2) + (Parenthesized (InfixApp 3 / 4))
--
-- and `1 * (2 + 3) / 4' is parsed as
--
--    InfixApp (InfixApp 1 (Parenthesized (InfixApp 2 + 3))) / 4
--
-- Thus we _know_ that the second operand of an infix application,
-- i.e. the e2 in `InfixApp e1 op e2', can _never_ be a bare infix
-- application that we might have to consider during fixup.
--  
fixup :: Isa.Term -> ContextM Isa.Term
fixup origExpr@(Isa.InfixApp (Isa.InfixApp e1 op1 e2) op2 e3)
    -- (e1 `op1` e2) `op2` e3, where we assume that (e1 `op1` e2) is correct
    -- already; so we have to only find the proper place for the (`op2` e3).
    = do (assoc1', prio1) <- lookupOp op1
         (assoc2', prio2) <- lookupOp op2
         let assoc1 = normalizeAssociativity assoc1'
         let assoc2 = normalizeAssociativity assoc2'
         case prio2 `compare` prio1 of
           LT -> return origExpr
           GT -> fixup (Isa.InfixApp e2 op2 e3) >>= (return . Isa.InfixApp e1 op1)
           EQ -> if assoc2 /= assoc1 then
                     die (Msg.assoc_mismatch op1 assoc1 op2 assoc2)
                 else case assoc2 of
                        Isa.AssocLeft  -> return (Isa.InfixApp (Isa.InfixApp e1 op1 e2) op2 e3) -- i.e. origExpr
                        Isa.AssocRight -> return (Isa.InfixApp e1 op1 (Isa.InfixApp e2 op2 e3))
                        Isa.AssocNone  -> die ("fixup InfixApp: Internal error (AssocNone should " ++
                                               "have already been normalized away.)")
fixup expr@(Isa.InfixApp _ _ _) = return expr

normalizeAssociativity (Isa.AssocNone) = Isa.AssocLeft -- as specified in Haskell98.
normalizeAssociativity etc = etc

lookupOp :: Isa.Term -> ContextM (Isa.Assoc, Int)
lookupOp (Isa.Var name)
    = do optable <- queryContext optable
         case lookup name optable of
           Just (assoc, prio) -> return (assoc, prio)
           Nothing            -> do warn (Msg.missing_infix_decl name)
                                    return (Isa.AssocLeft, 9) -- default values in Haskell98
lookupOp junk = barf "lookupOp: " junk

lookupSig :: Isa.Name -> ContextM Isa.TypeSig
lookupSig fname
    = do seensigs  <- queryContext fsignatures
         case (lookup fname seensigs) of
           Nothing        -> die (Msg.missing_fun_sig fname)
           Just signature -> return signature

lookupThy :: ContextM Isa.Theory
lookupThy = do thy <- queryContext theory
               case thy of Nothing -> die "lookupThy"
                           Just t  -> return t
