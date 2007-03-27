
module Converter where

import Language.Haskell.Hsx
import qualified IsaSyntax as Isa


data Context    = Context 
    { signatures :: [(Isa.Name, Isa.TypeSig)]  -- alist of (function name, its type signature)
    }

data ContextM v = ContextM (Context -> (v, Context)) 

instance Monad ContextM where
    return value 
        = ContextM (\context -> (value, context))
    ContextM cf0 >>= f
        = ContextM $ \c0 -> let (v1, c1)     = cf0 c0
                                ContextM cf1 = f v1
                                (v2, c2)     = cf1 c1 in (v2, c2)

updateContext :: (Context -> Context) -> ContextM ()
updateContext update
    = ContextM (\c -> ((), update c))

queryContext :: (Context -> a) -> ContextM a
queryContext query
    = ContextM (\c -> (query c, c))
      

class Convert a b | a -> b where
    convert :: a -> ContextM b


data Convertion a = ConvSuccess a | ConvFailed String
  deriving (Eq, Ord, Show)


emptyContext = Context { signatures = [] } 

converter                        :: ParseResult HsModule -> Convertion Isa.Cmd
converter (ParseFailed loc msg)  = ConvFailed (show loc ++ " -- " ++ msg)
converter (ParseOk parseRes)     = let ContextM cf = convert parseRes
                                       (result,_)  = cf emptyContext
                                   in ConvSuccess result

barf str obj = error (str ++ ": Pattern match exhausted for " ++ show obj)


instance Convert HsModule Isa.Cmd where
    convert (HsModule _loc modul _exports _imports decls)
        = do theory <- convert modul
             cmds   <- mapM convert decls
             return (Isa.TheoryCmd theory cmds)

instance Convert Module Isa.Theory where
    convert (Module name) = return (Isa.Theory name)


instance Convert HsName Isa.Name where
    convert (HsIdent  str) = return (Isa.Name str)
    convert (HsSymbol str) = return (Isa.Name str)

instance Convert HsQName Isa.Name where
    convert (UnQual name)     = (convert name)
    convert (Qual modul name) = do theory <- convert modul
                                   return (Isa.QName theory (case name of
                                                              HsIdent str  -> str
                                                              HsSymbol str -> str))
    -- FIXME: convert (Special spcon)


instance Convert HsDecl Isa.Cmd where
    convert (HsTypeDecl _loc tyconN tyvarNs typ)
        = do tyvars <- (mapM convert tyvarNs) 
             tycon  <- (convert tyconN)
             typ'   <- (convert typ)
             return (Isa.TypesCmd [(Isa.TypeSpec tyvars tycon, typ')])

    convert (HsDataDecl _loc _context tyconN tyvarNs condecls _deriving)
        = do tyvars    <- mapM convert tyvarNs
             tycon     <- convert tyconN
             condecls' <- mapM cnvt condecls
             return (Isa.DatatypeCmd (Isa.TypeSpec tyvars tycon) condecls')
           where cnvt (HsQualConDecl _loc _FIXME _context decl)
                     = case decl of
                         HsConDecl name types -> do name'  <- convert name
                                                    tyvars <- mapM convert types
                                                    return (name', tyvars)
                         -- HsRecDecl ; FIXME: Record types.

    convert (HsTypeSig _loc names typ)
        = do names' <- mapM convert names
             typ'   <- convert typ
             sigs   <- queryContext signatures
             let newsigs = map (\n -> (n, Isa.TypeSig n typ')) names'
             updateContext (\c -> c { signatures = newsigs ++ sigs})
             return (Isa.Comment (show (map snd newsigs))) -- show type sigs in comment; FIXME

    convert (HsFunBind matchs)
        = let (names, patterns, rhss) = unzip3 (map splitMatch matchs)
          in do fname'    <- convert (names!!0)            -- as all names are equal, pick first one.
                patterns' <- mapM (mapM convert) patterns  -- each pattern is a list of HsPat.
                rhss'     <- mapM convert rhss
                seensigs  <- queryContext signatures 
                case (lookup fname' seensigs) of
                  Nothing        -> error ("Missing function signature for " ++ (show fname') ++ " (FIXME)")
                  Just signature -> return (Isa.FunCmd fname' signature (zip patterns' rhss'))
            where splitMatch (HsMatch _loc name patterns rhs _wherebinds)
                      = (name, patterns, rhs)


instance Convert HsType Isa.Type where
    convert (HsTyVar name)        = (convert name)  >>= (\n -> return (Isa.TyVar n))
    convert (HsTyCon qname)       = (convert qname) >>= (\n -> return (Isa.TyCon n []))
    convert (HsTyFun type1 type2) = do type1' <- convert type1
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
    convert tyapp@(HsTyApp _ _) 
        = do (tyconN, tyvars) <- grovel tyapp -- flattens chain of type application.
             return (Isa.TyCon tyconN tyvars)
        where grovel :: HsType -> ContextM (Isa.Name, [Isa.Type])
              grovel (HsTyApp (HsTyCon tyconN) tyvar@(HsTyVar _))
                  = do tyconN' <- convert tyconN
                       tyvar'  <- convert tyvar
                       return (tyconN', [tyvar'])
              grovel (HsTyApp tyapp@(HsTyApp _ _) tyvar@(HsTyVar _))
                  = do (tyconN, tyvars) <- grovel tyapp
                       tyvar'          <- convert tyvar
                       -- Innermost type variable in a chain of type application
                       -- was the first/leftmost type variable given in the original
                       -- textual representation. So we _gotta_ append onto the end:
                       return (tyconN, tyvars ++ [tyvar'])
              grovel junk = barf "HsType -> Isa.Type (grovel HsTyApp)" junk

    convert junk = barf "HsType -> Isa.Type" junk

instance Convert HsBangType Isa.Type where
    convert (HsBangedTy typ)   = convert typ
    convert (HsUnBangedTy typ) = convert typ -- despite Isabelle/HOL being strict.
                

instance Convert HsPat Isa.Term where
    convert (HsPLit literal) = (convert literal) >>= (\l -> return (Isa.Literal l))
    convert (HsPVar name)    = (convert name)    >>= (\n -> return (Isa.Var n))


instance Convert HsRhs Isa.Term where
    convert (HsUnGuardedRhs exp) = convert exp
    -- convert (HsGuardedRhss rhss) ; FIXME


instance Convert HsQOp Isa.Term where
    convert (HsQVarOp qname) = do qname' <- convert qname; return (Isa.Var qname')

instance Convert HsLiteral Isa.Literal where
    convert (HsInt i) = return (Isa.Int i)

instance Convert HsExp Isa.Term where
    convert (HsLit lit)       = (convert lit)   >>= (\l -> return (Isa.Literal l))
    convert (HsVar qname)     = (convert qname) >>= (\n -> return (Isa.Var n))
    convert (HsParen exp)     = (convert exp)   >>= (\e -> return (Isa.Parenthesized e))
    convert (HsApp exp1 exp2) = do exp1' <- convert exp1
                                   exp2' <- convert exp2
                                   return (Isa.App exp1' exp2')
    convert (HsInfixApp exp1 op exp2) 
        = do exp1' <- convert exp1
             exp2' <- convert exp2
             op'   <- convert op
             return (Isa.App (Isa.App op' exp1') exp2')

    convert junk = barf "HsExp -> Isa.Term" junk


cnv str = let (ConvSuccess res) = converter (parseModule str)
	      str2 = "foo = " ++ show res
	      (ParseOk foo) = parseModule str2
            in do putStrLn (prettyPrint foo)