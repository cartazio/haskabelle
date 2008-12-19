{-# LANGUAGE PatternGuards #-}

{-| Author: Tobias C. Rittweiler, TU Muenchen

Pretty printing of abstract Isar/HOL theory.
-}

module Importer.Printer
    ( pprint
    ) where

import Maybe
import Control.Monad

import Importer.Utilities.Misc
import Importer.Utilities.Isa (renameIsaCmd, namesFromIsaCmd, 
                               mk_InstanceCmd_name)

import qualified Importer.IsaSyntax as Isa
import qualified Importer.LexEnv as Env

import Importer.Adapt.Mapping (adaptionTable, AdaptionTable(..))
import Importer.Adapt.Raw (used_thy_names, reserved_keywords)

import Language.Haskell.Exts.Syntax as Hs (SpecialCon(..), QName(..))

import qualified Text.PrettyPrint as P



data PPState = PPState { globalEnv        :: Env.GlobalE,
                         currentTheory    :: Isa.Theory,
                         -- Are we in an Infix Application?
                         currentAppFlavor :: Maybe AppFlavor,
                         currentTyScheme  :: [(Isa.Name, [Isa.Name])],
                         -- If True, we're already in doubly-quoted section.
                         withinHOL        :: Bool
                       }

data DocM v = DocM (PPState -> (v, PPState))

emptyPPState = PPState { globalEnv = Env.initialGlobalEnv,
                         currentTheory = Isa.Theory "Scratch",
                         currentAppFlavor = Nothing,
                         currentTyScheme = [],
                         withinHOL = False
                       }

instance Monad DocM where
    return value = DocM (\state -> (value, state))
    DocM sf0 >>= f
        = DocM $ \s0 -> let (v1, s1) = sf0 s0
                            DocM sf1 = f v1
                            (v2, s2) = sf1 s1 in (v2, s2)

queryPP :: (PPState -> field) -> DocM field
queryPP query
    = DocM $ \pps -> (query pps, pps)

updatePP :: (PPState -> PPState) -> DocM ()
updatePP update
    = DocM $ \pps -> ((), update pps)

type Doc = DocM P.Doc

-- The pretty printing combinators

empty :: Doc
empty = return P.empty

nest :: Int -> Doc -> Doc
nest i dm = dm >>= return . P.nest i


-- Literals

text, ptext :: String -> Doc
text  = return . P.text
ptext = return . P.text

char :: Char -> Doc
char = return . P.char

int :: Int -> Doc
int = return . P.int

integer :: Integer -> Doc
integer = return . P.integer

float :: Float -> Doc
float = return . P.float

double :: Double -> Doc
double = return . P.double

rational :: Rational -> Doc
rational = return . P.rational


-- Constants

semi,comma,colon,space,equals,dot,apostroph,asterisk :: Doc
semi   = return P.semi
comma  = return P.comma
colon  = return P.colon
space  = return P.space
equals = return P.equals

dot       = char '.'
apostroph = char '\''
asterisk  = char '*'
plus      = char '+'

lparen,rparen,lbrack,rbrack,lbrace,rbrace :: Doc
lparen = return  P.lparen
rparen = return  P.rparen
lbrack = return  P.lbrack
rbrack = return  P.rbrack
lbrace = return  P.lbrace
rbrace = return  P.rbrace


-- Simple Combining Forms

parens, brackets, braces, quotes, doubleQuotes, bananas, blankline :: Doc -> Doc
parens d       = d >>= return . P.parens
brackets d     = d >>= return . P.brackets
braces d       = d >>= return . P.braces
quotes d       = d >>= return . P.quotes
doubleQuotes d = d >>= return . P.doubleQuotes

bananas d      = text "(|" <+> d <+> text "|)"
blankline d    = space $$ d

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

withCurrentTheory :: Isa.Theory -> Doc -> Doc
withCurrentTheory thy d
    = do oldthy <- queryPP (\pps -> currentTheory pps)
         updatePP (\pps -> pps { currentTheory = thy })
         result <- d
         updatePP (\pps -> pps { currentTheory = thy })
         return result

maybeWithinHOL :: Doc -> Doc
maybeWithinHOL d   
    = do within_p <- queryPP withinHOL
         if within_p then d
                     else do updatePP (\pps -> pps { withinHOL = True })
                             result <- doubleQuotes d
                             updatePP (\pps -> pps { withinHOL = False })
                             return result

withinHOL_if :: Bool -> Doc -> Doc
withinHOL_if pred doc
    | pred = do within_p <- queryPP withinHOL
                if within_p then doc
                            else do updatePP (\pps -> pps { withinHOL = True })
                                    result <- doubleQuotes doc
                                    updatePP (\pps -> pps { withinHOL = False })
                                    return result
    | otherwise = doc

withinApplication :: AppFlavor -> Doc -> Doc
withinApplication app d
    = do old_app <- queryPP (\pps -> currentAppFlavor pps)
         updatePP (\pps -> pps { currentAppFlavor = Just app })
         result <- d
         updatePP (\pps -> pps { currentAppFlavor = old_app })
         return result


withTyScheme :: [(Isa.Name, [Isa.Name])] -> Doc -> Doc
withTyScheme ctx d
    = do old_ctx <- queryPP (\pps -> currentTyScheme pps)
         updatePP (\pps -> pps { currentTyScheme = ctx })
         result <- d
         updatePP (\pps -> pps { currentTyScheme = old_ctx })
         return result

comment :: Doc -> Doc
comment d = text "(*" <+> d <+> text "*)"

-- fill-paragraph str = vcat $ map text (lines str)

-- Combinators

(<>),(<+>),($$),($+$) :: Doc -> Doc -> Doc
(<>) = liftM2 (P.<>)
(<+>) = liftM2 (P.<+>)
($$) = liftM2 (P.$$)
($+$) = liftM2 (P.$+$)

ncat, hcat,hsep,vcat,sep,cat,fsep,fcat :: [Doc] -> Doc
ncat = foldr ($+$) empty
hcat dl = sequence dl >>= return . P.hcat
hsep dl = sequence dl >>= return . P.hsep
vcat dl = sequence dl >>= return . P.vcat
sep dl  = sequence dl >>= return . P.sep
cat dl  = sequence dl >>= return . P.cat
fsep dl = sequence dl >>= return . P.fsep
fcat dl = sequence dl >>= return . P.fcat

-- Some More

hang :: Doc -> Int -> Doc -> Doc
hang dM i rM = do{d<-dM; r<-rM; return $ P.hang d i r}

punctuate :: Doc -> [Doc] -> [Doc]
punctuate _ []      = []
punctuate p (d1:ds) = go d1 ds
                    where go d [] = [d]
                          go d (e:es) = (d <> p) : go e es

accentuate :: Doc -> [Doc] -> [Doc]
accentuate d list = map (d<>) list

indent = 3

-- data Info ...

class Printer a where
    pprint' :: a -> DocM P.Doc
    pprint  :: a -> Env.GlobalE -> P.Doc
    pprint obj env = let DocM sf          = pprint' obj
                         (result, _state) = sf (emptyPPState { globalEnv = env })
                         doc              = result
                     in doc


instance Printer Isa.DatatypeDef where
    pprint' (Isa.DatatypeDef tyspec dataspecs)
        = pprint' tyspec 
          <+> vcat (zipWith (<+>) (equals : repeat (char '|'))
                                  (map ppconstr dataspecs))
          where ppconstr (Isa.Constructor con types) 
                    = hsep $ pprint' con : map pprint' types


instance Printer Isa.Cmd where
    pprint' (Isa.Comment string) = empty -- blankline $ comment string
    pprint' (Isa.Block cmds)     = blankline $ vcat $ map pprint' cmds
    pprint' (Isa.TheoryCmd thy imps cmds)
        = do env <- queryPP globalEnv
             let imps' = map pprint' (imps ++ [Isa.Theory Env.prelude])
             withCurrentTheory thy $
               text "theory" <+> pprint' thy                     $+$
               text "imports " <> fsep  imps'    $+$
               text "begin"                                      $+$
               (vcat $ map pprint' cmds)                         $+$
               text "\nend"

    pprint' (Isa.DatatypeCmd (def:defs)) = 
        let fstDef = text "datatype" <+> pprint' def
            restDefs = map ((text "and     " <+>) . pprint') defs
        in blankline $ vcat (fstDef:restDefs)
          

    pprint' (Isa.RecordCmd tyspec conspecs)
        = blankline $
          text "record" <+> pprint' tyspec <+> equals $$
          space <+> vcat (map pp conspecs)
          where pp (slotName, slotType) = pprint' slotName <+> text "::" <+> pprint' slotType

    pprint' (Isa.DefinitionCmd vname tysig matching)
        = case matching of
            (pat, term)
                -> blankline $
                   text "definition" <+> ppHeader vname tysig $$
                   text "where" $$
                   space <+> (maybeWithinHOL $ ppEquation pat term)
        where 
          ppHeader n sig
              | isEmptySig sig = pprint' n
              | otherwise      = pprint' n <+> text "::" <+> maybeWithinHOL (pprint' sig)
          ppEquation pat term
              = do thy <- queryPP currentTheory 
                   env <- queryPP globalEnv
                   let lookup = (\n -> lookupIdentifier thy n env)
                   pprint' pat <+> equals <+> parensIf (isCompound term lookup) (pprint' term)

    pprint' (Isa.PrimrecCmd fnames tysigs equations)
        = printFunDef "primrec" fnames tysigs equations

    pprint' (Isa.FunCmd fnames tysigs equations)
        = printFunDef "fun" fnames tysigs equations

    pprint' (Isa.ClassCmd classN superclassNs typesigs)
        = blankline $
          text "class" <+> pprint' classN 
                       <+> equals 
                       <+> hsep (punctuate plus (map pprint' superclassNs))
                       <+> (if null typesigs then empty else plus) $$
          space <> space <> vcat (zipWith (<+>) (repeat (text "fixes"))
                                                (map ppSig typesigs))
        where ppSig (Isa.TypeSig n t)
                  = pprint' n <+> text "::" <+> pprint' t
          
    pprint' (Isa.InstanceCmd classN typ cmds)
        = do thy <- queryPP currentTheory
             let cmds' = map (renameInstanceCmd thy typ) cmds
             blankline $
               text "instantiation" <+> pprint' typ <+> text "::" <+> pprint' classN $$
               text "begin" $$
               space <> space <> vcat (map pprint' cmds') $$
               (blankline $
                text "instance .." $$
                text "end")
        where
          renameInstanceCmd thy t c
              = let renams = [ (n, mk_InstanceCmd_name n t) | n <- namesFromIsaCmd c ]
                in renameIsaCmd thy renams c
 
    pprint' (Isa.InfixDeclCmd op assoc prio)
        = comment $ text "infix" <> pp assoc <+> int prio <+> pprint' op
          where pp Isa.AssocNone  = text ""
                pp Isa.AssocLeft  = text "l"
                pp Isa.AssocRight = text "r"
    
    pprint' (Isa.TypesCmd aliases) = text "type" <+> vcat (map pp aliases)
        where pp (spec, typ) = pprint' spec <+> equals <+> pprint' typ

printFunDef cmd fnames tysigs equations
    = blankline $
      text cmd <+> vcat (punctuate (text " and ") (map ppHeader (zip fnames tysigs))) $$
      text "where" $$
      vcat (zipWith (<+>) (space : repeat (char '|'))
            (map ppEquation equations))
    where 
      ppHeader (fn, sig)
          | isEmptySig sig = pprint' fn
          | otherwise      = pprint' fn <+> text "::" <+> maybeWithinHOL (pprint' sig)
      ppEquation (fname, pattern, term) 
          = do thy <- queryPP currentTheory 
               env <- queryPP globalEnv
               let lookup = (\n -> lookupIdentifier thy n env)
               maybeWithinHOL $
                              pprint' fname <+> 
                              hsep (map pprint' pattern) <+> 
                              equals <+> 
                              parensIf (isCompound term lookup) (pprint' term)

instance Printer Isa.Theory where
    pprint' (Isa.Theory name) = text name

instance Printer Isa.TypeSpec where
    pprint' (Isa.TypeSpec [] tycon)
        = pprint' tycon
    pprint' (Isa.TypeSpec tyvars tycon)
        = let tyvars' = parens . hsep . punctuate comma . accentuate apostroph $ 
                        map pprint' tyvars
          in tyvars' <+> pprint' tycon

instance Printer Isa.Name where
    pprint' n@(Isa.Name _)      = pprintName n
    pprint' (Isa.QName _ str)   = pprintName (Isa.Name str) -- FIXME

pprintName n@(Isa.Name str)
    = withinHOL_if (isReservedKeyword str) 
      $ do thy <- queryPP currentTheory 
           env <- queryPP globalEnv
           app <- queryPP currentAppFlavor
           case app of
             Just (InfixApp _ _ _) -> text str
             _  -> let lookup = (\n -> lookupIdentifier thy n env)
                   in if (isInfixOp n lookup || isUnaryOp n lookup)
                      then parens $ text "op" <+> text str
                      else text str


instance Printer Isa.Type where
    pprint' (Isa.TyNone)      = text ""
    pprint' (Isa.TyVar vname) 
        = do alist <- queryPP currentTyScheme
             let tyvar_doc = apostroph <> pprint' vname
             case lookup vname alist of
               Nothing       -> tyvar_doc
               Just [classN] -> parens (tyvar_doc <+> text "::" <+> pprint' classN)
               Just classNs  
                   -> parens $ tyvar_doc <+> 
                               text "::" <+> 
                               (braces . vcat . punctuate comma . map pprint' $ classNs)

    pprint' (Isa.TyCon cname []) = pprint' cname 
    pprint' (Isa.TyCon cname tyvars) 
        = do maybeWithinHOL $
               hsep (map pp tyvars) <+> pprint' cname
          where pp tyvar = parensIf (isCompoundType tyvar) (pprint' tyvar)

    pprint' (Isa.TyScheme [] t)  = pprint' t
    pprint' (Isa.TyScheme ctx t) = withTyScheme ctx (pprint' t)

    pprint' (Isa.TyFun t1 t2)
        = maybeWithinHOL $
            case t1 of Isa.TyFun _ _ -> parens (pprint' t1) <+> text "=>" <+> pprint' t2
                       _             -> pprint' t1          <+> text "=>" <+> pprint' t2

    pprint' (Isa.TyTuple types)
        = maybeWithinHOL $
            hsep (punctuate (space<>asterisk) (map pprint' types))


instance Printer Isa.TypeSig where
    pprint' (Isa.TypeSig _name typ) = pprint' typ

instance Printer Isa.Literal where
    -- We annotate Integer literals explicitly to be of our sort "num"
    -- (cf. Prelude.thy), because otherwise Isabelle's type inference
    -- would come up with a too general type, resulting in
    -- non-workingness.
    pprint' (Isa.Int i)      = let cc = colon <> colon in
                               integer i
                               -- parens $ integer i  <> cc <> text "_" <> cc <> text "num"
    pprint' (Isa.Char ch)    = text "CHR " <+> quotes (quotes (char ch))
    pprint' (Isa.String str) = quotes . quotes . text $ str

instance Printer Isa.Term where
    pprint' (Isa.Var vname)         = pprint' vname
    pprint' (Isa.Literal lit)       = pprint' lit
    pprint' (Isa.Parenthesized t)   
        = do thy <- queryPP currentTheory 
             env <- queryPP globalEnv
             let lookup = (\n -> lookupIdentifier thy n env)
             parensIf (not (isSelfEvaluating t lookup)) 
               $ pprint' t

    pprint' app @ (Isa.App t1 t2)   
        = do thy <- queryPP currentTheory 
             env <- queryPP globalEnv
             let lookup = (\n -> lookupIdentifier thy n env)
             let flavor = categorizeApp app lookup
             withinApplication flavor $
               case flavor of
                 ListApp  l      -> pprintAsList l
                 TupleApp l      -> pprintAsTuple l
                 InfixApp x op y -> let x' = parensIf (isCompound x lookup) $ pprint' x
                                        y' = parensIf (isCompound y lookup) $ pprint' y
                                    in  x' <+> pprint' op <+> y'
                 FunApp          -> pprint' t1 <+> parensIf (isCompound t2 lookup) (pprint' t2)
                 UnaryOpApp      -> pprint' t1 <+> parensIf (isCompound t2 lookup) (pprint' t2)

    pprint' (Isa.If t1 t2 t3)
        = fsep [text "if"   <+> pprint' t1,
                text "then" <+> pprint' t2,
                text "else" <+> pprint' t3]

    pprint' lexpr@(Isa.Lambda _ _)
        = let (argNs, body) = flattenLambdas lexpr in 
          fsep [text "%" <+> hsep (map pprint' argNs) <+> dot,
                nest 2 (pprint' body)]

    pprint' (Isa.RecConstr recordN updates)
        = pprint' recordN <+> (bananas . vcat . punctuate comma $ map pp updates)
          where pp (vname, typ) = pprint' vname <+> equals <+> pprint' typ

    pprint' (Isa.RecUpdate term updates)
        = pprint' term <+> (bananas . vcat . punctuate comma $ map pp updates)
          where pp (vname, typ) = pprint' vname <+> text ":=" <+> pprint' typ

    pprint' (Isa.Case term matchs)
         = hang (text "case" <+> pprint' term <+> text "of")
                1
                (vcat $ zipWith (<+>) (space : repeat (char '|'))
                                      (map pp matchs))
           where pp (pat, term) = (pprint' pat) <+> text "=>" <+> pprint' term


    pprint' (Isa.Let bindings body)
        = text "let" <+> vcat (punctuate semi (map ppBinding bindings))
                   $$ text "in" <+> pprint' body
          where ppBinding (pat, term)
                    = pprint' pat <+> equals <+> pprint' term

    pprint' (Isa.ListComp body stmts)
        = brackets $ pprint' body <+> text "." <+>
                       (vcat (punctuate comma (map ppStmt stmts)))
        where
          ppStmt (Isa.Guard b)
              = pprint' b
          ppStmt (Isa.Generator (p, e)) 
              = pprint' p <+> text "<-" <+> pprint' e

    pprint' (Isa.DoBlock pre stmts post) = 
        text pre <+> (vcat $ (printStmts stmts) ++ [text post])
        where printStmts [stmt] = [pprint' stmt]
              printStmts (stmt:stmts) = (pprint' stmt <> semi) : (printStmts stmts)

instance Printer Isa.Stmt where
    pprint' (Isa.DoGenerator pat exp) = pprint' pat <+> text "<-" <+> pprint' exp
    pprint' (Isa.DoQualifier exp) = pprint' exp


reAdaptEnvName :: Env.EnvName -> Maybe Env.EnvName
reAdaptEnvName name
    = let AdaptionTable mappings = adaptionTable
          mappings' = [ (Env.identifier2name id2, Env.identifier2name id1) 
                            | (id1, id2) <- mappings ]
      in lookup name mappings'

isNil, isCons, isPairCon :: Isa.Name -> Bool

mk_isFoo foo n
    = let n' = reAdaptEnvName (Env.fromIsa n)
      in case n' of
           Nothing -> False
           Just x -> case Env.toHsk x of
                       Special con -> con == foo
                       _ -> False

isNil     = mk_isFoo Hs.ListCon
isCons    = mk_isFoo Hs.Cons
isPairCon = mk_isFoo (Hs.TupleCon 2)

isEmptySig (Isa.TypeSig _ Isa.TyNone) = True
isEmptySig _ = False

isReservedKeyword :: String -> Bool
isReservedKeyword str = str `elem` reserved_keywords

pprintAsList :: [Isa.Term] -> DocM P.Doc
pprintAsList list = let (xs, [Isa.Var nil]) = splitAt (length list - 1) list
                    in assert (isNil nil) 
                         $ brackets (hsep (punctuate comma (map pprint' xs)))

pprintAsTuple :: [Isa.Term] -> DocM P.Doc
pprintAsTuple = parens . hsep . punctuate comma . map pprint'


data AppFlavor = ListApp [Isa.Term] 
               | TupleApp [Isa.Term] 
               | InfixApp Isa.Term Isa.Term Isa.Term 
               | UnaryOpApp
               | FunApp
  deriving (Show)

-- This makes use of pattern guards which are not Haskell98, but quite
-- portable across implementations nontheless.
--
-- Cf. http://www.haskell.org/ghc/docs/latest/html/users_guide/syntax-extns.html#pattern-guards
--

categorizeApp :: Isa.Term -> (Isa.Name -> Maybe Env.Identifier) -> AppFlavor
categorizeApp app@(Isa.App (Isa.App (Isa.Var opN) t1) t2) lookupFn
    | isCons opN,    Just list <- flattenListApp app  = ListApp list
    | isPairCon opN, Just list <- flattenTupleApp app = TupleApp list
    | isInfixOp opN lookupFn                          = InfixApp t1 (Isa.Var opN) t2
categorizeApp (Isa.App (Isa.Var opN) _) lookupFn
    | isUnaryOp opN lookupFn                              = UnaryOpApp
    | otherwise                                           = FunApp
categorizeApp _ _ = FunApp

flattenListApp :: Isa.Term -> Maybe [Isa.Term]
flattenListApp app = let list = unfoldr1 split app in 
                     case last list of -- proper list?
                       (Isa.Var c) | isNil c -> Just list
                       _ -> Nothing
  where
    split (Isa.App (Isa.App (Isa.Var c) x) xs) | isCons c = Just (x, xs)
    split _ = Nothing

flattenTupleApp :: Isa.Term -> Maybe [Isa.Term]
flattenTupleApp app = let list = unfoldr1 split app in
                      if (length list) > 1 then Just list
                                           else Nothing
  where
    split (Isa.App (Isa.App (Isa.Var c) x) xs) | isPairCon c = Just (x, xs)
    split _ = Nothing

-- flattenLambdas ``%x . %y . %z . foo'' => ([x,y,z], foo)
--
flattenLambdas :: Isa.Term -> ([Isa.Name], Isa.Term)
flattenLambdas (Isa.Lambda arg1 (Isa.Lambda arg2 body)) 
    = let (args, real_body) = flattenLambdas body
      in ([arg1,arg2]++args, real_body)
flattenLambdas (Isa.Lambda arg body) = ([arg], body)
flattenLambdas t = ([], t)

isSelfEvaluating :: Isa.Term -> (Isa.Name -> Maybe Env.Identifier) -> Bool
isSelfEvaluating t lookupFn
    = case t of
        Isa.Var _            -> True
        Isa.Literal _        -> True
        Isa.Parenthesized _  -> True
        Isa.App _ _          -> case categorizeApp t lookupFn of
                                  ListApp  _     -> True
                                  TupleApp _     -> True
                                  FunApp         -> False
                                  UnaryOpApp     -> False
                                  InfixApp _ _ _ -> False
        _ -> False

isCompound :: Isa.Term -> (Isa.Name -> Maybe Env.Identifier) -> Bool
isCompound t lookupFn
    = case t of
        Isa.Var _            -> False
        Isa.Literal _        -> False
        Isa.Parenthesized _  -> False
        Isa.App _ _          -> case categorizeApp t lookupFn of
                                  ListApp  _     -> False
                                  TupleApp _     -> False
                                  FunApp         -> False
                                  UnaryOpApp     -> True
                                  InfixApp _ _ _ -> True
        _ -> True

isCompoundType :: Isa.Type -> Bool
isCompoundType t = case t of
                     Isa.TyVar _    -> False
                     Isa.TyCon _ [] -> False
                     _              -> True
                     
isInfixOp :: Isa.Name -> (Isa.Name -> Maybe Env.Identifier) -> Bool                 
isInfixOp name lookupFn
    = case lookupFn name of
        Just id -> Env.isInfixOp id
        _       -> False

isUnaryOp :: Isa.Name -> (Isa.Name -> Maybe Env.Identifier) -> Bool
isUnaryOp name lookupFn
    = case lookupFn name of
        Just id -> Env.isUnaryOp id
        _       -> False

lookupIdentifier :: Isa.Theory -> Isa.Name -> Env.GlobalE -> Maybe Env.Identifier
lookupIdentifier thy n globalEnv
    = Env.lookupConstant (Env.fromIsa thy) (Env.fromIsa n) globalEnv
