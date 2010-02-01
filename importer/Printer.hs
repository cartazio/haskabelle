{-# LANGUAGE PatternGuards #-}

{-| Author: Tobias C. Rittweiler, TU Muenchen

Pretty printing of abstract Isar/HOL theory.
-}

module Importer.Printer (pprint) where

import Importer.Library
import qualified Importer.AList as AList
import Control.Monad (liftM2)

import qualified Text.PrettyPrint as P

import qualified Language.Haskell.Exts as Hsx (SpecialCon(..), QName(..))

import Importer.Adapt as Adapt (AdaptionTable(AdaptionTable))
import qualified Importer.Ident_Env as Ident_Env

import qualified Importer.Isa as Isa


data PPState = PPState { globalEnv        :: Ident_Env.GlobalE,
                         currentTheory    :: Isa.ThyName,
                         -- Are we in an Infix Application?
                         currentAppFlavor :: Maybe AppFlavor,
                         currentTyScheme  :: [(Isa.Name, [Isa.Name])],
                         -- If True, we're already in doubly-quoted section.
                         withinHOL        :: Bool
                       }

data DocM v = DocM (PPState -> (v, PPState))

emptyPPState = PPState { globalEnv = Ident_Env.initialGlobalEnv,
                         currentTheory = Isa.ThyName "Scratch",
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

semi, comma, colon, dot, apostroph, space :: Doc
lparen, rparen, lbrack, rbrack, lbrace, rbrace :: Doc

semi = return P.semi
comma = return P.comma
colon = return P.colon
dot = char '.'
apostroph = char '\''
space  = return P.space

lparen = return P.lparen
rparen = return P.rparen
lbrack = return P.lbrack
rbrack = return P.rbrack
lbrace = return P.lbrace
rbrace = return P.rbrace

equals, prod, plus, rightarrow :: Doc

equals = return P.equals
prod = text "\\<times>"
plus = char '+'
rightarrow = text "\\<Rightarrow>"




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

withCurrentTheory :: Isa.ThyName -> Doc -> Doc
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

ncat, hcat, hsep, vcat, sep, cat, fsep, fcat, parcommas, brcommas :: [Doc] -> Doc
ncat = foldr ($+$) empty
hcat dl = sequence dl >>= return . P.hcat
hsep dl = sequence dl >>= return . P.hsep
vcat dl = sequence dl >>= return . P.vcat
sep dl  = sequence dl >>= return . P.sep
cat dl  = sequence dl >>= return . P.cat
fsep dl = sequence dl >>= return . P.fsep
fcat dl = sequence dl >>= return . P.fcat
parcommas dl = sequence dl >>= return . P.parens . P.hsep . P.punctuate P.comma
brcommas dl = sequence dl >>= return . P.braces . P.hsep . P.punctuate P.comma

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

class Printer a where
    pprint' :: AdaptionTable -> [String] -> a -> DocM P.Doc
    pprint  :: AdaptionTable -> [String] -> Ident_Env.GlobalE -> a -> P.Doc
    pprint adapt reserved env obj = let
      DocM sf = pprint' adapt reserved obj
      (doc, _state) = sf (emptyPPState { globalEnv = env })
      in doc

instance Printer Isa.Module where

    pprint' adapt reserved (Isa.Module thy imps cmds)
        = do env <- queryPP globalEnv
             let imps' = map (pprint' adapt reserved) (imps ++ [Isa.ThyName Ident_Env.prelude])
             withCurrentTheory thy $
               text "theory" <+> pprint' adapt reserved thy $+$
               text "imports " <> fsep  imps' $+$
               text "begin" $+$
               (vcat $ map (pprint' adapt reserved) cmds) $+$
               text "\nend\n"

instance Printer Isa.Function_Stmt where

    pprint' adapt reserved (Isa.Function_Stmt kind sigs eqns) =
      blankline $
        text prologue <+> vcat (punctuate (text " and ") (map (pprint' adapt reserved) sigs)) $$
        text "where" $$
        vcat (zipWith (<+>) (space : repeat (char '|'))
          (map pprint_eqn eqns)) $$
        text epilogue
      where 
        (prologue, epilogue) = case kind of
          Isa.Definition -> ("definition", "")
          Isa.Primrec -> ("primrec", "")
          Isa.Fun -> ("fun", "")
          Isa.Function_Sorry -> ("function (sequential)", "sorry termination sorry")
        pprint_eqn (fname, pattern, term) = do
          thy <- queryPP currentTheory 
          env <- queryPP globalEnv
          let lookup = (\n -> lookupIdentifier thy n env)
          maybeWithinHOL $
            pprint' adapt reserved fname <+> 
            hsep (map (pprint' adapt reserved) pattern) <+> 
            equals <+> 
            parensIf (isCompound adapt term lookup) (pprint' adapt reserved term)

printFunDef adapt reserved prologue epilogue tysigs equations
    = blankline $
      text prologue <+> vcat (punctuate (text " and ") (map (pprint' adapt reserved) tysigs)) $$
      text "where" $$
      vcat (zipWith (<+>) (space : repeat (char '|'))
            (map ppEquation equations)) $$
      text epilogue
    where 
      ppEquation (fname, pattern, term) 
          = do thy <- queryPP currentTheory 
               env <- queryPP globalEnv
               let lookup = (\n -> lookupIdentifier thy n env)
               maybeWithinHOL $
                              pprint' adapt reserved fname <+> 
                              hsep (map (pprint' adapt reserved) pattern) <+> 
                              equals <+> 
                              parensIf (isCompound adapt term lookup) (pprint' adapt reserved term)

instance Printer Isa.Stmt where

    pprint' adapt reserved (Isa.Comment string) = empty -- blankline $ comment string

    pprint' adapt reserved (Isa.Datatype (decl : decls)) =
      blankline $ vcat (text "datatype" <+> pprintDecl decl :
        map ((text "and     " <+>) . pprintDecl) decls) where
        pprintDecl (tyspec, dataspecs) =
          pprint' adapt reserved tyspec  <+> vcat (zipWith (<+>) (equals : repeat (char '|'))
            (map pprintConstr dataspecs))
        pprintConstr (con, types)  =
          hsep $ pprint' adapt reserved con : map (pprint' adapt reserved) types

    pprint' adapt reserved (Isa.Record tyspec conspecs)
        = blankline $
          text "record" <+> pprint' adapt reserved tyspec <+> equals $$
          space <+> vcat (map pp conspecs)
          where pp (slotName, slotType) = pprint' adapt reserved slotName <+> text "::" <+> pprint' adapt reserved slotType

    pprint' adapt reserved (Isa.Function stmt) = pprint' adapt reserved stmt

    pprint' adapt reserved (Isa.Class classN superclassNs typesigs)
        = blankline $
          text "class"
          <+> pprint' adapt reserved classN 
          <+> (if null superclassNs && null typesigs then empty else equals)
          <+> hsep (punctuate plus (map (pprint' adapt reserved) superclassNs))
          <+> (if null superclassNs || null typesigs then empty else plus) $$
            space <> space <>
              vcat (zipWith (<+>) (repeat (text "fixes")) (map ppSig typesigs))
        where ppSig (Isa.TypeSign n arities t)
                  = pprint' adapt reserved n <+> text "::" <+> withTyScheme arities (pprint' adapt reserved t)
          
    pprint' adapt reserved (Isa.Instance classN tycoN arities stmts) = do
      thy <- queryPP currentTheory
      let stmts' = map (renameFunctionStmt thy) stmts
      blankline $
        text "instantiation" <+> (if is_prod then text ['"', '*', '"'] else pprint' adapt reserved tycoN) <+> text "::"
          <+> (if null arities then pprint' adapt reserved classN
            else parcommas (map (pprint_sort adapt reserved . snd) arities) <+> pprint' adapt reserved classN) $$
          text "begin" $$
          space <> space <> vcat (map (pprint' adapt reserved) stmts') $$
          (blankline $ text "instance sorry\n" $$ text "end")
      where
        is_prod = Isa.base_name_of tycoN == "*"
        suffix = if is_prod then "prod" else Isa.base_name_of tycoN
        suffix_tyco (Isa.QName t n) = Isa.QName t (concat [n, "_", suffix])
        suffix_tyco (Isa.Name n) = Isa.Name (concat [n, "_", suffix])
        renameTypeSign (Isa.TypeSign name vs ty) = Isa.TypeSign (suffix_tyco name) vs ty
        renameClause (name, pats, body) = (suffix_tyco name, pats, body)
        renameFunctionStmt thy (Isa.Function_Stmt kind tysigs clauses) =
          Isa.Function_Stmt kind (map renameTypeSign tysigs) (map renameClause clauses)

    pprint' adapt reserved (Isa.TypeSynonym aliases) = blankline $ text "types" <+> vcat (map pp aliases)
        where pp (spec, typ) = pprint' adapt reserved spec <+> equals <+> pprint' adapt reserved typ

instance Printer Isa.ThyName where
    pprint' adapt reserved (Isa.ThyName name) =
      text (map (\c -> if c == '.' then '_' else c) name)
      -- FIXME need uniform rename of theory names

instance Printer Isa.TypeSpec where
    pprint' adapt reserved (Isa.TypeSpec [] tycon)
        = pprint' adapt reserved tycon
    pprint' adapt reserved (Isa.TypeSpec tyvars tycon)
        = let tyvars' = parens . hsep . punctuate comma . accentuate apostroph $ 
                        map (pprint' adapt reserved) tyvars
          in tyvars' <+> pprint' adapt reserved tycon

instance Printer Isa.Name where
  pprint' adapt reserved n = case n of
    Isa.Name str -> pprintName reserved str
    Isa.QName _ str -> pprintName reserved str -- FIXME

pprintName reserved str = withinHOL_if (isReservedKeyword str) 
      $ do thy <- queryPP currentTheory 
           env <- queryPP globalEnv
           app <- queryPP currentAppFlavor
           case app of
             Just (InfixApp _ _ _) -> text str
             _  -> let lookup s = lookupIdentifier thy (Isa.Name s) env
                   in if (isInfixOp lookup str || isUnaryOp lookup str)
                      then parens $ text "op" <+> text str
                      else text str
      where
        isReservedKeyword :: String -> Bool
        isReservedKeyword str = str `elem` reserved

pprint_sort :: AdaptionTable -> [String] -> [Isa.Name] -> DocM P.Doc
pprint_sort adapt reserved [cls] = pprint' adapt reserved cls
pprint_sort adapt reserved sort = brcommas $ map (pprint' adapt reserved) sort

instance Printer Isa.Type where
    pprint' adapt reserved (Isa.NoType) = text ""
    pprint' adapt reserved (Isa.TVar vname) 
        = do alist <- queryPP currentTyScheme
             let tyvar_doc = apostroph <> pprint' adapt reserved vname
             let sort = these (lookup vname alist)
             if null sort
               then tyvar_doc
               else parens (tyvar_doc <+> text "::" <+> pprint_sort adapt reserved sort)

    pprint' adapt reserved (Isa.Type cname []) = pprint' adapt reserved cname 
    pprint' adapt reserved (Isa.Type cname [typ]) =
      maybeWithinHOL $
        parensIf (isCompoundType typ) (pprint' adapt reserved typ)
        <+> pprint' adapt reserved cname
    pprint' adapt reserved (Isa.Type (Isa.QName (Isa.ThyName "Prelude") "*") [typ1, typ2]) =
      maybeWithinHOL $ parensIf (isCompoundType typ1) (pprint' adapt reserved typ1)
        <+> text "*" <+> parensIf (isCompoundType typ2) (pprint' adapt reserved typ2)
    pprint' adapt reserved (Isa.Type cname typs) =
      maybeWithinHOL $
        parcommas (map (pprint' adapt reserved) typs)
        <+> pprint' adapt reserved cname

    pprint' adapt reserved (Isa.Func t1 t2)
        = maybeWithinHOL $
            case t1 of Isa.Func _ _ -> parens (pprint' adapt reserved t1) <+> rightarrow <+> pprint' adapt reserved t2
                       _             -> pprint' adapt reserved t1          <+> rightarrow <+> pprint' adapt reserved t2


instance Printer Isa.TypeSign where
  pprint' adapt reserved (Isa.TypeSign name _ Isa.NoType) = pprint' adapt reserved name
  pprint' adapt reserved (Isa.TypeSign name arities typ) = pprint' adapt reserved name <+> text "::"
    <+> maybeWithinHOL (withTyScheme arities (pprint' adapt reserved typ))
    
instance Printer Isa.Literal where
    -- We annotate Integer literals explicitly to be of our sort "num"
    -- (cf. Prelude.thy), because otherwise Isabelle's type inference
    -- would come up with a too general type, resulting in
    -- non-workingness.
    pprint' adapt reserved (Isa.Int i)      = let cc = colon <> colon in
                               integer i
                               -- parens $ integer i  <> cc <> text "_" <> cc <> text "num"
    pprint' adapt reserved (Isa.Char ch)    = text "CHR" <+> quotes (quotes (char ch))
    pprint' adapt reserved (Isa.String str) = quotes . quotes . text $ str

instance Printer Isa.Term where
    pprint' adapt reserved (Isa.Const vname)         = pprint' adapt reserved vname
    pprint' adapt reserved (Isa.Literal lit)       = pprint' adapt reserved lit
    pprint' adapt reserved (Isa.Parenthesized t)   
        = do thy <- queryPP currentTheory 
             env <- queryPP globalEnv
             let lookup = (\n -> lookupIdentifier thy n env)
             parensIf (not (isSelfEvaluating adapt t lookup)) 
               $ pprint' adapt reserved t

    pprint' adapt reserved app @ (Isa.App t1 t2)   
        = do thy <- queryPP currentTheory 
             env <- queryPP globalEnv
             let lookup = (\n -> lookupIdentifier thy n env)
             let flavor = categorizeApp adapt app lookup
             withinApplication flavor $
               case flavor of
                 ListApp  l      -> pprintAsList adapt reserved l
                 TupleApp l      -> pprintAsTuple adapt reserved l
                 InfixApp x op y -> let x' = parensIf (isCompound adapt x lookup) $ pprint' adapt reserved x
                                        y' = parensIf (isCompound adapt y lookup) $ pprint' adapt reserved y
                                    in  x' <+> pprint' adapt reserved op <+> y'
                 FunApp          -> pprint' adapt reserved t1 <+> parensIf (isCompound adapt t2 lookup) (pprint' adapt reserved t2)
                 UnaryOpApp      -> pprint' adapt reserved t1 <+> parensIf (isCompound adapt t2 lookup) (pprint' adapt reserved t2)

    pprint' adapt reserved (Isa.If t1 t2 t3)
        = fsep [text "if"   <+> pprint' adapt reserved t1,
                text "then" <+> pprint' adapt reserved t2,
                text "else" <+> pprint' adapt reserved t3]

    pprint' adapt reserved lexpr@(Isa.Abs _ _)
        = let (argNs, body) = flattenLambdas lexpr in 
          fsep [text "%" <+> hsep (map (pprint' adapt reserved) argNs) <+> dot,
                nest 2 (pprint' adapt reserved body)]

    pprint' adapt reserved (Isa.RecConstr recordN updates)
        = pprint' adapt reserved recordN <+> (bananas . vcat . punctuate comma $ map pp updates)
          where pp (vname, typ) = pprint' adapt reserved vname <+> equals <+> pprint' adapt reserved typ

    pprint' adapt reserved (Isa.RecUpdate term updates)
        = pprint' adapt reserved term <+> (bananas . vcat . punctuate comma $ map pp updates)
          where pp (vname, typ) = pprint' adapt reserved vname <+> text ":=" <+> pprint' adapt reserved typ

    pprint' adapt reserved (Isa.Case term matchs)
         = hang (text "case" <+> pprint' adapt reserved term <+> text "of")
                1
                (vcat $ zipWith (<+>) (space : repeat (char '|'))
                                      (map pp matchs))
           where pp (pat, term) = (pprint' adapt reserved pat) <+> rightarrow <+> pprint' adapt reserved term


    pprint' adapt reserved (Isa.Let bindings body)
        = text "let" <+> vcat (punctuate semi (map ppBinding bindings))
                   $$ text "in" <+> pprint' adapt reserved body
          where ppBinding (pat, term)
                    = pprint' adapt reserved pat <+> equals <+> pprint' adapt reserved term

    pprint' adapt reserved (Isa.ListCompr body stmts)
        = brackets $ pprint' adapt reserved body <+> text "." <+>
                       (vcat (punctuate comma (map ppStmt stmts)))
        where
          ppStmt (Isa.Guard b)
              = pprint' adapt reserved b
          ppStmt (Isa.Generator (p, e)) 
              = pprint' adapt reserved p <+> text "<-" <+> pprint' adapt reserved e

    pprint' adapt reserved (Isa.DoBlock pre stmts post) = 
        text pre <+> (vcat $ (printStmts stmts) ++ [text post])
        where printStmts [stmt] = [pprint' adapt reserved stmt]
              printStmts (stmt:stmts) = (pprint' adapt reserved stmt <> semi) : (printStmts stmts)

instance Printer Isa.DoBlockFragment where
    pprint' adapt reserved (Isa.DoGenerator pat exp) = pprint' adapt reserved pat <+> text "<-" <+> pprint' adapt reserved exp
    pprint' adapt reserved (Isa.DoQualifier exp) = pprint' adapt reserved exp


reAdaptEnvName :: AdaptionTable -> Ident_Env.Name -> Maybe Ident_Env.Name
reAdaptEnvName adapt name
    = let AdaptionTable mappings = adapt
          mappings' = [ (Ident_Env.identifier2name id2, Ident_Env.identifier2name id1) 
                            | (id1, id2) <- mappings ]
      in lookup name mappings'

isNil, isCons, isPairCon :: AdaptionTable -> Isa.Name -> Bool

mk_isFoo adapt foo n = case reAdaptEnvName adapt (Ident_Env.fromIsa n) of
  Nothing -> False
  Just x -> case Ident_Env.toHsk x of
    Hsx.Special con -> con == foo
    _ -> False

isNil adapt = mk_isFoo adapt Hsx.ListCon
isCons adapt = mk_isFoo adapt Hsx.Cons
isPairCon adapt = mk_isFoo adapt (Hsx.TupleCon 2)

pprintAsList :: AdaptionTable -> [String] -> [Isa.Term] -> DocM P.Doc
pprintAsList adapt reserved ts = brackets (hsep (punctuate comma (map (pprint' adapt reserved) ts)))

pprintAsTuple :: AdaptionTable -> [String] -> (Isa.Term, Isa.Term) -> DocM P.Doc
pprintAsTuple adapt reserved (t1, t2) = (parens . hsep . punctuate comma . map (pprint' adapt reserved)) [t1, t2]


data AppFlavor = ListApp [Isa.Term] 
               | TupleApp (Isa.Term, Isa.Term)
               | InfixApp Isa.Term Isa.Term Isa.Term 
               | UnaryOpApp
               | FunApp
  deriving (Show)

-- This makes use of pattern guards which are not Haskell98, but quite
-- portable across implementations nontheless.
--
-- Cf. http://www.haskell.org/ghc/docs/latest/html/users_guide/syntax-extns.html#pattern-guards
--

categorizeApp :: AdaptionTable -> Isa.Term -> (Isa.Name -> Maybe Ident_Env.Identifier) -> AppFlavor
categorizeApp adapt app@(Isa.App (Isa.App (Isa.Const opN) t1) t2) lookupFn
    | isCons adapt opN, Just list <- flattenListApp adapt app = ListApp list
    | isPairCon adapt opN, Just list <- destTupleApp adapt app = TupleApp list
    | isInfixOp lookupFn opN = InfixApp t1 (Isa.Const opN) t2
categorizeApp _ (Isa.App (Isa.Const opN) _) lookupFn
    | isUnaryOp lookupFn opN = UnaryOpApp
    | otherwise = FunApp
categorizeApp _ _ _ = FunApp

flattenListApp :: AdaptionTable -> Isa.Term -> Maybe [Isa.Term]
flattenListApp adapt t = case uncombr dest_cons t of
    (ts, Isa.Const c) | isNil adapt c -> Just ts
    _ -> Nothing
  where
    dest_cons (Isa.App (Isa.App (Isa.Const c) t1) t2) | isCons adapt c = Just (t1, t2)
    dest_cons _ = Nothing

destTupleApp :: AdaptionTable -> Isa.Term -> Maybe (Isa.Term, Isa.Term)
destTupleApp adapt (Isa.App (Isa.App (Isa.Const c) t1) t2) | isPairCon adapt c = Just (t1, t2)
destTupleApp _ _ = Nothing

-- flattenLambdas ``%x . %y . %z . foo'' => ([x,y,z], foo)
--
flattenLambdas :: Isa.Term -> ([Isa.Name], Isa.Term)
flattenLambdas (Isa.Abs arg1 (Isa.Abs arg2 body)) 
    = let (args, real_body) = flattenLambdas body
      in ([arg1,arg2]++args, real_body)
flattenLambdas (Isa.Abs arg body) = ([arg], body)
flattenLambdas t = ([], t)

isSelfEvaluating :: AdaptionTable -> Isa.Term -> (Isa.Name -> Maybe Ident_Env.Identifier) -> Bool
isSelfEvaluating adapt t lookupFn
    = case t of
        Isa.Const _            -> True
        Isa.Literal _        -> True
        Isa.Parenthesized _  -> True
        Isa.App _ _          -> case categorizeApp adapt t lookupFn of
                                  ListApp  _     -> True
                                  TupleApp _     -> True
                                  FunApp         -> False
                                  UnaryOpApp     -> False
                                  InfixApp _ _ _ -> False
        _ -> False

isCompound :: AdaptionTable -> Isa.Term -> (Isa.Name -> Maybe Ident_Env.Identifier) -> Bool
isCompound adapt t lookupFn
    = case t of
        Isa.Const _            -> False
        Isa.Literal _        -> False
        Isa.Parenthesized _  -> False
        Isa.App _ _          -> case categorizeApp adapt t lookupFn of
                                  ListApp  _     -> False
                                  TupleApp _     -> False
                                  FunApp         -> False
                                  UnaryOpApp     -> True
                                  InfixApp _ _ _ -> True
        _ -> True

isCompoundType :: Isa.Type -> Bool
isCompoundType t = case t of
                     Isa.TVar _    -> False
                     Isa.Type _ [] -> False
                     _              -> True
                     
isInfixOp :: (a -> Maybe Ident_Env.Identifier) -> a -> Bool
isInfixOp lookupFn name 
    = case lookupFn name of
        Just id -> Ident_Env.isInfixOp id
        _       -> False

isUnaryOp :: (a -> Maybe Ident_Env.Identifier) -> a -> Bool
isUnaryOp lookupFn name
    = case lookupFn name of
        Just id -> Ident_Env.isUnaryOp id
        _       -> False

lookupIdentifier :: Isa.ThyName -> Isa.Name -> Ident_Env.GlobalE -> Maybe Ident_Env.Identifier
lookupIdentifier thy n globalEnv
    = Ident_Env.lookupConstant (Ident_Env.fromIsa thy) (Ident_Env.fromIsa n) globalEnv
