{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Munich

Pretty printing of abstract Isar/HOL theory.
-}

module Importer.Printer where

import Importer.Utilities.Misc
import qualified Importer.IsaSyntax as Isa

import qualified Text.PrettyPrint as P



data PPState = PPState { withinHOL :: Bool }

data DocM v = DocM (PPState -> (v, PPState))

emptyPPState = PPState { withinHOL = False }

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

maybeWithinHOL :: Doc -> Doc
maybeWithinHOL d   
    = do within_p <- queryPP withinHOL
         if within_p then d
                     else do updatePP (\pps -> pps { withinHOL = True })
                             result <- doubleQuotes d
                             updatePP (\pps -> pps { withinHOL = False })
                             return result

comment :: Doc -> Doc
comment d = text "(*" <+> d <+> text "*)"

-- fill-paragraph str = vcat $ map text (lines str)

-- Combinators

(<>),(<+>),($$),($+$) :: Doc -> Doc -> Doc
aM <> bM  = do{a<-aM; b<-bM; return (a P.<> b)}
aM <+> bM = do{a<-aM; b<-bM; return (a P.<+> b)}
aM $$ bM  = do{a<-aM; b<-bM; return (a P.$$ b)}
aM $+$ bM = do{a<-aM; b<-bM; return (a P.$+$ b)}

hcat,hsep,vcat,sep,cat,fsep,fcat :: [Doc] -> Doc
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
    pprint  :: a -> P.Doc
    pprint obj = let DocM sf          = pprint' obj
                     (result, _state) = sf emptyPPState
                     doc              = result
                 in doc


instance Printer Isa.Cmd where
    pprint' (Isa.Comment string) = empty -- blankline $ comment string
    pprint' (Isa.Block cmds)     = blankline $ vcat $ map pprint' cmds
    pprint' (Isa.TheoryCmd thy cmds)
        = text "theory" <+> pprint' thy $$
          text "imports Main"           $$
          text "begin"                  $$
          (vcat $ map pprint' cmds)

    pprint' (Isa.DatatypeCmd tyspec dataspecs)
        = blankline $
          text "datatype" <+> pprint' tyspec --FIXME tyspec in this case has to be treated differently
          <+> vcat (zipWith (<+>) (equals : repeat (char '|'))
                                  (map pp dataspecs))
          where pp (Isa.Constructor con types) = hsep $ pprint' con : map pprint' types

    pprint' (Isa.RecordCmd tyspec conspecs)
        = blankline $
          text "record" <+> pprint' tyspec <+> equals $$
          space <+> vcat (map pp conspecs)
          where pp (slotName, slotType) = pprint' slotName <+> text "::" <+> pprint' slotType

    pprint' (Isa.DefinitionCmd vname tysig matching)
        = case matching of
            (pat, term)
                -> blankline $
                   text "definition" <+> pprint' vname <+> text "::" <+> pprint' tysig $$
                   text "where" $$
                   space <+> (maybeWithinHOL $ pprint' pat <+> equals <+> pprint' term)

    pprint' (Isa.FunCmd fnames tysigs equations)
        = blankline $
          text "fun" <+> vcat (punctuate (text " and ") (map ppHeader (zip fnames tysigs))) $$
          text "where" $$
          vcat (zipWith (<+>) (space : repeat (char '|'))
                              (map ppEquation equations))
          where ppHeader (fn, sig)
                    = pprint' fn <+> text "::" <+> maybeWithinHOL (pprint' sig)
                ppEquation (fname, pattern, term) 
                    = maybeWithinHOL $
                        pprint' fname <+> hsep (map pprint' pattern) <+> equals <+> pprint' term
 
    pprint' (Isa.InfixDeclCmd op assoc prio)
        = comment $ text "infix" <> pp assoc <+> int prio <+> pprint' op
          where pp Isa.AssocNone  = text ""
                pp Isa.AssocLeft  = text "l"
                pp Isa.AssocRight = text "r"

instance Printer Isa.Theory where
    pprint' (Isa.Theory name) = text name

instance Printer Isa.TypeSpec where
    pprint' (Isa.TypeSpec [] tycon)
        = pprint' tycon
    pprint' (Isa.TypeSpec tyvars tycon)
        = let tyvars' = parens . hsep . punctuate comma . accentuate apostroph $ map pprint' tyvars
          in maybeWithinHOL $ tyvars' <+> pprint' tycon

instance Printer Isa.Name where
    pprint' (Isa.Name str) = text str
    --pprint' (Isa.QName thy str) = pprint' thy <> dot <> text str
    pprint' (Isa.QName thy str) = text str -- FIXME

instance Printer Isa.Type where
    pprint' (Isa.TyVar vname) = apostroph <> pprint' vname

    pprint' (Isa.TyCon cname []) = pprint' cname 
    pprint' (Isa.TyCon cname tyvars) 
        = maybeWithinHOL $
               hsep (map pp tyvars) <+> pprint' cname
          where pp tyvar = parensIf (isCompoundType tyvar) (pprint' tyvar)

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
    pprint' (Isa.Int i)      = integer i
    pprint' (Isa.String str) = doubleQuotes $ text str

instance Printer Isa.Term where
    pprint' (Isa.Var vname)         = pprint' vname
    pprint' (Isa.Literal lit)       = pprint' lit
    pprint' (Isa.Parenthesized t)   = parens $ pprint' t

    pprint' app @ (Isa.App t1 t2)   
        = case categorizeApp app of
            ListApp  l      -> pprintAsList l
            TupleApp l      -> pprintAsTuple l
            InfixApp x op y -> let x' = parensIf (isCompound x) $ pprint' x
                                   y' = parensIf (isCompound y) $ pprint' y
                               in  x' <+> pprint' op <+> y'
            MiscApp         -> pprint' t1 <+> parensIf (isCompound t2) (pprint' t2)

    pprint' (Isa.If t1 t2 t3)
        = fsep [text "if"   <+> pprint' t1,
                text "then" <+> pprint' t2,
                text "else" <+> pprint' t3]

    pprint' (Isa.Lambda vars body)
        = fsep [text "%" <+> hsep (map pprint' vars) <+> dot,
                nest 2 (pprint' body)]

    pprint' (Isa.RecConstr recordN updates)
        = pprint' recordN <+> (bananas . vcat . punctuate comma $ map pp updates)
          where pp (vname, typ) = pprint' vname <+> equals <+> pprint' typ

    pprint' (Isa.RecUpdate term updates)
        = pprint' term <+> (bananas . vcat . punctuate comma $ map pp updates)
          where pp (vname, typ) = pprint' vname <+> text ":=" <+> pprint' typ

    pprint' (Isa.Case term matchs)
         = hang (text "case" <+> pprint' term <+> text "of")
                2
                (vcat $ zipWith (<+>) (space : repeat (char '|'))
                                      (map pp matchs))
           where pp (pat, term) = (pprint' pat) <+> text "=>" <+> pprint' term

    pprint' (Isa.Let bindings body)
        = text "let" <+> fsep (map ppBinding bindings)
          $$ text "in" <+> pprint' body
          where ppBinding (pat, term)
                    = pprint' pat <+> equals <+> pprint' term


pprintAsList :: [Isa.Term] -> DocM P.Doc
pprintAsList = brackets . hsep . punctuate comma . map pprint'

pprintAsTuple :: [Isa.Term] -> DocM P.Doc
pprintAsTuple = parens . hsep . punctuate comma . map pprint'


data AppFlavor = ListApp [Isa.Term] 
               | TupleApp [Isa.Term] 
               | InfixApp Isa.Term Isa.Term Isa.Term 
               | MiscApp
  deriving (Show)

-- This makes use of pattern guards which are not Haskell98, but quite
-- portable across implementations nontheless.
--
-- Cf. http://www.haskell.org/ghc/docs/latest/html/users_guide/syntax-extns.html#pattern-guards
--
categorizeApp :: Isa.Term -> AppFlavor
categorizeApp app@(Isa.App (Isa.App (Isa.Var c) t1) t2) 
    | Isa.isCons c,    Just list <- flattenListApp app  = ListApp list
    | Isa.isPairCon c, Just list <- flattenTupleApp app = TupleApp list
    | isInfixOp c                                       = InfixApp t1 (Isa.Var c) t2
categorizeApp _                                         = MiscApp

flattenListApp :: Isa.Term -> Maybe [Isa.Term]
flattenListApp app = let list = unfoldr1 split app in 
                     case last list of -- proper list?
                       (Isa.Var c) | Isa.isNil c -> Just list
                       _ -> Nothing
  where
    split (Isa.App (Isa.App (Isa.Var c) x) xs) | Isa.isCons c = Just (x, xs)
    split _ = Nothing

flattenTupleApp :: Isa.Term -> Maybe [Isa.Term]
flattenTupleApp app = let list = unfoldr1 split app in
                      if (length list) > 1 then Just list
                                           else Nothing
  where
    split (Isa.App (Isa.App (Isa.Var c) x) xs) | Isa.isPairCon c = Just (x, xs)
    split _ = Nothing


isCompound :: Isa.Term -> Bool
isCompound (Isa.App (Isa.App (Isa.Var c) _) _)  -- FIXME: temporary to avoid the extra parens
    | Isa.isPairCon c = False                   --  in `((x,y)) : z'; should be handled by
isCompound t = case t of                        --  checking for infix priorities.
                Isa.Var _            -> False
                Isa.Literal _        -> False
                Isa.Parenthesized _  -> False
                _ -> True

isCompoundType :: Isa.Type -> Bool
isCompoundType t = case t of
                     Isa.TyVar _    -> False
                     Isa.TyCon _ [] -> False
                     _              -> True
                                      
isInfixOp name = Isa.isCons name -- FIXME