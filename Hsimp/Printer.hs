
module Hsimp.Printer where

import qualified Hsimp.IsaSyntax as Isa

import Control.Exception (assert)
import Debug.Trace (trace)

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

semi,comma,colon,space,equals,dot,apostroph :: Doc
semi   = return P.semi
comma  = return P.comma
colon  = return P.colon
space  = return P.space
equals = return P.equals

dot       = char '.'
apostroph = char '\''

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

comment :: String -> Doc
comment str    = text "(*" <+> (vcat $ map text (lines str)) <+> text "*)"


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
          text "imports Main"          $$
          text "begin"                 $$
          (vcat $ map pprint' cmds)

    pprint' (Isa.DatatypeCmd tyspec dataspecs)
        = blankline $
          text "datatype" <+> pprint' tyspec 
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
            (pattern, term) 
                -> blankline $
                   text "definition" <+> pprint' vname <+> text "::" <+> pprint' tysig $$
                   text "where" $$
                   space <+> (maybeWithinHOL $ 
                                hsep (map pprint' pattern) <+> equals <+> pprint' term)

    pprint' (Isa.FunCmd vname tysig matchs)
        = blankline $ 
          text "fun" <+> pprint' vname <+> text "::" <+> pprint' tysig $$
          text "where" $$
          vcat (zipWith (<+>) (space : repeat (char '|')) 
                              (map pp matchs))
          where pp (pattern, term) = maybeWithinHOL $ 
                                       hsep (map pprint' pattern) <+> equals <+> pprint' term
  

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
    pprint' (Isa.QName thy str) = pprint' thy <> dot <> text str

instance Printer Isa.Type where
    pprint' (Isa.TyVar vname) = apostroph <> pprint' vname

    pprint' (Isa.TyCon cname []) = pprint' cname 
    pprint' (Isa.TyCon cname tyvars) 
        = maybeWithinHOL $
            hsep (map pprint' tyvars) <+> pprint' cname

    pprint' (Isa.TyFun t1 t2) 
        = maybeWithinHOL $
              case t1 of Isa.TyFun _ _ -> parens (pprint' t1) <+> text "=>" <+> pprint' t2
                         _             -> pprint' t1          <+> text "=>" <+> pprint' t2

instance Printer Isa.TypeSig where
    pprint' (Isa.TypeSig _name typ) = pprint' typ 

instance Printer Isa.Term where
    pprint' (Isa.Var vname)         = pprint' vname
    pprint' (Isa.Con cname)         = pprint' cname
    pprint' (Isa.Literal lit)       = pprint' lit
    pprint' (Isa.Parenthesized t)   = parens $ pprint' t
    pprint' (Isa.App t1 t2)         = pprint' t1 <+> pprint' t2
    pprint' (Isa.InfixApp t1 op t2) = pprint' t1 <+> pprint' op <+> pprint' t2
    pprint' (Isa.If t1 t2 t3)       = fsep [text "if",   pprint' t1,
                                           text "then", pprint' t2,
                                           text "else", pprint' t3]
    pprint' (Isa.Lambda vars body)  = fsep [text "%" <> hsep (map pprint' vars) <+> dot, pprint' body]

    pprint' (Isa.RecConstr recordN updates)
        = pprint' recordN <+> (bananas . vcat . punctuate comma $ map pp updates)
          where pp (vname, typ) = pprint' vname <+> equals <+> pprint' typ

    pprint' (Isa.RecUpdate term updates)
        = pprint' term <+> (bananas . vcat . punctuate comma $ map pp updates)
          where pp (vname, typ) = pprint' vname <+> text ":=" <+> pprint' typ

instance Printer Isa.Literal where
    pprint' (Isa.Int i)      = integer i
    pprint' (Isa.String str) = doubleQuotes $ text str

