
module Hsimp.Printer where

import qualified Hsimp.IsaSyntax as Isa

import Control.Exception (assert)
import Text.PrettyPrint

accentuate :: Doc -> [Doc] -> [Doc]
accentuate d list = map (d<>) list 

dot, apostroph :: Doc
dot       = char '.'
apostroph = char '\''

withinHOL = doubleQuotes

comment str = text "(*" <+> (vcat $ map text (lines str)) <+> text "*)"

blankline doc = space $$ doc

indent = 3

--is :: a -> b -> Boolean

class Printer a where
    pprint :: a -> Doc

instance Printer Isa.Cmd where
    pprint (Isa.Comment string) = empty -- blankline $ comment string
    pprint (Isa.Block cmds)     = blankline $ vcat $ map pprint cmds
    pprint (Isa.TheoryCmd thy cmds)
        = text "theory" <+> pprint thy $$
          text "imports Main"          $$
          text "begin"                 $$
          (vcat $ map pprint cmds)

    pprint (Isa.DatatypeCmd tyspec dataspecs)
        = blankline $
          text "datatype" <+> pprint tyspec 
          <+> vcat (zipWith (<+>) (equals : repeat (char '|'))
                                  (map pp dataspecs))
          where pp (con, types) = hsep $ pprint con : map pprint types

    pprint (Isa.DefinitionCmd vname tysig match)
        = let (pattern, term) = match 
          in blankline $
             text "definition" <+> pprint vname <+> text "::" <+> pprint tysig $$
             text "where" $$
             space <+> hsep (map pprint pattern) <+> equals <+> pprint term

    pprint (Isa.FunCmd vname tysig matchs)
        = blankline $ 
          text "fun" <+> pprint vname <+> text "::" <+> pprint tysig $$
          text "where" $$
          vcat (zipWith (<+>) (space : repeat (char '|')) 
                                           (map pp matchs))
          where pp (pattern, term) = hsep (map pprint pattern) <+> equals <+> pprint term
  

instance Printer Isa.Theory where
    pprint (Isa.Theory name) = text name

instance Printer Isa.TypeSpec where
    pprint (Isa.TypeSpec tyvars tycon)
        = let tyvars' = parens . hsep . punctuate comma . accentuate apostroph $ map pprint tyvars
          in tyvars' <+> pprint tycon

instance Printer Isa.Name where
    pprint (Isa.Name str) = text str
    pprint (Isa.QName thy str) = pprint thy <> dot <> text str

instance Printer Isa.Type where
    pprint (Isa.TyVar vname) = apostroph <> pprint vname

    pprint (Isa.TyCon cname tyvars) 
        = hsep (map pprint tyvars) <+> pprint cname

    pprint (Isa.TyFun t1 t2) 
        = case t1 of Isa.TyFun _ _ -> parens (pprint t1) <+> text "=>" <+> pprint t2
                     _             -> pprint t1          <+> text "=>" <+> pprint t2

instance Printer Isa.TypeSig where
    pprint (Isa.TypeSig _name typ) = pprint typ 

instance Printer Isa.Term where
    pprint (Isa.Var vname)         = pprint vname
    pprint (Isa.Con cname)         = pprint cname
    pprint (Isa.Literal lit)       = pprint lit
    pprint (Isa.Parenthesized t)   = parens $ pprint t
    pprint (Isa.App t1 t2)         = pprint t1 <+> pprint t2
    pprint (Isa.InfixApp t1 op t2) = pprint t1 <+> pprint op <+> pprint t2
    pprint (Isa.If t1 t2 t3)       = fsep [text "if",   pprint t1,
                                           text "then", pprint t2,
                                           text "else", pprint t3]


instance Printer Isa.Literal where
    pprint (Isa.Int i) = integer i