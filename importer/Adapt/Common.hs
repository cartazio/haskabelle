{-  ID:         $Id$
    Author:     Tobias C. Rittweiler and Florian Haftmann, TU Muenchen

Basic data structures for adaption table.
-}

module Importer.Adapt.Common (OpKind(..), Assoc(..), AdaptionEntry(..),
                              primitive_tycon_table, primitive_datacon_table,
                              hsk_infix_ops) where

import Language.Haskell.Exts

data OpKind = Type 
            | Variable 
            | Function 
            | RawHskOp 
            | UnaryOp Int 
            | InfixOp Assoc Int
  deriving Show

data Assoc = RightAssoc | LeftAssoc | NoneAssoc
  deriving Show

data AdaptionEntry = Haskell String OpKind
                   | Isabelle String OpKind
  deriving Show


primitive_tycon_table, primitive_datacon_table :: [(HsSpecialCon, HsQName)]

primitive_tycon_table 
    = [(HsListCon,    Qual (Module "Prelude") (HsIdent "ListTyCon")),
       (HsTupleCon 2, Qual (Module "Prelude") (HsIdent "PairTyCon"))
      ]

primitive_datacon_table 
    = [(HsCons,       Qual (Module "Prelude") (HsIdent ":")),
       (HsListCon,    Qual (Module "Prelude") (HsIdent "[]")),
       (HsTupleCon 2, Qual (Module "Prelude") (HsIdent "PairDataCon"))
      ]

hsk_infix_ops :: [(String, OpKind)]
hsk_infix_ops = [
  ("Prelude.(.)",  InfixOp RightAssoc 9),
  ("Prelude.(&&)", InfixOp LeftAssoc 3),
  ("Prelude.(||)", InfixOp LeftAssoc 2),
  ("Prelude.(:)",  InfixOp RightAssoc 5),
  ("Prelude.(++)", InfixOp RightAssoc 5),
  ("Prelude.(+)",  InfixOp LeftAssoc 6),
  ("Prelude.(*)",  InfixOp LeftAssoc 7),
  ("Prelude.(-)",  InfixOp LeftAssoc 6)]
