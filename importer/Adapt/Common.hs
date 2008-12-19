{-  Author: Tobias C. Rittweiler and Florian Haftmann, TU Muenchen

Basic data structures for adaption table.
-}

module Importer.Adapt.Common (OpKind(..), RawClassInfo(..), Assoc(..), AdaptionEntry(..),
                              primitive_tycon_table, primitive_datacon_table,
                              hsk_infix_ops) where

import qualified Language.Haskell.Exts as Hs

data RawClassInfo = RawClassInfo 
    { superclasses :: [String],
      methods      :: [(String, String)],
      classVar     :: String
    }
  deriving (Eq, Show)

data OpKind = Type 
            | Variable 
            | Function
            | RawHskOp          -- placeholder
            | UnaryOp Int 
            | InfixOp Assoc Int
            | Class RawClassInfo
  deriving (Eq, Show)

data Assoc = RightAssoc | LeftAssoc | NoneAssoc
  deriving (Eq, Show)

data AdaptionEntry = Haskell String OpKind
                   | Isabelle String OpKind
  deriving (Eq, Show)


primitive_tycon_table, primitive_datacon_table :: [(Hs.SpecialCon, Hs.QName)]

primitive_tycon_table 
    = [(Hs.ListCon,    Hs.Qual (Hs.ModuleName "Prelude") (Hs.Ident "ListTyCon")),
       (Hs.UnitCon,    Hs.Qual (Hs.ModuleName "Prelude") (Hs.Ident "UnitTyCon")),
       (Hs.TupleCon 2, Hs.Qual (Hs.ModuleName "Prelude") (Hs.Ident "PairTyCon"))
      ]

primitive_datacon_table 
    = [(Hs.Cons,       Hs.Qual (Hs.ModuleName "Prelude") (Hs.Ident ":")),
       (Hs.ListCon,    Hs.Qual (Hs.ModuleName "Prelude") (Hs.Ident "[]")),
       (Hs.UnitCon,    Hs.Qual (Hs.ModuleName "Prelude") (Hs.Ident "()")),
       (Hs.TupleCon 2, Hs.Qual (Hs.ModuleName "Prelude") (Hs.Ident "PairDataCon"))
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
  ("Prelude.(-)",  InfixOp LeftAssoc 6),
  ("Prelude.(==)", InfixOp NoneAssoc 4),
  ("Prelude.(<=)", InfixOp NoneAssoc 4),
  ("Prelude.(>=)", InfixOp NoneAssoc 4),
  ("Prelude.(<)",  InfixOp NoneAssoc 4),
  ("Prelude.(>)",  InfixOp NoneAssoc 4),
  ("Prelude.(!!)", InfixOp LeftAssoc 9)
  ]
