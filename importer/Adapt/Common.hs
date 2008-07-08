{-  ID:         $Id$
    Author:     Tobias C. Rittweiler and Florian Haftmann, TU Muenchen

Basic data structures for adaption table.
-}

module Importer.Adapt.Common (OpKind(..), Assoc(..), AdaptionEntry(..),
                              primitive_tycon_table, primitive_datacon_table) where

import Language.Haskell.Exts

data OpKind = Variable | Function | Op Int | InfixOp Assoc Int | Type
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
