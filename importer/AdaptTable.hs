{-  ID:         $Id$
    Author:     Tobias C. Rittweiler and Florian Haftmann, TU Muenchen

Basic data structures for adaption table.
-}

module Importer.AdaptTable (OpKind(..), Assoc(..), AdaptionEntry(..)) where

import qualified Importer.LexEnv as Env

data OpKind = Variable | Function | Op Int | InfixOp Assoc Int | Type
  deriving Show

data Assoc = RightAssoc | LeftAssoc | NoneAssoc
  deriving Show

data AdaptionEntry = Haskell String OpKind
                   | Isabelle String OpKind
  deriving Show
