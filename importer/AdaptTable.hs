{-  ID:         $Id$
    Author:     Tobias C. Rittweiler and Florian Haftmann, TU Muenchen

Basic data structures for adaption table.
-}

module Importer.AdaptTable (OpKind(..), Assoc(..), AdaptionEntry(..)) where

import qualified Importer.LexEnv as Env

data OpKind = Variable | Function | InfixOp Assoc Int 
            | Data [Constructor]
  deriving Show

data Assoc = RightAssoc | LeftAssoc | NoneAssoc
  deriving Show

data AdaptionEntry = Haskell String OpKind String
                   | Isabelle String OpKind String
  deriving Show
