{-  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Precedence of infix operators.
-}

module Importer.Adapt.Precedence where

import Importer.Adapt.Common

precedences :: [(String, OpKind)]
precedences = [
  ("Prelude.(.)", InfixOp RightAssoc 9),
  ("Prelude.(&&)", InfixOp LeftAssoc 3),
  ("Prelude.(||)", InfixOp LeftAssoc 2),
  ("Prelude.(:)", InfixOp RightAssoc 5),
  ("Prelude.(++)", InfixOp RightAssoc 5),
  ("Prelude.(+)", InfixOp LeftAssoc 6),
  ("Prelude.(*)", InfixOp LeftAssoc 7),
  ("Prelude.(-)", InfixOp LeftAssoc 6)]
