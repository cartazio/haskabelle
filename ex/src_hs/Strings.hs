module Strings where

import Radix
import Nats

digit10 :: Nat -> Char
digit10 Zero = '0'
digit10 (Succ Zero) = '1'
digit10 (Succ (Succ Zero)) = '2'
digit10 (Succ (Succ (Succ Zero))) = '3'
digit10 (Succ (Succ (Succ (Succ Zero)))) = '4'
digit10 (Succ (Succ (Succ (Succ (Succ Zero))))) = '5'
digit10 (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))) = '6'
digit10 (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))) = '7'
digit10 (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))) = '8'
digit10 (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))) = '9'

radix_digit10 :: Nat -> String
radix_digit10 = radix digit10
  (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))))
