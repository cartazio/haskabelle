module Strings where

import Nats

digit10 :: Nat -> Char
digit10 Zero = '0'
digit10 (Suc Zero) = '1'
digit10 (Suc (Suc Zero)) = '2'
digit10 (Suc (Suc (Suc Zero))) = '3'
digit10 (Suc (Suc (Suc (Suc Zero)))) = '4'
digit10 (Suc (Suc (Suc (Suc (Suc Zero))))) = '5'
digit10 (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))) = '6'
digit10 (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))) = '7'
digit10 (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))))) = '8'
digit10 (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))))) = '9'

{- radix_digit10 :: Nat -> String
radix_digit10 = radix digit10
  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))))))) -}
