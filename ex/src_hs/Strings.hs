module Strings where

import Radix
import Nats

digit10 :: Nat -> Char
digit10 Zero_nat = '0'
digit10 (Suc Zero_nat) = '1'
digit10 (Suc (Suc Zero_nat)) = '2'
digit10 (Suc (Suc (Suc Zero_nat))) = '3'
digit10 (Suc (Suc (Suc (Suc Zero_nat)))) = '4'
digit10 (Suc (Suc (Suc (Suc (Suc Zero_nat))))) = '5'
digit10 (Suc (Suc (Suc (Suc (Suc (Suc Zero_nat)))))) = '6'
digit10 (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero_nat))))))) = '7'
digit10 (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero_nat)))))))) = '8'
digit10 (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero_nat))))))))) = '9'

radix_digit10 :: Nat -> String
radix_digit10 = radix digit10
  (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero_nat))))))))))
