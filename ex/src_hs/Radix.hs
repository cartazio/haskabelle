module Radix where

import Nats

divmod :: Nat -> Nat -> (Nat, Nat) ; {-# HASKABELLE permissive divmod #-}
divmod m n = if eq_nat n Zero_nat || less_nat m n then (Zero_nat, m)
    else let (q, r) = divmod (minus_nat m n) n
         in (Suc q, r)

radix :: (Nat -> a) -> Nat -> Nat -> [a] ; {-# HASKABELLE permissive radix rad0 #-}
radix ch _ Zero_nat = [ch Zero_nat]
radix ch r n = reverse (rad ch r n) where
  rad _ _ Zero_nat = []
  rad ch r n       = let (m, d) = divmod n r in ch d : rad ch r m 

radix_10 :: Nat -> [Nat]
radix_10 = radix id (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero_nat))))))))))
