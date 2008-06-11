module Radix where

import Nats

divmod :: Nat -> Nat -> (Nat, Nat)
divmod m n = if eq_nat n Zero_nat || less_nat m n then (Zero_nat, m)
    else let (q, r) = divmod (minus_nat m n) n
         in (Suc q, r)

radix :: (Nat -> a) -> Nat -> Nat -> [a]
radix ch _ Zero_nat = [ch Zero_nat]
radix ch r n = reverse (rad n) where
  rad Zero_nat = []
  rad n = ch d : rad m where
    (m, d) = divmod n r

radix_10 :: Nat -> [Nat]
radix_10 = radix id (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero_nat))))))))))
