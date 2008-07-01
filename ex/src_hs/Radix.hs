module Radix where

import Nats

divmod :: Nat -> Nat -> (Nat, Nat)
divmod m n = if eq_nat n Zero_nat || less_nat m n then (Zero_nat, m)
    else let (q, r) = divmod (minus_nat m n) n
         in (Suc q, r)

radix :: (Nat -> a) -> Nat -> Nat -> [a]
radix ch _ Zero_nat = [ch Zero_nat]
radix ch r n = reverse (rad ch r n) where
  rad _ _ Zero_nat = []
  rad ch r n       = let (m, d) = divmod n r in ch d : rad ch r m 

radix_10 :: Nat -> [Nat]
radix_10 = radix id (toNat 10)

-- toNat :: Int -> Nat
-- toNat 0 = Zero_nat
-- toNat n = Suc (toNat (n-1))

-- fromNat :: Nat -> Int
-- fromNat Zero_nat = 0
-- fromNat (Suc n) = 1 + fromNat n

-- divmod' :: Int -> Int -> (Int, Int)
-- divmod' m n = let (q,r) = divmod (toNat m) (toNat n)
--               in (fromNat q, fromNat r)