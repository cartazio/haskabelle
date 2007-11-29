module Radix where

import Nat

radix :: (Nat -> Char) -> Nat -> Nat -> String
radix ch _ Zero = [ch Zero]
radix ch r n = reverse (rad n) where
  rad n = ch d : rad m
  (m, d) = divmod n r

radix_10 :: Nat -> String
radix_10 = radix (\n -> toEnum (num n + 48))
  (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))))
