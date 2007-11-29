module Radix where

import Nat

radix :: (Nat -> a) -> Nat -> Nat -> [a]
radix ch _ Zero = [ch Zero]
radix ch r n = reverse (rad n) where
  rad Zero = []
  rad n = ch d : rad m where
    (m, d) = divmod n r

radix_10 = radix id (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))))
