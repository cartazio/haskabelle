
module Guards where

import Nats

foo n | not (less_nat n Zero_nat) = Suc (Zero_nat)
      | otherwise                 = Zero_nat

bar n | not (less_nat n ten)      = Suc (Suc (Zero_nat))
      | eq_nat n ten              = Suc (Zero_nat)
      | otherwise                 = Zero_nat
    where ten = (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero_nat))))))))))