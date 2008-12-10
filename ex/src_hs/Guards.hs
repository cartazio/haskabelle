module Guards where

import Nats

foo n | not (less_nat n Zero_nat) = Suc (Zero_nat)
      | otherwise                 = Zero_nat

bar n | not (less_nat n ten)      = Suc (Suc (Zero_nat))
      | eq_nat n ten              = Suc (Zero_nat)
      | otherwise                 = Zero_nat
    where ten = (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero_nat))))))))))

zero  = Zero_nat
one   = Suc (Zero_nat)
two   = Suc (Suc (Zero_nat))
three = Suc (Suc (Suc (Zero_nat)))

quux n | eq_nat n three       = zero
       | less_nat n three     = one
       | greater_nat n three  = two

foomb mb = case mb of
             Nothing -> zero
             Just n
                 | eq_nat n three       -> zero
                 | less_nat n three     -> one
                 | greater_nat n three  -> two

fallthrough n = case n of
                  n | eq_nat n (Suc Zero_nat) -> zero
                  Zero_nat -> one
                  _ -> two
                       