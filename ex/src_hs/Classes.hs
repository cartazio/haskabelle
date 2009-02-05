module Classes where

import Nats

class Monoid a where
    nothing :: a
    plus :: a -> a -> a


instance Monoid Integer where
  nothing = 0
  plus    = (+)

-- prevent name clash with Prelude.sum
summ :: (Monoid a) => [a] -> a
summ [] = nothing
summ (x:xs) = plus x (summ xs)

class (Monoid a) => Group a where
    inverse :: a -> a

instance Group Integer where
    inverse = negate

sub :: (Group a) => a -> a -> a
sub a b = plus a (inverse b)

-- pow :: (Group a) => Integer -> a -> a
-- pow 0 _ = nothing
-- pow k x = if k < 0 then pow (- k) (inverse x)
--           else plus x (pow (k - 1) x)
