module Classes where

import Nats


{- some algebra -}

class Monoid a where
  nothing :: a
  plus :: a -> a -> a

instance Monoid Nat where
  nothing = Zero_nat
  plus = plus_nat

instance Monoid Integer where
  nothing = 0
  plus = (+)

summ :: forall a. (Monoid a) => [a] -> a
summ [] = nothing
summ (x : xs) = plus x (summ xs)

class (Monoid a) => Group a where
  inverse :: a -> a

instance Group Integer where
  inverse = negate

sub :: forall a. (Group a) => a -> a -> a
sub a b = plus a (inverse b)

pow_nat :: forall a. (Monoid a) => Nat -> a -> a
pow_nat Zero_nat _ = nothing
pow_nat (Suc n) x = plus x (pow_nat n x)

pow_int :: forall a. (Group a) => Integer -> a -> a; {-# HASKABELLE permissive pow_int #-}
pow_int k x =
  if k == 0 then nothing
  else if k < 0 then pow_int (- k) (inverse x)
  else plus x (pow_int (k - 1) x)


{- standard orderings -}

class (Eq a) => Order a where
  less_eq :: a -> a -> Bool
  less :: a -> a -> Bool

instance Order Nat where
  less_eq = less_eq_nat
  less = less_nat

instance Order Integer where
  less_eq = (<=)
  less = (<)

{-instance (Order a) => Order [a] where
  less_eq (x : xs) (y : ys) = less x y || x == y && less_eq xs ys
  less_eq [] xs = True
  less_eq (x : xs) [] = False
  less xs ys = less_eq xs ys && not (xs == ys)

instance (Order a, Order b) => Order (a, b) where
  less_eq (x, y) (w, z) = less x w || x == w && less_eq y z
  less p q = less_eq p q && not (p == q)-}
