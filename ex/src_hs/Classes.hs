module Classes where

import Nats


{- some algebra -}

class Monoid a where
  nothing :: a
  plus :: a -> a -> a

instance Monoid Nat where
  nothing = Zero
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
pow_nat Zero _ = nothing
pow_nat (Suc n) x = plus x (pow_nat n x)

pow_int :: forall a. (Group a) => Integer -> a -> a; {-# HASKABELLE permissive pow_int #-}
pow_int k x =
  if k == 0 then nothing
  else if k < 0 then pow_int (- k) (inverse x)
  else plus x (pow_int (k - 1) x)


{- standard orderings -}

class Order a where
  less_eq :: a -> a -> Bool
  less :: a -> a -> Bool

instance Order Nat where
  less_eq = less_eq_nat
  less = less_nat

instance Order Integer where
  less_eq = (<=)
  less = (<)

instance (Order a, Order b) => Order (a, b) where
  less_eq (x, y) (w, z) = less x w || not (less w x) && less_eq y z
  less (x, y) (w, z) = less x w || not (less w x) && less y z

instance (Order a) => Order [a] where
  less_eq (x : xs) (y : ys) = less x y || not (less y x) && less_eq xs ys
  less_eq [] xs = True
  less_eq (x : xs) [] = False
  less (x : xs) (y : ys) = less x y || not (less y x) && less xs ys
  less xs [] = False
  less [] (x : xs) = True


data Linord = Less | Equal | Greater

class Eq a => Linorder a where
  linord :: a -> a -> Linord

instance Linorder Nat where
  linord Zero (Suc _) = Less
  linord Zero Zero = Equal
  linord (Suc _) Zero = Greater
  linord (Suc m) (Suc n) = linord m n

instance Linorder Integer where
  linord k l = if k < l then Less
    else if l < k then Greater else Equal

instance (Linorder a, Linorder b) => Linorder (a, b) where
  linord (x, y) (w, z) = case linord x w of
    Less -> Less
    Equal -> linord y z
    Greater -> Greater

instance (Linorder a) => Linorder [a] where
  linord [] [] = Equal
  linord xs [] = Greater
  linord [] ys = Less
  linord (x : xs) (y : ys) = case linord x y of
    Less -> Less
    Equal -> linord xs ys
    Greater -> Greater
