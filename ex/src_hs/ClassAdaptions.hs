
module ClassAdaptions where

data Nat = Suc Nat | Zero_nat deriving Show;

instance Eq Nat where
  (==) Zero_nat Zero_nat = True
  (==) (Suc m) (Suc n)   = m == n
  (==) Zero_nat (Suc a)  = False
  (==) (Suc a) Zero_nat  = False


class (Eq a) => Neq a where
    neq :: a -> a -> Bool

fromEq :: (Eq a) => a -> a -> b -> Maybe b
fromEq a1 a2 b = if a1 == a2 then Just b else Nothing

fromNeq :: (Neq a) => a -> a -> b -> Maybe b
fromNeq a1 a2 b = if neq a1 a2 then Just b else Nothing
