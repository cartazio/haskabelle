
module ClassAdaptions where

data Nat = Succ Nat | Zero deriving Show;

instance Eq Nat where
  Zero == Zero = True
  (Succ m) == (Succ n) = m == n
  Zero == (Succ n) = False
  (Succ m) == Zero = False

class (Eq a) => Ident a where
  ident :: a -> a -> Bool

fromEq :: (Eq a) => a -> a -> b -> Maybe b
fromEq a1 a2 b = if a1 == a2 then Just b else Nothing

fromIdent :: (Ident a) => a -> a -> b -> Maybe b
fromIdent a1 a2 b = if ident a1 a2 then Just b else Nothing
