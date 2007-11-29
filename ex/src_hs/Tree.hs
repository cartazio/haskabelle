module Simple where

import Nat

data Tree a = Tip a | Branch (Tree a) (Tree a)

size :: Tree a -> Nat
size (Tip a) = Succ Zero
size (Branch x y) = plus (size x) (size y)

insert :: a -> Tree a -> Tree a
insert x (Tip y) = Branch (Tip x) (Tip y)
insert x (Branch y z) = if less_eq (size y) (size z)
  then Branch (insert x y) z
  else Branch y (insert x z)

