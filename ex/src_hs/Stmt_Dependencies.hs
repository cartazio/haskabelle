module Stmt_Dependencies where


data Twin a b = Twin a b

dest_Twin :: Twin a b -> (a, b)
dest_Twin (Twin x y) = (x, y)

f :: a -> (a, a)
f x = dest_Twin (g x)

g :: a -> Twin a a
g x = Twin (h x) (h x)

h :: a -> a
h x = x

{-double :: a -> Twin a a
double x = Twin x x-}

k :: (a, b) -> (a, b)
k (x, y) = dest_Twin (Twin x y)
