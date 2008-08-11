
module ListComprehensions where

list = [1, 2, 3, 4, 5]

dot_product f l1 l2 = [ f x y | x <- l1, y <- l2 ]

list2 = dot_product (+) list list