
module ListComprehensions where

list = [1, 2, 3, 4, 5]

dot_product f l1 l2 = [ f x y | x <- l1, y <- l2 ]

list2 = dot_product (+) list list

list3 = [ x*x | x <- list, x == 1 || x == 2 ]

-- list4 = [ if (x == 1) then "eins" else "zwei" | x <- list, x == 1 || x == 2 ]