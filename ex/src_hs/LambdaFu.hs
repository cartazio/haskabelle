
module LambdaFu where

-- Testing simple lambda expressions. LC-style pair encoding.

true  = \x y -> x
false = \x y -> y

pair   = \x y f -> f x y
first  = \p -> p true
second = \p -> p false
nil    = \x -> true
null   = \p -> p (\x y -> false) 


-- Testing lambda expressions with simple pattern matching:

maybe_numbers = [Just 1,Just 3,Just 5,Just 7]
numbers = map (\(Just i) -> i) maybe_numbers






