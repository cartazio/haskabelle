module Integers where

fibs :: Integer -> [Integer] -> [Integer]
fibs k xs 
    = if k <= 0 then reverse xs
                else fibs (k - 1) ys' 
      where ys' = case xs of
                    (x : y : _) -> x + y : xs
                    _ -> 1 : xs

-- Same as above, but using pattern guards.

-- fibs2 :: Integer -> [Integer] -> [Integer]
-- fibs2 k xs | k <= 0 = reverse xs
--            | True   = fibs (k - 1) ys'
--            where ys' = case xs of
--                          (x : y : _) -> x + y : xs
--                          _ -> 1 : xs
