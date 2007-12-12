module Integers where

fibs :: Integer -> [Integer] -> [Integer]
fibs k xs = if k <= 0 then reverse xs
  else fibs (k - 1) ys' where
    ys' = case xs of
      (x : y : _) -> x + y : xs
      _ -> 1 : xs
