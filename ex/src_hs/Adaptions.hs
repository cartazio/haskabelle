-- some rather fundamental adaptions

module Adaptions where

implies :: Bool -> Bool -> Bool
implies False _ = True
implies True True = True
implies True False = False

nand :: Bool -> Bool -> Bool
nand p q = not (p && q)

nor :: Bool -> Bool -> Bool
nor p q = not (p || q)

append :: [a] -> [a] -> [a]
append [] ys = ys
append xs [] = xs
append (x:xs) ys = x : append xs ys

rev :: [a] -> [a]
rev [] = []
rev (x:xs) = append (rev xs) [x]

who_am_i_smile :: (a -> b) -> Maybe a -> Maybe b
who_am_i_smile f Nothing = Nothing
who_am_i_smile f (Just x) = Just (f x)
