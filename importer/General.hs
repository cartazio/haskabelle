{-  ID:         $Id$
    Author:     Tobias C. Rittweiler and Florian Haftmann, TU Munich

Generic functions
-}

module Importer.General where

-- FIXME: perhaps names should follow Haskell conventions: splitLast, combLeft etc.

split_last :: [a] -> ([a], a)
split_last xs = (init xs, last xs)

comb_left :: (a -> b -> a) -> a -> [b] -> a
comb_left = foldl

comb_right :: (a -> b -> b) -> [a] -> b -> b
comb_right = flip . foldr

comb_right_improper :: (a -> a -> a) -> [a] -> a
comb_right_improper f xs = comb_right f xs' x where (xs', x) = split_last xs

dest_comb_left :: (a -> Maybe (a, b)) -> a -> (a, [b])
dest_comb_left f = dest [] where
  dest ys x = case f x of
    Nothing -> (x, ys)
    Just (x', y) -> dest (y : ys) x'

dest_comb_right :: (b -> Maybe (a, b)) -> b -> ([a], b)
dest_comb_right f y = case f y of
  Nothing -> ([], y)
  Just (x, y') -> (x : xs, y'') where (xs, y'') = dest_comb_right f y'

dest_comb_right_improper :: (a -> Maybe (a, a)) -> a -> [a]
dest_comb_right_improper f x = case f x of
  Nothing -> [x]
  Just (x1, x2) -> x1 : dest_comb_right_improper f x2
