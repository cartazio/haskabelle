{-  ID:         $Id$
    Author:     Tobias C. Rittweiler and Florian Haftmann, TU Munich

Generic functions
-}

module Importer.General where

splitLast :: [a] -> ([a], a)
splitLast xs = (init xs, last xs)

combLeft :: (a -> b -> a) -> a -> [b] -> a
combLeft = foldl

combRight :: (a -> b -> b) -> [a] -> b -> b
combRight = flip . foldr

combRightImproper :: (a -> a -> a) -> [a] -> a
combRightImproper f xs = combRight f xs' x where (xs', x) = splitLast xs

destCombLeft :: (a -> Maybe (a, b)) -> a -> (a, [b])
destCombLeft f = dest [] where
  dest ys x = case f x of
    Nothing -> (x, ys)
    Just (x', y) -> dest (y : ys) x'

destCombRight :: (b -> Maybe (a, b)) -> b -> ([a], b)
destCombRight f y = case f y of
  Nothing -> ([], y)
  Just (x, y') -> (x : xs, y'') where (xs, y'') = destCombRight f y'

destCombRightImproper :: (a -> Maybe (a, a)) -> a -> [a]
destCombRightImproper f x = case f x of
  Nothing -> [x]
  Just (x1, x2) -> x1 : destCombRightImproper f x2
