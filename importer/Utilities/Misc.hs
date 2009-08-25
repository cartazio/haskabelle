{-| Author: Tobias C. Rittweiler and Florian Haftmann, TU Muenchen

Generic functions.
-}

module Importer.Utilities.Misc (
  assert, tracing,
  (|>), (*>),
  pair, rpair, map_both,
  fold, map_filter, flat, maps, nth_map, map_index, fold_index, map2, fold2, map_split, insert, remove,
  accumulate, has_duplicates, burrow_indices,
  unfoldr, unfoldr1, unfoldl, unfoldl1,
  liftM, mapsM,
  groupAlist, wordsBy
) where

import qualified List
import qualified Maybe
import Monad (liftM)
import Control.Exception (assert)
import Debug.Trace (trace)


{- diagnostics -}

tracing :: (a -> String) -> a -> a
tracing f x = trace (f x) x


{- functions -}

infixl 1 |>
x |> f = f x

infixl 1 *>
f *> g = g . f


{- pairs -}

rpair :: b -> a -> (a, b)
rpair y x = (x, y)

pair :: a -> b -> (a, b)
pair x y = (x, y)

map_both :: (a -> b) -> (a, a) -> (b, b)
map_both f (x, y) = (f x, f y)


{- lists -}

fold :: (a -> b -> b) -> [a] -> b -> b
fold f [] y = y
fold f (x:xs) y = fold f xs (f x y)

map_filter :: (a -> Maybe b) -> [a] -> [b]
map_filter = Maybe.mapMaybe

flat :: [[a]] -> [a]
flat = List.concat

maps :: (a -> [b]) -> [a] -> [b]
maps = List.concatMap

index_to_large :: a
index_to_large = [] !! 0

nth_map :: Int -> (a -> a) -> [a] -> [a]
nth_map 0 f (x : xs) = f x : xs
nth_map n f (x : xs) = x : nth_map (n - 1) f xs
nth_map _ _ [] = index_to_large

map_index :: ((Int, a) -> b) -> [a] -> [b]
map_index f = mapp 0 where
  mapp _ [] = []
  mapp i (x : xs) = f (i, x) : mapp (i + 1) xs

fold_index :: ((Int, a) -> b -> b) -> [a] -> b -> b
fold_index f = foldd 0 where
  foldd _ [] y = y
  foldd i (x : xs) y = foldd (i + 1) xs (f (i, x) y)

unequal_lengths :: a
unequal_lengths = error "UnequalLengths"

map2 :: (a -> b -> c) -> [a] -> [b] -> [c]
map2 f [] [] = []
map2 f (x : xs) (y : ys) = f x y : map2 f xs ys
map2 _ _ _ = unequal_lengths;

fold2 :: (a -> b -> c -> c) -> [a] -> [b] -> c -> c
fold2 f [] [] z = z
fold2 f (x : xs) (y : ys) z = fold2 f xs ys (f x y z)
fold2 f _ _ _ = unequal_lengths;

map_split :: (a -> (b, c)) -> [a] -> ([b], [c])
map_split f [] = ([], [])
map_split f (x : xs) =
  let
    (y, w) = f x
    (ys, ws) = map_split f xs
  in (y : ys, w : ws)

insert :: Eq a => a -> [a] -> [a]
insert x xs = if x `elem` xs then xs else x : xs

remove :: Eq a => a -> [a] -> [a]
remove = List.delete

accumulate :: (a -> [b] -> [b]) -> a -> [b]
accumulate f x = f x []

has_duplicates :: Eq a => [a] -> Bool
has_duplicates = dups where
  dups [] = False
  dups (x : xs) = x `elem` xs || dups xs

burrow_indices :: [Int] -> ([a] -> [a]) -> [a] -> [a]
burrow_indices is f xs =
  let
    ys = f (map ((!!) xs) is)
  in if length xs /= length ys then unequal_lengths
  else fold (\i -> nth_map i (\_ -> ys !! i)) is xs


{- structural operations -}

unfoldr, unfoldl    :: (b -> Maybe (a, b)) -> b -> [a]
unfoldr1, unfoldl1  :: (a -> Maybe (a, a)) -> a -> [a]

unfoldr f x = List.unfoldr f x

unfoldl f x = aux [] f x
    where aux acc f x = case f x of
                Nothing     -> []
                Just (z, x') -> aux (z:acc) f x'

unfoldr1 f x 
    = case f x of Nothing -> [x]
                  Just (z, x') -> z : unfoldr1 f x'

unfoldl1 f x = aux [] f x
    where aux acc f x = case f x of
                          Nothing -> x:acc
                          Just (z, x') -> aux (z:acc) f x'


{- monads -}

mapsM :: Monad m => (a -> m [b]) -> [a] -> m [b]
mapsM f [] = return []
mapsM f (x : xs) = do
  ys <- f x
  zs <- mapsM f xs
  return (ys ++ zs)


{- misc -}

groupAlist :: Eq a => [(a, b)] -> [(a, [b])]
groupAlist xs = map (\k -> (k, [ l | (k', l) <- xs, k' == k ]))
                  $ List.nub (map fst xs)

wordsBy            :: (a -> Bool) -> [a] -> [[a]]
wordsBy pred l     =  case dropWhile pred l of
                      [] -> []
                      l' -> w : wordsBy pred l''
                            where (w, l'') = break pred l'
