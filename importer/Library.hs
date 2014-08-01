{-| Author: Tobias C. Rittweiler and Florian Haftmann, TU Muenchen

A collection of generic functions.
-}

module Importer.Library (
  assert, asserting, tracing,
  (|>), (*>),
  pair, rpair, map_fst, map_snd, map_both, map_pair,
  the, these, the_default,
  split_list,
  filter_out, fold, fold_rev, map_filter, flat, maps,
  map2, fold2, map_split,
  nth_map, map_index, fold_index, burrow_indices,
  insert, remove, has_duplicates, accumulate, 
  separate, slice,
  perhaps, perhaps_map, ultimately,
  combl, combr, uncombl, uncombr,
  liftM, filterM, mapsM, when,
  catchIO
) where

import qualified Data.List as List
import qualified Data.Maybe as Maybe
import qualified Control.Monad as Monad
import qualified Control.Exception as Exception
import qualified Debug.Trace as Debug


{- diagnostics -}

trace :: String -> a -> a
trace = Debug.trace

assert :: Bool -> a -> a
assert = Exception.assert

tracing :: (a -> String) -> a -> a
tracing f x = trace (f x) x

asserting :: (a -> Bool) -> a -> a
asserting f x = assert (f x) x


{- functions -}

infixl 1 |>
x |> f = f x

infixl 1 *>
f *> g = g . f


{- pairs -}

pair :: a -> b -> (a, b)
pair x y = (x, y)

rpair :: b -> a -> (a, b)
rpair y x = (x, y)

map_fst :: (a -> b) -> (a, c) -> (b, c)
map_fst f (x, y) = (f x, y)

map_snd :: (a -> b) -> (c, a) -> (c, b)
map_snd f (x, y) = (x, f y)

map_both :: (a -> b) -> (a, a) -> (b, b)
map_both f (x, y) = (f x, f y)

map_pair :: (a -> b) -> (c -> d) -> (a, c) -> (b, d)
map_pair f g (x, y) = (f x, g y)


{- options -}

the :: Maybe a -> a
the = Maybe.fromJust

these :: Maybe [a] -> [a]
these Nothing = []
these (Just xs) = xs

the_default :: a -> Maybe a -> a
the_default = Maybe.fromMaybe


{- lists -}

split_list :: [a] -> Maybe (a, [a])
split_list [] = Nothing
split_list (x : xs) = Just (x, xs)

filter_out :: (a -> Bool) -> [a] -> [a]
filter_out f = filter (not . f)

fold :: (a -> b -> b) -> [a] -> b -> b
fold f [] y = y
fold f (x : xs) y = fold f xs (f x y)

fold_rev :: (a -> b -> b) -> [a] -> b -> b
fold_rev _ [] y = y
fold_rev f (x : xs) y = f x (fold_rev f xs y)

map_filter :: (a -> Maybe b) -> [a] -> [b]
map_filter = Maybe.mapMaybe

flat :: [[a]] -> [a]
flat = List.concat

maps :: (a -> [b]) -> [a] -> [b]
maps = List.concatMap


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


index_too_large :: a
index_too_large = [] !! 0

nth_map :: Int -> (a -> a) -> [a] -> [a]
nth_map 0 f (x : xs) = f x : xs
nth_map n f (x : xs) = x : nth_map (n - 1) f xs
nth_map _ _ [] = index_too_large

map_index :: ((Int, a) -> b) -> [a] -> [b]
map_index f = mapp 0 where
  mapp _ [] = []
  mapp i (x : xs) = f (i, x) : mapp (i + 1) xs

fold_index :: ((Int, a) -> b -> b) -> [a] -> b -> b
fold_index f = foldd 0 where
  foldd _ [] y = y
  foldd i (x : xs) y = foldd (i + 1) xs (f (i, x) y)

burrow_indices :: [Int] -> ([a] -> [a]) -> [a] -> [a]
burrow_indices is f xs =
  let
    ys = f (map ((!!) xs) is)
  in if length xs /= length ys then unequal_lengths
  else fold (\i -> nth_map i (\_ -> ys !! i)) is xs


insert :: Eq a => a -> [a] -> [a]
insert x xs = if x `elem` xs then xs else x : xs

remove :: Eq a => a -> [a] -> [a]
remove = List.delete

has_duplicates :: Eq a => [a] -> Bool
has_duplicates = dups where
  dups [] = False
  dups (x : xs) = x `elem` xs || dups xs

accumulate :: (a -> [b] -> [b]) -> a -> [b]
accumulate f x = f x []


separate :: a -> [[a]] -> [a]
separate _ [] = []
separate _ [ys] = ys
separate x (ys : yss) = ys ++ x : separate x yss

slice :: (a -> Bool) -> [a] -> [[a]]
slice f [] = []
slice f xs = let (ys, zs) = List.break f xs
  in ys : if null zs then [] else slice f (List.tail zs)


perhaps :: (a -> Maybe a) -> a -> a
perhaps f x = the_default x (f x)

perhaps_map :: (a -> Maybe b) -> [a] -> Maybe [b]
perhaps_map f [] = Just []
perhaps_map f (x : xs) = case f x of
  Nothing -> Nothing
  Just y -> case perhaps_map f xs of
    Nothing -> Nothing
    Just ys -> Just (y : ys)

ultimately :: (a -> Maybe (b, a)) -> a -> ([b], a)
ultimately f x = case f x of
  Nothing -> ([], x)
  Just (r, y) -> let (rs, z) = ultimately f y in (r : rs, z)


{- structural operations -}

combl :: (a -> b -> a) -> a -> [b] -> a
combl f = flip (fold (flip f))

combr :: (b -> a -> a) -> [b] -> a -> a
combr = fold_rev

uncombl :: (a -> Maybe (a, b)) -> a -> (a, [b])
uncombl dest x = uncomb x [] where
  uncomb x zs = case dest x of
    Nothing -> (x, zs)
    Just (y, z) -> uncomb y (z : zs)

uncombr :: (a -> Maybe (b, a)) -> a -> ([b], a)
uncombr dest x = case dest x of
  Nothing -> ([], x)
  Just (z, y) -> (z : zs, y') where (zs, y') = uncombr dest y


{- monads -}

liftM :: Monad m => (a -> b) -> m a -> m b
liftM = Monad.liftM

filterM :: Monad m => (a -> m Bool) -> [a] -> m [a]
filterM = Monad.filterM

mapsM :: Monad m => (a -> m [b]) -> [a] -> m [b]
mapsM f [] = return []
mapsM f (x : xs) = do
  ys <- f x
  zs <- mapsM f xs
  return (ys ++ zs)

when :: Monad m => Bool -> m () -> m ()
when = Monad.when


{- exceptions -}
catchIO :: IO a -> (IOError -> IO a) -> IO a
catchIO = Exception.catch
