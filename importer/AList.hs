{-| Author: Florian Haftmann, TU Muenchen

Association lists -- lists of (key, value) pairs.
-}

module Importer.AList (lookup, defined, update, upd_default, delete,
  map_entry, map_default, make, group) where

import Prelude (Eq, Bool(..), Maybe(..), Integer, id, const, (==), (||), (+), (-), map)
import Importer.Library (fold_rev)

find_index :: Eq a => [(a, b)] -> a -> Integer
find_index xs key = find xs 0 where
  find [] _ = -1
  find ((key', value) : xs) i =
    if key == key' then i else find xs (i + 1)

map_index :: Eq a => a -> ([(a, b)] -> [(a, b)]) -> ((a, b) -> [(a, b)] -> [(a, b)])
  -> [(a, b)] -> [(a, b)]
map_index key f_none f_some xs = (if i == -1 then f_none else mapp i) xs where
  i = find_index xs key;
  mapp 0 (x : xs) = f_some x xs
  mapp i (x : xs) = x : mapp (i - 1) xs

lookup :: Eq a => [(a, b)] -> a -> Maybe b
lookup [] _ = Nothing
lookup ((key, value) : xs) key' =
  if key' == key then Just value
  else lookup xs key'

defined :: Eq a => [(a, b)] -> a -> Bool
defined [] _ = False
defined ((key, value) : xs) key' =
  key' == key || defined xs key'

update :: Eq a => (a, b) -> [(a, b)] -> [(a, b)]
update (x @ (key, value)) =
  map_index key ((:) x) (const ((:) x));

upd_default :: Eq a => (a, b) -> [(a, b)] -> [(a, b)]
upd_default (key, value) xs =
  if defined xs key then xs else (key, value) : xs

delete :: Eq a => a -> [(a, b)] -> [(a, b)]
delete key = map_index key id (const id)

map_entry :: Eq a => a -> (b -> b) -> [(a, b)] -> [(a, b)]
map_entry key f = map_index key id (\ (key, value) -> (:) (key, f value))

map_default :: Eq a => (a, b) -> (b -> b) -> [(a, b)] -> [(a, b)]
map_default (key, value) f =
  map_index key ((:) (key, f value)) (\ (key, value) -> (:) (key, f value))

make :: (a -> b) -> [a] -> [(a, b)]
make keyfun = map keypair where
  keypair x = (x, keyfun x)

group :: Eq a => [(a, b)] -> [(a, [b])]
group xs = fold_rev (\ (k, v) -> map_default (k, []) ((:) v)) xs []
