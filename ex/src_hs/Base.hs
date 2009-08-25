module Base where

fold f [] y = y
fold f (x : xs) y = fold f xs (f x y)

fold_map :: (a -> s -> (b, s)) -> [a] -> s -> ([b], s)
fold_map f [] y = ([], y)
fold_map f (x:xs) y =
  let
    (x', y') = f x y
    (xs', y'') = fold_map f xs y'
  in (x' : xs', y'')

maps :: (a -> [b]) -> [a] -> [b]
maps f [] = []
maps f (x : xs) = f x ++ maps f xs

map_index :: ((Int, a) -> b) -> [a] -> [b]
map_index f = mapp 0 where
  mapp _ [] = []
  mapp i (x : xs) = f (i, x) : mapp (i + 1) xs

map2 :: (a -> b -> c) -> [a] -> [b] -> [c]
map2 _ [] [] = []
map2 f (x : xs) (y : ys) = f x y : map2 f xs ys
map2 _ _ _ = error "unequal lengths"

map_split :: (a -> (b, c)) -> [a] -> ([b], [c])
map_split f [] = ([], [])
map_split f (x : xs) =
  let
    (y, w) = f x
    (ys, ws) = map_split f xs
  in (y : ys, w : ws)

map_product :: (a -> b -> c) -> [a] -> [b] -> [c]
map_product f _ [] = []
map_product f [] _ = []
map_product f (x : xs) ys = map (f x) ys ++ map_product f xs ys

member :: Eq a => [a] -> a -> Bool
member [] y = False
member (x : xs) y = x == y || member xs y

distincts :: Eq a => [a] -> [a]
distincts [] = []
distincts (x : xs) = if member xs x then distincts xs else x : distincts xs
