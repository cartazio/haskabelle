module Cover where

import Base
-- import Data.Array -- Use immutable arrays

array :: a -> [(Int, b)] -> [(Int, b)]
array dims init_elems = init_elems

-- ordered powerset
pw :: [a] -> [[[a]]]
pw [] = [[[]]]
pw (x:xs) = zipWith (++) (xs' ++ [[]]) ([] : map (map (x:)) xs')
    where xs' = pw xs

pw' = map reverse . foldl (++) [] . pw . reverse


-- Simple covering algorithm
naive_cover c xs ys = head [ zs | zs <- pw' xs, all (covered c zs) ys ]
    where covered c zs y = any (`c` y) zs
-- Essential covering elements

essential c xs ys = distincts (fold (++) (map unique_cover c xs ys) [])
    where unique_cover c xs y = case filter (`c` y) xs of
                                  [x] -> [x]
                                  _ -> []

fromto :: Int -> Int -> [Int]
fromto a b
    | a < b     = a : fromto (a+1) b
    | a == b    = [a]
    | otherwise = []

-- Turn an arbitrary covering problem into one over the integer, given a covering matrix
matrix_cover f c xs ys =
    let maxi = length xs - 1
        maxj = length ys - 1
        is = fromto 0 maxi -- FIXME: [0 .. maxi]
        js = fromto 0 maxj -- FIXME: [0 .. maxj]
        a = array ((0,0), (maxi, maxj)) [ ((i,j), c (xs !! i) (ys !! j)) | i <- is, j <- js ]
    in map (xs !!) (f (\i j -> a !! (i, j)) is js)


remove_dom_rows c xs ys = sups (dom c ys) xs
    where dom c ys x x' = all (\y -> c x' y || not (c x y)) ys

remove_dom_cols c xs ys = sups (dom c xs) ys
    where dom c xs y y' = all (\x -> c x y || not (c x y')) xs

-- Filter until we reach a fixed-point
filter_dominance c (xs, ys) = 
    let ys' = remove_dom_cols c xs ys
        xs' = remove_dom_rows c xs ys'
    in if length xs == length xs' && length ys == length ys' 
       then (xs, ys)
       else filter_dominance c (xs', ys')


stepwise_cover c xs ys =
    let (xs', ys') = filter_dominance c (xs, ys) -- essentials first?
        es = essential c xs' ys'
    in es ++ naive_cover c (filter (not . (`elem` es)) xs') (filter (\y -> not $ any (`c` y) xs) ys')

matrix_stepwise_cover = matrix_cover stepwise_cover



