module Base where

-- General stuff
fold f [] y = y
fold f (x:xs) y = fold f xs (f x y)


fold_map :: (a -> s -> (b, s)) -> [a] -> s -> ([b], s)
fold_map f [] y = ([], y)
fold_map f (x:xs) y =
      let (x', y') = f x y
          (xs', y'') = fold_map f xs y'
      in (x' : xs', y'')


cprod [] = [[]]
cprod (xs:xss) = [ y : ys | y <- xs, ys <- cprod xss ]

distincts [] = [] -- FIXME: make tail recursive
distincts (x:xs) | elem x xs' = xs'
                | otherwise  = x : xs'
    where xs' = distincts xs

suplist_ins f x [] = [x]
suplist_ins f x ys 
      | any (f x) ys = ys 
      | otherwise     = x : filter (\y -> not (f y x)) ys

sups f = foldr (suplist_ins f) []

unordered_pairs [] = []
unordered_pairs (x:xs) = map ((,) x) (x:xs) ++ unordered_pairs xs

pos_neg_filter p xs = pnf p xs ([], [])
    where pnf p [] (pos, neg) = (reverse pos, reverse neg)
          pnf p (x:xs) (pos, neg)
              | p x       = pnf p xs (x:pos, neg)
              | otherwise = pnf p xs (pos, x:neg)

