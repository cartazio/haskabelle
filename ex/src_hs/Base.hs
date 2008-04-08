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

distinct [] = [] -- FIXME: make tail recursive
distinct (x:xs) | elem x xs' = xs'
                | otherwise  = x : xs'
    where xs' = distinct xs



suplist_ins :: (a -> a -> Bool) ->  a -> [a] -> [a]

suplist_ins (<<=) x [] = [x]
suplist_ins (<<=) x ys 
    | any (x <<=) ys = ys 
    | otherwise     = x : [ y | y <- ys, not (y <<= x) ]

sups (<<=) = foldr (suplist_ins (<<=)) []

unordered_pairs [] = []
unordered_pairs (x:xs) = map ((,) x) (x:xs) ++ unordered_pairs xs

pos_neg_filter p xs = pnf xs ([], [])
    where pnf [] (pos, neg) = (reverse pos, reverse neg)
          pnf (x:xs) (pos, neg)
              | p x       = pnf xs (x:pos, neg)
              | otherwise = pnf xs (pos, x:neg)

