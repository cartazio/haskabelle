
module AsPatterns where


foo [] = []
foo (a@(x1,x2):b@(y1,y2):rest) = a:b:rest

bar x = case x of
          [a@(b,c)] -> Just a
          c@(a@(x1,x2):b@(y1,y2):rest) -> Just c

quux x = (\a@(r,s) -> x ++ [a])

unsound :: [Int] -> [Int]
unsound l@(_:_) = 0 : l
unsound l@([]) = 1 : l
