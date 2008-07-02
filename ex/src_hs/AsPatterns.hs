
module AsPatterns where

foo [] = []
foo (a@(x1,x2):b@(y1,y2):rest) = a:b:rest

bar x = case x of
          [a@(b,c)] -> Just a
          (a@(x1,x2):b@(y1,y2):rest) -> Nothing

quux x = (\a@(r,s) -> x ++ [a])