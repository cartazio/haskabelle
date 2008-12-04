
module AsPatterns where

data MyRecord = A{ one :: [Int], two:: Int, three :: Char }

f () = ()

foo [] = []
foo (a@(x1,x2):b@(y1,y2):rest) = a:b:rest

bar x = case x of
          [a@(b,c)] -> a
          c@(a@(x1,x2):b@(y1,y2):rest) -> a

quux x = (\a@(r,s) -> x ++ [a])

unsound :: [Int] -> [Int]
unsound l@(_:_) = 0 : l
unsound l@([]) = 1 : l

record :: MyRecord -> MyRecord
record a@A{one = []} = a