module MutualRecursion where

iseven 0 = True
iseven n = isodd (n-1)

isodd 0 = False
isodd n = iseven (n-1)


data Exp = Plus Exp Exp | Times Exp Exp | If Bexp Exp Exp | Val Int

data Bexp = Equal Exp Exp | Greater Exp Exp