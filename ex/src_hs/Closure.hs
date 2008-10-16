module Closure
where


foo x y = bar 1
        where bar y = bar' y + x
              w = fun x
              bar' z = x + y + z + w
              fun  z = z + x

foo2 x = let f g = g 1
             g f = f 1
         in f (+2) 

