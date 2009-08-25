module Shadowing
where

foo = let foo = (\x -> x + 1)
          v = foo 1
      in v
    where foo x = x