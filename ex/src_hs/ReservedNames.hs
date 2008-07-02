
module ReservedNames where

foo nat set = nat : ([nat] ++ set)

bar nat = let set = [nat] in set

quux nat = frob nat []
    where frob nat set = [nat] : set