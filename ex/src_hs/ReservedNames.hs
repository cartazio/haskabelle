
module ReservedNames where

foo nat set = nat : ([nat] ++ set)

bar nat = let set = [nat] in set

quux nat = frob nat []
    where frob nat set = nat : set

zurp x = knorks x []
    where knorks x set = [x] ++ set