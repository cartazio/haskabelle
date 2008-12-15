module LazyLet
where

fun = let x = some
          some = 2
      in (x,some)
    where some = 1


foo x = let (even,odd) = (\x -> if x == 0 then True else odd (x-1))
            odd = (\x -> if x == 0 then False else even (x-1))
         in even x


foo2 x = let even x = if x == 0 then True else odd (x-1)
             odd x = if x == 0 then False else even (x-1)
         in even x

-- myX:myXs = [1,2,3]

--even = (\x -> if x == 0 then True else odd (x-1))
--odd = (\x -> if x == 0 then False else even (x-1))