module LazyLet
where

fun = let x = some
          some = 2
      in (x,some)
    where some = 1