module Twin where


data Twin a b = Twin a b

dest_Twin :: Twin a b -> (a, b)
dest_Twin (Twin x y) = (x, y)

mk_Twin :: (a, b) -> Twin a b
mk_Twin = uncurry Twin
