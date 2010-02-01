module Records where

data Identity a = Id { this :: a }

data MyRecord = A { aField1 :: String, common1 :: Bool, common2 :: Int }
              | B { bField1 :: Bool, bField2 :: Int, common1 :: Bool, common2 :: Int }
              | C Bool Int String

constr :: MyRecord
constr = A { aField1 = "foo", common1 = True }

update :: MyRecord -> MyRecord
update x = x { common2 = 1, common1 = False }

pattern :: MyRecord -> Int
pattern A { common2 = val } = val
pattern B { bField2 = val } = val
pattern (C _ val _) = val
