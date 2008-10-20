module Records where

data MyRecord = A{aField1 :: Int, aField2 :: String, common :: Char}
              | B{bField1 :: Bool, bField2 :: Int, bField3 :: Int, common :: Char}
              | C Bool Bool String



fun2 :: MyRecord -> MyRecord
fun2 a@A{aField2 = v} = a{aField2 = v ++ "foo"}
fun2 b@B{bField3 = v} = b{bField2 = v + 3}
fun2 (C v1 v2 v3) = C v2 v1 "foo"

update2 x = x{common = 'a'}

getChar :: MyRecord -> Char
getChar = common

update :: MyRecord -> MyRecord
update x = x{aField2 = "foo"}

fun :: MyRecord -> Int
fun a@A{aField1 = val} = val
fun b@B{bField3 = val} = val
fun (C v1 v2 v3) = 1

foo :: MyRecord -> Int
foo a = aField1 a