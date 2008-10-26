module MutualRecursion where

evalExp :: Exp -> Int
evalExp (Plus e1 e2) = evalExp e1 + evalExp e2 
evalExp (Times e1 e2) = evalExp e1 * evalExp e2
evalExp (ITE b e1 e2)
    | evalBexp b = evalExp e1
    | otherwise  = evalExp e2
evalExp (Val i) = i

evalBexp :: Bexp -> Bool
evalBexp (Equal e1 e2) = evalExp e1 == evalExp e2
evalBexp (Greater e1 e2) = evalExp e1 > evalExp e2

data Exp = Plus Exp Exp | Times Exp Exp | ITE Bexp Exp Exp | Val Int

data Bexp = Equal Exp Exp | Greater Exp Exp



extract x = x {a = True}


data Record = Record{a :: Bool, b :: Int}

