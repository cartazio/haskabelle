module Nat where

data Nat = Zero | Succ Nat

plus :: Nat -> Nat -> Nat
plus Zero n = n
plus (Succ m) n = Succ (plus m n)

minus :: Nat -> Nat -> Nat
minus m Zero = m
minus (Succ m) (Succ n) = minus m n

mult :: Nat -> Nat -> Nat
mult Zero n = Zero
mult (Succ m) n = plus n (mult m n)

less_eq :: Nat -> Nat -> Bool
less :: Nat -> Nat -> Bool

less_eq Zero n = True
less_eq (Succ m) n = less m n
less n Zero = False
less n (Succ m) = less_eq n m

divmod :: Nat -> Nat -> (Nat, Nat)
divmod Zero n = (Zero, Zero)
divmod m Zero = (Zero, m)
divmod m n = if less m n then (Zero, m) else (Succ r, s) where (r, s) = divmod (minus m n) n

num :: Num a => Nat -> a
num Zero = 0
num (Succ n) = num n + 1