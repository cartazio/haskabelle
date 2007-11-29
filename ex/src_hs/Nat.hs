module Nat where

data Nat = Zero | Succ Nat

plus :: Nat -> Nat -> Nat
plus Zero n = n
plus (Succ m) n = Succ (plus m n)

mult :: Nat -> Nat -> Nat
mult Zero n = Zero
mult (Succ m) n = plus n (mult m n)

less_eq :: Nat -> Nat -> Bool
less :: Nat -> Nat -> Bool

less_eq Zero n = True
less_eq (Succ m) n = less m n
less n Zero = False
less n (Succ m) = less_eq n m
