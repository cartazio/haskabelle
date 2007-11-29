module Primitive where

data Nat = Zero | Succ Nat

id :: a -> a
id x = x

foo :: a -> a
foo = \x -> x

incr :: Nat -> Nat
incr n = Succ n

decr :: Nat -> Nat
decr (Succ n) = n
