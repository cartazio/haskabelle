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


-- The following is to test mutually-recursive function definitions.

data Boolean = Verum | Falsum

isEven :: Nat -> Boolean
isEven Zero        = Verum
isEven (Succ Zero) = Falsum
isEven n           = isOdd (decr n)

isOdd :: Nat -> Boolean
isOdd Zero        = Falsum
isOdd (Succ Zero) = Verum
isOdd n           = isEven (decr n)