module Stmt where

{- term algebra -}

type Var = String

-- sorts
type Class = String
type Sort = [Class]

-- types
type Tyco = String
data Type = Tyco :%% [Type] -- note the infix constructor notation
  | Type :-> Type -- function space
  | TVar Var

-- terms
type Const = String
data Term = Const ::: Type
  | Var Var
  | Term :$ Term -- application
  | (Var, Type) :|-> Term -- abstraction


{- statement syntax -}

data Stmt = Data -- continue here
  | Class -- continue here
  | Fun
      Const                    -- constant to be defined
      ([(Var, Sort)], Type)     -- type scheme of constant (schematic polymorphism!)
      [([Term], Term)]          -- equations (arguments, right hand side)
  | Inst -- continue here
