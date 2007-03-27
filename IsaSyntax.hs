module IsaSyntax (
                  Cmd(..), Theory(..),
                  TypeSpec(..), TypeSig(..), Type(..), 
                  Name(..), Literal(..), Term(..)
                 ) where

newtype Theory = Theory String
  deriving (Eq, Ord, Show)

data Name      = QName   Theory String | Name String 
  deriving (Eq, Show)

type VarName   = Name
type ConName   = Name


data Cmd = 
    TheoryCmd Theory [Cmd]
    --
    -- datatype ('a, 'b) typeconstr = Constr1 | Constr2 'a 'b 
    --
    | DatatypeCmd TypeSpec [(ConName, [Type])]
    --
    -- types 'a synonym1       = type1
    --       ('a, 'b) synonym2 = type2
    --
    | TypesCmd [(TypeSpec, Type)]
    --
    -- fun fib :: "nat ⇒ nat"
    -- where
    --   "fib 0 = 1"
    -- | "fib (Suc 0) = 1"
    -- | "fib (Suc (Suc n)) = fib n + fib (Suc n)"
    --
    | FunCmd VarName TypeSig [(Pattern, Term)]
    | Comment String
  deriving (Show)

type Pattern = [Term]

data TypeSpec = TypeSpec [VarName] ConName
  deriving (Show)

data TypeSig = TypeSig Name Type
  deriving (Show)

data Type = TyVar VarName
          | TyCon ConName [Type]
          | TyFun Type Type
          | TyApp Type Type  -- FIXME: maybe unneccesary

  deriving (Show)


data Literal = Int Integer | Float Rational 
  deriving (Show)


type Const = String
type Op = Name

data Term = Const ::: Type
          | Literal Literal
          | Var VarName
          | Lambda (VarName, Type) Term 
          | App Term Term
          | Parenthesized Term
  deriving (Show)


