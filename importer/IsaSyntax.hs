{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Munich

Abstract syntactic representation of Isar/HOL theory.
-}

module Importer.IsaSyntax (
                  Cmd(..), Theory(..),
                  TypeSpec(..), TypeSig(..), Type(..),
                  Name(..), Literal(..), Term(..), Assoc(..),
                  Prio, ConSpec(..),
                  tname_bool,
                  tname_pair, cname_pair,
                  tname_list, cname_nil, cname_cons
                 ) where

newtype Theory = Theory String
  deriving (Eq, Ord, Show)

data Name      = QName Theory String | Name String
  deriving (Eq, Show)

type VarName   = Name
type ConName   = Name
type OpName    = Name

data Cmd =
    Block [Cmd]

    | TheoryCmd Theory [Cmd]
    --
    -- datatype "('a, 'b) typeconstr" = Constr1 | Constr2 "'a list" 'b
    --
    | DatatypeCmd TypeSpec [ConSpec]
    --
    -- record point
    --   Xcoord :: int
    --   Ycoord :: int
    --
    | RecordCmd TypeSpec [(VarName, Type)]
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
    | FunCmd VarName TypeSig [([Pat], Term)]
    --
    -- definition id :: "'a ⇒ 'a"
    -- where
    --   "id a = a"
    --
    | DefinitionCmd VarName TypeSig ([Pat], Term)
    | InfixDeclCmd OpName Assoc Prio
    | Comment String
  deriving (Show)


type Prio = Int

data Assoc = AssocNone | AssocLeft | AssocRight
  deriving (Show, Eq, Ord)

type Pat = Term

data TypeSpec = TypeSpec [VarName] ConName
  deriving (Show)

data TypeSig = TypeSig Name Type
  deriving (Show)

data Type = TyVar VarName
          | TyCon ConName [Type]
          | TyFun Type Type
          | TyTuple [Type]

  deriving (Show)

data ConSpec = Constructor ConName [Type]
  deriving (Show)

data Literal = Int Integer | String String
  deriving (Show)


type Const = String

data Term = Literal Literal
          | Var VarName -- FIXME: proper representation of constants
          | Con VarName -- FIXME: distinction Var/Con is not necessary
          | Lambda [Term] Term -- FIXME: Lambda [t1, t2] t == Lambda t1 (Lambda t2) t
          | App Term Term
          | InfixApp Term Term Term -- FIXME: Is only used as
                                    -- intermediate holding pace in
                                    -- Convert.hs
          | If Term Term Term
          | Parenthesized Term -- FIXME: should also be only intermediate
          | RecConstr VarName [(Name, Term)]
          | RecUpdate Term [(Name, Term)]
          | Case Term [(Pat, Term)]
  deriving (Show)

-- FIXME place this into some kind of "Haskell system compatibility file"
tname_bool  = Name "Bool" -- FIXME

tname_pair  = QName (Theory "Prelude") "*"
cname_pair  = QName (Theory "Prelude") "(,)"

tname_list  = QName (Theory "Prelude") "[]"
cname_nil   = QName (Theory "Prelude") "[]"
cname_cons  = QName (Theory "Prelude") ":"
