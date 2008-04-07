{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen

Abstract syntactic representation of Isar/HOL theory.
-}

module Importer.IsaSyntax (module Importer.IsaSyntax) where

import Data.Generics.Basics
import Data.Generics.Instances


newtype Theory = Theory String
  deriving (Show, Eq, Ord, Data, Typeable)

data Name      = QName Theory String | Name String
  deriving (Show, Eq, Ord, Data, Typeable)

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
    | FunCmd [VarName] [TypeSig] [(VarName, [Pat], Term)]
    --
    -- definition id :: "'a ⇒ 'a"
    -- where
    --   "id a = a"
    --
    | DefinitionCmd VarName TypeSig (Pat, Term)
    | InfixDeclCmd OpName Assoc Prio
    | Comment String
  deriving (Show, Data, Typeable)


type Prio = Int

data Assoc = AssocNone | AssocLeft | AssocRight
  deriving (Show, Eq, Ord, Data, Typeable)

type Pat = Term

data TypeSpec = TypeSpec [VarName] ConName
  deriving (Show, Eq, Data, Typeable)

data TypeSig = TypeSig Name Type
  deriving (Show, Eq, Data, Typeable)

data Type = TyVar VarName
          | TyCon ConName [Type]
          | TyFun Type Type
          | TyTuple [Type]
          | TyNone
  deriving (Show, Eq, Data, Typeable)

data ConSpec = Constructor ConName [Type]
  deriving (Show, Eq, Data, Typeable)

data Literal = Int Integer | String String
  deriving (Show, Eq, Data, Typeable)


type Const = String

data Term = Literal Literal
          | Var VarName
          | Lambda [VarName] Term -- FIXME: Lambda [t1, t2] t == Lambda t1 (Lambda t2) t
          | App Term Term
          | If Term Term Term
          | Let [(Pat, Term)] Term
          | Case Term [(Pat, Term)]
          | Parenthesized Term
          | RecConstr VarName [(Name, Term)]
          | RecUpdate Term [(Name, Term)]
  deriving (Show, Data, Typeable)

-- FIXME place this into some kind of "Haskell system compatibility file"
tnameBool   = Name "Bool" -- FIXME

tnamePair   = QName (Theory "Prelude") "*"
cnamePair   = QName (Theory "Prelude") "(,)"

tnameList   = QName (Theory "Prelude") "list"
cnameNil    = QName (Theory "Prelude") "[]"
cnameCons   = QName (Theory "Prelude") "#"

mknil       = Var cnameNil
mkcons x y  = App (App (Var cnameCons) x) y
mkpair x y  = App (App (Var cnamePair) x) y

mkInfixApp t1 op t2
    = App (App op t1) t2

isPairCon x = x == cnamePair
isCons    x = x == cnameCons
isNil     x = x == cnameNil

