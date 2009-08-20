{-# LANGUAGE DeriveDataTypeable #-}

{-| Author: Tobias C. Rittweiler, TU Muenchen

Abstract representation of Isar/HOL theory.
-}

module Importer.Isa (ThyName(..), Name(..), Type(..), Literal(..), Term(..), Pat,
  ListComprFragment(..), DoBlockFragment(..),
  Stmt(..), TypeSpec(..), TypeSig(..)) where

import Data.Generics.Basics
import Data.Generics.Instances

import Data.Graph as Graph


{- Names -}

newtype ThyName = ThyName String
  deriving (Show, Eq, Ord, Data, Typeable)

data Name = QName ThyName String | Name String
  deriving (Show, Eq)

data Type =
    Type Name [Type]
  | Func Type Type
  | Prod [Type]
  | TVar Name
  | NoType
  | TyScheme [(Name, [Name])] Type -- FIXME: remove from this type
  deriving Show


{- Expressions -}

data Literal = Int Integer | Char Char | String String
  deriving Show

data Term =
    Literal Literal
  | Const Name
  | Abs Name Term
  | App Term Term
  | If Term Term Term
  | Let [(Pat, Term)] Term
  | Case Term [(Pat, Term)]
  | ListCompr Term [ListComprFragment]
  | RecConstr Name [(Name, Term)]
  | RecUpdate Term [(Name, Term)]
  | DoBlock String [DoBlockFragment] String -- syntactic sugar for translating Haskell do expressions
  | Parenthesized Term
  deriving Show

type Pat = Term

data ListComprFragment = Generator (Pat, Term) | Guard Term
  deriving Show

data DoBlockFragment = DoGenerator Pat Term
  | DoQualifier Term
  | DoLetStmt [(Pat, Term)]
  deriving Show


{- Statements -}

data TypeSpec = TypeSpec [Name] Name
  deriving Show

data TypeSig = TypeSig Name Type
  deriving Show

data Stmt = Block [Stmt] -- FIXM get rid of
  | TheoryOpening ThyName [ThyName] [Stmt] -- FIXM get rid of
  | Datatype [(TypeSpec, [(Name, [Type])])]
  | Record TypeSpec [(Name, Type)]
  | TypeSynonym [(TypeSpec, Type)]
  | Definition Name TypeSig (Pat, Term)
  | Primrec [Name] [TypeSig] [(Name, [Pat], Term)]
  | Fun [Name] [TypeSig] [(Name, [Pat], Term)]
  | Class Name [Name] [TypeSig]
  | Instance Name Type [Stmt]
  | Comment String
  deriving Show


topologize :: Ord b => (a -> (b, [b])) -> [a] -> [[a]]
topologize f xs = (map list_of_SCC . stronglyConnComp . map add_edges) xs
  where
    add_edges x = let (node, nodes) = f x in (x, node, nodes)
    list_of_SCC (Graph.AcyclicSCC x) = [x]
    list_of_SCC (Graph.CyclicSCC xs) = xs
