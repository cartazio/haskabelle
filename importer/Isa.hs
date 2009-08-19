{-# LANGUAGE DeriveDataTypeable #-}

{-| Author: Tobias C. Rittweiler, TU Muenchen

Abstract representation of Isar/HOL theory.
-}

module Importer.Isa where

import Data.Generics.Basics
import Data.Generics.Instances

import Data.Graph as Graph

newtype ThyName = ThyName String
  deriving (Show, Eq, Ord, Data, Typeable)

data Name = QName ThyName String | Name String
  deriving (Show, Eq, Ord, Data, Typeable)

data DatatypeDef = DatatypeDef TypeSpec [ConSpec]
                   deriving (Eq,Show, Data, Typeable)

data Type =
    Type Name [Type]
  | TyFun Type Type
  | TyTuple [Type] -- FIXME: unused
  | TyVar Name
  | TyNone
  | TyScheme [(Name, [Name])] Type -- FIXME: remove from this type
  deriving (Show, Eq, Data, Typeable)

data Literal = Int Integer | Char Char | String String
  deriving (Show, Eq, Data, Typeable)

type Pat = Term

data Term =
    Literal Literal
  | Const Name
  | Abs Name Term
  | App Term Term
  | If Term Term Term
  | Let [(Pat, Term)] Term
  | Case Term [(Pat, Term)]
  | ListComp Term [ListCompStmt]
  | RecConstr Name [(Name, Term)]
  | RecUpdate Term [(Name, Term)]
  | DoBlock String [Stmt] String -- syntactic sugar for translating Haskell do expressions
  | Parenthesized Term
  deriving (Show, Data, Typeable)

{-|
  This type represents Isabelle commands.
-}
data Cmd = Block [Cmd]  -- ^a block of commands
         | TheoryCmd ThyName [ThyName] [Cmd]  -- ^the command introducing a theory
         
         {-|
           A data type command: @datatype ('a, 'b) "typeconstr" = Constr1 | Constr2 "'a list" 'b@
          -}
         | DatatypeCmd [DatatypeDef]
         
         {-|
           Record type declaration:
           
           @
           record point = 
           Xcoord :: int
           Ycoord :: int
           @
          -}
         | RecordCmd TypeSpec [(Name, Type)]
         
         {-|
           Type synonym declaration:
           
           @
           types 'a synonym1       = type1
                 ('a, 'b) synonym2 = type2
           @
          -}
         | TypesCmd [(TypeSpec, Type)]
         
         {-|
           Primitive recursive function definition:
           
           @
           primrec add :: "nat => nat => nat"
           where
                "add 0 y = y"
              | "add (Suc x) y = Suc (add x y)"
           @
          -}
         | PrimrecCmd [Name] [TypeSig] [(Name, [Pat], Term)]
         
         {-|
           Function definition:
           
           @
           fun fib :: "nat => nat"
           where
                "fib 0 = 1"
              | "fib (Suc 0) = 1"
              | "fib (Suc (Suc n)) = fib n + fib (Suc n)"
           @
          -}
         | FunCmd [Name] [TypeSig] [(Name, [Pat], Term)]
         
         {-|
           Constant definition.

           definition id :: "int"
           where
           "id a = a"
          -}
         | DefinitionCmd Name TypeSig (Pat, Term)
         
         {-|
           A class declaration
          -}
         | ClassCmd Name [Name] [TypeSig]
         
         {-|
           An instance declaration.
          -}
         | InstanceCmd Name Type [Cmd]
         
         {-|
           An operator infix annotation.
          -}
         | InfixDeclCmd Name Assoc Prio
           
         {-|
           A comment.
          -}
         | Comment String
  deriving (Show, Data, Typeable)

{-|
  This type represents precedence values of an infix annotation.
-}
type Prio = Int

{-|
  This type represents associativity modes of an infix annotation.
-}
data Assoc = AssocNone | AssocLeft | AssocRight
  deriving (Show, Eq, Ord, Data, Typeable)

{-|
  This type represents patterns.
-}


{-|
  This type represents constructors applied to variables.
-}
data TypeSpec = TypeSpec [Name] Name
  deriving (Show, Eq, Data, Typeable)

{-|
  This type represents type signatures (i.e. a typed name).
-}
data TypeSig = TypeSig Name Type
  deriving (Show, Eq, Data, Typeable)

{-|
  This type represents types.
-}

{-|
  This type represents constructor declaration (as part of a data type
  declaration).
-}
data ConSpec = Constructor Name [Type]
  deriving (Show, Eq, Data, Typeable)

{-|
  This type represents literals.
-}

data Stmt = DoGenerator Pat Term
          | DoQualifier Term
--          | DoLetStmt [(Pat, Term)]
            deriving (Show, Data, Typeable)

{-|
  This type represents statements of list comprehensions.
-}
data ListCompStmt = Generator (Pat, Term)
                  | Guard Term
  deriving (Show, Data, Typeable)


topologize :: Ord b => (a -> (b, [b])) -> [a] -> [[a]]
topologize f xs = (map list_of_SCC . stronglyConnComp . map add_edges) xs
  where
    add_edges x = let (node, nodes) = f x in (x, node, nodes)
    list_of_SCC (Graph.AcyclicSCC x) = [x]
    list_of_SCC (Graph.CyclicSCC xs) = xs
