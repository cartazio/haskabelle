{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen

Abstract syntactic representation of Isar/HOL theory.
-}

module Importer.IsaSyntax (module Importer.IsaSyntax) where

import Data.Generics.Basics
import Data.Generics.Instances

{-|
  This type represents the name of a theory.
-}
newtype Theory = Theory String
  deriving (Show, Eq, Ord, Data, Typeable)

{-|
  This type represents names (being either qualified or unqualified).
-}
data Name      = QName Theory String | Name String
  deriving (Show, Eq, Ord, Data, Typeable)

{-|
  This type represents names of variables.
-}
type VarName   = Name
{-|
  This type represents names of constructors.
-}
type ConName   = Name
{-|
  This type represents names of operators.
-}
type OpName    = Name
{-|
  This type represents names of classes.
-}
type ClassName = Name

data DatatypeDef = DatatypeDef TypeSpec [ConSpec]
                   deriving (Eq,Show, Data, Typeable)

{-|
  This type represents Isabelle commands.
-}
data Cmd = Block [Cmd]  -- ^a block of commands
         | TheoryCmd Theory [Cmd]  -- ^the command introducing a theory
         
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
         | RecordCmd TypeSpec [(VarName, Type)]
         
         {-|
           Type synonym declaration:
           
           @
           types 'a synonym1       = type1
                 ('a, 'b) synonym2 = type2
           @
          -}
         | TypesCmd [(TypeSpec, Type)]
         
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
         | FunCmd [VarName] [TypeSig] [(VarName, [Pat], Term)]
         
         {-|
           Constant definition.

           definition id :: "int"
           where
           "id a = a"
          -}
         | DefinitionCmd VarName TypeSig (Pat, Term)
         
         {-|
           A class declaration
          -}
         | ClassCmd ClassName [ClassName] [TypeSig]
         
         {-|
           An instance declaration.
          -}
         | InstanceCmd ClassName Type [Cmd]
         
         {-|
           An operator infix annotation.
          -}
         | InfixDeclCmd OpName Assoc Prio
           
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
type Pat = Term

{-|
  This type represents constructors applied to variables.
-}
data TypeSpec = TypeSpec [VarName] ConName
  deriving (Show, Eq, Data, Typeable)

{-|
  This type represents type signatures (i.e. a typed name).
-}
data TypeSig = TypeSig Name Type
  deriving (Show, Eq, Data, Typeable)

{-|
  This type represents types.
-}
data Type = TyVar VarName
          | TyScheme [(VarName, [ClassName])] Type
          | TyCon ConName [Type]
          | TyFun Type Type
          | TyTuple [Type] -- FIXME: unused
          | TyNone
  deriving (Show, Eq, Data, Typeable)

{-|
  This type represents constructor declaration (as part of a data type
  declaration).
-}
data ConSpec = Constructor ConName [Type]
  deriving (Show, Eq, Data, Typeable)

{-|
  This type represents literals.
-}
data Literal = Int Integer | Char Char | String String
  deriving (Show, Eq, Data, Typeable)

{-|
  This type represents terms.
-}
data Term = Literal Literal
          | Var VarName
          | Lambda VarName Term -- FIXME: Lambda [t1, t2] t == Lambda t1 (Lambda t2) t
          | App Term Term
          | If Term Term Term
          | Let [(Pat, Term)] Term
          | Case Term [(Pat, Term)]
          | Parenthesized Term
          | ListComp Term [ListCompStmt]
          | RecConstr VarName [(Name, Term)]
          | RecUpdate Term [(Name, Term)]
          | DoBlock String [Stmt] String -- syntactic sugar for
                                         -- translating Haskell do
                                         -- expressions
  deriving (Show, Data, Typeable)

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
