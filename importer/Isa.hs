{-# LANGUAGE DeriveDataTypeable #-}

{-| Author: Tobias C. Rittweiler, TU Muenchen

Abstract representation of Isar/HOL theory.
-}

module Importer.Isa (ThyName(..), Name(..), Type(..), Literal(..), Term(..), Pat,
  ListComprFragment(..), DoBlockFragment(..),
  Stmt(..), TypeSpec(..), TypeSign(..), Module(..)) where

import Importer.Utilities.Misc

import Data.Generics.Basics
import Data.Generics.Instances

import Data.Graph as Graph


{- Names -}

newtype ThyName = ThyName String
  deriving (Show, Eq, Ord, Data, Typeable)

data Name = QName ThyName String | Name String
  deriving (Show, Eq)


{- Expressions -}

data Type =
    Type Name [Type]
  | Func Type Type
  | Prod [Type]
  | TVar Name
  | NoType
  | TyScheme [(Name, [Name])] Type -- FIXME: remove from this type
  deriving Show

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

data ListComprFragment =
    Generator (Pat, Term)
  | Guard Term
  deriving Show

data DoBlockFragment =
    DoGenerator Pat Term
  | DoQualifier Term
  | DoLetStmt [(Pat, Term)]
  deriving Show


{- Statements -}

data TypeSpec = TypeSpec [Name] Name
  deriving Show

data TypeSign = TypeSign Name Type
  deriving Show

data Stmt =
    Datatype [(TypeSpec, [(Name, [Type])])]
  | Record TypeSpec [(Name, Type)]
  | TypeSynonym [(TypeSpec, Type)]
  | Definition TypeSign (Pat, Term)
  | Primrec [TypeSign] [(Name, [Pat], Term)]
  | Fun [TypeSign] [(Name, [Pat], Term)]
  | Class Name [Name] [TypeSign]
  | Instance Name Type [Stmt]
  | Comment String
  deriving Show

data Module = Module ThyName [ThyName] [Stmt]
  deriving Show


{- Identifier categories -}

data Ident = ClassI Name | TycoI Name | ConstI Name
  deriving Eq

add_idents_type :: Type -> [Ident] -> [Ident]
add_idents_type (Type n tys) =
  insert (TycoI n) *> fold add_idents_type tys
add_idents_type (Func ty1 ty2) =
  add_idents_type ty1 *> add_idents_type ty2
add_idents_type (Prod tys) =
  fold add_idents_type tys
add_idents_type (TVar _) =
  id
add_idents_type NoType =
  id
add_idents_type (TyScheme vs ty) =
  fold (insert . ClassI) (concatMap snd vs) *> add_idents_type ty-- FIXME

add_idents_term :: Term -> [Ident] -> [Ident]
add_idents_term (Literal _) =
  id
add_idents_term (Const n) =
  insert (ConstI n)
add_idents_term (Abs n t) =
  add_idents_term t
add_idents_term (App t1 t2) =
 add_idents_term t1 *> add_idents_term t2
add_idents_term (If tb t1 t2) =
  add_idents_term tb *> add_idents_term t1 *> add_idents_term t2
add_idents_term (Let bs t) =
  fold (\(p, t) -> add_idents_term p *> add_idents_term t) bs *> add_idents_term t
add_idents_term (Case t bs) =
  add_idents_term t *> fold (\(p, t) -> add_idents_term p *> add_idents_term t) bs
add_idents_term (ListCompr t cprs) =
  add_idents_term t *> fold add_idents_compr cprs
add_idents_term (RecConstr n fs) =
  insert (ConstI n) *> fold (\(n, t) -> insert (ConstI n) *> add_idents_term t) fs
add_idents_term (RecUpdate t fs) = 
  add_idents_term t *> fold (\(n, t) -> insert (ConstI n) *> add_idents_term t) fs
add_idents_term (DoBlock _ dobls _) =
  fold add_idents_dobl dobls
add_idents_term (Parenthesized t) = 
  add_idents_term t

add_idents_compr :: ListComprFragment -> [Ident] -> [Ident]
add_idents_compr (Generator (p, t)) =
  add_idents_term p *> add_idents_term t
add_idents_compr (Guard t) =
  add_idents_term t

add_idents_dobl :: DoBlockFragment -> [Ident] -> [Ident]
add_idents_dobl (DoGenerator p t) =
  add_idents_term p *> add_idents_term t
add_idents_dobl (DoQualifier t) =
  add_idents_term t
add_idents_dobl (DoLetStmt bs) =
    fold (\(p, t) -> add_idents_term p *> add_idents_term t) bs

add_idents_typespec :: TypeSpec -> [Ident] -> [Ident]
add_idents_typespec (TypeSpec _ n) =
  insert (TycoI n)

idents_of_typesign :: TypeSign -> (Ident, [Ident])
idents_of_typesign (TypeSign n ty) =
  (ConstI n, accumulate add_idents_type ty)

idents_of_stmt :: Stmt -> (([Ident], [Ident]), [Ident])
idents_of_stmt (Datatype specs) =
  let
    xs1 = accumulate (fold (add_idents_typespec . fst)) specs
    xs2 = accumulate (fold (fold (insert . ConstI . fst) . snd)) specs
    xs3 = accumulate (fold (fold (fold add_idents_type . snd) . snd)) specs
  in ((xs1, xs2), xs3)
idents_of_stmt (Record tyspec selectors) =
  let
    xs1 = accumulate add_idents_typespec tyspec
    xs2 = accumulate (fold (\(n, _) -> insert (ConstI n))) selectors
    xs3 = accumulate (fold (\(_, ty) -> add_idents_type ty)) selectors
  in ((xs1, xs2), xs3)
idents_of_stmt (TypeSynonym specs) =
  let
    xs1 = accumulate (fold (add_idents_typespec . fst)) specs
    xs3 = accumulate (fold (add_idents_type . snd)) specs
  in ((xs1, []), xs3)
idents_of_stmt (Definition sig (p, t)) =
  let
    (x1, xs3a) = idents_of_typesign sig
    xs3b = xs3a |> add_idents_term p |> add_idents_term t
  in (([x1], []), xs3b)
idents_of_stmt (Primrec sigs eqns) =
  let
    (xs1, xs3a) = map_split idents_of_typesign sigs
    xs3b = flat xs3a |> fold (\(_, ps, t) -> fold add_idents_term ps *> add_idents_term t) eqns
  in ((xs1, []), xs3b)
idents_of_stmt (Fun sigs eqns) =
  let
    (xs1, xs3a) = map_split idents_of_typesign sigs
    xs3b = flat xs3a |> fold (\(_, ps, t) -> fold add_idents_term ps *> add_idents_term t) eqns
  in ((xs1, []), xs3b)
idents_of_stmt (Class n superclasses sigs) =
  let
    x1 = ClassI n
    (xs2, xs3a) = map_split idents_of_typesign sigs
    xs3b = flat xs3a |> fold (insert . ClassI) superclasses
  in (([x1], xs2), xs3b)
idents_of_stmt (Instance n ty stmts) = -- this is only an approximation
  let
    xs3a = [ClassI n] |> add_idents_type ty
    (_, xs3b) = map_split idents_of_stmt stmts
    xs3 = fold insert (flat xs3b) xs3a
  in (([], []), xs3)
idents_of_stmt (Comment _) =
  (([], []), [])

{-data Module = Module ThyName [ThyName] [Stmt]
  deriving Show-}


topologize :: Ord b => (a -> (b, [b])) -> [a] -> [[a]]
topologize f xs = (map list_of_SCC . stronglyConnComp . map add_edges) xs
  where
    add_edges x = let (node, nodes) = f x in (x, node, nodes)
    list_of_SCC (Graph.AcyclicSCC x) = [x]
    list_of_SCC (Graph.CyclicSCC xs) = xs
