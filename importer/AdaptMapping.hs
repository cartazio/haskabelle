-- THIS IS A GENERATED FILE - DO NOT EDIT!
-- $Id$

module Importer.AdaptMapping where

import Importer.AdaptTable

rawAdaptionTable = [(Haskell "Prelude.Bool" Type "Prelude.Bool", Isabelle "bool" Type "bool"),
  (Haskell "Prelude.List" Type "Prelude.List", Isabelle "List.list" Type "List.list"),
  (Haskell "Prelude.Maybe" Type "Prelude.Maybe", Isabelle "Datatype.option" Type "Datatype.option"),
  (Haskell "Prelude.True" Function "bool", Isabelle "True" Function "bool"),
  (Haskell "Prelude.False" Function "bool", Isabelle "False" Function "bool"),
  (Haskell "Prelude.&&" (InfixOp RightAssoc 35) "bool => bool => bool", Isabelle "&" (InfixOp RightAssoc 35) "bool => bool => bool"),
  (Haskell "Prelude.||" (InfixOp RightAssoc 30) "bool => bool => bool", Isabelle "|" (InfixOp RightAssoc 30) "bool => bool => bool"),
  (Haskell "Prelude.[]" Function "'a list", Isabelle "List.list.Nil" Function "'a list"),
  (Haskell "Prelude.:" (InfixOp RightAssoc 65) "'a => 'a list => 'a list", Isabelle "#" (InfixOp RightAssoc 65) "'a => 'a list => 'a list"),
  (Haskell "Prelude.head" Function "'a list => 'a", Isabelle "List.hd" Function "'a list => 'a"),
  (Haskell "Prelude.tail" Function "'a list => 'a list", Isabelle "List.tl" Function "'a list => 'a list"),
  (Haskell "Prelude.++" (InfixOp RightAssoc 65) "'a list => 'a list => 'a list", Isabelle "@" (InfixOp RightAssoc 65) "'a list => 'a list => 'a list"),
  (Haskell "Prelude.Nothing" Function "'a option", Isabelle "Datatype.option.None" Function "'a option"),
  (Haskell "Prelude.Just" Function "'a ~=> 'a", Isabelle "Datatype.option.Some" Function "'a ~=> 'a")]
