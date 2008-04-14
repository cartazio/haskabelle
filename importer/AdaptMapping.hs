-- THIS IS A GENERATED FILE - DO NOT EDIT!
-- $Id$

module Importer.AdaptMapping where

import Importer.AdaptTable

rawAdaptionTable = [(Haskell "Prelude.Bool" Type "Prelude.Bool", Isabelle "bool" Type "bool"),
  (Haskell "Prelude.List" Type "Prelude.List", Isabelle "List.list" Type "List.list"),
  (Haskell "Prelude.Maybe" Type "Prelude.Maybe", Isabelle "Datatype.option" Type "Datatype.option"),
  (Haskell "Prelude.True" Function "bool", Isabelle "True" Function "bool"),
  (Haskell "Prelude.False" Function "bool", Isabelle "False" Function "bool"),
  (Haskell "Prelude.&&" Function "bool => bool => bool", Isabelle "op &" Function "bool => bool => bool"),
  (Haskell "Prelude.||" Function "bool => bool => bool", Isabelle "op |" Function "bool => bool => bool"),
  (Haskell "Prelude.[]" Function "'a list", Isabelle "List.list.Nil" Function "'a list"),
  (Haskell "Prelude.:" Function "'a => 'a list => 'a list", Isabelle "List.list.Cons" Function "'a => 'a list => 'a list"),
  (Haskell "Prelude.head" Function "'a list => 'a", Isabelle "List.hd" Function "'a list => 'a"),
  (Haskell "Prelude.tail" Function "'a list => 'a list", Isabelle "List.tl" Function "'a list => 'a list"),
  (Haskell "Prelude.++" Function "'a list => 'a list => 'a list", Isabelle "List.append" Function "'a list => 'a list => 'a list"),
  (Haskell "Prelude.Nothing" Function "'a option", Isabelle "Datatype.option.None" Function "'a option"),
  (Haskell "Prelude.Just" Function "'a ~=> 'a", Isabelle "Datatype.option.Some" Function "'a ~=> 'a")]