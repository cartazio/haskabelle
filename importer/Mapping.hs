{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen
-}

module Importer.Mapping (initialGlobalEnv, AdaptionTable(..), adaptionTable) where

import List (intersperse, groupBy, sortBy)

import qualified Data.Map as Map

import Language.Haskell.Hsx

import Importer.Utilities.Misc (wordsBy, prettyShow', trace)
import Importer.Utilities.Hsk (string2HsName)

import qualified Importer.LexEnv as Env

import qualified Importer.IsaSyntax as Isa

data OpKind = Variable | Function | InfixOp Assoc Int 
            | Type
  deriving Show

data Assoc = RightAssoc | LeftAssoc | NoneAssoc
  deriving Show

data AdaptionEntry = Haskell String OpKind String
                   | Isabelle String OpKind String
  deriving Show

data AdaptionTable = AdaptionTable [(Env.Identifier, Env.Identifier)]
  deriving Show

rawAdaptionTable 
    = [
       (Haskell  "Prelude.:" (InfixOp RightAssoc  5) "a -> [a] -> [a]",
        Isabelle "Prelude.#" (InfixOp RightAssoc  5) "a -> [a] -> [a]"),

       (Haskell  "Prelude.+"  (InfixOp LeftAssoc  7) "Int -> Int -> Int",
        Isabelle "Main.+"     (InfixOp LeftAssoc  7) "Int -> Int -> Int"),
       (Haskell  "Prelude.-"  (InfixOp LeftAssoc  7) "Int -> Int -> Int",
        Isabelle "Main.-"     (InfixOp LeftAssoc  7) "Int -> Int -> Int"),

       (Haskell  "Prelude.<=" (InfixOp LeftAssoc  4) "Int -> Int -> Bool",
        Isabelle "Prelude.<=" (InfixOp LeftAssoc  4) "Int -> Int -> Bool"),

--        (Haskell "Prelude.List"   Type "Prelude.List", 
--         Isabelle "List.list"     Type "List.list"),
--        (Haskell "Prelude.[]"     Function "List a", 
--         Isabelle "List.list.Nil" Function "List a"),
--       (Haskell "Prelude.:" (InfixOp RightAssoc 65) "'a -> 'a list -> 'a list", Isabelle "#" (InfixOp RightAssoc 65) "'a -> 'a list -> 'a list"),
       (Haskell  "Prelude.head" Function "[a] -> a",
        Isabelle "List.hd"   Function "[a] -> a"),
       (Haskell  "Prelude.tail" Function "[a] -> a",
        Isabelle "List.tl"   Function "[a] -> a"),
       (Haskell  "Prelude.++"   (InfixOp RightAssoc 5) "[a] -> [a] -> [a]",
        Isabelle "List.@"       (InfixOp RightAssoc 65) "[a] -> [a] -> [a]"),

--        (Haskell "Prelude.Maybe"         Type "Prelude.Maybe", 
--         Isabelle "Datatype.option"      Type "Datatype.option"),
--        (Haskell "Prelude.Nothing"       Function "Maybe a", 
--         Isabelle "Datatype.option.None" Function "Maybe a"),
--        (Haskell "Prelude.Just"          Function "a -> Maybe a", 
--         Isabelle "Datatype.option.Some" Function "a -> Maybe a"),

       (Haskell  "Prelude.Bool"  Type "Bool",
        Isabelle "Prelude.bool"  Type "Bool"),
       (Haskell  "Prelude.True"  Function "Bool",
        Isabelle "Prelude.True"  Function "Bool"),
       (Haskell  "Prelude.False" Function "Bool",
        Isabelle "Prelude.False" Function "Bool"),
       (Haskell "Prelude.&&" (InfixOp RightAssoc 3) "Bool -> Bool -> Bool", 
        Isabelle "&" (InfixOp RightAssoc 35) "Bool -> Bool -> Bool"),
       (Haskell "Prelude.||" (InfixOp RightAssoc 2) "Bool -> Bool -> Bool", 
        Isabelle "|" (InfixOp RightAssoc 30) "Bool -> Bool -> Bool")
      ]

-- rawAdaptionTable = [(Haskell "Prelude.Bool" Type "Prelude.Bool", Isabelle "bool" Type "bool"),

--   (Haskell "Prelude.True" Function "bool", Isabelle "True" Function "bool"),
--   (Haskell "Prelude.False" Function "bool", Isabelle "False" Function "bool"),


-- ]


adaptionTable :: AdaptionTable
adaptionTable 
    = AdaptionTable 
        $ map (\(hEntry, iEntry) -> (parseEntry hEntry, parseEntry iEntry))
              rawAdaptionTable 

initialGlobalEnv :: Env.GlobalE
initialGlobalEnv 
    = Env.makeGlobalEnv importNothing exportAll (hskIdentifiers adaptionTable)
    where importNothing = const []
          exportAll     = const True
          hskIdentifiers (AdaptionTable mapping) = map fst mapping


parseEntry :: AdaptionEntry -> Env.Identifier

parseEntry (Haskell raw_identifier op raw_type)
     = let (moduleID, identifierID) = parseRawIdentifier raw_identifier
       in makeIdentifier op moduleID identifierID (parseRawType raw_type)
parseEntry (Isabelle raw_identifier op raw_type)
     = let (moduleID, identifierID) = parseRawIdentifier raw_identifier
       in makeIdentifier op moduleID identifierID (parseRawType raw_type)

parseRawIdentifier :: String -> (String, String)
parseRawIdentifier string
    = let parts      = wordsBy (== '.') string
          identifier = last parts
          modul      = concat $ intersperse "." (init parts)
      in (modul, identifier)

parseRawType :: String -> Env.EnvType
parseRawType _ = Env.EnvTyNone
-- parseRawType string
--     = -- trace ("string = " ++ show string) $
--       let (ParseOk (HsModule _ _ _ _ [HsTypeSig _ _ hstyp])) 
--               = parseFileContents ("foo :: " ++ string)
--       in Env.fromHsk hstyp


makeIdentifier :: OpKind -> Env.ModuleID -> Env.IdentifierID -> Env.EnvType -> Env.Identifier
makeIdentifier Variable m identifier t
    = Env.Variable $ Env.makeLexInfo m identifier t
makeIdentifier Function m identifier t
    = Env.Function $ Env.makeLexInfo m identifier t
makeIdentifier (InfixOp assoc prio) m identifier t
    = Env.InfixOp (Env.makeLexInfo m identifier t) (transformAssoc assoc) prio
makeIdentifier Type m identifier t
    = Env.Type (Env.makeLexInfo m identifier t) []

transformAssoc :: Assoc -> Env.EnvAssoc
transformAssoc RightAssoc = Env.EnvAssocRight
transformAssoc LeftAssoc  = Env.EnvAssocLeft
transformAssoc NoneAssoc  = Env.EnvAssocNone
