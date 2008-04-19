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

data OpKind = Variable | Function | InfixOp Assoc Int | Type
  deriving Show

data Assoc = RightAssoc | LeftAssoc | NoneAssoc
  deriving Show

data AdaptionEntry = Haskell String OpKind
                   | Isabelle String OpKind
  deriving Show

data AdaptionTable = AdaptionTable [(Env.Identifier, Env.Identifier)]
  deriving Show

rawAdaptionTable 
    = [
       (Haskell "Prelude.+"  (InfixOp LeftAssoc  7),    Isabelle "Main.+"        (InfixOp LeftAssoc  7)),
       (Haskell "Prelude.-"  (InfixOp LeftAssoc  7),    Isabelle "Main.-"        (InfixOp LeftAssoc  7)),

       (Haskell "Prelude.<=" (InfixOp LeftAssoc  4),    Isabelle "Prelude.<="    (InfixOp LeftAssoc  4)),

       (Haskell "Prelude.List" Type,                    Isabelle "List.list"     Type),
       (Haskell "Prelude.[]"   Function,                Isabelle "List.list.Nil" Function),
       (Haskell "Prelude.:"    (InfixOp RightAssoc 65), Isabelle "#"             (InfixOp RightAssoc 65)),
       (Haskell "Prelude.head" Function,                Isabelle "List.hd"       Function),
       (Haskell "Prelude.tail" Function,                Isabelle "List.tl"       Function),
       (Haskell "Prelude.++"   (InfixOp RightAssoc 5),  Isabelle "List.@"        (InfixOp RightAssoc 65)),

       (Haskell "Prelude.Maybe"   Type,                 Isabelle "Datatype.option" Type),
       (Haskell "Prelude.Nothing" Function,             Isabelle "Datatype.option.None" Function),
       (Haskell "Prelude.Just"    Function,             Isabelle "Datatype.option.Some" Function),

       (Haskell "Prelude.Bool"  Type,                   Isabelle "Prelude.bool"  Type),
       (Haskell "Prelude.True"  Function,               Isabelle "Prelude.True"  Function),
       (Haskell "Prelude.False" Function,               Isabelle "Prelude.False" Function),
       (Haskell "Prelude.&&"    (InfixOp RightAssoc 3), Isabelle "&"             (InfixOp RightAssoc 35)),
       (Haskell "Prelude.||"    (InfixOp RightAssoc 2), Isabelle "|"             (InfixOp RightAssoc 30))
      ]


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

parseEntry (Haskell raw_identifier op)
     = let (moduleID, identifierID) = parseRawIdentifier raw_identifier
       in makeIdentifier op moduleID identifierID Env.EnvTyNone
parseEntry (Isabelle raw_identifier op)
     = let (moduleID, identifierID) = parseRawIdentifier raw_identifier
       in makeIdentifier op moduleID identifierID Env.EnvTyNone

parseRawIdentifier :: String -> (String, String)
parseRawIdentifier string
    = let parts      = wordsBy (== '.') string
          identifier = last parts
          modul      = concat $ intersperse "." (init parts)
      in (modul, identifier)

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
