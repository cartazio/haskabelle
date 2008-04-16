{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen
-}

module Importer.Mapping (initialGlobalEnv, AdaptionTable(..), adaptionTable) where

import List (intersperse, groupBy, sortBy)

import qualified Data.Map as Map

import Language.Haskell.Hsx

import Importer.Utilities.Misc (wordsBy, prettyShow')
import Importer.Utilities.Hsk (string2HsName)

import qualified Importer.LexEnv as Env

import Importer.Convert.Trivia (convert_trivia)

import qualified Importer.IsaSyntax as Isa

rawAdaptionTable 
    = [
       (Haskell  "Prelude.:" "a -> [a] -> [a]" (InfixOp RightAssoc  5),
        Isabelle "Prelude.#" "a -> [a] -> [a]" (InfixOp RightAssoc  5)),

       (Haskell  "Prelude.+"  "Int -> Int -> Int" (InfixOp LeftAssoc  7),
        Isabelle "Main.+"     "Int -> Int -> Int" (InfixOp LeftAssoc  7)),
       (Haskell  "Prelude.-"  "Int -> Int -> Int" (InfixOp LeftAssoc  7),
        Isabelle "Main.-"     "Int -> Int -> Int" (InfixOp LeftAssoc  7)),

       (Haskell  "Prelude.<=" "Int -> Int -> Bool" (InfixOp LeftAssoc  4),
        Isabelle "Prelude.<=" "Int -> Int -> Bool" (InfixOp LeftAssoc  4)),

       (Haskell  "Prelude.head" "[a] -> a" Function,
        Isabelle "Prelude.hd"   "[a] -> a" Function),
       (Haskell  "Prelude.tail" "[a] -> a" Function,
        Isabelle "Prelude.tl"   "[a] -> a" Function),
       (Haskell  "Prelude.++"   "[a] -> [a] -> [a]" (InfixOp RightAssoc 5),
        Isabelle "List.@"       "[a] -> [a] -> [a]" (InfixOp RightAssoc 5)),

       (Haskell  "Prelude.Bool"  "Bool" (Data [Constructor "True" "Bool", Constructor "False" "Bool"]),
        Isabelle "Prelude.bool"  "bool" (Data [Constructor "True" "bool", Constructor "False" "bool"]))
      ]

adaptionTable :: AdaptionTable
adaptionTable 
    = AdaptionTable 
        $ do (hEntry, iEntry) <- rawAdaptionTable 
             zip (parseEntry hEntry) (parseEntry iEntry)

initialGlobalEnv :: Env.GlobalE
initialGlobalEnv 
    = Env.makeGlobalEnv importNothing exportAll (hskIdentifiers adaptionTable)
    where importNothing = const []
          exportAll     = const True
          hskIdentifiers (AdaptionTable mapping) = map fst mapping


parseEntry :: AdaptionEntry -> [Env.Identifier]

parseEntry (Haskell raw_identifier raw_type op)
     = let (moduleID, identifierID) = parseRawIdentifier raw_identifier
       in  (makeIdentifiers op moduleID identifierID (parseRawType raw_type))
parseEntry (Isabelle raw_identifier raw_type op)
     = let (moduleID, identifierID) = parseRawIdentifier raw_identifier
       in  (makeIdentifiers op moduleID identifierID (parseRawType raw_type))

parseRawIdentifier :: String -> (String, String)
parseRawIdentifier string
    = let parts      = wordsBy (== '.') string
          identifier = last parts
          modul      = concat $ intersperse "." (init parts)
      in (modul, identifier)

parseRawType :: String -> Env.EnvType
parseRawType string
    = let (ParseOk (HsModule _ _ _ _ [HsTypeSig _ _ hstyp])) 
              = parseFileContents ("foo :: " ++ string)
      in Env.fromHsk hstyp


makeIdentifiers :: OpKind -> Env.ModuleID -> Env.IdentifierID -> Env.EnvType -> [Env.Identifier]
makeIdentifiers Variable m identifier t
    = [Env.Variable $ Env.makeLexInfo m identifier t]
makeIdentifiers Function m identifier t
    = [Env.Function $ Env.makeLexInfo m identifier t]
makeIdentifiers (InfixOp assoc prio) m identifier t
    = [Env.InfixOp (Env.makeLexInfo m identifier t) (transformAssoc assoc) prio]
makeIdentifiers (Data cs) m identifierID t
    = let constructors = map (makeConstructor m) cs 
      in [Env.Type (Env.makeLexInfo m identifierID t) constructors] ++ constructors

makeConstructor m (Constructor identifier raw_type)
    = (\[x] -> x) $ makeIdentifiers Function m identifier (parseRawType raw_type)

transformAssoc :: Assoc -> Env.EnvAssoc
transformAssoc RightAssoc = Env.EnvAssocRight
transformAssoc LeftAssoc  = Env.EnvAssocLeft
transformAssoc NoneAssoc  = Env.EnvAssocNone
