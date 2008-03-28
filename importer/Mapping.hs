
module Importer.Mapping (initialGlobalEnv, AdaptionTable(..), adaptionTable) where

import List (intersperse, groupBy, sortBy)

import qualified Data.Map as Map

import Language.Haskell.Hsx

import Importer.Utilities.Misc (wordsBy, prettyShow')
import Importer.Utilities.Hsk (string2HsName)

import qualified Importer.LexEnv as Env

import Importer.Convert.Trivia (convert_trivia)

import qualified Importer.IsaSyntax as Isa


data OpKind = Variable | Function | InfixOp Assoc Int | Type
  deriving Show

data Assoc = RightAssoc | LeftAssoc | NoneAssoc
  deriving Show

data AdaptionEntry = Haskell String OpKind String
                   | Isabelle String OpKind String
  deriving Show

data AdaptionTable = AdaptionTable [(Env.Identifier, Env.Identifier)]

rawAdaptionTable 
    = [(Haskell  "Prelude.:" (InfixOp RightAssoc  5) "a -> [a] -> [a]",
        Isabelle "Prelude.#" (InfixOp RightAssoc  5) "a -> [a] -> [a]"),

       (Haskell  "Prelude.+"  (InfixOp LeftAssoc  7) "Int -> Int -> Int",
        Isabelle "Main.+"     (InfixOp LeftAssoc  7) "Int -> Int -> Int"),
       (Haskell  "Prelude.-"  (InfixOp LeftAssoc  7) "Int -> Int -> Int",
        Isabelle "Main.-"     (InfixOp LeftAssoc  7) "Int -> Int -> Int"),

       (Haskell  "Prelude.<=" (InfixOp LeftAssoc  4) "Int -> Int -> Bool",
        Isabelle "Prelude.<=" (InfixOp LeftAssoc  4) "Int -> Int -> Bool"),

       (Haskell  "Prelude.head" Function "[a] -> a",
        Isabelle "Prelude.hd"   Function "[a] -> a"),
       (Haskell  "Prelude.tail" Function "[a] -> a",
        Isabelle "Prelude.tl"   Function "[a] -> a"),
       (Haskell  "Prelude.++" (InfixOp RightAssoc 5) "[a] -> [a] -> [a]",
        Isabelle "List.@"     (InfixOp RightAssoc 5) "[a] -> [a] -> [a]"),

       (Haskell  "Prelude.Bool"  Type "Bool",
        Isabelle "Prelude.bool"  Type "bool"),
       (Haskell  "Prelude.True"  Function "Bool",
        Isabelle "Prelude.True"  Function "bool"),
       (Haskell  "Prelude.False" Function "Bool",
        Isabelle "Prelude.False" Function "bool")
      ]

adaptionTable :: AdaptionTable
adaptionTable 
    = AdaptionTable 
        $ map (\(hEntry, iEntry) -> (parseEntry hEntry, parseEntry iEntry))
              rawAdaptionTable

initialGlobalEnv :: Env.GlobalE
initialGlobalEnv 
    = Env.makeGlobalEnv exportAll (hskIdentifiers adaptionTable)
    where exportAll = const True
          hskIdentifiers (AdaptionTable mapping) = map fst mapping

-- mk_initialGlobalE :: [(Module, HskIdentifier)] -> GlobalE
-- mk_initialGlobalE hskentries
--     = HskGlobalEnv $ Map.fromList (map (\(m, hsks) -> (m, mk_initialModuleEnv (m, hsks)))
--                                        (unzipAdaptionEntries hskentries))
--     where unzipAdaptionEntries :: [(Module, HskIdentifier)] -> [(Module, [HskIdentifier])]
--           unzipAdaptionEntries entries
--               = map (\(m:_, hsks) -> (m, hsks)) 
--                 $ map unzip 
--                   $ groupBy (\(m1,_) (m2,_) -> m1 == m2) 
--                     $ sortBy (\(m1,_) (m2,_) -> m1 `compare` m2) entries

-- mk_initialModuleEnv :: (Module, [HskIdentifier]) -> ModuleE
-- mk_initialModuleEnv (m, hskidents)
--     = HskModuleEnv m [] (mk_exports_list hskidents) (mk_initialLexEnv hskidents)
--     where mk_exports_list idents = map (HsEVar . identifier2name) idents

-- mk_initialLexEnv :: [HskIdentifier] -> LexE
-- mk_initialLexEnv hskidents
--     = HskLexEnv $ Map.fromListWith failDups (zip (map identifier2name hskidents) hskidents)
--     where failDups a b
--               = error ("Duplicate entries in the Adaption Table: " 
--                        ++ prettyShow' "a" a ++ "\n" ++ prettyShow' "b" b)


parseEntry :: AdaptionEntry -> Env.Identifier
parseEntry (Haskell raw_identifier op raw_type)
     = let (moduleID, identifierID) = parseRawIdentifier raw_identifier
       in  (makeIdentifier op moduleID identifierID (parseRawType raw_type))
parseEntry (Isabelle raw_identifier op raw_type)
     = let (moduleID, identifierID) = parseRawIdentifier raw_identifier
       in  (makeIdentifier op moduleID identifierID (parseRawType raw_type))

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
