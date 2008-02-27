
module Importer.Mapping (initialGlobalEnv, AdaptionTable(..), adaptionTable) where

import List (intersperse, groupBy, sortBy)

import qualified Data.Map as Map

import Language.Haskell.Hsx

import Importer.LexEnv
import Importer.Utilities.Misc (wordsBy)
import Importer.Utilities.Hsk (string2HsName)

import Importer.Convert.Trivia (convert_trivia)

import qualified Importer.IsaSyntax as Isa


data OpKind = Function | InfixOp Assoc Int
  deriving Show

data Assoc = RightAssoc | LeftAssoc | NoneAssoc
  deriving Show

data AdaptionEntry = Haskell String OpKind String
                   | Isabelle String OpKind String
  deriving Show

data AdaptionTable = AdaptionTable [(HskIdentifier, IsaIdentifier)]

rawAdaptionTable 
    = [(Haskell  "Prelude.:" (InfixOp RightAssoc  5) "a -> [a] -> [a]",
        Isabelle "Prelude.#" (InfixOp RightAssoc  5) "a -> [a] -> [a]"),

       (Haskell  "Prelude.+"  (InfixOp LeftAssoc  7) "Int -> Int -> Int",
        Isabelle "Main.+"     (InfixOp LeftAssoc  7) "Int -> Int -> Int"),
       (Haskell  "Prelude.-"  (InfixOp LeftAssoc  7) "Int -> Int -> Int",
        Isabelle "Main.-"     (InfixOp LeftAssoc  7) "Int -> Int -> Int"),

       (Haskell  "Prelude.++" (InfixOp RightAssoc 5) "[a] -> [a] -> [a]",
        Isabelle "List.@"     (InfixOp RightAssoc 5) "[a] -> [a] -> [a]"),

       (Haskell  "Arrows.&&&" (InfixOp RightAssoc 5) "[a] -> [a] -> [a]",
        Isabelle "Foo.%%%"    (InfixOp RightAssoc 5) "[a] -> [a] -> [a]"),
       (Haskell  "Prelude.!!" (InfixOp RightAssoc 5) "[a] -> [a] -> [a]",
        Isabelle "List.!"     (InfixOp RightAssoc 5) "[a] -> [a] -> [a]")
      ]

adaptionTable :: AdaptionTable
adaptionTable 
    = AdaptionTable 
        $ map (\(hEntry, iEntry) 
                   -> (snd $ parseHaskellEntry hEntry, snd $ parseIsabelleEntry iEntry))
              rawAdaptionTable

initialGlobalEnv :: GlobalE
initialGlobalEnv 
    = mk_initialGlobalE (map (parseHaskellEntry . fst) rawAdaptionTable)


mk_initialGlobalE :: [(Module, HskIdentifier)] -> GlobalE
mk_initialGlobalE hskentries
    = HskGlobalEnv $ Map.fromList (map (\(m, hsks) -> (m, mk_initialModuleEnv (m, hsks)))
                                       (unzipAdaptionEntries hskentries))
    where unzipAdaptionEntries :: [(Module, HskIdentifier)] -> [(Module, [HskIdentifier])]
          unzipAdaptionEntries entries
              = map (\(m:_, hsks) -> (m, hsks)) 
                $ map unzip 
                  $ groupBy (\(m1,_) (m2,_) -> m1 == m2) 
                    $ sortBy (\(m1,_) (m2,_) -> m1 `compare` m2) entries

mk_initialModuleEnv :: (Module, [HskIdentifier]) -> ModuleE
mk_initialModuleEnv (m, hskidents)
    = HskModuleEnv m [] (mk_exports_list hskidents) (mk_initialLexEnv hskidents)
    where mk_exports_list idents = map (HsEVar . identifier2name) idents

mk_initialLexEnv :: [HskIdentifier] -> LexE
mk_initialLexEnv hskidents
    = HskLexEnv $ Map.fromListWith failDups (zip (map identifier2name hskidents) hskidents)
    where failDups a b
              = error ("Duplicate entries in the Adaption Table: " ++ show a ++ ", " ++ show b)


parseHaskellEntry :: AdaptionEntry -> (Module, HskIdentifier)
parseHaskellEntry (Haskell raw_identifier op raw_type)
     = let (modul, ident) = parseRawIdentifier raw_identifier
           modul' = Module modul
           ident' = string2HsName ident
       in (modul', makeHskIdentifier op modul' ident' (parseRawType raw_type))

parseRawIdentifier :: String -> (String, String)
parseRawIdentifier string
    = let parts      = wordsBy (== '.') string
          identifier = last parts
          modul      = concat $ intersperse "." (init parts)
      in (modul, identifier)

parseRawType :: String -> HsType
parseRawType string
    = let (ParseOk (HsModule _ _ _ _ [HsTypeSig _ _ typ])) 
              = parseFileContents ("foo :: " ++ string)
      in typ

makeHskIdentifier :: OpKind -> Module -> HsName -> HsType -> HskIdentifier
makeHskIdentifier Function m identifier t
    = HskFunction $ makeHskLexInfo m identifier t
makeHskIdentifier (InfixOp assoc prio) m identifier t
    = HskInfixOp (makeHskLexInfo m identifier t) (toHsAssoc assoc) prio

makeHskLexInfo :: Module -> HsName -> HsType -> HskLexInfo
makeHskLexInfo m identifier t
    = HskLexInfo { identifier = UnQual identifier,
                    typeOf    = Just t,
                    moduleOf  = m }

toHsAssoc :: Assoc -> HsAssoc
toHsAssoc RightAssoc = HsAssocRight
toHsAssoc LeftAssoc  = HsAssocLeft
toHsAssoc NoneAssoc  = HsAssocNone


parseIsabelleEntry :: AdaptionEntry -> (Isa.Theory, IsaIdentifier)
parseIsabelleEntry (Isabelle raw_identifier op raw_type)
     = let (thy, ident) = parseRawIdentifier raw_identifier
           thy'   = Isa.Theory thy
           ident' = Isa.Name ident
       in (thy', makeIsaIdentifier op thy' ident' (convert_trivia (parseRawType raw_type)))

makeIsaIdentifier :: OpKind -> Isa.Theory -> Isa.Name -> Isa.Type -> IsaIdentifier
makeIsaIdentifier Function thy identifier t
    = IsaFunction $ makeIsaLexInfo thy identifier t
makeIsaIdentifier (InfixOp assoc prio) thy identifier t
    = IsaInfixOp (makeIsaLexInfo thy identifier t) (toIsaAssoc assoc) prio

makeIsaLexInfo :: Isa.Theory -> Isa.Name -> Isa.Type -> IsaLexInfo
makeIsaLexInfo thy identifier t
    = IsaLexInfo {  _identifier =  identifier,
                    _typeOf     =  t,
                    _theoryOf   =  thy }

toIsaAssoc :: Assoc -> Isa.Assoc
toIsaAssoc RightAssoc = Isa.AssocRight
toIsaAssoc LeftAssoc  = Isa.AssocLeft
toIsaAssoc NoneAssoc  = Isa.AssocNone
