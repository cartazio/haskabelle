{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen
-}

module Importer.Adapt.Mapping 
    (AdaptionTable(..), adaptionTable, makeGlobalEnv_FromAdaptionTable) 
where

import List (intersperse, groupBy, sortBy)

import qualified Data.Map as Map

import Language.Haskell.Hsx

import Importer.Utilities.Misc (wordsBy, prettyShow', trace)
import Importer.Utilities.Hsk (string2HsName)

import qualified Importer.LexEnv as Env

import qualified Importer.IsaSyntax as Isa

import Importer.Adapt.Common

import Importer.Adapt.Raw (raw_adaption_table)

data AdaptionTable = AdaptionTable [(Env.Identifier, Env.Identifier)]
  deriving Show

adaptionTable :: AdaptionTable
adaptionTable 
    = AdaptionTable 
        $ map (\(hEntry, iEntry) -> (parseEntry hEntry, parseEntry iEntry))
              raw_adaption_table 

makeGlobalEnv_FromAdaptionTable :: AdaptionTable -> Env.GlobalE
makeGlobalEnv_FromAdaptionTable adaptionTable
    = Env.makeGlobalEnv importNothing exportAll (hskIdentifiers adaptionTable)
    where importNothing = const []
          exportAll     = const True
          hskIdentifiers (AdaptionTable mapping) = map fst mapping


parseEntry :: AdaptionEntry -> Env.Identifier

parseEntry (Haskell raw_identifier op)
    = let (moduleID, identifierID) = parseRawIdentifier raw_identifier
      in makeIdentifier op moduleID identifierID Env.EnvTyNone
parseEntry (Isabelle raw_identifier op)
    -- the raw identifier may look like "Datatype.option.None", where
    -- "Datatype" is the ModuleID, and "None" is the real identifier,
    -- and "option" basically noisy garbage.
    = let (moduleID, identifierID) = parseRawIdentifier raw_identifier
          moduleID'                = (case wordsBy (== '.') moduleID of 
                                        []  -> moduleID
                                        m:_ -> m)
      in makeIdentifier op moduleID' identifierID Env.EnvTyNone

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
makeIdentifier (Op prio) m identifier t
    = Env.Op (Env.makeLexInfo m identifier t) prio
makeIdentifier (InfixOp assoc prio) m identifier t
    = Env.InfixOp (Env.makeLexInfo m identifier t) (transformAssoc assoc) prio
makeIdentifier Type m identifier t
    = Env.Type (Env.makeLexInfo m identifier t) []

transformAssoc :: Assoc -> Env.EnvAssoc
transformAssoc RightAssoc = Env.EnvAssocRight
transformAssoc LeftAssoc  = Env.EnvAssocLeft
transformAssoc NoneAssoc  = Env.EnvAssocNone
