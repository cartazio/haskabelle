{-| Author: Tobias C. Rittweiler, TU Muenchen

Auxiliary.
-}

module Importer.Utilities.Isa (prettyShow, prettyShow') where

import Importer.Library
import qualified Importer.AList as AList

import Maybe (fromMaybe)
import Control.Monad.State (runState, get, put, foldM)
import Data.Generics.Biplate (universeBi)

import qualified Language.Haskell.Exts as Hsx
import qualified Importer.Isa as Isa


prettyShow' prefix obj = let str = prefix ++ " = " ++ show obj
                             (Hsx.ParseOk (Hsx.Module _ _ _ _ _ _ decls)) 
                                 = Hsx.parseModule str
                         in concatMap Hsx.prettyPrint decls

prettyShow obj = prettyShow' "foo" obj
