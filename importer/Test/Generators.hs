{-# OPTIONS_GHC -fglasgow-exts -XTemplateHaskell #-}

{-|
  This module provides data generators as used by /QuickCheck/ for types from external
  libraries. Data generators of types defined in this application should be defined
  locally with the definition of the type.
-}

module Importer.Test.Generators where

import Importer.Test.Utils
import Test.QuickCheck
import Test.QuickCheck.Arbitrary
import Language.Haskell.TH
import Control.Monad
import Control.Monad.State
import Language.Haskell.Exts.Syntax
import Language.Haskell.Exts.Pretty
import Data.Set (Set)
import qualified Data.Set as Set hiding (Set)

-- some example declarations
{-
instance Arbitrary SrcLoc where
    arbitrary = liftM3 SrcLoc arbitrary arbitrary arbitrary
    shrink (SrcLoc a b c) = [SrcLoc a' b' c' | a' <- shrink a, b' <- shrink b, c' <- shrink c]

instance Arbitrary SrcLoc where
    arbitrary = sized $ \ size -> let newSize = ((size - 1) `div` 3) `max` 0 in
                do a <- resize newSize arbitrary 
                   b <- resize newSize arbitrary
                   c <- resize newSize arbitrary
                   return $ SrcLoc a b c
    shrink (SrcLoc a b c) = [SrcLoc a' b' c' | a' <- shrink a, b' <- shrink b, c' <- shrink c]
-}

instance (Arbitrary a , Ord a) => Arbitrary (Set a) where
    arbitrary = liftM Set.fromList  arbitrary 


$(deriveArbitrary_shrink ''SrcLoc
  [|
     do size <- sized (\ n -> elements [0..n])
        let symbol = elements $ ['a'..'z'] ++ ['A'..'Z'] ++ "._-"
        let sep = return '/'
        let single = frequency [(5,symbol),(1,sep)]
        file <- replicateM size single
        NonNegative line <- arbitrary
        NonNegative col <- arbitrary
        return $ SrcLoc file line col
   |])

{-|
  This generator only generates type signatures
-}

$(deriveGenForConstrs "typeSigDecl" ['HsTypeSig])

$(deriveArbitraryAll [
--   ''SrcLoc,
   ''Module,
   ''HsSpecialCon,
   ''HsQName,
   ''HsName,
   ''HsIPName,
   ''HsQOp,
   ''HsOp,
   ''HsCName,
   ''HsExportSpec,
   ''HsImportDecl,
   ''HsImportSpec,
   ''HsAssoc,
   ''DataOrNew,
   ''HsConDecl,
   ''HsGadtDecl,
   ''HsQualConDecl,
   ''HsMatch,
   ''HsIPBind,
   ''HsBinds,
   ''HsDecl,
   ''HsModule,
   ''HsClassDecl,
   ''HsInstDecl,
   ''HsBangType,
   ''HsRhs,
   ''HsGuardedRhs,
   ''HsType,
   ''HsBoxed,
   ''HsTyVarBind,
   ''HsKind,
   ''HsFunDep,
   ''HsAsst,
   ''HsLiteral,
   ''HsExp,
   ''HsXName,
   ''HsXAttr,
   ''HsBracket,
   ''HsSplice,
   ''HsSafety,
   ''HsCallConv,
   ''HsPat,
   ''HsPXAttr,
   ''HsRPatOp,
   ''HsRPat,
   ''HsPatField,
   ''HsStmt,
   ''HsFieldUpdate,
   ''HsAlt,
   ''HsGuardedAlts,
   ''HsGuardedAlt
  ])
