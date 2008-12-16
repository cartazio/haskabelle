{-# LANGUAGE TemplateHaskell #-}

{-| Author: Patrick Bahr, NICTA

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

instance Arbitrary HsReify where
    arbitrary = error "Arbitrary HsReify"

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

{-|
  HsBinds
-}
$(deriveArbitraryForConstrs ['HsBDecls])

{-|
  HsLiteral
-}
$(deriveArbitraryForConstrs ['HsChar,'HsString, 'HsInt])

{-|
  HsPat
-}
$(deriveArbitraryForConstrs [
   'HsPVar,
   'HsPLit,
   'HsPNeg,
   'HsPInfixApp,
   'HsPApp,
   'HsPTuple,
   'HsPList,
   'HsPParen,
   'HsPRec,
   'HsPAsPat,
   'HsPWildCard
--   'HsPIrrPat,
--   'HsPatTypeSig
  ])

{-|
  HsClassDecl
-}
$(deriveArbitraryForConstrs [
   'HsClsDecl
--   'HsClsDataFam,
--   'HsClsTyFam,
--   'HsClsTyDef
   ])

{-|
  HsExp
-}
$(deriveArbitraryForConstrs [
   'HsVar,
   'HsIPVar,
   'HsCon,
   'HsLit,
   'HsInfixApp,
   'HsApp,
   'HsNegApp,
   'HsLambda,
   'HsLet,
   'HsDLet,
   'HsWith,
   'HsIf,
   'HsCase,
   'HsDo,
   'HsMDo,
   'HsTuple,
   'HsList,
   'HsParen,
   'HsLeftSection,
   'HsRightSection,
   'HsRecConstr,
   'HsRecUpdate,
   'HsEnumFrom,
   'HsEnumFromTo,
   'HsEnumFromThen,
   'HsEnumFromThenTo,
   'HsListComp,
   'HsExpTypeSig
--   'HsAsPat,
--   'HsWildCard,
--   'HsIrrPat,

-- Post-ops for parsing left sections and regular patterns. Not to be left in the final tree.
--   'HsPostOp,

-- HaRP
--   'HsSeqRP,
--   'HsGuardRP,
--   'HsEitherRP,
--   'HsCAsRP,
    
-- Template Haskell
--   'HsVarQuote,
--   'HsTypQuote,
--   'HsBracketExp,
--   'HsSpliceExp,
    
-- Hsx
--   'HsXTag,
--   'HsXETag,
--   'HsXPcdata,
--   'HsXExpTag,
--   'HsXRPats
   ])

$(deriveArbitraryAll [
--   ''SrcLoc,
   ''HsRhs,
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
   ''HsDecl,
   ''HsModule,
   ''HsInstDecl,
   ''HsBangType,
   ''HsGuardedRhs,
   ''HsType,
   ''HsBoxed,
   ''HsTyVarBind,
   ''HsKind,
   ''HsFunDep,
   ''HsAsst,
   ''HsXName,
   ''HsXAttr,
   ''HsBracket,
   ''HsSplice,
   ''HsSafety,
   ''HsCallConv,
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
