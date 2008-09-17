{-# OPTIONS_GHC -fglasgow-exts -XTemplateHaskell #-}

module Importer.Test.Generators where

import Importer.Test.Utils
import Test.QuickCheck
import Language.Haskell.TH
import Control.Monad
import Language.Haskell.Exts.Syntax
import Language.Haskell.Exts.Pretty

-- some example declarations
{-
instance Arbitrary SrcLoc where
    arbitrary = liftM3 SrcLoc arbitrary arbitrary arbitrary
    shrink (SrcLoc a b c) = [SrcLoc a' b' c' | a' <- shrink a, b' <- shrink b, c' <- shrink c]
-}


$(deriveArbitraryAll [
   ''SrcLoc,
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