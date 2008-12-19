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

$(deriveGenForConstrs "typeSigDecl" ['Hs.TypeSig])

{-|
  Hs.Binds
-}
$(deriveArbitraryForConstrs ['Hs.BDecls])

{-|
  HsLiteral
-}
$(deriveArbitraryForConstrs ['HsChar,'HsString, 'HsInt])

{-|
  Hs.Pat
-}
$(deriveArbitraryForConstrs [
   'Hs.PVar,
   'Hs.PLit,
   'Hs.PNeg,
   'Hs.PInfixApp,
   'Hs.PApp,
   'Hs.PTuple,
   'Hs.PList,
   'Hs.PParen,
   'Hs.PRec,
   'Hs.PAsPat,
   'Hs.PWildCard
--   'HsPIrrPat,
--   'Hs.PatTypeSig
  ])

{-|
  Hs.ClassDecl
-}
$(deriveArbitraryForConstrs [
   'Hs.ClsDecl
--   'Hs.ClsDataFam,
--   'Hs.ClsTyFam,
--   'Hs.ClsTyDef
   ])

{-|
  Hs.Exp
-}
$(deriveArbitraryForConstrs [
   'Hs.Var,
   'HsIPVar,
   'Hs.Con,
   'HsLit,
   'Hs.InfixApp,
   'Hs.App,
   'HsNegApp,
   'Hs.Lambda,
   'Hs.Let,
   'HsDLet,
   'HsWith,
   'Hs.If,
   'Hs.Case,
   'HsDo,
   'Hs.MDo,
   'Hs.Tuple,
   'Hs.List,
   'HsParen,
   'Hs.LeftSection,
   'Hs.RightSection,
   'HsRecConstr,
   'HsRecUpdate,
   'HsEnumFrom,
   'HsEnumFromTo,
   'HsEnumFromThen,
   'HsEnumFromThenTo,
   'Hs.ListComp,
   'Hs.ExpTypeSig
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
--   'Hs.VarQuote,
--   'Hs.TypQuote,
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
   ''Hs.Rhs,
   ''Hs.ModuleName,
   ''Hs.SpecialCon,
   ''Hs.QName,
   ''Hs.Name,
   ''HsIPName,
   ''Hs.QOp,
   ''HsOp,
   ''HsCName,
   ''Hs.ExportSpec,
   ''Hs.ImportDecl,
   ''HsImportSpec,
   ''Hs.Assoc,
   ''DataOrNew,
   ''Hs.ConDecl,
   ''HsGadtDecl,
   ''Hs.QualConDecl,
   ''Hs.Match,
   ''Hs.IPBind,
   ''Hs.Decl,
   ''Hs.ModuleName,
   ''Hs.InstDecl,
   ''Hs.BangType,
   ''Hs.GuardedRhs,
   ''Hs.Type,
   ''HsBoxed,
   ''Hs.TyVarBind,
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
   ''Hs.PatField,
   ''Hs.Stmt,
   ''Hs.FieldUpdate,
   ''Hs.Alt,
   ''Hs.GuardedAlts,
   ''Hs.GuardedAlt
  ])
