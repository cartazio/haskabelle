
module Importer.Utilities.Hsx ( extractBindingNames ) where

import Importer.Utilities.Misc (concatMapM)

import Data.Generics.PlateData
import Language.Haskell.Hsx


extractBindingNames :: HsBinds -> Maybe [HsName]

extractBindingNames (HsBDecls decls) = concatMapM fromHsDecl decls
    where fromHsDecl (HsInfixDecl _ _ _ ops) = Just (universeBi ops :: [HsName])
          fromHsDecl (HsPatBind _ pat _ _)   = Just (universeBi pat :: [HsName])
          fromHsDecl (HsFunBind (m:ms))      = case m of 
                                                 HsMatch _ fname _ _ _ -> Just [fname]
          fromHsDecl (HsTypeSig _ _ _)       = Just []
          fromHsDecl _                       = Nothing
