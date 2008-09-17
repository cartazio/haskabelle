{-# OPTIONS_GHC -fglasgow-exts -XTemplateHaskell #-}
{-|
  This module provides template functions to derive instance declarations of data types for the class 'Arbitrary'.
-}

module Importer.Test.Utils
    ( deriveArbitrary,
      deriveArbitraryAll,
      deriveArbitrary_shrink
    ) where

import Test.QuickCheck
import Language.Haskell.TH
import Control.Monad

abstractConType :: Con -> (Name,Int)
abstractConType (NormalC constr args) = (constr, length args)
abstractConType (RecC constr args) = (constr, length args)
abstractConType (InfixC _ constr _) = (constr, 2)
abstractConType (ForallC _ _ constr) = abstractConType constr

newNames :: Int -> String -> Q [Name]
newNames n name = replicateM n (newName name)

generateArbitraryDecl :: [Con] -> Q Dec
generateArbitraryDecl constrs
    = do let genList = listE $ map (constrGen . abstractConType) constrs
         arbitraryBody <- [| oneof $genList |]
         let arbitraryClause = Clause [] (NormalB arbitraryBody) []
         return $ FunD 'arbitrary [arbitraryClause]
    where constrGen (constr, n)
              = do varNs <- newNames n "x"
                   let binds = map (\var -> BindS (VarP var) (VarE 'arbitrary)) varNs
                   let varExps = (map VarE) varNs 
                   let con = ConE constr
                   let apps = return $ foldl1 AppE  (con: varExps)
                   ret <- noBindS [|return $ $apps|] 
                   let stmtSeq = binds ++ [ret]
                   return $ DoE stmtSeq

generateShrinkDecl :: [Con] -> Q Dec
generateShrinkDecl constrs
    = let clauses = map (generateClause.abstractConType) constrs
      in funD 'shrink clauses
  where generateClause (constr, n)
            = do varNs <- newNames n "x"
                 resVarNs <- newNames n "x'"
                 binds <- mapM (\(var,resVar) -> bindS (varP resVar) [| $(varE var) : shrink $(varE var) |]) $ zip varNs resVarNs
                 let ret = NoBindS $ AppE (VarE 'return) (foldl1 AppE ( ConE constr: map VarE resVarNs ))
                     stmtSeq = binds ++ [ret]
                     pat = ConP constr $ map VarP varNs
                 return $ Clause [pat] (NormalB $ AppE (VarE 'tail) (DoE stmtSeq)) []
{-|
  This template function generates the definition of the 'shrink' function of the class
  'Arbitrary' for the given data type name. It is necessary that all types that are used
  by the data type definition are themselves instances of 'Arbitrary'.
  
  Usage:
  
  @
    instance Arbitrary (MyDatatype a b c) where
      arbitrary = /<custom definition>/
      $(deriveArbitrary_shrink ''MyDatatype)
  @
-}
deriveArbitrary_shrink :: Name -> Q [Dec]
deriveArbitrary_shrink dt
    = do TyConI (DataD _cxt _name _args constrs _deriving) <- abstractNewtypeQ $ reify dt
         liftM (:[]) $ generateShrinkDecl constrs

{-|
  This template function generates an instance declaration of the given data type 
  name for the class 'Arbitrary'. It is necessary that all types that are used by the data type definition are 
  themselves instances of 'Arbitrary'.
-}
deriveArbitrary :: Name -> Q [Dec]
deriveArbitrary dt = do TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify dt
                        let complType = foldl1 AppT (ConT name : map VarT args)
                        let classType = AppT (ConT ''Arbitrary) complType
                        arbitraryDecl <- generateArbitraryDecl constrs
                        shrinkDecl <- generateShrinkDecl constrs
                        return $ [InstanceD [] classType [arbitraryDecl, shrinkDecl]]

{-|
  This template function generates instance declaration for each data type name in the
  given list for the class 'Arbitrary'. It is necessary that all types that are used
  by the data type definitions are themselves instances of 'Arbitrary'.
-}
deriveArbitraryAll :: [Name] -> Q [Dec]
deriveArbitraryAll = liftM concat . mapM deriveArbitrary

abstractNewtypeQ :: Q Info -> Q Info
abstractNewtypeQ = liftM abstractNewtype

abstractNewtype :: Info -> Info
abstractNewtype (TyConI (NewtypeD cxt name args constr derive))
    = TyConI (DataD cxt name args [constr] derive)
abstractNewtype owise = owise