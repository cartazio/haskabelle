{-# OPTIONS_GHC -fglasgow-exts -XTemplateHaskell #-}
{-|
  This module provides template functions to derive instance declarations of data types for the class 'Arbitrary'.
-}

module Importer.Test.Utils
    ( deriveArbitrary,
      deriveArbitraryAll,
      deriveArbitrary_shrink,
      deriveGenForConstrs
    ) where

import Test.QuickCheck
import Language.Haskell.TH
import Control.Monad
import Data.Maybe

abstractConType :: Con -> (Name,Int)
abstractConType (NormalC constr args) = (constr, length args)
abstractConType (RecC constr args) = (constr, length args)
abstractConType (InfixC _ constr _) = (constr, 2)
abstractConType (ForallC _ _ constr) = abstractConType constr

newNames :: Int -> String -> Q [Name]
newNames n name = replicateM n (newName name)

{-|
  This function takes the name of a constructor and returns all constructor
  for the corresponding type.
-}
getTypeConstrs :: Name -> Q (Name,[Con])
getTypeConstrs name = do DataConI _name _type datatypeName _fixity <- reify name
                         TyConI tyDecl <- reify datatypeName
                         let ret =
                                 case tyDecl of
                                   NewtypeD _ _ _ constr _ -> [constr]
                                   DataD _ _ _ constrs _ -> constrs 
                         return (datatypeName, ret)

lookupConstr :: Name -> [Con] -> Maybe Con
lookupConstr name [] =  Nothing
lookupConstr name (constr : constrs) = case constr of
                                         NormalC cname _ -> if cname == name
                                                           then Just constr
                                                           else lookupConstr name constrs
                                         _ -> lookupConstr name constrs


generateArbitraryDecl :: [Con] -> Q Dec
generateArbitraryDecl = generateGenDecl 'arbitrary

generateGenDecl :: Name -> [Con] -> Q Dec
generateGenDecl genName constrs
    = do let genList = listE $ map (constrGen (length constrs) . abstractConType) constrs
         genBody <- [| oneof $genList |]
         let genClause = Clause [] (NormalB genBody) []
         return $ FunD genName [genClause]
    where constrGen constrCount (constr, n)
              = do varNs <- newNames n "x"
                   newSizeN <- newName "newSize"
                   let newSizeE = varE newSizeN
                   let newSizeP = varP newSizeN
                   let constrsE = litE . IntegerL . toInteger $ constrCount
                   let binds = (`map` varNs) (\var -> bindS
                                                     (varP var)
                                                     [| resize $newSizeE arbitrary |] )
                   let apps =  appsE (conE constr: map varE varNs)
                   let build = doE $
                               binds ++
                               [noBindS [|return $apps|]]
                   [| sized $ \ size ->
                        $(letE [valD 
                              newSizeP
                              (normalB [|((size - 1) `div` $constrsE ) `max` 0|])
                              [] ]
                          build) |]

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
      $(deriveArbitrary_shrink ''MyDatatype [| /<custom definition for arbitrary>/ |])
  @
-}
deriveArbitrary_shrink :: Name -> Q Exp -> Q [Dec]
deriveArbitrary_shrink dt arbitraryExp
    = do TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify dt
         let complType = foldl1 AppT (ConT name : map VarT args)
         let classType = AppT (ConT ''Arbitrary) complType
         arbitraryDecl <- funD 'arbitrary [clause [] (normalB arbitraryExp) []]
         shrinkDecl <- generateShrinkDecl constrs
         return $ [InstanceD [] classType [arbitraryDecl, shrinkDecl]]


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

{-|
  This template function generates a generator for a data type using only
  the given constructors
-}
deriveGenForConstrs :: String -> [Name] -> Q [Dec]
deriveGenForConstrs genName constrNs
    = do let defName = mkName genName
         if (null constrNs) then report False "List of constructors must not be empty!" >> return [] else do
           (typeName, typeConstrs) <- getTypeConstrs $ head constrNs
           let maybeConstrs = map (`lookupConstr` typeConstrs) constrNs
           let confl = notFound maybeConstrs constrNs
           when (not $ null confl) $ fail $ (show $ head confl) ++ " is not a constructor for " ++ (show typeName) ++"!"
           let constrs = map fromJust maybeConstrs                     
           liftM (:[]) $ generateGenDecl (mkName genName) constrs
    where notFound :: [Maybe Con] -> [Name] -> [Name]
          notFound cons names = foldr (\ e l -> case e of
                                               (Nothing, name) -> name : l
                                               (Just _,_) -> l
                                    ) []  $ zip cons names

abstractNewtypeQ :: Q Info -> Q Info
abstractNewtypeQ = liftM abstractNewtype

abstractNewtype :: Info -> Info
abstractNewtype (TyConI (NewtypeD cxt name args constr derive))
    = TyConI (DataD cxt name args [constr] derive)
abstractNewtype owise = owise