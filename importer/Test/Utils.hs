{-# LANGUAGE TemplateHaskell #-}

{-| Author: Patrick Bahr, NICTA

This module provides template functions to derive instance declarations of data types for the class 'Arbitrary'.
-}

module Importer.Test.Utils
    ( -- * Deriving Functions
      deriveArbitrary,
      deriveArbitraryAll,
      deriveArbitraryForConstrs,
      deriveArbitrary_shrink,
      deriveGenForConstrs
      
    -- * What is Derived
    -- $example

    -- ** Deriving @arbitrary@
    -- $example_arbitrary

    -- ** Deriving @shrink@
    -- $example_shrink

    -- ** Using @deriveGenForConstrs@
    -- $example_partial
    ) where

import Test.QuickCheck
import Language.Haskell.TH
import Control.Monad
import Data.Maybe


{- $example
  Let's assume we have the following data type:

  @
  data Foo = FooA A B
           | FooB C D E
           | FooC F
  @

  where we also assume that we have the types @A@, ..., @F@.

  The function 'deriveArbitrary' will produces the following for @Foo@
  
  @
  instance Arbitrary Foo where
    arbitrary = ...
    shrink = ...
  @

  Details of the definition of @arbitrary@ and @shrink@ are shown in the subsequent sections.
 -}

{- $example_arbitrary

  @
  arbitrary = oneof [genFooA , genFooB , genFooC]
    where genFooA = sized $ \ size ->
                    let newSize = (((size - 1) `div` 2) `max` 0)
                    in do x1 <- resize newSize arbitrary
                          x2 <- resize newSize arbitrary
                          return $ FooA x1 x2
          genFooB = sized $ \ size ->
                    let newSize = (((size - 1) `div` 3) `max` 0)
                    in do x1 <- resize newSize arbitrary
                          x2 <- resize newSize arbitrary
                          x3 <- resize newSize arbitrary
                          return $ FooB x1 x2 x3
          genFooC = sized $ \ size ->
                    let newSize = (((size - 1) `div` 1) `max` 0)
                    in do x1 <- resize newSize arbitrary
                          return $ FooC x1
  @

-}

{- $example_shrink
   
  @
  shrink (FooA x1 x2)    = tail [ FooA x1' x2' | x1' <- x1 : shrink x1, x2' <- x2 : shrink x2 ]
  shrink (FooB x1 x2 x3) = tail [ FooB x1' x2' x3 | x1' <- x1 : shrink x1, x2' <- x2 : shrink x2, x3' <- x3 : shrink x3 ]
  shrink (FooC x1)       = tail [ FooC x1' | x1' <- x1 : shrink x1]
  @
  
-}

{- $example_partial
   
  The function 'deriveGenForConstrs' generates a generator that only
  produces values of a subset of the possible values of the
  type. The generator only generates values that can be constructed by
   the constructors given as the argument to 'deriveGenForConstrs'.

  For example the splice @$(deriveGenForConstrs \"noFooB\" [\'FooA, \'FooB])@ 
  will produces the following result:

  @
  noFooB = oneof [genFooA , genFooC]
    where genFooA = sized $ \ size ->
                    let newSize = (((size - 1) `div` 2) `max` 0)
                    in do x1 <- resize newSize arbitrary
                          x2 <- resize newSize arbitrary
                          return $ FooA x1 x2
          genFooC = sized $ \ size ->
                    let newSize = (((size - 1) `div` 1) `max` 0)
                    in do x1 <- resize newSize arbitrary
                          return $ FooC x1
  @
  
-}


--------------------------
-- Exported Definitions --
--------------------------

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
    = do (_,constrs) <- getConstrs constrNs
         liftM (:[]) $ generateGenDecl (mkName genName) constrs


deriveArbitraryForConstrs :: [Name] -> Q[Dec]
deriveArbitraryForConstrs constrNs =
    do (dt,constrs') <- getConstrs constrNs
       TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify dt
       let complType = foldl1 AppT (ConT name : map VarT args)
       let classType = AppT (ConT ''Arbitrary) complType
       arbitraryDecl <- generateArbitraryDecl constrs'
       shrinkDecl <- generateShrinkDecl constrs
       return $ [InstanceD [] classType [arbitraryDecl, shrinkDecl]]

--------------------------
-- Internal definitions --
--------------------------

getConstrs :: [Name] -> Q (Name,[Con])
getConstrs constrNs
    = do if (null constrNs) then report False "List of constructors must not be empty!" >> return undefined else do
           (typeName, typeConstrs) <- getTypeConstrs $ head constrNs
           let maybeConstrs = map (`lookupConstr` typeConstrs) constrNs
           let confl = notFound maybeConstrs constrNs
           when (not $ null confl) $ fail $ (show $ head confl) ++ " is not a constructor for " ++ (show typeName) ++"!"
           return (typeName, map fromJust maybeConstrs)
    where notFound :: [Maybe Con] -> [Name] -> [Name]
          notFound cons names = foldr (\ e l -> case e of
                                               (Nothing, name) -> name : l
                                               (Just _,_) -> l
                                    ) []  $ zip cons names
{-|
  This function provides the name and the arity of the given data constructor.
-}
abstractConType :: Con -> (Name,Int)
abstractConType (NormalC constr args) = (constr, length args)
abstractConType (RecC constr args) = (constr, length args)
abstractConType (InfixC _ constr _) = (constr, 2)
abstractConType (ForallC _ _ constr) = abstractConType constr

{-|
  This function provides a list (of the given length) of new names based
  on the given string.
-}
newNames :: Int -> String -> Q [Name]
newNames n name = replicateM n (newName name)

{-|
  This function takes the name of a constructor and returns the type it constructs and
  all constructors for this type.
-}
getTypeConstrs :: Name -> Q (Name,[Con])
getTypeConstrs name = do DataConI _name _type datatypeName _fixity <- reify name
                         TyConI tyDecl <- reify datatypeName
                         let ret =
                                 case tyDecl of
                                   NewtypeD _ _ _ constr _ -> [constr]
                                   DataD _ _ _ constrs _ -> constrs 
                         return (datatypeName, ret)

{-|
  This function checks whether the given name names one of the given constructors.
  If so the first such constructor is returned, if not @Nothing@ is returned.
-}
lookupConstr :: Name -> [Con] -> Maybe Con
lookupConstr name [] =  Nothing
lookupConstr name (constr : constrs) = case constr of
                                         NormalC cname _ -> if cname == name
                                                           then Just constr
                                                           else lookupConstr name constrs
                                         _ -> lookupConstr name constrs

{-|
  This function generates a declaration of the method 'arbitrary' for the given
  list of constructors using 'generateGenDecl'.
-}
generateArbitraryDecl :: [Con] -> Q Dec
generateArbitraryDecl = generateGenDecl 'arbitrary

{-|
  This function generates a declaration of a generator having the given name using
  the given constructors, i.e., something like this:
  
  @
  \<name\> :: Gen \<type\>
  \<name\> = ...
  @

  where @\<type\>@ is the type of the given constructors. If the constructors do not belong
  to the same type this function fails. The generated function will generate only elements of
  this type using the given constructors. All argument types of these constructors are supposed
  to be instances of 'Arbitrary'.
-}
generateGenDecl :: Name -> [Con] -> Q Dec
generateGenDecl genName constrs
    = do let genList = listE $ map (constrGen . abstractConType) constrs
         genBody <- [| oneof $genList |]
         let genClause = Clause [] (NormalB genBody) []
         return $ FunD genName [genClause]
    where constrGen (constr, n)
              = do varNs <- newNames n "x"
                   newSizeN <- newName "newSize"
                   let newSizeE = varE newSizeN
                   let newSizeP = varP newSizeN
                   let constrsE = litE . IntegerL . toInteger $ n
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

{-|
  This function generates a declaration for the method 'shrink' using the given constructors.
  The constructors are supposed to belong to the same type.
-}
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
  This is the @Q@-lifted version of 'abstractNewtypeQ.
-}
abstractNewtypeQ :: Q Info -> Q Info
abstractNewtypeQ = liftM abstractNewtype

{-|
  This function abstracts away @newtype@ declaration, it turns them into
  @data@ declarations.
-}
abstractNewtype :: Info -> Info
abstractNewtype (TyConI (NewtypeD cxt name args constr derive))
    = TyConI (DataD cxt name args [constr] derive)
abstractNewtype owise = owise