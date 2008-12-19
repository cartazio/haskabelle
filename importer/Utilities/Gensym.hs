{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-| Author: Tobias C. Rittweiler, TU Muenchen
-}

module Importer.Utilities.Gensym where

import Control.Monad.State

import qualified Language.Haskell.Exts as Hs (Name(..), QName(..))
import qualified Importer.IsaSyntax as Isa (Name(..))

newtype GensymM a = GensymM (State Int a)
    deriving (Monad, Functor, MonadFix, MonadState Int)

--deriving instance State Int GensymM

{-|
  This function generates a fresh symbol based on the given string.
-}
gensym :: String -> GensymM String
gensym prefix = do count <- get
                   put $ (count+1)
                   return (prefix ++ (show count))

genHsName :: Hs.Name -> GensymM Hs.Name
genHsName (Hs.Ident  prefix) = liftM Hs.Ident  (gensym prefix) 
genHsName (Hs.Symbol prefix) = liftM Hs.Symbol (gensym prefix) 

genHsQName :: Hs.QName -> GensymM Hs.QName
genHsQName (Hs.Qual m prefix)  = liftM (Hs.Qual m) (genHsName prefix)
genHsQName (Hs.UnQual prefix)  = liftM Hs.UnQual   (genHsName prefix)
genHsQName junk = error ("junk = " ++ show junk)

genIsaName :: Isa.Name -> GensymM Isa.Name
genIsaName (Isa.QName t prefix) = liftM (Isa.QName t) (gensym prefix)
genIsaName (Isa.Name prefix)    = liftM Isa.Name      (gensym prefix)

evalGensym :: Int -> GensymM a -> a
evalGensym init (GensymM state) =  evalState state init

runGensym :: Int -> GensymM a -> (a, Int)
runGensym init (GensymM state)  = runState state init