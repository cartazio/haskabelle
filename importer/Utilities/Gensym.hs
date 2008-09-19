{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen
-}

module Importer.Utilities.Gensym where

import Control.Monad.State

import Language.Haskell.Exts (HsName(..), HsQName(..))
import Importer.IsaSyntax (Name(..))

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

genHsName :: HsName -> GensymM HsName
genHsName (HsIdent  prefix) = liftM HsIdent  (gensym prefix) 
genHsName (HsSymbol prefix) = liftM HsSymbol (gensym prefix) 

genHsQName :: HsQName -> GensymM HsQName
genHsQName (Qual m prefix)  = liftM (Qual m) (genHsName prefix)
genHsQName (UnQual prefix)  = liftM UnQual   (genHsName prefix)
genHsQName junk = error ("junk = " ++ show junk)

genIsaName :: Name -> GensymM Name
genIsaName (QName t prefix) = liftM (QName t) (gensym prefix)
genIsaName (Name prefix)    = liftM Name      (gensym prefix)

evalGensym :: Int -> GensymM a -> a
evalGensym init (GensymM state) =  evalState state init

runGensym :: Int -> GensymM a -> (a, Int)
runGensym init (GensymM state)  = runState state init