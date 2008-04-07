{-  ID:         $Id: Importer.hs 632 2008-02-27 06:02:00Z rittweil $
    Author:     Tobias C. Rittweiler, TU Muenchen
-}

module Importer.Utilities.Gensym where

import Control.Monad.State

import Language.Haskell.Hsx (HsName(..), HsQName(..))
import Importer.IsaSyntax (Name(..))

newtype GensymCount = GensymCount Int

gensym :: String -> State GensymCount String
gensym prefix = do (GensymCount count) <- get; put $ GensymCount (count+1)
                   return (prefix ++ (show count))

genHsName (HsIdent  prefix) = liftM HsIdent  (gensym prefix) 
genHsName (HsSymbol prefix) = liftM HsSymbol (gensym prefix) 

genHsQName (Qual m prefix)  = liftM (Qual m) (genHsName prefix)
genHsQName (UnQual prefix)  = liftM UnQual   (genHsName prefix)

genIsaName (QName t prefix) = liftM (QName t) (gensym prefix)
genIsaName (Name prefix)    = liftM Name      (gensym prefix)

runGensym init state = evalState state (GensymCount init)