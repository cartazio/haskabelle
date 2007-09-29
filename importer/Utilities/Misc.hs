{-  ID:         $Id$
    Author:     Tobias C. Rittweiler and Florian Haftmann, TU Munich

Generic functions.
-}

module Importer.Utilities.Misc (
  assert, trace, concatMapM, map2,
  unfoldr, unfoldr1, unfoldl, unfoldl1,
  prettyShow', prettyShow, prettyHsx,
) where

import Control.Exception (assert)
import Debug.Trace (trace)
import Monad (liftM)
import qualified List

import qualified Language.Haskell.Hsx as Hsx


unfoldr, unfoldl    :: (b -> Maybe (a,b)) -> b -> [a]
unfoldr1, unfoldl1  :: (a -> Maybe (a, a)) -> a -> [a]

unfoldr f x = List.unfoldr f x

unfoldl f x = aux [] f x
    where aux acc f x = case f x of
                Nothing     -> []
                Just (z, x') -> aux (z:acc) f x'

unfoldr1 f x = 
    case f x of Nothing -> [x]
                Just (z, x') -> z : unfoldr1 f x'

unfoldl1 f x = aux [] f x
    where aux acc f x = case f x of
                          Nothing -> x:acc
                          Just (z, x') -> aux (z:acc) f x'


concatMapM     :: Monad m => (a -> m [b]) -> [a] -> m [b] 
concatMapM f xs = liftM concat (mapM f xs)

map2 :: (a -> b -> c) -> [a] -> [b] -> [c]
map2 = zipWith

prettyShow' prefix obj = let str = prefix ++ " = " ++ show obj
                             (Hsx.ParseOk (Hsx.HsModule _ _ _ _ decls)) = Hsx.parseModule str
                         in concatMap Hsx.prettyPrint decls

prettyShow obj = prettyShow' "foo" obj

prettyHsx hs = Hsx.prettyPrint hs

