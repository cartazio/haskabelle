{-  ID:         $Id$
    Author:     Tobias C. Rittweiler and Florian Haftmann, TU Muenchen

Generic functions.
-}

module Importer.Utilities.Misc (
  assert, trace, concatMapM, map2, hasDuplicates,
  unfoldr, unfoldr1, unfoldl, unfoldl1, lookupBy, wordsBy,
  prettyShow', prettyShow, prettyHsx, groupAlist
) where

import Control.Exception (assert)
import Debug.Trace (trace)
import Monad (liftM)
import qualified List

import qualified Language.Haskell.Exts as Hsx

unfoldr, unfoldl    :: (b -> Maybe (a,b)) -> b -> [a]
unfoldr1, unfoldl1  :: (a -> Maybe (a, a)) -> a -> [a]

unfoldr f x = List.unfoldr f x

unfoldl f x = aux [] f x
    where aux acc f x = case f x of
                Nothing     -> []
                Just (z, x') -> aux (z:acc) f x'

unfoldr1 f x 
    = case f x of Nothing -> [x]
                  Just (z, x') -> z : unfoldr1 f x'

unfoldl1 f x = aux [] f x
    where aux acc f x = case f x of
                          Nothing -> x:acc
                          Just (z, x') -> aux (z:acc) f x'


concatMapM     :: Monad m => (a -> m [b]) -> [a] -> m [b] 
concatMapM f xs = liftM concat (mapM f xs)

map2 :: (a -> b -> c) -> [a] -> [b] -> [c]
map2 = zipWith

lookupBy                :: (a -> b -> Bool) -> a -> [(b, c)] -> Maybe c
lookupBy eq key []      =  Nothing
lookupBy eq key ((x,y):xys)
    | key `eq` x        =  Just y
    | otherwise         =  lookupBy eq key xys

groupAlist :: Eq a => [(a, b)] -> [(a, [b])]
groupAlist xs = map (\k -> (k, [ l | (k', l) <- xs, k' == k ]))
                  $ List.nub (map fst xs)

wordsBy            :: (a -> Bool) -> [a] -> [[a]]
wordsBy pred l     =  case dropWhile pred l of
                      [] -> []
                      l' -> w : wordsBy pred l''
                            where (w, l'') = break pred l'

hasDuplicates :: Eq a => [a] -> Bool
hasDuplicates list = or (map (\(x:xs) -> x `elem` xs) tails')
    where tails' = filter (not . null) (List.tails list)


prettyShow' prefix obj = let str = prefix ++ " = " ++ show obj
                             (Hsx.ParseOk (Hsx.HsModule _ _ _ _ decls)) 
                                 = Hsx.parseModule str
                         in concatMap Hsx.prettyPrint decls

prettyShow obj = prettyShow' "foo" obj

prettyHsx hs = Hsx.prettyPrint hs