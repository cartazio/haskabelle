{-  ID:         $Id: General.hs 416 2007-07-17 07:03:59Z haftmann $
    Author:     Tobias C. Rittweiler and Florian Haftmann, TU Munich

Generic functions
-}

module Importer.Utilities where

import qualified List as List

import qualified Language.Haskell.Hsx as Hsx

unfoldl, unfoldr    :: (b -> Maybe (a,b)) -> b -> [a]

unfoldl f x = aux [] f x
    where aux acc f x = case f x of
                Nothing     -> []
                Just (z, x') -> aux (z:acc) f x'

unfoldr f x = List.unfoldr f x


unfoldl1, unfoldr1  :: (a -> Maybe (a, a)) -> a -> [a]

unfoldl1 f x = aux [] f x
    where aux acc f x = case f x of
                          Nothing -> x:acc
                          Just (z, x') -> aux (z:acc) f x'
unfoldr1 f x = 
    case f x of Nothing -> [x]
                Just (z, x') -> z : unfoldr1 f x'



prettyShow' prefix obj = let str = prefix ++ " = " ++ show obj
                             (Hsx.ParseOk (Hsx.HsModule _ _ _ _ decls)) = Hsx.parseModule str
                         in concatMap Hsx.prettyPrint decls

prettyShow obj = prettyShow' "foo" obj
