{-  ID:         $Id: General.hs 416 2007-07-17 07:03:59Z haftmann $
    Author:     Tobias C. Rittweiler and Florian Haftmann, TU Munich

Generic functions
-}

module Importer.Utilities where

import qualified List as List

import Language.Haskell.Hsx

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


-- foo (HsTyApp (HsTyApp (HsTyCon c) x) xs) = Just (x, xs)
-- foo (HsTyApp xs x@(HsTyVar _)) = Just (x, xs)
-- foo _ = Nothing

bar (HsApp (HsApp (HsVar c) x) xs) = Just (x, xs)
bar _ = Nothing

-- HsTyApp (HsTyApp (HsTyApp (HsTyCon (UnQual (HsIdent "T")))
--                                    (HsTyVar (HsIdent "a"))))
--                  (HsTyVar (HsIdent "b"))) 
--         (HsTyVar (HsIdent "c"))