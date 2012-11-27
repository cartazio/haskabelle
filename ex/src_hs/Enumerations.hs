{-# OPTIONS_GHC -fglasgow-exts #-}

module Enumerations where {


data Nat = Zero | Suc Nat;

mapa :: forall b a. (b -> a) -> [b] -> [a];
mapa f [] = [];
mapa f (x : xs) = f x : mapa f xs;

list_case :: forall a b. a -> (b -> [b] -> a) -> [b] -> a;
list_case f1 f2 (a : list) = f2 a list;
list_case f1 f2 [] = f1;

zipa :: forall a b. [a] -> [b] -> [(a, b)];
zipa xs [] = [];
zipa xs (y : ys) = case xs of {
                     [] -> [];
                     z : zs -> (z, y) : zipa zs ys;
                   };

class Finite a where {
};

class (Finite a) => Enuma a where {
  enum :: [a];
};

data Sum a b = Inl a | Inr b;

append :: forall a. [a] -> [a] -> [a];
append [] ys = ys;
append (x : xs) ys = x : append xs ys;

enuma :: forall a b. (Enuma a, Enuma b) => [(Sum a b)];
enuma = append (mapa Inl enum) (mapa Inr enum);

producta :: forall a b. [a] -> [b] -> [(a, b)];
producta [] uu = [];
producta (x : xs) ys = append (mapa (\ a -> (x, a)) ys) (producta xs ys);

enumb :: forall a b. (Enuma a, Enuma b) => [(a, b)];
enumb = producta enum enum;

map_of :: forall b a. (Eq b) => [(b, a)] -> b -> Maybe a;
map_of ((l, v) : ps) k = (if l == k then Just v else map_of ps k);
map_of [] k = Nothing;

the :: forall a. Maybe a -> a;
the (Just x) = x;

list_all :: forall a. (a -> Bool) -> [a] -> Bool;
list_all p [] = True;
list_all p (x : xs) = p x && list_all p xs;

eq_fun :: forall a b. (Enuma a, Eq b) => (a -> b) -> (a -> b) -> Bool;
eq_fun f g = list_all (\ x -> f x == g x) enum;

concata :: forall a. [[a]] -> [a];
concata [] = [];
concata (x : xs) = append x (concata xs);

n_lists :: forall a. Nat -> [a] -> [[a]];
n_lists Zero xs = [[]];
n_lists (Suc n) xs =
  concata (mapa (\ ys -> mapa (\ y -> y : ys) xs) (n_lists n xs));

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suc m) n = plus_nat m (Suc n);
plus_nat Zero n = n;

len :: [a] -> Nat;
len [] = Zero;
len (_ : xs) = Suc (len xs);

enum_fun :: forall a b. (Eq a, Enuma a, Enuma b) => [(a -> b)];
enum_fun =
  let {
    enum_a = enum;
  } in mapa (\ ys -> the . map_of (zipa enum_a ys))
         (n_lists (len enum_a) enum);

sublists :: forall a. [a] -> [[a]];
sublists [] = [[]];
sublists (x : xs) =
  let {
    xss = sublists xs;
  } in append (mapa (\ a -> x : a) xss) xss;

enum_bool :: [Bool];
enum_bool = [False, True];

enum_unit :: [()];
enum_unit = [()];

enum_option :: forall a. (Enuma a) => [(Maybe a)];
enum_option = Nothing : mapa Just enum;

}
