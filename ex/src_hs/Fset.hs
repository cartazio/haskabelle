{-# OPTIONS_GHC -fglasgow-exts #-}

module Fset where {


data Nat = Zero | Suc Nat;

newtype Fset a = Set [a];

mapb :: forall b a. (b -> a) -> [b] -> [a];
mapb f [] = [];
mapb f (x : xs) = f x : mapb f xs;

membera :: forall a. (Eq a) => a -> [a] -> Bool;
membera x [] = False;
membera x (y : ys) = x == y || membera x ys;

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera x xs then remdups xs else x : remdups xs);

mapa :: forall b a. (Eq a) => (b -> a) -> Fset b -> Fset a;
mapa f (Set xs) = Set (remdups (mapb f xs));

length_unique :: forall a. (Eq a) => [a] -> Nat;
length_unique [] = Zero;
length_unique (x : xs) =
  (if membera x xs then length_unique xs else Suc (length_unique xs));

card :: forall a. (Eq a) => Fset a -> Nat;
card (Set xs) = length_unique xs;

nulla :: forall a. [a] -> Bool;
nulla [] = True;
nulla (x : xs) = False;

empty :: forall a. Fset a;
empty = Set [];

list_ex :: forall a. (a -> Bool) -> [a] -> Bool;
list_ex p [] = False;
list_ex p (x : xs) = p x || list_ex p xs;

exists :: forall a. (a -> Bool) -> Fset a -> Bool;
exists p (Set xs) = list_ex p xs;

member :: forall a. (Eq a) => Fset a -> a -> Bool;
member a y = exists (\ aa -> y == aa) a;

filterb :: forall a. (a -> Bool) -> [a] -> [a];
filterb p [] = [];
filterb p (x : xs) = (if p x then x : filterb p xs else filterb p xs);

filtera :: forall a. (a -> Bool) -> Fset a -> Fset a;
filtera p (Set xs) = Set (filterb p xs);

inter :: forall a. (Eq a) => Fset a -> Fset a -> Fset a;
inter a b = filtera (member a) b;

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera x xs then xs else x : xs);

insert :: forall a. (Eq a) => a -> Fset a -> Fset a;
insert x (Set xs) = Set (inserta x xs);

foldla :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldla f a [] = a;
foldla f a (x : xs) = foldla f (f a x) xs;

union :: forall a. (Eq a) => Fset a -> Fset a -> Fset a;
union (Set xs) a = foldla (\ aa x -> insert x aa) a xs;

list_all :: forall a. (a -> Bool) -> [a] -> Bool;
list_all p [] = True;
list_all p (x : xs) = p x && list_all p xs;

foralla :: forall a. (a -> Bool) -> Fset a -> Bool;
foralla p (Set xs) = list_all p xs;

intera :: forall a. (Eq a) => Fset (Fset a) -> Fset a;
intera (Set (a : asa)) = foldla inter a asa;

remove_all :: forall a. (Eq a) => a -> [a] -> [a];
remove_all x xs = filterb (not . (\ a -> x == a)) xs;

remove :: forall a. (Eq a) => a -> Fset a -> Fset a;
remove x (Set xs) = Set (remove_all x xs);

uniona :: forall a. (Eq a) => Fset (Fset a) -> Fset a;
uniona (Set asa) = foldla union empty asa;

subfset_eq :: forall a. (Eq a) => Fset a -> Fset a -> Bool;
subfset_eq a b = foralla (member b) a;

eq_fset :: forall a. (Eq a) => Fset a -> Fset a -> Bool;
eq_fset a b = subfset_eq a b && subfset_eq b a;

subfset :: forall a. (Eq a) => Fset a -> Fset a -> Bool;
subfset a b = subfset_eq a b && not (subfset_eq b a);

is_empty :: forall a. Fset a -> Bool;
is_empty (Set xs) = nulla xs;

subtracta :: forall a. (Eq a) => Fset a -> Fset a -> Fset a;
subtracta (Set xs) a = foldla (\ aa x -> remove x aa) a xs;

}
