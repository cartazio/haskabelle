{-# OPTIONS_GHC -fglasgow-exts #-}

module TreeMapping where {


data Nat = Zero | Suc Nat;

class Orda a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

mapa :: forall b a. (b -> a) -> [b] -> [a];
mapa f [] = [];
mapa f (x : xs) = f x : mapa f xs;

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) (Suc n) = nth xs n;
nth (x : xs) Zero = x;

insert :: forall a. (Eq a) => a -> (a -> Bool) -> a -> Bool;
insert y a x = y == x || a x;

class (Orda a) => Preorder a where {
};

class (Preorder a) => Bot a where {
  bot :: a;
};

instance Orda Bool where {
  less_eq True b = b;
  less_eq False b = True;
  less True b = False;
  less False b = b;
};

instance Preorder Bool where {
};

instance Bot Bool where {
  bot = False;
};

bot_fun :: forall a b. (Bot b) => a -> b;
bot_fun = (\ _ -> bot);

set :: forall a. (Eq a) => [a] -> a -> Bool;
set [] = bot_fun;
set (x : xs) = insert x (set xs);

data Tree a b = Empty | Branch b a (Tree a b) (Tree a b);

dropa :: forall a. Nat -> [a] -> [a];
dropa n [] = [];
dropa n (x : xs) = case n of {
                     Zero -> x : xs;
                     Suc m -> dropa m xs;
                   };

class (Preorder a) => Order a where {
};

class (Order a) => Linorder a where {
};

insort :: forall a. (Linorder a) => a -> [a] -> [a];
insort x [] = [x];
insort x (y : ys) = (if less_eq x y then x : y : ys else y : insort x ys);

sort :: forall a. (Linorder a) => [a] -> [a];
sort [] = [];
sort (x : xs) = insort x (sort xs);

takea :: forall a. Nat -> [a] -> [a];
takea n [] = [];
takea n (x : xs) = case n of {
                     Zero -> [];
                     Suc m -> x : takea m xs;
                   };

data Itself a = Type;

append :: forall a. [a] -> [a] -> [a];
append [] ys = ys;
append (x : xs) ys = x : append xs ys;

keysa :: forall a b. (Linorder a) => Tree a b -> [a];
keysa Empty = [];
keysa (Branch uu k l r) = k : append (keysa l) (keysa r);

member :: forall a. (Eq a) => a -> [a] -> Bool;
member x [] = False;
member x (y : ys) = x == y || member x ys;

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if member x xs then remdups xs else x : remdups xs);

lookupb :: forall a b. (Eq a, Linorder a) => Tree a b -> a -> Maybe b;
lookupb Empty = (\ _ -> Nothing);
lookupb (Branch v k l r) =
  (\ k' ->
    (if k' == k then Just v
      else (if less_eq k' k then lookupb l k' else lookupb r k')));

is_none :: forall a. Maybe a -> Bool;
is_none (Just x) = False;
is_none Nothing = True;

filtera :: forall a. (a -> Bool) -> [a] -> [a];
filtera p [] = [];
filtera p (x : xs) = (if p x then x : filtera p xs else filtera p xs);

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suc m) n = plus_nat m (Suc n);
plus_nat Zero n = n;

size_list :: forall a. [a] -> Nat;
size_list [] = Zero;
size_list (a : list) = plus_nat (size_list list) (Suc Zero);

sizea :: forall a b. (Eq a, Linorder a) => Tree a b -> Nat;
sizea t =
  size_list
    (filtera (\ x -> not (is_none x)) (mapa (lookupb t) (remdups (keysa t))));

foldla :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldla f a [] = a;
foldla f a (x : xs) = foldla f (f a x) xs;

newtype (Linorder a) => Map a b = Tree (Tree a b);

eq_nat :: Nat -> Nat -> Bool;
eq_nat (Suc nat') Zero = False;
eq_nat Zero (Suc nat') = False;
eq_nat (Suc nat) (Suc nat') = eq_nat nat nat';
eq_nat Zero Zero = True;

updatea :: forall a b. (Eq a, Linorder a) => a -> b -> Tree a b -> Tree a b;
updatea k v Empty = Branch v k Empty Empty;
updatea k' v' (Branch v k l r) =
  (if k' == k then Branch v' k l r
    else (if less_eq k' k then Branch v k (updatea k' v' l) r
           else Branch v k l (updatea k' v' r)));

keys :: forall a b. (Eq a, Linorder a) => Map a b -> a -> Bool;
keys (Tree t) =
  set (filtera (\ k -> not (is_none (lookupb t k))) (remdups (keysa t)));

size :: forall a b. (Eq a, Linorder a) => Map a b -> Nat;
size (Tree t) = sizea t;

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat (Suc m) n = less_nat m n;
less_eq_nat Zero n = True;

less_nat :: Nat -> Nat -> Bool;
less_nat m (Suc n) = less_eq_nat m n;
less_nat n Zero = False;

eq_tree :: forall a b. (Eq a, Eq b) => Tree a b -> Tree a b -> Bool;
eq_tree (Branch b' a' tree1' tree2') Empty = False;
eq_tree Empty (Branch b' a' tree1' tree2') = False;
eq_tree (Branch b a tree1 tree2) (Branch b' a' tree1' tree2') =
  b == b' && (a == a' && (eq_tree tree1 tree1' && eq_tree tree2 tree2'));
eq_tree Empty Empty = True;

empty :: forall a b. (Linorder a) => Map a b;
empty = Tree Empty;

minus_nat :: Nat -> Nat -> Nat;
minus_nat (Suc m) (Suc n) = minus_nat m n;
minus_nat Zero n = Zero;
minus_nat m Zero = m;

lookupa :: forall a b. (Eq a, Linorder a) => Map a b -> a -> Maybe b;
lookupa (Tree t) = lookupb t;

update :: forall a b. (Eq a, Linorder a) => a -> b -> Map a b -> Map a b;
update k v (Tree t) = Tree (updatea k v t);

replace :: forall a b. (Eq a, Linorder a) => a -> b -> Map a b -> Map a b;
replace k v m = (if is_none (lookupa m k) then m else update k v m);

}
