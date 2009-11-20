{-# OPTIONS_GHC -fglasgow-exts #-}

module Lists where {


data Inta = Number_of_int Inta | Bit1 Inta | Bit0 Inta | Min | Pls;

data Nat = Suc Nat | Zero;

leta :: forall b a. b -> (b -> a) -> a;
leta s f = f s;

class Orda a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

hd :: forall a. [a] -> a;
hd (x : xs) = x;

tl :: forall a. [a] -> [a];
tl [] = [];
tl (x : xs) = xs;

class Plus a where {
  plus :: a -> a -> a;
};

class Zero a where {
  zero :: a;
};

preda :: Inta -> Inta;
preda (Bit1 k) = Bit0 k;
preda (Bit0 k) = Bit1 (preda k);
preda Min = Bit0 Min;
preda Pls = Min;

succa :: Inta -> Inta;
succa (Bit1 k) = Bit0 (succa k);
succa (Bit0 k) = Bit1 k;
succa Min = Pls;
succa Pls = Bit1 Pls;

data Nibble = NibbleF | NibbleE | NibbleD | NibbleC | NibbleB | NibbleA
  | Nibble9 | Nibble8 | Nibble7 | Nibble6 | Nibble5 | Nibble4 | Nibble3
  | Nibble2 | Nibble1 | Nibble0;

data Chara = Chara Nibble Nibble;

mapa :: forall b a. (b -> a) -> [b] -> [a];
mapa f [] = [];
mapa f (x : xs) = f x : mapa f xs;

nat_case :: forall t. t -> (Nat -> t) -> Nat -> t;
nat_case f1 f2 (Suc nat) = f2 nat;
nat_case f1 f2 Zero = f1;

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) n = (case n of {
                   Zero -> x;
                   Suc a -> nth xs a;
                 });

foldla :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldla f a [] = a;
foldla f a (x : xs) = foldla f (f a x) xs;

rev :: forall a. [a] -> [a];
rev xs = foldla (\ xsa x -> x : xsa) [] xs;

insert :: forall a. (Eq a) => a -> (a -> Bool) -> a -> Bool;
insert y a x = y == x || a x;

empty :: forall a. a -> Bool;
empty x = False;

set :: forall a. (Eq a) => [a] -> a -> Bool;
set [] = empty;
set (x : xs) = insert x (set xs);

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat (Suc m) n = less_nat m n;
less_eq_nat Zero n = True;

less_nat :: Nat -> Nat -> Bool;
less_nat m (Suc n) = less_eq_nat m n;
less_nat n Zero = False;

list_case :: forall t a. t -> (a -> [a] -> t) -> [a] -> t;
list_case f1 f2 (a : list) = f2 a list;
list_case f1 f2 [] = f1;

zipa :: forall a b. [a] -> [b] -> [(a, b)];
zipa xs [] = [];
zipa xs (y : ys) =
  (case xs of {
    [] -> [];
    z : zs -> (z, y) : zipa zs ys;
  });

dropa :: forall a. Nat -> [a] -> [a];
dropa n [] = [];
dropa n (x : xs) =
  (case n of {
    Zero -> x : xs;
    Suc m -> dropa m xs;
  });

nulla :: forall a. [a] -> Bool;
nulla [] = True;
nulla (x : xs) = False;

lasta :: forall a. [a] -> a;
lasta (x : xs) = (if nulla xs then x else lasta xs);

class (Orda a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

class (Order a) => Linorder a where {
};

insort :: forall a. (Linorder a) => a -> [a] -> [a];
insort x [] = [x];
insort x (y : ys) =
  (if less_eq x y then x : y : ys else y : insort x ys);

sort :: forall a. (Linorder a) => [a] -> [a];
sort [] = [];
sort (x : xs) = insort x (sort xs);

takea :: forall a. Nat -> [a] -> [a];
takea n [] = [];
takea n (x : xs) =
  (case n of {
    Zero -> [];
    Suc m -> x : takea m xs;
  });

class (Linorder a) => Finite_intvl_succ a where {
  successor :: a -> a;
};

data Itself a = Type;

foldra :: forall b a. (b -> a -> a) -> [b] -> a -> a;
foldra f [] a = a;
foldra f (x : xs) a = f x (foldra f xs a);

membera :: forall a. a -> (a -> Bool) -> Bool;
membera x s = s x;

append :: forall a. [a] -> [a] -> [a];
append [] ys = ys;
append (x : xs) ys = x : append xs ys;

concata :: forall a. [[a]] -> [a];
concata [] = [];
concata (x : xs) = append x (concata xs);

filtera :: forall a. (a -> Bool) -> [a] -> [a];
filtera p [] = [];
filtera p (x : xs) = (if p x then x : filtera p xs else filtera p xs);

member :: forall a. (Eq a) => a -> [a] -> Bool;
member x [] = False;
member x (y : ys) = x == y || member x ys;

rotate1 :: forall a. [a] -> [a];
rotate1 xs = (case xs of {
               [] -> [];
               x : xsa -> append xsa [x];
             });

fun_pow :: forall a. Nat -> (a -> a) -> a -> a;
fun_pow Zero f = id;
fun_pow (Suc n) f = f . fun_pow n f;

rotate :: forall a. Nat -> [a] -> [a];
rotate n = fun_pow n rotate1;

sorted :: forall a. (Linorder a) => [a] -> Bool;
sorted [] = True;
sorted [x] = True;
sorted (x : y : zs) = less_eq x y && sorted (y : zs);

splice :: forall a. [a] -> [a] -> [a];
splice (x : xs) (y : ys) = x : y : splice xs ys;
splice xs [] = xs;

plus_int :: Inta -> Inta -> Inta;
plus_int (Number_of_int v) (Number_of_int w) =
  Number_of_int (plus_int v w);
plus_int (Bit1 k) (Bit1 l) = Bit0 (plus_int k (succa l));
plus_int (Bit1 k) (Bit0 l) = Bit1 (plus_int k l);
plus_int (Bit0 k) (Bit1 l) = Bit1 (plus_int k l);
plus_int (Bit0 k) (Bit0 l) = Bit0 (plus_int k l);
plus_int k Min = preda k;
plus_int k Pls = k;
plus_int Min k = preda k;
plus_int Pls k = k;

butlast :: forall a. [a] -> [a];
butlast [] = [];
butlast (x : xs) = (if nulla xs then [] else x : butlast xs);

list_ex :: forall a. (a -> Bool) -> [a] -> Bool;
list_ex p [] = False;
list_ex p (x : xs) = p x || list_ex p xs;

class (Plus a) => Semigroup_add a where {
};

class (Zero a, Semigroup_add a) => Monoid_add a where {
};

listsum :: forall a. (Monoid_add a) => [a] -> a;
listsum [] = zero;
listsum (x : xs) = plus x (foldla plus zero xs);

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if member x xs then remdups xs else x : remdups xs);

remove1 :: forall a. (Eq a) => a -> [a] -> [a];
remove1 x [] = [];
remove1 x (y : xs) = (if x == y then xs else y : remove1 x xs);

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suc m) n = plus_nat m (Suc n);
plus_nat Zero n = n;

size_list :: forall a. [a] -> Nat;
size_list [] = Zero;
size_list (a : list) = plus_nat (size_list list) (Suc Zero);

split :: forall b c a. (b -> c -> a) -> (b, c) -> a;
split f (a, b) = f a b;

distinct :: forall a. (Eq a) => [a] -> Bool;
distinct [] = True;
distinct (x : xs) = not (member x xs) && distinct xs;

list_all :: forall a. (a -> Bool) -> [a] -> Bool;
list_all p [] = True;
list_all p (x : xs) = p x && list_all p xs;

list_rec :: forall t a. t -> (a -> [a] -> t -> t) -> [a] -> t;
list_rec f1 f2 [] = f1;
list_rec f1 f2 (a : list) = f2 a list (list_rec f1 f2 list);

char_size :: Chara -> Nat;
char_size c = Zero;

dropWhilea :: forall a. (a -> Bool) -> [a] -> [a];
dropWhilea p [] = [];
dropWhilea p (x : xs) = (if p x then dropWhilea p xs else x : xs);

option_case :: forall t a. t -> (a -> t) -> Maybe a -> t;
option_case f1 f2 (Just a) = f2 a;
option_case f1 f2 Nothing = f1;

filtermap :: forall a b. (a -> Maybe b) -> [a] -> [b];
filtermap f [] = [];
filtermap f (x : xs) =
  (case f x of {
    Nothing -> filtermap f xs;
    Just y -> y : filtermap f xs;
  });

list_all2 :: forall a b. (a -> b -> Bool) -> [a] -> [b] -> Bool;
list_all2 p (x : xs) (y : ys) = p x y && list_all2 p xs ys;
list_all2 p xs [] = nulla xs;
list_all2 p [] ys = nulla ys;

list_size :: forall a. (a -> Nat) -> [a] -> Nat;
list_size fa [] = Zero;
list_size fa (a : list) =
  plus_nat (plus_nat (fa a) (list_size fa list)) (Suc Zero);

partition :: forall a. (a -> Bool) -> [a] -> ([a], [a]);
partition p [] = ([], []);
partition p (x : xs) =
  let {
    a = partition p xs;
    (yes, no) = a;
  } in (if p x then (x : yes, no) else (yes, x : no));

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) =
  (if x == y then removeAll x xs else y : removeAll x xs);

replicatea :: forall a. Nat -> a -> [a];
replicatea Zero x = [];
replicatea (Suc n) x = x : replicatea n x;

size_char :: Chara -> Nat;
size_char c = Zero;

takeWhilea :: forall a. (a -> Bool) -> [a] -> [a];
takeWhilea p [] = [];
takeWhilea p (x : xs) = (if p x then x : takeWhilea p xs else []);

list_inter :: forall a. (Eq a) => [a] -> [a] -> [a];
list_inter [] bs = [];
list_inter (a : asa) bs =
  (if member a bs then a : list_inter asa bs else list_inter asa bs);

map_filter :: forall a b. (a -> b) -> (a -> Bool) -> [a] -> [b];
map_filter f p [] = [];
map_filter f p (x : xs) =
  (if p x then f x : map_filter f p xs else map_filter f p xs);

nibble_rec ::
  forall t.
    t -> t -> t -> t -> t -> t -> t ->
t -> t -> t -> t -> t -> t -> t -> t -> t -> Nibble -> t;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble0 = f1;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble1 = f2;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble2 = f3;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble3 = f4;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble4 = f5;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble5 = f6;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble6 = f7;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble7 = f8;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble8 = f9;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble9 = f10;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  NibbleA = f11;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  NibbleB = f12;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  NibbleC = f13;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  NibbleD = f14;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  NibbleE = f15;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  NibbleF = f16;

itself_char :: Itself Chara;
itself_char = Type;

itself_list :: forall a. Itself [a];
itself_list = Type;

list_update :: forall a. [a] -> Nat -> a -> [a];
list_update [] i v = [];
list_update (x : xs) i v =
  (case i of {
    Zero -> v : xs;
    Suc j -> x : list_update xs j v;
  });

nibble_case ::
  forall t.
    t -> t -> t -> t -> t -> t -> t ->
t -> t -> t -> t -> t -> t -> t -> t -> t -> Nibble -> t;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  NibbleF = f16;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  NibbleE = f15;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  NibbleD = f14;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  NibbleC = f13;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  NibbleB = f12;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  NibbleA = f11;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble9 = f10;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble8 = f9;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble7 = f8;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble6 = f7;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble5 = f6;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble4 = f5;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble3 = f4;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble2 = f3;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble1 = f2;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
  Nibble0 = f1;

nibble_size :: Nibble -> Nat;
nibble_size Nibble0 = Zero;
nibble_size Nibble1 = Zero;
nibble_size Nibble2 = Zero;
nibble_size Nibble3 = Zero;
nibble_size Nibble4 = Zero;
nibble_size Nibble5 = Zero;
nibble_size Nibble6 = Zero;
nibble_size Nibble7 = Zero;
nibble_size Nibble8 = Zero;
nibble_size Nibble9 = Zero;
nibble_size NibbleA = Zero;
nibble_size NibbleB = Zero;
nibble_size NibbleC = Zero;
nibble_size NibbleD = Zero;
nibble_size NibbleE = Zero;
nibble_size NibbleF = Zero;

size_nibble :: Nibble -> Nat;
size_nibble Nibble0 = Zero;
size_nibble Nibble1 = Zero;
size_nibble Nibble2 = Zero;
size_nibble Nibble3 = Zero;
size_nibble Nibble4 = Zero;
size_nibble Nibble5 = Zero;
size_nibble Nibble6 = Zero;
size_nibble Nibble7 = Zero;
size_nibble Nibble8 = Zero;
size_nibble Nibble9 = Zero;
size_nibble NibbleA = Zero;
size_nibble NibbleB = Zero;
size_nibble NibbleC = Zero;
size_nibble NibbleD = Zero;
size_nibble NibbleE = Zero;
size_nibble NibbleF = Zero;

itself_nibble :: Itself Nibble;
itself_nibble = Type;

length_unique :: forall a. (Eq a) => [a] -> Nat;
length_unique [] = Zero;
length_unique (x : xs) =
  (if member x xs then length_unique xs else Suc (length_unique xs));

successor_int :: Inta -> Inta;
successor_int = (\ i -> plus_int i (Number_of_int (Bit1 Pls)));

}
