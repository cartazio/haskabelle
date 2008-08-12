module ListsAndMaps where {


data Inta = Number_of_int Inta | Bit1 Inta | Bit0 Inta | Min | Pls;

data Nat = Suc Nat | Zero_nat;

leta :: forall b a. b -> (b -> a) -> a;
leta s f = f s;

class Orda a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

hd :: forall a. [a] -> a;
hd (x : xs) = x;

tl :: forall a. [a] -> [a];
tl (x : xs) = xs;
tl [] = [];

eqop :: forall a. (Eq a) => a -> a -> Bool;
eqop a = (\ b -> a == b);

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
mapa f (x : xs) = f x : mapa f xs;
mapa f [] = [];

nat_case :: forall t. t -> (Nat -> t) -> Nat -> t;
nat_case f1 f2 Zero_nat = f1;
nat_case f1 f2 (Suc nat) = f2 nat;

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) n = (case n of {
                   Zero_nat -> x;
                   Suc a -> nth xs a;
                 });

foldla :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldla f a (x : xs) = foldla f (f a x) xs;
foldla f a [] = a;

rev :: forall a. [a] -> [a];
rev xs = foldla (\ xsa x -> x : xsa) [] xs;

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat (Suc m) n = less_nat m n;
less_eq_nat Zero_nat n = True;

less_nat :: Nat -> Nat -> Bool;
less_nat m (Suc n) = less_eq_nat m n;
less_nat n Zero_nat = False;

-- No Termination order
-- upt :: Nat -> Nat -> [Nat];
-- upt i j = (if less_nat i j then i : upt (Suc i) j else []);

list_case :: forall t a. t -> (a -> [a] -> t) -> [a] -> t;
list_case f1 f2 [] = f1;
list_case f1 f2 (a : list) = f2 a list;

zipa :: forall a b. [a] -> [b] -> [(a, b)];
zipa xs (y : ys) = (case xs of {
                     [] -> [];
                     z : zs -> (z, y) : zipa zs ys;
                   });
zipa xs [] = [];

dropa :: forall a. Nat -> [a] -> [a];
dropa n (x : xs) = (case n of {
                     Zero_nat -> x : xs;
                     Suc m -> dropa m xs;
                   });
dropa n [] = [];

nulla :: forall a. [a] -> Bool;
nulla (x : xs) = False;
nulla [] = True;

lasta :: forall a. [a] -> a;
lasta (x : xs) = (if nulla xs then x else lasta xs);

class (Orda a) => Order a where {
};

class (Order a) => Linorder a where {
};

insort :: forall a. (Linorder a) => a -> [a] -> [a];
insort x (y : ys) = (if less_eq x y then x : y : ys else y : insort x ys);
insort x [] = [x];

sort :: forall a. (Linorder a) => [a] -> [a];
sort (x : xs) = insort x (sort xs);
sort [] = [];

takea :: forall a. Nat -> [a] -> [a];
takea n (x : xs) = (case n of {
                     Zero_nat -> [];
                     Suc m -> x : takea m xs;
                   });
takea n [] = [];

class (Linorder a) => Finite_intvl_succ a where {
  successor :: a -> a;
};

-- No Termination order
-- upto :: forall a. (Finite_intvl_succ a) => a -> a -> [a];
-- upto i j = (if less_eq i j then i : upto (successor i) j else []);

data Itself a = Type;

foldra :: forall b a. (b -> a -> a) -> [b] -> a -> a;
foldra f (x : xs) a = f x (foldra f xs a);
foldra f [] a = a;

map_of :: forall b c. (Eq b) => [(b, c)] -> b -> Maybe c;
map_of ((l, v) : ps) k = (if eqop l k then Just v else map_of ps k);
map_of [] k = Nothing;

append :: forall a. [a] -> [a] -> [a];
append (x : xs) ys = x : append xs ys;
append [] ys = ys;

concata :: forall a. [[a]] -> [a];
concata (x : xs) = append x (concata xs);
concata [] = [];

filtera :: forall a. (a -> Bool) -> [a] -> [a];
filtera p (x : xs) = (if p x then x : filtera p xs else filtera p xs);
filtera p [] = [];

member :: forall a. (Eq a) => a -> [a] -> Bool;
member x (y : ys) = (if eqop y x then True else member x ys);
member x [] = False;

rotate1 :: forall a. [a] -> [a];
rotate1 xs = (case xs of {
               [] -> [];
               x : xsa -> append xsa [x];
             });

fun_pow :: forall a. Nat -> (a -> a) -> a -> a;
fun_pow (Suc n) f = f . fun_pow n f;
fun_pow Zero_nat f = id;

rotate :: forall a. Nat -> [a] -> [a];
rotate n = fun_pow n rotate1;

sorted :: forall a. (Linorder a) => [a] -> Bool;
sorted (x : y : zs) = less_eq x y && sorted (y : zs);
sorted [x] = True;
sorted [] = True;

splice :: forall a. [a] -> [a] -> [a];
splice (x : xs) (y : ys) = x : y : splice xs ys;
splice xs [] = xs;
splice [] ys = ys;

option_case :: forall t a. t -> (a -> t) -> Maybe a -> t;
option_case f1 f2 Nothing = f1;
option_case f1 f2 (Just a) = f2 a;

map_add :: forall a b. (a -> Maybe b) -> (a -> Maybe b) -> a -> Maybe b;
map_add m1 m2 =
  (\ x -> (case m2 x of {
            Nothing -> m1 x;
            Just a -> Just a;
          }));

plus_int :: Inta -> Inta -> Inta;
plus_int (Number_of_int v) (Number_of_int w) = Number_of_int (plus_int v w);
plus_int (Bit1 k) (Bit1 l) = Bit0 (plus_int k (succa l));
plus_int (Bit1 k) (Bit0 l) = Bit1 (plus_int k l);
plus_int (Bit0 k) (Bit1 l) = Bit1 (plus_int k l);
plus_int (Bit0 k) (Bit0 l) = Bit0 (plus_int k l);
plus_int k Min = preda k;
plus_int k Pls = k;
plus_int Min k = preda k;
plus_int Pls k = k;

butlast :: forall a. [a] -> [a];
butlast (x : xs) = (if nulla xs then [] else x : butlast xs);
butlast [] = [];

eq_nibble :: Nibble -> Nibble -> Bool;
eq_nibble Nibble0 Nibble0 = True;
eq_nibble Nibble1 Nibble1 = True;
eq_nibble Nibble2 Nibble2 = True;
eq_nibble Nibble3 Nibble3 = True;
eq_nibble Nibble4 Nibble4 = True;
eq_nibble Nibble5 Nibble5 = True;
eq_nibble Nibble6 Nibble6 = True;
eq_nibble Nibble7 Nibble7 = True;
eq_nibble Nibble8 Nibble8 = True;
eq_nibble Nibble9 Nibble9 = True;
eq_nibble NibbleA NibbleA = True;
eq_nibble NibbleB NibbleB = True;
eq_nibble NibbleC NibbleC = True;
eq_nibble NibbleD NibbleD = True;
eq_nibble NibbleE NibbleE = True;
eq_nibble NibbleF NibbleF = True;
eq_nibble Nibble0 Nibble1 = False;
eq_nibble Nibble0 Nibble2 = False;
eq_nibble Nibble0 Nibble3 = False;
eq_nibble Nibble0 Nibble4 = False;
eq_nibble Nibble0 Nibble5 = False;
eq_nibble Nibble0 Nibble6 = False;
eq_nibble Nibble0 Nibble7 = False;
eq_nibble Nibble0 Nibble8 = False;
eq_nibble Nibble0 Nibble9 = False;
eq_nibble Nibble0 NibbleA = False;
eq_nibble Nibble0 NibbleB = False;
eq_nibble Nibble0 NibbleC = False;
eq_nibble Nibble0 NibbleD = False;
eq_nibble Nibble0 NibbleE = False;
eq_nibble Nibble0 NibbleF = False;
eq_nibble Nibble1 Nibble2 = False;
eq_nibble Nibble1 Nibble3 = False;
eq_nibble Nibble1 Nibble4 = False;
eq_nibble Nibble1 Nibble5 = False;
eq_nibble Nibble1 Nibble6 = False;
eq_nibble Nibble1 Nibble7 = False;
eq_nibble Nibble1 Nibble8 = False;
eq_nibble Nibble1 Nibble9 = False;
eq_nibble Nibble1 NibbleA = False;
eq_nibble Nibble1 NibbleB = False;
eq_nibble Nibble1 NibbleC = False;
eq_nibble Nibble1 NibbleD = False;
eq_nibble Nibble1 NibbleE = False;
eq_nibble Nibble1 NibbleF = False;
eq_nibble Nibble2 Nibble3 = False;
eq_nibble Nibble2 Nibble4 = False;
eq_nibble Nibble2 Nibble5 = False;
eq_nibble Nibble2 Nibble6 = False;
eq_nibble Nibble2 Nibble7 = False;
eq_nibble Nibble2 Nibble8 = False;
eq_nibble Nibble2 Nibble9 = False;
eq_nibble Nibble2 NibbleA = False;
eq_nibble Nibble2 NibbleB = False;
eq_nibble Nibble2 NibbleC = False;
eq_nibble Nibble2 NibbleD = False;
eq_nibble Nibble2 NibbleE = False;
eq_nibble Nibble2 NibbleF = False;
eq_nibble Nibble3 Nibble4 = False;
eq_nibble Nibble3 Nibble5 = False;
eq_nibble Nibble3 Nibble6 = False;
eq_nibble Nibble3 Nibble7 = False;
eq_nibble Nibble3 Nibble8 = False;
eq_nibble Nibble3 Nibble9 = False;
eq_nibble Nibble3 NibbleA = False;
eq_nibble Nibble3 NibbleB = False;
eq_nibble Nibble3 NibbleC = False;
eq_nibble Nibble3 NibbleD = False;
eq_nibble Nibble3 NibbleE = False;
eq_nibble Nibble3 NibbleF = False;
eq_nibble Nibble4 Nibble5 = False;
eq_nibble Nibble4 Nibble6 = False;
eq_nibble Nibble4 Nibble7 = False;
eq_nibble Nibble4 Nibble8 = False;
eq_nibble Nibble4 Nibble9 = False;
eq_nibble Nibble4 NibbleA = False;
eq_nibble Nibble4 NibbleB = False;
eq_nibble Nibble4 NibbleC = False;
eq_nibble Nibble4 NibbleD = False;
eq_nibble Nibble4 NibbleE = False;
eq_nibble Nibble4 NibbleF = False;
eq_nibble Nibble5 Nibble6 = False;
eq_nibble Nibble5 Nibble7 = False;
eq_nibble Nibble5 Nibble8 = False;
eq_nibble Nibble5 Nibble9 = False;
eq_nibble Nibble5 NibbleA = False;
eq_nibble Nibble5 NibbleB = False;
eq_nibble Nibble5 NibbleC = False;
eq_nibble Nibble5 NibbleD = False;
eq_nibble Nibble5 NibbleE = False;
eq_nibble Nibble5 NibbleF = False;
eq_nibble Nibble6 Nibble7 = False;
eq_nibble Nibble6 Nibble8 = False;
eq_nibble Nibble6 Nibble9 = False;
eq_nibble Nibble6 NibbleA = False;
eq_nibble Nibble6 NibbleB = False;
eq_nibble Nibble6 NibbleC = False;
eq_nibble Nibble6 NibbleD = False;
eq_nibble Nibble6 NibbleE = False;
eq_nibble Nibble6 NibbleF = False;
eq_nibble Nibble7 Nibble8 = False;
eq_nibble Nibble7 Nibble9 = False;
eq_nibble Nibble7 NibbleA = False;
eq_nibble Nibble7 NibbleB = False;
eq_nibble Nibble7 NibbleC = False;
eq_nibble Nibble7 NibbleD = False;
eq_nibble Nibble7 NibbleE = False;
eq_nibble Nibble7 NibbleF = False;
eq_nibble Nibble8 Nibble9 = False;
eq_nibble Nibble8 NibbleA = False;
eq_nibble Nibble8 NibbleB = False;
eq_nibble Nibble8 NibbleC = False;
eq_nibble Nibble8 NibbleD = False;
eq_nibble Nibble8 NibbleE = False;
eq_nibble Nibble8 NibbleF = False;
eq_nibble Nibble9 NibbleA = False;
eq_nibble Nibble9 NibbleB = False;
eq_nibble Nibble9 NibbleC = False;
eq_nibble Nibble9 NibbleD = False;
eq_nibble Nibble9 NibbleE = False;
eq_nibble Nibble9 NibbleF = False;
eq_nibble NibbleA NibbleB = False;
eq_nibble NibbleA NibbleC = False;
eq_nibble NibbleA NibbleD = False;
eq_nibble NibbleA NibbleE = False;
eq_nibble NibbleA NibbleF = False;
eq_nibble NibbleB NibbleC = False;
eq_nibble NibbleB NibbleD = False;
eq_nibble NibbleB NibbleE = False;
eq_nibble NibbleB NibbleF = False;
eq_nibble NibbleC NibbleD = False;
eq_nibble NibbleC NibbleE = False;
eq_nibble NibbleC NibbleF = False;
eq_nibble NibbleD NibbleE = False;
eq_nibble NibbleD NibbleF = False;
eq_nibble NibbleE NibbleF = False;
eq_nibble Nibble1 Nibble0 = False;
eq_nibble Nibble2 Nibble0 = False;
eq_nibble Nibble3 Nibble0 = False;
eq_nibble Nibble4 Nibble0 = False;
eq_nibble Nibble5 Nibble0 = False;
eq_nibble Nibble6 Nibble0 = False;
eq_nibble Nibble7 Nibble0 = False;
eq_nibble Nibble8 Nibble0 = False;
eq_nibble Nibble9 Nibble0 = False;
eq_nibble NibbleA Nibble0 = False;
eq_nibble NibbleB Nibble0 = False;
eq_nibble NibbleC Nibble0 = False;
eq_nibble NibbleD Nibble0 = False;
eq_nibble NibbleE Nibble0 = False;
eq_nibble NibbleF Nibble0 = False;
eq_nibble Nibble2 Nibble1 = False;
eq_nibble Nibble3 Nibble1 = False;
eq_nibble Nibble4 Nibble1 = False;
eq_nibble Nibble5 Nibble1 = False;
eq_nibble Nibble6 Nibble1 = False;
eq_nibble Nibble7 Nibble1 = False;
eq_nibble Nibble8 Nibble1 = False;
eq_nibble Nibble9 Nibble1 = False;
eq_nibble NibbleA Nibble1 = False;
eq_nibble NibbleB Nibble1 = False;
eq_nibble NibbleC Nibble1 = False;
eq_nibble NibbleD Nibble1 = False;
eq_nibble NibbleE Nibble1 = False;
eq_nibble NibbleF Nibble1 = False;
eq_nibble Nibble3 Nibble2 = False;
eq_nibble Nibble4 Nibble2 = False;
eq_nibble Nibble5 Nibble2 = False;
eq_nibble Nibble6 Nibble2 = False;
eq_nibble Nibble7 Nibble2 = False;
eq_nibble Nibble8 Nibble2 = False;
eq_nibble Nibble9 Nibble2 = False;
eq_nibble NibbleA Nibble2 = False;
eq_nibble NibbleB Nibble2 = False;
eq_nibble NibbleC Nibble2 = False;
eq_nibble NibbleD Nibble2 = False;
eq_nibble NibbleE Nibble2 = False;
eq_nibble NibbleF Nibble2 = False;
eq_nibble Nibble4 Nibble3 = False;
eq_nibble Nibble5 Nibble3 = False;
eq_nibble Nibble6 Nibble3 = False;
eq_nibble Nibble7 Nibble3 = False;
eq_nibble Nibble8 Nibble3 = False;
eq_nibble Nibble9 Nibble3 = False;
eq_nibble NibbleA Nibble3 = False;
eq_nibble NibbleB Nibble3 = False;
eq_nibble NibbleC Nibble3 = False;
eq_nibble NibbleD Nibble3 = False;
eq_nibble NibbleE Nibble3 = False;
eq_nibble NibbleF Nibble3 = False;
eq_nibble Nibble5 Nibble4 = False;
eq_nibble Nibble6 Nibble4 = False;
eq_nibble Nibble7 Nibble4 = False;
eq_nibble Nibble8 Nibble4 = False;
eq_nibble Nibble9 Nibble4 = False;
eq_nibble NibbleA Nibble4 = False;
eq_nibble NibbleB Nibble4 = False;
eq_nibble NibbleC Nibble4 = False;
eq_nibble NibbleD Nibble4 = False;
eq_nibble NibbleE Nibble4 = False;
eq_nibble NibbleF Nibble4 = False;
eq_nibble Nibble6 Nibble5 = False;
eq_nibble Nibble7 Nibble5 = False;
eq_nibble Nibble8 Nibble5 = False;
eq_nibble Nibble9 Nibble5 = False;
eq_nibble NibbleA Nibble5 = False;
eq_nibble NibbleB Nibble5 = False;
eq_nibble NibbleC Nibble5 = False;
eq_nibble NibbleD Nibble5 = False;
eq_nibble NibbleE Nibble5 = False;
eq_nibble NibbleF Nibble5 = False;
eq_nibble Nibble7 Nibble6 = False;
eq_nibble Nibble8 Nibble6 = False;
eq_nibble Nibble9 Nibble6 = False;
eq_nibble NibbleA Nibble6 = False;
eq_nibble NibbleB Nibble6 = False;
eq_nibble NibbleC Nibble6 = False;
eq_nibble NibbleD Nibble6 = False;
eq_nibble NibbleE Nibble6 = False;
eq_nibble NibbleF Nibble6 = False;
eq_nibble Nibble8 Nibble7 = False;
eq_nibble Nibble9 Nibble7 = False;
eq_nibble NibbleA Nibble7 = False;
eq_nibble NibbleB Nibble7 = False;
eq_nibble NibbleC Nibble7 = False;
eq_nibble NibbleD Nibble7 = False;
eq_nibble NibbleE Nibble7 = False;
eq_nibble NibbleF Nibble7 = False;
eq_nibble Nibble9 Nibble8 = False;
eq_nibble NibbleA Nibble8 = False;
eq_nibble NibbleB Nibble8 = False;
eq_nibble NibbleC Nibble8 = False;
eq_nibble NibbleD Nibble8 = False;
eq_nibble NibbleE Nibble8 = False;
eq_nibble NibbleF Nibble8 = False;
eq_nibble NibbleA Nibble9 = False;
eq_nibble NibbleB Nibble9 = False;
eq_nibble NibbleC Nibble9 = False;
eq_nibble NibbleD Nibble9 = False;
eq_nibble NibbleE Nibble9 = False;
eq_nibble NibbleF Nibble9 = False;
eq_nibble NibbleB NibbleA = False;
eq_nibble NibbleC NibbleA = False;
eq_nibble NibbleD NibbleA = False;
eq_nibble NibbleE NibbleA = False;
eq_nibble NibbleF NibbleA = False;
eq_nibble NibbleC NibbleB = False;
eq_nibble NibbleD NibbleB = False;
eq_nibble NibbleE NibbleB = False;
eq_nibble NibbleF NibbleB = False;
eq_nibble NibbleD NibbleC = False;
eq_nibble NibbleE NibbleC = False;
eq_nibble NibbleF NibbleC = False;
eq_nibble NibbleE NibbleD = False;
eq_nibble NibbleF NibbleD = False;
eq_nibble NibbleF NibbleE = False;

eq_char :: Chara -> Chara -> Bool;
eq_char (Chara nibble1 nibble2) (Chara nibble1' nibble2') =
  eq_nibble nibble1 nibble1' && eq_nibble nibble2 nibble2';

list_ex :: forall a. (a -> Bool) -> [a] -> Bool;
list_ex p (x : xs) = p x || list_ex p xs;
list_ex p [] = False;

class (Plus a) => Semigroup_add a where {
};

class (Zero a, Semigroup_add a) => Monoid_add a where {
};

listsum :: forall a. (Monoid_add a) => [a] -> a;
listsum (x : xs) = plus x (foldla plus zero xs);
listsum [] = zero;

remdups :: forall a. (Eq a) => [a] -> [a];
remdups (x : xs) = (if member x xs then remdups xs else x : remdups xs);
remdups [] = [];

remove1 :: forall a. (Eq a) => a -> [a] -> [a];
remove1 x (y : xs) = (if eqop x y then xs else y : remove1 x xs);
remove1 x [] = [];

map_comp :: forall b c a. (b -> Maybe c) -> (a -> Maybe b) -> a -> Maybe c;
map_comp f g = (\ k -> (case g k of {
                         Nothing -> Nothing;
                         Just a -> f a;
                       }));

map_upds :: forall a b. (Eq a) => (a -> Maybe b) -> [a] -> [b] -> a -> Maybe b;
map_upds m xs ys = map_add m (map_of (rev (zipa xs ys)));

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suc m) n = plus_nat m (Suc n);
plus_nat Zero_nat n = n;

char_rec :: forall t. (Nibble -> Nibble -> t) -> Chara -> t;
char_rec f1 (Chara nibble1 nibble2) = f1 nibble1 nibble2;

distinct :: forall a. (Eq a) => [a] -> Bool;
distinct (x : xs) = not (member x xs) && distinct xs;
distinct [] = True;

list_all :: forall a. (a -> Bool) -> [a] -> Bool;
list_all p (x : xs) = p x && list_all p xs;
list_all p [] = True;

list_rec :: forall t a. t -> (a -> [a] -> t -> t) -> [a] -> t;
list_rec f1 f2 (a : list) = f2 a list (list_rec f1 f2 list);
list_rec f1 f2 [] = f1;

char_case :: forall t. (Nibble -> Nibble -> t) -> Chara -> t;
char_case f1 (Chara nibble1 nibble2) = f1 nibble1 nibble2;

char_size :: Chara -> Nat;
char_size (Chara nibble1 nibble2) = Zero_nat;

dropWhilea :: forall a. (a -> Bool) -> [a] -> [a];
dropWhilea p (x : xs) = (if p x then dropWhilea p xs else x : xs);
dropWhilea p [] = [];

filtermap :: forall a b. (a -> Maybe b) -> [a] -> [b];
filtermap f (x : xs) =
  (case f x of {
    Nothing -> filtermap f xs;
    Just y -> y : filtermap f xs;
  });
filtermap f [] = [];

list_all2 :: forall a b. (a -> b -> Bool) -> [a] -> [b] -> Bool;
list_all2 p (x : xs) (y : ys) = p x y && list_all2 p xs ys;
list_all2 p xs [] = nulla xs;
list_all2 p [] ys = nulla ys;

list_size :: forall a. (a -> Nat) -> [a] -> Nat;
list_size fa (a : list) =
  plus_nat (plus_nat (fa a) (list_size fa list)) (Suc Zero_nat);
list_size fa [] = Zero_nat;

split :: forall b c a. (b -> c -> a) -> (b, c) -> a;
split f (a, b) = f a b;

partition :: forall a. (a -> Bool) -> [a] -> ([a], [a]);
partition p (x : xs) =
  let {
    a = partition p xs;
    (yes, no) = a;
  } in (if p x then (x : yes, no) else (yes, x : no));
partition p [] = ([], []);

replicatea :: forall a. Nat -> a -> [a];
replicatea (Suc n) x = x : replicatea n x;
replicatea Zero_nat x = [];

size_char :: Chara -> Nat;
size_char (Chara nibble1 nibble2) = Zero_nat;

size_list :: forall a. [a] -> Nat;
size_list (a : list) = plus_nat (size_list list) (Suc Zero_nat);
size_list [] = Zero_nat;

takeWhilea :: forall a. (a -> Bool) -> [a] -> [a];
takeWhilea p (x : xs) = (if p x then x : takeWhilea p xs else []);
takeWhilea p [] = [];

list_inter :: forall a. (Eq a) => [a] -> [a] -> [a];
list_inter (a : asa) bs =
  (if member a bs then a : list_inter asa bs else list_inter asa bs);
list_inter [] bs = [];

map_filter :: forall a b. (a -> b) -> (a -> Bool) -> [a] -> [b];
map_filter f p (x : xs) =
  (if p x then f x : map_filter f p xs else map_filter f p xs);
map_filter f p [] = [];

nibble_rec ::
  forall t.
    t -> t -> t -> t -> t -> t -> t -> t ->
 t -> t -> t -> t -> t -> t -> t -> t -> Nibble -> t;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleF = f16;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleE = f15;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleD = f14;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleC = f13;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleB = f12;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleA = f11;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble9 = f10;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble8 = f9;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble7 = f8;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble6 = f7;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble5 = f6;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble4 = f5;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble3 = f4;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble2 = f3;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble1 = f2;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble0 = f1;

itself_char :: Itself Chara;
itself_char = Type;

itself_list :: forall a. Itself [a];
itself_list = Type;

list_update :: forall a. [a] -> Nat -> a -> [a];
list_update (x : xs) i v =
  (case i of {
    Zero_nat -> v : xs;
    Suc j -> x : list_update xs j v;
  });
list_update [] i v = [];

nibble_case ::
  forall t.
    t -> t -> t -> t -> t -> t -> t -> t ->
 t -> t -> t -> t -> t -> t -> t -> t -> Nibble -> t;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble0 = f1;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble1 = f2;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble2 = f3;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble3 = f4;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble4 = f5;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble5 = f6;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble6 = f7;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble7 = f8;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble8 = f9;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble9 =
  f10;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleA =
  f11;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleB =
  f12;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleC =
  f13;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleD =
  f14;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleE =
  f15;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleF =
  f16;

nibble_size :: Nibble -> Nat;
nibble_size NibbleF = Zero_nat;
nibble_size NibbleE = Zero_nat;
nibble_size NibbleD = Zero_nat;
nibble_size NibbleC = Zero_nat;
nibble_size NibbleB = Zero_nat;
nibble_size NibbleA = Zero_nat;
nibble_size Nibble9 = Zero_nat;
nibble_size Nibble8 = Zero_nat;
nibble_size Nibble7 = Zero_nat;
nibble_size Nibble6 = Zero_nat;
nibble_size Nibble5 = Zero_nat;
nibble_size Nibble4 = Zero_nat;
nibble_size Nibble3 = Zero_nat;
nibble_size Nibble2 = Zero_nat;
nibble_size Nibble1 = Zero_nat;
nibble_size Nibble0 = Zero_nat;

size_nibble :: Nibble -> Nat;
size_nibble NibbleF = Zero_nat;
size_nibble NibbleE = Zero_nat;
size_nibble NibbleD = Zero_nat;
size_nibble NibbleC = Zero_nat;
size_nibble NibbleB = Zero_nat;
size_nibble NibbleA = Zero_nat;
size_nibble Nibble9 = Zero_nat;
size_nibble Nibble8 = Zero_nat;
size_nibble Nibble7 = Zero_nat;
size_nibble Nibble6 = Zero_nat;
size_nibble Nibble5 = Zero_nat;
size_nibble Nibble4 = Zero_nat;
size_nibble Nibble3 = Zero_nat;
size_nibble Nibble2 = Zero_nat;
size_nibble Nibble1 = Zero_nat;
size_nibble Nibble0 = Zero_nat;

itself_nibble :: Itself Nibble;
itself_nibble = Type;

successor_int :: Inta -> Inta;
successor_int = (\ i -> plus_int i (Number_of_int (Bit1 Pls)));

}
