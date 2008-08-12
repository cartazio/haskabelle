module Lists where {


data Nat = Suc Lists.Nat | Zero_nat;

data Set a = Insert a (Lists.Set a) | Empty;

hd :: forall a. [a] -> a;
hd (x : xs) = x;

tl :: forall a. [a] -> [a];
tl (x : xs) = xs;
tl [] = [];

bex :: forall a. Lists.Set a -> (a -> Bool) -> Bool;
bex Lists.Empty p = False;
bex (Lists.Insert a aa) p = p a || Lists.bex aa p;

mapa :: forall b a. (b -> a) -> [b] -> [a];
mapa f (x : xs) = f x : Lists.mapa f xs;
mapa f [] = [];

nat_case :: forall t. t -> (Lists.Nat -> t) -> Lists.Nat -> t;
nat_case f1 f2 Lists.Zero_nat = f1;
nat_case f1 f2 (Lists.Suc n) = f2 n;

nth :: forall a. [a] -> Lists.Nat -> a;
nth (x : xs) n =
  (case n of {
    Lists.Zero_nat -> x;
    Lists.Suc a -> Lists.nth xs a;
  });

foldla :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldla f a (x : xs) = Lists.foldla f (f a x) xs;
foldla f a [] = a;

rev :: forall a. [a] -> [a];
rev xs = Lists.foldla (\ xsa x -> x : xsa) [] xs;

set :: forall a. [a] -> Lists.Set a;
set (x : xs) = Lists.Insert x (Lists.set xs);
set [] = Lists.Empty;

less_eq_nat :: Lists.Nat -> Lists.Nat -> Bool;
less_eq_nat (Lists.Suc m) n = Lists.less_nat m n;
less_eq_nat Lists.Zero_nat n = True;

less_nat :: Lists.Nat -> Lists.Nat -> Bool;
less_nat m (Lists.Suc n) = Lists.less_eq_nat m n;
less_nat n Lists.Zero_nat = False;

list_case :: forall t a. t -> (a -> [a] -> t) -> [a] -> t;
list_case f1 f2 [] = f1;
list_case f1 f2 (a : list) = f2 a list;

zipa :: forall a b. [a] -> [b] -> [(a, b)];
zipa xs (y : ys) =
  (case xs of {
    [] -> [];
    z : zs -> (z, y) : Lists.zipa zs ys;
  });
zipa xs [] = [];

dropa :: forall a. Lists.Nat -> [a] -> [a];
dropa n (x : xs) =
  (case n of {
    Lists.Zero_nat -> x : xs;
    Lists.Suc m -> Lists.dropa m xs;
  });
dropa n [] = [];

nulla :: forall a. [a] -> Bool;
nulla (x : xs) = False;
nulla [] = True;

lasta :: forall a. [a] -> a;
lasta (x : xs) = (if Lists.nulla xs then x else Lists.lasta xs);

insort :: Nat -> [Nat] -> [Nat];
insort x (y : ys) =
  (if Lists.less_eq_nat x y then x : y : ys else y : Lists.insort x ys);
insort x [] = [x];

sort :: [Nat] -> [Nat];
sort (x : xs) = Lists.insort x (Lists.sort xs);
sort [] = [];

takea :: forall a. Lists.Nat -> [a] -> [a];
takea n (x : xs) =
  (case n of {
    Lists.Zero_nat -> [];
    Lists.Suc m -> x : Lists.takea m xs;
  });
takea n [] = [];

eq_nat :: Lists.Nat -> Lists.Nat -> Bool;
eq_nat Lists.Zero_nat Lists.Zero_nat = True;
eq_nat (Lists.Suc m) (Lists.Suc n) = Lists.eq_nat m n;
eq_nat Lists.Zero_nat (Lists.Suc a) = False;
eq_nat (Lists.Suc a) Lists.Zero_nat = False;

foldra :: forall b a. (b -> a -> a) -> [b] -> a -> a;
foldra f (x : xs) a = f x (Lists.foldra f xs a);
foldra f [] a = a;

map_of :: forall c. [(Nat, c)] -> Nat -> Maybe c;
map_of ((l, v) : ps) k = (if Lists.eq_nat l k then Just v else Lists.map_of ps k);
map_of [] k = Nothing;

append :: forall a. [a] -> [a] -> [a];
append (x : xs) ys = x : Lists.append xs ys;
append [] ys = ys;

concata :: forall a. [[a]] -> [a];
concata (x : xs) = Lists.append x (Lists.concata xs);
concata [] = [];

filtera :: forall a. (a -> Bool) -> [a] -> [a];
filtera p (x : xs) =
  (if p x then x : Lists.filtera p xs else Lists.filtera p xs);
filtera p [] = [];

member :: Nat -> [Nat] -> Bool;
member x (y : ys) = (if Lists.eq_nat y x then True else Lists.member x ys);
member x [] = False;

rotate1 :: forall a. [a] -> [a];
rotate1 xs = (case xs of {
               [] -> [];
               x : xsa -> Lists.append xsa [x];
             });

fun_pow :: forall a. Lists.Nat -> (a -> a) -> a -> a;
fun_pow (Lists.Suc n) f = f . Lists.fun_pow n f;
fun_pow Lists.Zero_nat f = id;

rotate :: forall a. Lists.Nat -> [a] -> [a];
rotate n = Lists.fun_pow n Lists.rotate1;

sorted :: [Nat] -> Bool;
sorted (x : y : zs) = Lists.less_eq_nat x y && Lists.sorted (y : zs);
sorted [x] = True;
sorted [] = True;

splice :: forall a. [a] -> [a] -> [a];
splice (x : xs) (y : ys) = x : y : Lists.splice xs ys;
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

butlast :: forall a. [a] -> [a];
butlast (x : xs) = (if Lists.nulla xs then [] else x : Lists.butlast xs);
butlast [] = [];

list_ex :: forall a. (a -> Bool) -> [a] -> Bool;
list_ex p (x : xs) = p x || Lists.list_ex p xs;
list_ex p [] = False;

listsum :: [Nat] -> Nat;
listsum (x : xs) = Lists.plus_nat x (Lists.foldla Lists.plus_nat Lists.Zero_nat xs);
listsum [] = Lists.Zero_nat;

remdups :: [Nat] -> [Nat];
remdups (x : xs) =
  (if Lists.member x xs then Lists.remdups xs else x : Lists.remdups xs);
remdups [] = [];

remove1 :: Nat -> [Nat] -> [Nat];
remove1 x (y : xs) = (if Lists.eq_nat x y then xs else y : Lists.remove1 x xs);
remove1 x [] = [];

plus_nat :: Lists.Nat -> Lists.Nat -> Lists.Nat;
plus_nat (Lists.Suc m) n = Lists.plus_nat m (Lists.Suc n);
plus_nat Lists.Zero_nat n = n;

size_list :: forall a. [a] -> Lists.Nat;
size_list (a : list) =
  Lists.plus_nat (Lists.size_list list) (Lists.Suc Lists.Zero_nat);
size_list [] = Lists.Zero_nat;

map_comp :: forall b c a. (b -> Maybe c) -> (a -> Maybe b) -> a -> Maybe c;
map_comp f g = (\ k -> (case g k of {
                         Nothing -> Nothing;
                         Just a -> f a;
                       }));

map_upds :: forall b. (Nat -> Maybe b) -> [Nat] -> [b] -> Nat -> Maybe b;
map_upds m xs ys =
  Lists.map_add m (Lists.map_of (Lists.rev (Lists.zipa xs ys)));

distincts :: [Nat] -> Bool;
distincts (x : xs) = not (Lists.member x xs) && Lists.distincts xs;
distincts [] = True;

list_all :: forall a. (a -> Bool) -> [a] -> Bool;
list_all p (x : xs) = p x && Lists.list_all p xs;
list_all p [] = True;

list_rec :: forall t a. t -> (a -> [a] -> t -> t) -> [a] -> t;
list_rec f1 f2 (a : list) = f2 a list (Lists.list_rec f1 f2 list);
list_rec f1 f2 [] = f1;

dropWhilea :: forall a. (a -> Bool) -> [a] -> [a];
dropWhilea p (x : xs) = (if p x then Lists.dropWhilea p xs else x : xs);
dropWhilea p [] = [];

filtermap :: forall a b. (a -> Maybe b) -> [a] -> [b];
filtermap f (x : xs) =
  (case f x of {
    Nothing -> Lists.filtermap f xs;
    Just y -> y : Lists.filtermap f xs;
  });
filtermap f [] = [];

list_all2 :: forall a b. (a -> b -> Bool) -> [a] -> [b] -> Bool;
list_all2 p (x : xs) (y : ys) = p x y && Lists.list_all2 p xs ys;
list_all2 p xs [] = Lists.nulla xs;
list_all2 p [] ys = Lists.nulla ys;

list_size :: forall a. (a -> Lists.Nat) -> [a] -> Lists.Nat;
list_size fa (a : list) =
  Lists.plus_nat (Lists.plus_nat (fa a) (Lists.list_size fa list))
    (Lists.Suc Lists.Zero_nat);
list_size fa [] = Lists.Zero_nat;

split :: forall b c a. (b -> c -> a) -> (b, c) -> a;
split f (a, b) = f a b;

partition :: forall a. (a -> Bool) -> [a] -> ([a], [a]);
partition p (x : xs) =
  let {
    a = Lists.partition p xs;
    (yes, no) = a;
  } in (if p x then (x : yes, no) else (yes, x : no));
partition p [] = ([], []);

replicatea :: forall a. Lists.Nat -> a -> [a];
replicatea (Lists.Suc n) x = x : Lists.replicatea n x;
replicatea Lists.Zero_nat x = [];

takeWhilea :: forall a. (a -> Bool) -> [a] -> [a];
takeWhilea p (x : xs) = (if p x then x : Lists.takeWhilea p xs else []);
takeWhilea p [] = [];

list_inter :: forall a. [Nat] -> [Nat] -> [Nat];
list_inter (a : asa) bs =
  (if Lists.member a bs then a : Lists.list_inter asa bs
    else Lists.list_inter asa bs);
list_inter [] bs = [];

map_filter :: forall a b. (a -> b) -> (a -> Bool) -> [a] -> [b];
map_filter f p (x : xs) =
  (if p x then f x : Lists.map_filter f p xs else Lists.map_filter f p xs);
map_filter f p [] = [];

list_update :: forall a. [a] -> Lists.Nat -> a -> [a];
list_update (x : xs) i v =
  (case i of {
    Lists.Zero_nat -> v : xs;
    Lists.Suc j -> x : Lists.list_update xs j v;
  });
list_update [] i v = [];

}
