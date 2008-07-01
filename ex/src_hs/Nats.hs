module Nats where {


data Nat = Suc Nat | Zero_nat deriving Show;

eq_nat :: Nat -> Nat -> Bool;
eq_nat Zero_nat Zero_nat = True;
eq_nat (Suc m) (Suc n) = eq_nat m n;
eq_nat Zero_nat (Suc a) = False;
eq_nat (Suc a) Zero_nat = False;

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat (Suc m) n = less_nat m n;
less_eq_nat Zero_nat n = True;

less_nat :: Nat -> Nat -> Bool;
less_nat m (Suc n) = less_eq_nat m n;
less_nat n Zero_nat = False;

mina :: Nat -> Nat -> Nat;
mina a b = (if less_eq_nat a b then a else b);

nat_rec :: forall t. t -> (Nat -> t -> t) -> Nat -> t;
nat_rec f1 f2 (Suc n) = f2 n (nat_rec f1 f2 n);
nat_rec f1 f2 Zero_nat = f1;

one_nat :: Nat;
one_nat = Suc Zero_nat;

maxa :: Nat -> Nat -> Nat;
maxa a b = (if less_eq_nat a b then b else a);

nat_case :: forall t. t -> (Nat -> t) -> Nat -> t;
nat_case f1 f2 Zero_nat = f1;
nat_case f1 f2 (Suc n) = f2 n;

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suc m) n = plus_nat m (Suc n);
plus_nat Zero_nat n = n;

minus_nat :: Nat -> Nat -> Nat;
minus_nat (Suc m) (Suc n) = minus_nat m n;
minus_nat Zero_nat n = Zero_nat;
minus_nat m Zero_nat = m;

times_nat :: Nat -> Nat -> Nat;
times_nat (Suc m) n = plus_nat n (times_nat m n);
times_nat Zero_nat n = Zero_nat;

}
