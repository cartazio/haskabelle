{-# OPTIONS_GHC -fglasgow-exts #-}

module Rationals where {


data Nat = Zero | Suc Nat;

leta :: forall b a. b -> (b -> a) -> a;
leta s f = f s;

class One a where {
  one :: a;
};

class Orda a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

nat_aux :: Integer -> Nat -> Nat;
nat_aux i n = (if i <= 0 then n else nat_aux (i - 1) (Suc n));

nat :: Integer -> Nat;
nat i = nat_aux i Zero;

class Plus a where {
  plus :: a -> a -> a;
};

class Zero a where {
  zero :: a;
};

class Minus a where {
  minus :: a -> a -> a;
};

class Times a where {
  times :: a -> a -> a;
};

data Itself a = Type;

class Inverse a where {
  inverse :: a -> a;
  divide :: a -> a -> a;
};

class Uminus a where {
  neg :: a -> a;
};

instance Times Integer where {
  times a b = a * b;
};

class (Times a) => Dvd a where {
};

instance Dvd Integer where {
};

class (One a, Zero a) => Zero_neq_one a where {
};

class (Times a) => Semigroup_mult a where {
};

class (Plus a) => Semigroup_add a where {
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Ab_semigroup_add a, Semigroup_mult a) => Semiring a where {
};

class (Times a, Zero a) => Mult_zero a where {
};

class (Zero a, Semigroup_add a) => Monoid_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

class (Comm_monoid_add a, Mult_zero a, Semiring a) => Semiring_0 a where {
};

class (Semigroup_add a) => Cancel_semigroup_add a where {
};

class (Ab_semigroup_add a,
        Cancel_semigroup_add a) => Cancel_ab_semigroup_add a where {
};

class (Cancel_ab_semigroup_add a,
        Comm_monoid_add a) => Cancel_comm_monoid_add a where {
};

class (Cancel_comm_monoid_add a, Semiring_0 a) => Semiring_0_cancel a where {
};

class (One a, Times a) => Power a where {
};

class (Semigroup_mult a, Power a) => Monoid_mult a where {
};

class (Monoid_mult a, Semiring_0 a, Zero_neq_one a) => Semiring_1 a where {
};

class (Semiring_0_cancel a, Semiring_1 a) => Semiring_1_cancel a where {
};

split :: forall b c a. (b -> c -> a) -> (b, c) -> a;
split f (a, b) = f a b;

abs_int :: Integer -> Integer;
abs_int i = (if i < 0 then negate i else i);

sgn_int :: Integer -> Integer;
sgn_int i = (if i == 0 then 0 else (if 0 < i then 1 else negate 1));

apsnd :: forall c b a. (c -> b) -> (a, c) -> (a, b);
apsnd f (x, y) = (x, f y);

divmod_int :: Integer -> Integer -> (Integer, Integer); {-# HASKABELLE permissive divmod_int divmod'0 #-};
divmod_int k l =
  (if k == 0 then (0, 0)
    else (if l == 0 then (0, k)
           else apsnd (\ a -> sgn_int l * a)
                  (if sgn_int k == sgn_int l
                    then (\k l -> divmod' (abs k) (abs l)) k l
                    else let {
                           (r, s) = (\k l -> divmod' (abs k) (abs l)) k l;
                         } in (if s == 0 then (negate r, 0)
                                else (negate r - 1, abs_int l - s))))) where  {
    divmod' k l = if l == 0 || k < l then (0, k)
      else let (q, r) = divmod' (k - l) l in (q + 1, r);
  };

class (Minus a, Uminus a, Monoid_add a) => Group_add a where {
};

class (Cancel_comm_monoid_add a, Group_add a) => Ab_group_add a where {
};

class (Ab_group_add a, Semiring_0_cancel a) => Ring a where {
};

class (Ring a, Semiring_1_cancel a) => Ring_1 a where {
};

of_int :: forall a. (Ring_1 a) => Integer -> a; {-# HASKABELLE permissive of_int #-};
of_int k =
  (if k == 0 then zero
    else (if k < 0 then neg (of_int (negate k))
           else let {
                  (l, m) = divmod_int k 2;
                  l' = of_int l;
                } in (if m == 0 then plus l' l' else plus (plus l' l') one)));

instance One Integer where {
  one = 1;
};

eq_nat :: Nat -> Nat -> Bool;
eq_nat (Suc nat') Zero = False;
eq_nat Zero (Suc nat') = False;
eq_nat (Suc nat) (Suc nat') = eq_nat nat nat';
eq_nat Zero Zero = True;

of_nat_aux :: forall a. (Semiring_1 a) => (a -> a) -> Nat -> a -> a;
of_nat_aux inc Zero i = i;
of_nat_aux inc (Suc n) i = of_nat_aux inc n (inc i);

of_nat :: forall a. (Semiring_1 a) => Nat -> a; {-# HASKABELLE permissive of_nat #-};
of_nat n = of_nat_aux (\ i -> plus i one) n zero;

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

data Chara = Chara Nibble Nibble;

class (Dvd a) => Div a where {
  diva :: a -> a -> a;
  moda :: a -> a -> a;
};

minus_nat :: Nat -> Nat -> Nat;
minus_nat (Suc m) (Suc n) = minus_nat m n;
minus_nat Zero n = Zero;
minus_nat m Zero = m;

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat (Suc m) n = less_nat m n;
less_eq_nat Zero n = True;

less_nat :: Nat -> Nat -> Bool;
less_nat m (Suc n) = less_eq_nat m n;
less_nat n Zero = False;

divmod :: Nat -> Nat -> (Nat, Nat); {-# HASKABELLE permissive divmod #-};
divmod m n =
  (if eq_nat n Zero || less_nat m n then (Zero, m)
    else let {
           (q, a) = divmod (minus_nat m n) n;
         } in (Suc q, a));

mod_nat :: Nat -> Nat -> Nat;
mod_nat m n = snd (divmod m n);

gcd_nat :: Nat -> Nat -> Nat; {-# HASKABELLE permissive gcd_nat #-};
gcd_nat x y = (if eq_nat y Zero then x else gcd_nat y (mod_nat x y));

instance Zero Integer where {
  zero = 1;
};

instance Zero_neq_one Integer where {
};

instance Semigroup_mult Integer where {
};

instance Plus Integer where {
  plus a b = a + b;
};

instance Semigroup_add Integer where {
};

instance Ab_semigroup_add Integer where {
};

instance Semiring Integer where {
};

instance Mult_zero Integer where {
};

instance Monoid_add Integer where {
};

instance Comm_monoid_add Integer where {
};

instance Semiring_0 Integer where {
};

instance Power Integer where {
};

instance Monoid_mult Integer where {
};

instance Semiring_1 Integer where {
};

gcd_int :: Integer -> Integer -> Integer;
gcd_int x y = of_nat (gcd_nat (nat (abs_int x)) (nat (abs_int y)));

data Rat = Fract Integer Integer;

collect :: forall a. (a -> Bool) -> a -> Bool;
collect p = p;

scomp :: forall a c d b. (a -> (c, d)) -> (c -> d -> b) -> a -> b;
scomp f g = (\ x -> let {
                      (a, b) = f x;
                    } in g a b);

data Typerep = Typerep String [Typerep];

data Term = Const String Typerep | App Term Term;

mod_int :: Integer -> Integer -> Integer;
mod_int a b = snd (divmod_int a b);

div_int :: Integer -> Integer -> Integer;
div_int a b = fst (divmod_int a b);

instance Div Integer where {
  diva = div_int;
  moda = mod_int;
};

maxaa :: forall a. (a -> a -> Bool) -> a -> a -> a;
maxaa less_eq a b = (if less_eq a b then b else a);

maxa :: forall a. (Orda a) => a -> a -> a;
maxa = maxaa less_eq;

minaa :: forall a. (a -> a -> Bool) -> a -> a -> a;
minaa less_eq a b = (if less_eq a b then a else b);

mina :: forall a. (Orda a) => a -> a -> a;
mina = minaa less_eq;

class (Semiring_1 a) => Semiring_char_0 a where {
};

class (Semiring_char_0 a, Ring_1 a) => Ring_char_0 a where {
};

eq_rat :: Rat -> Rat -> Bool;
eq_rat (Fract a b) (Fract c d) =
  (if b == 0 then c == 0 || d == 0
    else (if d == 0 then a == 0 || b == 0 else a * d == b * c));

class (Times a, Zero a) => No_zero_divisors a where {
};

class (No_zero_divisors a, Ring a) => Ring_no_zero_divisors a where {
};

class (Ring_1 a, Ring_no_zero_divisors a) => Ring_1_no_zero_divisors a where {
};

class (Inverse a, Ring_1_no_zero_divisors a) => Division_ring a where {
};

class (Semigroup_mult a) => Ab_semigroup_mult a where {
};

class (Ab_semigroup_mult a, Semiring a) => Comm_semiring a where {
};

class (Comm_semiring a, Semiring_0 a) => Comm_semiring_0 a where {
};

class (Ab_semigroup_mult a, Monoid_mult a) => Comm_monoid_mult a where {
};

class (Comm_monoid_mult a, Comm_semiring_0 a, Dvd a,
        Semiring_1 a) => Comm_semiring_1 a where {
};

class (Comm_semiring_0 a,
        Semiring_0_cancel a) => Comm_semiring_0_cancel a where {
};

class (Comm_semiring_0_cancel a, Comm_semiring_1 a,
        Semiring_1_cancel a) => Comm_semiring_1_cancel a where {
};

class (Comm_semiring_0_cancel a, Ring a) => Comm_ring a where {
};

class (Comm_ring a, Comm_semiring_1_cancel a, Ring_1 a) => Comm_ring_1 a where {
};

class (Comm_ring_1 a, Ring_1_no_zero_divisors a) => Idom a where {
};

class (Division_ring a, Idom a) => Field a where {
};

class (Ring_char_0 a, Field a) => Field_char_0 a where {
};

of_rat :: forall a. (Field_char_0 a) => Rat -> a; {-# HASKABELLE permissive of_rat #-};
of_rat (Fract a b) =
  (if not (b == 0) then divide (of_int a) (of_int b) else zero);

one_rat :: Rat;
one_rat = Fract 1 1;

instance One Rat where {
  one = one_rat;
};

less_rat :: Rat -> Rat -> Bool;
less_rat (Fract a b) (Fract c d) =
  (if b == 0 then 0 < sgn_int c * sgn_int d
    else (if d == 0 then sgn_int a * sgn_int b < 0
           else (a * abs_int d * sgn_int b) < (c * abs_int b * sgn_int d)));

less_eq_rat :: Rat -> Rat -> Bool;
less_eq_rat (Fract a b) (Fract c d) =
  (if b == 0 then 0 <= sgn_int c * sgn_int d
    else (if d == 0 then sgn_int a * sgn_int b <= 0
           else (a * abs_int d * sgn_int b) <= (c * abs_int b * sgn_int d)));

instance Orda Rat where {
  less_eq = less_eq_rat;
  less = less_rat;
};

abs_rat :: Rat -> Rat;
abs_rat (Fract a b) = Fract (abs_int a) (abs_int b);

inf_rat :: Rat -> Rat -> Rat;
inf_rat = mina;

fract_norm :: Integer -> Integer -> Rat;
fract_norm a b =
  (if a == 0 || b == 0 then Fract 0 1
    else let {
           c = gcd_int a b;
         } in (if 0 < b then Fract (div_int a c) (div_int b c)
                else Fract (negate (div_int a c)) (negate (div_int b c))));

plus_rat :: Rat -> Rat -> Rat;
plus_rat (Fract a b) (Fract c d) =
  (if b == 0 then Fract c d
    else (if d == 0 then Fract a b else fract_norm (a * d + c * b) (b * d)));

instance Plus Rat where {
  plus = plus_rat;
};

times_rat :: Rat -> Rat -> Rat;
times_rat (Fract a b) (Fract c d) = fract_norm (a * c) (b * d);

instance Times Rat where {
  times = times_rat;
};

instance Semigroup_mult Rat where {
};

instance Semigroup_add Rat where {
};

instance Ab_semigroup_add Rat where {
};

instance Semiring Rat where {
};

zero_rat :: Rat;
zero_rat = Fract 0 1;

instance Zero Rat where {
  zero = zero_rat;
};

instance Mult_zero Rat where {
};

instance Monoid_add Rat where {
};

instance Comm_monoid_add Rat where {
};

instance Semiring_0 Rat where {
};

instance Cancel_semigroup_add Rat where {
};

instance Cancel_ab_semigroup_add Rat where {
};

instance Cancel_comm_monoid_add Rat where {
};

instance Semiring_0_cancel Rat where {
};

neg_rat :: Rat -> Rat;
neg_rat (Fract a b) = Fract (negate a) b;

instance Uminus Rat where {
  neg = neg_rat;
};

minus_rat :: Rat -> Rat -> Rat;
minus_rat (Fract a b) (Fract c d) =
  (if b == 0 then Fract (negate c) d
    else (if d == 0 then Fract a b else fract_norm (a * d - c * b) (b * d)));

instance Minus Rat where {
  minus = minus_rat;
};

instance Group_add Rat where {
};

instance Ab_group_add Rat where {
};

instance Ring Rat where {
};

instance Zero_neq_one Rat where {
};

instance Power Rat where {
};

instance Monoid_mult Rat where {
};

instance Semiring_1 Rat where {
};

instance Semiring_1_cancel Rat where {
};

instance Ring_1 Rat where {
};

sgn_rat :: Rat -> Rat;
sgn_rat (Fract a b) = of_int (sgn_int a * sgn_int b);

sup_rat :: Rat -> Rat -> Rat;
sup_rat = maxa;

divide_rat :: Rat -> Rat -> Rat;
divide_rat (Fract a b) (Fract c d) = fract_norm (a * d) (b * c);

instance No_zero_divisors Integer where {
};

class (Div a, Comm_semiring_1_cancel a,
        No_zero_divisors a) => Semiring_div a where {
};

instance Cancel_semigroup_add Integer where {
};

instance Cancel_ab_semigroup_add Integer where {
};

instance Cancel_comm_monoid_add Integer where {
};

instance Semiring_0_cancel Integer where {
};

instance Semiring_1_cancel Integer where {
};

instance Ab_semigroup_mult Integer where {
};

instance Comm_semiring Integer where {
};

instance Comm_semiring_0 Integer where {
};

instance Comm_monoid_mult Integer where {
};

instance Comm_semiring_1 Integer where {
};

instance Comm_semiring_0_cancel Integer where {
};

instance Comm_semiring_1_cancel Integer where {
};

instance Semiring_div Integer where {
};

}
