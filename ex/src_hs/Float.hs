{-# OPTIONS_GHC -fglasgow-exts #-}

module Float where {

positive :: Integer -> Integer;
positive k = if k < 0 then 0 else k;

leta :: forall b a. b -> (b -> a) -> a;
leta s f = f s;

class One a where {
  one :: a;
};

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

data Floata = Floata Integer Integer;

data Rat = Fract Integer Integer;

inverse_rat :: Rat -> Rat;
inverse_rat (Fract a b) =
  (if b == 0 then Fract 1 0
    else (if a < 0 then Fract (negate b) (negate a) else Fract b a));

newtype Reala = Ratreal Rat;

inverse_real :: Reala -> Reala;
inverse_real (Ratreal x) = Ratreal (inverse_rat x);

abs_int :: Integer -> Integer;
abs_int i = (if i < 0 then negate i else i);

split :: forall b c a. (b -> c -> a) -> (b, c) -> a;
split f (a, b) = f a b;

sgn_int :: Integer -> Integer;
sgn_int i = (if i == 0 then 0 else (if 0 < i then 1 else negate 1));

apsnd :: forall c b a. (c -> b) -> (a, c) -> (a, b);
apsnd f (x, y) = (x, f y);

div_mod :: Integer -> Integer -> (Integer, Integer); {-# HASKABELLE permissive div_mod #-};
div_mod m n =
  (if n == 0 || m < n then (0, m)
    else let {
           (q, a) = div_mod (m - n) n;
         } in (q + 1, a));

divmoda :: Integer -> Integer -> (Integer, Integer); {-# HASKABELLE permissive divmoda #-};
divmoda k l =
  (if k == 0 then (0, 0)
    else (if l == 0 then (0, k)
           else apsnd (\ a -> sgn_int l * a)
                  (if sgn_int k == sgn_int l
                    then (\k l -> div_mod (abs k) (abs l)) k l
                    else let {
                           (r, s) = (\k l -> div_mod (abs k) (abs l)) k l;
                         } in (if s == 0 then (negate r, 0)
                                else (negate r - 1, abs_int l - s)))));

div_int :: Integer -> Integer -> Integer;
div_int a b = fst (divmoda a b);

divmod :: Integer -> Integer -> (Integer, Integer);
divmod n m = (if m == 0 then (0, n) else div_mod n m);

mod_nat :: Integer -> Integer -> Integer;
mod_nat m n = snd (divmod m n);

gcd_nat :: Integer -> Integer -> Integer; {-# HASKABELLE permissive gcd_nat #-};
gcd_nat x y = (if y == 0 then x else gcd_nat y (mod_nat x y));

gcd_int :: Integer -> Integer -> Integer;
gcd_int x y =
  id (gcd_nat (positive (abs_int x)) (positive (abs_int y)));

fract_norm :: Integer -> Integer -> Rat;  {-# HASKABELLE permissive fract_norm #-};
fract_norm a b =
  (if a == 0 || b == 0 then Fract 0 1
    else let {
           c = gcd_int a b;
         } in (if 0 < b then Fract (div_int a c) (div_int b c)
                else Fract (negate (div_int a c)) (negate (div_int b c))));

times_rat :: Rat -> Rat -> Rat;
times_rat (Fract a b) (Fract c d) = fract_norm (a * c) (b * d);

times_real :: Reala -> Reala -> Reala;
times_real (Ratreal x) (Ratreal y) = Ratreal (times_rat x y);

instance Times Reala where {
  times = times_real;
};

class (One a, Times a) => Power a where {
};

one_real :: Reala;
one_real = Ratreal (Fract 1 1);

instance One Reala where {
  one = one_real;
};

instance Power Reala where {
};

minus_nat :: Integer -> Integer -> Integer;
minus_nat n m = positive (id n - id m);

power :: forall a. (Power a) => a -> Integer -> a;  {-# HASKABELLE permissive power #-};
power a n =
  (if n == 0 then one else times a (power a (minus_nat n 1)));

pow2 :: Integer -> Reala;
pow2 a =
  (if 0 <= a then power (Ratreal (Fract 2 1)) (positive a)
    else inverse_real (power (Ratreal (Fract 2 1)) (positive (negate a))));

class Neg a where {
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

class (Semigroup_mult a, Power a) => Monoid_mult a where {
};

class (Monoid_mult a, Semiring_0 a, Zero_neq_one a) => Semiring_1 a where {
};

class (Semiring_0_cancel a, Semiring_1 a) => Semiring_1_cancel a where {
};

class (Minus a, Neg a, Monoid_add a) => Group_add a where {
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
                  (l, m) = divmoda k 2;
                  l' = of_int l;
                } in (if m == 0 then plus l' l' else plus (plus l' l') one)));

instance One Integer where {
  one = 1;
};

foldla :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldla f a [] = a;
foldla f a (x : xs) = foldla f (f a x) xs;

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

data Chara = Chara Nibble Nibble;

class (Dvd a) => Div a where {
  diva :: a -> a -> a;
  moda :: a -> a -> a;
};

scale :: Floata -> Integer;
scale (Floata a b) = b;

instance Plus Integer where {
  plus a b = a + b;
};

instance Zero Integer where {
  zero = 0;
};

bitlen :: Integer -> Integer; {-# HASKABELLE permissive bitlen #-};
bitlen x =
  (if x == 0 then 0 else (if x == (-1) then 1 else 1 + bitlen (div_int x 2)));

times_float :: Floata -> Floata -> Floata;
times_float (Floata a_m a_e) (Floata b_m b_e) = Floata (a_m * b_m) (a_e + b_e);

mod_int :: Integer -> Integer -> Integer;
mod_int a b = snd (divmoda a b);

even_int :: Integer -> Bool;
even_int x = mod_int x 2 == 0;

normfloat :: Floata -> Floata; {-# HASKABELLE permissive normfloat #-};
normfloat (Floata a b) =
  (if not (a == 0) && even_int a then normfloat (Floata (div_int a 2) (b + 1))
    else (if a == 0 then Floata 0 0 else Floata a b));

instance Power Integer where {
};

lapprox_posrat :: Integer -> Integer -> Integer -> Floata;
lapprox_posrat prec x y =
  let {
    l = positive (id prec + bitlen y - bitlen x);
    d = div_int (x * power 2 l) y;
  } in normfloat (Floata d (negate (id l)));

neg_float :: Floata -> Floata;
neg_float (Floata m e) = Floata (negate m) e;

rapprox_posrat :: Integer -> Integer -> Integer -> Floata;
rapprox_posrat prec x y =
  let {
    l = positive (id prec + bitlen y - bitlen x);
    xa = x * power 2 l;
    d = div_int xa y;
    m = mod_int xa y;
  } in normfloat
         (Floata (d + (if m == 0 then 0 else 1)) (negate (id l)));

zero_float :: Floata;
zero_float = Floata 0 0;

rapprox_rat :: Integer -> Integer -> Integer -> Floata;
rapprox_rat prec x y =
  (if y == 0 then zero_float
    else (if 0 <= x
           then (if 0 < y then rapprox_posrat prec x y
                  else neg_float (lapprox_posrat prec x (negate y)))
           else (if 0 < y then neg_float (lapprox_posrat prec (negate x) y)
                  else rapprox_posrat prec (negate x) (negate y))));

float_divr :: Integer -> Floata -> Floata -> Floata;
float_divr prec (Floata m1 s1) (Floata m2 s2) =
  let {
    r = rapprox_rat prec m1 m2;
    f = Floata 1 (s1 - s2);
  } in times_float f r;

ceiling_fl :: Floata -> Floata;
ceiling_fl (Floata m e) =
  (if 0 <= e then Floata m e
    else Floata (div_int m (power 2 (positive (negate e))) + 1) 0);

plus_float :: Floata -> Floata -> Floata;
plus_float (Floata a_m a_e) (Floata b_m b_e) =
  (if a_e <= b_e then Floata (a_m + b_m * power 2 (positive (b_e - a_e))) a_e
    else Floata (a_m * power 2 (positive (a_e - b_e)) + b_m) b_e);

minus_float :: Floata -> Floata -> Floata;
minus_float z w = plus_float z (neg_float w);

lb_mod :: Integer -> Floata -> Floata -> Floata -> Floata;
lb_mod prec x ub lb =
  minus_float x (times_float (ceiling_fl (float_divr prec x lb)) ub);

lapprox_rat :: Integer -> Integer -> Integer -> Floata;
lapprox_rat prec x y =
  (if y == 0 then zero_float
    else (if 0 <= x
           then (if 0 < y then lapprox_posrat prec x y
                  else neg_float (rapprox_posrat prec x (negate y)))
           else (if 0 < y then neg_float (rapprox_posrat prec (negate x) y)
                  else lapprox_posrat prec (negate x) (negate y))));

float_divl :: Integer -> Floata -> Floata -> Floata;
float_divl prec (Floata m1 s1) (Floata m2 s2) =
  let {
    l = lapprox_rat prec m1 m2;
    f = Floata 1 (s1 - s2);
  } in times_float f l;

floor_fl :: Floata -> Floata;
floor_fl (Floata m e) =
  (if 0 <= e then Floata m e
    else Floata (div_int m (power 2 (positive (negate e)))) 0);

ub_mod :: Integer -> Floata -> Floata -> Floata -> Floata;
ub_mod prec x ub lb =
  minus_float x (times_float (floor_fl (float_divl prec x ub)) lb);

instance Div Integer where {
  diva = div_int;
  moda = mod_int;
};

eq_float :: Floata -> Floata -> Bool;
eq_float (Floata int1 int2) (Floata int1' int2') =
  int1 == int1' && int2 == int2';

mantissa :: Floata -> Integer;
mantissa (Floata a b) = a;

zero_real :: Reala;
zero_real = Ratreal (Fract 0 1);

instance Zero Reala where {
  zero = zero_real;
};

instance Zero_neq_one Reala where {
};

instance Semigroup_mult Reala where {
};

plus_rat :: Rat -> Rat -> Rat;
plus_rat (Fract a b) (Fract c d) =
  (if b == 0 then Fract c d
    else (if d == 0 then Fract a b else fract_norm (a * d + c * b) (b * d)));

plus_real :: Reala -> Reala -> Reala;
plus_real (Ratreal x) (Ratreal y) = Ratreal (plus_rat x y);

instance Plus Reala where {
  plus = plus_real;
};

instance Semigroup_add Reala where {
};

instance Ab_semigroup_add Reala where {
};

instance Semiring Reala where {
};

instance Mult_zero Reala where {
};

instance Monoid_add Reala where {
};

instance Comm_monoid_add Reala where {
};

instance Semiring_0 Reala where {
};

instance Monoid_mult Reala where {
};

instance Semiring_1 Reala where {
};

instance Cancel_semigroup_add Reala where {
};

instance Cancel_ab_semigroup_add Reala where {
};

instance Cancel_comm_monoid_add Reala where {
};

instance Semiring_0_cancel Reala where {
};

instance Semiring_1_cancel Reala where {
};

neg_rat :: Rat -> Rat;
neg_rat (Fract a b) = Fract (negate a) b;

neg_real :: Reala -> Reala;
neg_real (Ratreal x) = Ratreal (neg_rat x);

instance Neg Reala where {
  neg = neg_real;
};

minus_rat :: Rat -> Rat -> Rat;
minus_rat (Fract a b) (Fract c d) =
  (if b == 0 then Fract (negate c) d
    else (if d == 0 then Fract a b else fract_norm (a * d - c * b) (b * d)));

minus_real :: Reala -> Reala -> Reala;
minus_real (Ratreal x) (Ratreal y) = Ratreal (minus_rat x y);

instance Minus Reala where {
  minus = minus_real;
};

instance Group_add Reala where {
};

instance Ab_group_add Reala where {
};

instance Ring Reala where {
};

instance Ring_1 Reala where {
};

of_float :: Floata -> Reala;
of_float (Floata a b) = times_real (of_int a) (pow2 b);

round_up :: Integer -> Floata -> Floata; {-# HASKABELLE permissive round_up #-};
round_up prec (Floata m e) =
  let {
    d = bitlen m - id prec;
  } in (if 0 < d
         then let {
                p = power 2 (positive d);
                n = div_int m p;
                r = mod_int m p;
              } in Floata (n + (if r == 0 then 0 else 1)) (e + d)
         else Floata m e);

float_abs :: Floata -> Floata;
float_abs (Floata m e) = Floata (abs_int m) e;

abs_float :: Floata -> Floata;
abs_float x = float_abs x;

one_float :: Floata;
one_float = Floata 1 0;

instance Semigroup_mult Integer where {
};

instance Semigroup_add Integer where {
};

instance Ab_semigroup_add Integer where {
};

instance Semiring Integer where {
};

float_nprt :: Floata -> Floata;
float_nprt (Floata a e) = (if 0 <= a then zero_float else Floata a e);

float_pprt :: Floata -> Floata;
float_pprt (Floata a e) = (if 0 <= a then Floata a e else zero_float);

float_size :: Floata -> Integer;
float_size (Floata int1 int2) = 0;

less_rat :: Rat -> Rat -> Bool;
less_rat (Fract a b) (Fract c d) =
  (if b == 0 then 0 < sgn_int c * sgn_int d
    else (if d == 0 then sgn_int a * sgn_int b < 0
           else (a * abs_int d * sgn_int b) < c * (abs_int b * sgn_int d)));

less_real :: Reala -> Reala -> Bool;
less_real (Ratreal x) (Ratreal y) = less_rat x y;

less_float :: Floata -> Floata -> Bool;
less_float z w = less_real (of_float z) (of_float w);

round_down :: Integer -> Floata -> Floata; {-# HASKABELLE permissive round_down #-};
round_down prec (Floata m e) =
  let {
    d = bitlen m - id prec;
  } in (if 0 < d
         then let {
                p = power 2 (positive d);
                n = div_int m p;
              } in Floata n (e + d)
         else Floata m e);

instance Mult_zero Integer where {
};

instance Monoid_add Integer where {
};

instance Comm_monoid_add Integer where {
};

instance Semiring_0 Integer where {
};

instance Zero_neq_one Integer where {
};

instance Monoid_mult Integer where {
};

instance Semiring_1 Integer where {
};

class (Times a, Zero a) => No_zero_divisors a where {
};

instance No_zero_divisors Integer where {
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

less_eq_rat :: Rat -> Rat -> Bool;
less_eq_rat (Fract a b) (Fract c d) =
  (if b == 0 then 0 <= sgn_int c * sgn_int d
    else (if d == 0 then sgn_int a * sgn_int b <= 0
           else (a * abs_int d * sgn_int b) <= (c * abs_int b * sgn_int d)));

less_eq_real :: Reala -> Reala -> Bool;
less_eq_real (Ratreal x) (Ratreal y) = less_eq_rat x y;

less_eq_float :: Floata -> Floata -> Bool;
less_eq_float z w = less_eq_real (of_float z) (of_float w);

}
