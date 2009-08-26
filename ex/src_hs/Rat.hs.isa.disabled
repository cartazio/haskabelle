module Rat where {


data Inta = Number_of_int Rat.Inta | Bit1 Rat.Inta | Bit0 Rat.Inta | Min | Pls;

data Nat = Suc Rat.Nat | Zero_nat;

minus_nat :: Rat.Nat -> Rat.Nat -> Rat.Nat;
minus_nat (Rat.Suc m) (Rat.Suc n) = Rat.minus_nat m n;
minus_nat Rat.Zero_nat n = Rat.Zero_nat;
minus_nat m Rat.Zero_nat = m;

less_eq_nat :: Rat.Nat -> Rat.Nat -> Bool;
less_eq_nat (Rat.Suc m) n = Rat.less_nat m n;
less_eq_nat Rat.Zero_nat n = True;

less_nat :: Rat.Nat -> Rat.Nat -> Bool;
less_nat m (Rat.Suc n) = Rat.less_eq_nat m n;
less_nat n Rat.Zero_nat = False;

eq_nat :: Rat.Nat -> Rat.Nat -> Bool;
eq_nat Rat.Zero_nat Rat.Zero_nat = True;
eq_nat (Rat.Suc m) (Rat.Suc n) = Rat.eq_nat m n;
eq_nat Rat.Zero_nat (Rat.Suc a) = False;
eq_nat (Rat.Suc a) Rat.Zero_nat = False;

divmod :: Rat.Nat -> Rat.Nat -> (Rat.Nat, Rat.Nat);
divmod m n =
  (if Rat.eq_nat n Rat.Zero_nat || Rat.less_nat m n then (Rat.Zero_nat, m)
    else let {
           a = Rat.divmod (Rat.minus_nat m n) n;
           (q, aa) = a;
         } in (Rat.Suc q, aa));

mod_nat :: Rat.Nat -> Rat.Nat -> Rat.Nat;
mod_nat m n = snd (Rat.divmod m n);

gcda :: (Rat.Nat, Rat.Nat) -> Rat.Nat;
gcda (m, n) =
  (if Rat.eq_nat n Rat.Zero_nat then m else Rat.gcda (n, Rat.mod_nat m n));

preda :: Rat.Inta -> Rat.Inta;
preda (Rat.Bit1 k) = Rat.Bit0 k;
preda (Rat.Bit0 k) = Rat.Bit1 (Rat.preda k);
preda Rat.Min = Rat.Bit0 Rat.Min;
preda Rat.Pls = Rat.Min;

uminus_int :: Rat.Inta -> Rat.Inta;
uminus_int (Rat.Number_of_int w) = Rat.Number_of_int (Rat.uminus_int w);
uminus_int (Rat.Bit1 k) = Rat.Bit1 (Rat.preda (Rat.uminus_int k));
uminus_int (Rat.Bit0 k) = Rat.Bit0 (Rat.uminus_int k);
uminus_int Rat.Min = Rat.Bit1 Rat.Pls;
uminus_int Rat.Pls = Rat.Pls;

succa :: Rat.Inta -> Rat.Inta;
succa (Rat.Bit1 k) = Rat.Bit0 (Rat.succa k);
succa (Rat.Bit0 k) = Rat.Bit1 k;
succa Rat.Min = Rat.Pls;
succa Rat.Pls = Rat.Bit1 Rat.Pls;

plus_int :: Rat.Inta -> Rat.Inta -> Rat.Inta;
plus_int (Rat.Number_of_int v) (Rat.Number_of_int w) =
  Rat.Number_of_int (Rat.plus_int v w);
plus_int (Rat.Bit1 k) (Rat.Bit1 l) = Rat.Bit0 (Rat.plus_int k (Rat.succa l));
plus_int (Rat.Bit1 k) (Rat.Bit0 l) = Rat.Bit1 (Rat.plus_int k l);
plus_int (Rat.Bit0 k) (Rat.Bit1 l) = Rat.Bit1 (Rat.plus_int k l);
plus_int (Rat.Bit0 k) (Rat.Bit0 l) = Rat.Bit0 (Rat.plus_int k l);
plus_int k Rat.Min = Rat.preda k;
plus_int k Rat.Pls = k;
plus_int Rat.Min k = Rat.preda k;
plus_int Rat.Pls k = k;

minus_int :: Rat.Inta -> Rat.Inta -> Rat.Inta;
minus_int (Rat.Number_of_int v) (Rat.Number_of_int w) =
  Rat.Number_of_int (Rat.plus_int v (Rat.uminus_int w));

less_int :: Rat.Inta -> Rat.Inta -> Bool;
less_int (Rat.Bit1 k1) (Rat.Bit1 k2) = Rat.less_int k1 k2;
less_int (Rat.Bit1 k1) (Rat.Bit0 k2) = Rat.less_int k1 k2;
less_int (Rat.Bit0 k1) (Rat.Bit1 k2) = Rat.less_eq_int k1 k2;
less_int (Rat.Bit0 k1) (Rat.Bit0 k2) = Rat.less_int k1 k2;
less_int (Rat.Bit1 k) Rat.Min = Rat.less_int k Rat.Min;
less_int (Rat.Bit0 k) Rat.Min = Rat.less_eq_int k Rat.Min;
less_int (Rat.Bit1 k) Rat.Pls = Rat.less_int k Rat.Pls;
less_int (Rat.Bit0 k) Rat.Pls = Rat.less_int k Rat.Pls;
less_int Rat.Min (Rat.Bit1 k) = Rat.less_int Rat.Min k;
less_int Rat.Min (Rat.Bit0 k) = Rat.less_int Rat.Min k;
less_int Rat.Min Rat.Min = False;
less_int Rat.Min Rat.Pls = True;
less_int Rat.Pls (Rat.Bit1 k) = Rat.less_eq_int Rat.Pls k;
less_int Rat.Pls (Rat.Bit0 k) = Rat.less_int Rat.Pls k;
less_int Rat.Pls Rat.Min = False;
less_int Rat.Pls Rat.Pls = False;
less_int (Rat.Number_of_int k) (Rat.Number_of_int l) = Rat.less_int k l;

less_eq_int :: Rat.Inta -> Rat.Inta -> Bool;
less_eq_int (Rat.Bit1 k1) (Rat.Bit1 k2) = Rat.less_eq_int k1 k2;
less_eq_int (Rat.Bit1 k1) (Rat.Bit0 k2) = Rat.less_int k1 k2;
less_eq_int (Rat.Bit0 k1) (Rat.Bit1 k2) = Rat.less_eq_int k1 k2;
less_eq_int (Rat.Bit0 k1) (Rat.Bit0 k2) = Rat.less_eq_int k1 k2;
less_eq_int (Rat.Bit1 k) Rat.Min = Rat.less_eq_int k Rat.Min;
less_eq_int (Rat.Bit0 k) Rat.Min = Rat.less_eq_int k Rat.Min;
less_eq_int (Rat.Bit1 k) Rat.Pls = Rat.less_int k Rat.Pls;
less_eq_int (Rat.Bit0 k) Rat.Pls = Rat.less_eq_int k Rat.Pls;
less_eq_int Rat.Min (Rat.Bit1 k) = Rat.less_eq_int Rat.Min k;
less_eq_int Rat.Min (Rat.Bit0 k) = Rat.less_int Rat.Min k;
less_eq_int Rat.Min Rat.Min = True;
less_eq_int Rat.Min Rat.Pls = True;
less_eq_int Rat.Pls (Rat.Bit1 k) = Rat.less_eq_int Rat.Pls k;
less_eq_int Rat.Pls (Rat.Bit0 k) = Rat.less_eq_int Rat.Pls k;
less_eq_int Rat.Pls Rat.Min = False;
less_eq_int Rat.Pls Rat.Pls = True;
less_eq_int (Rat.Number_of_int k) (Rat.Number_of_int l) = Rat.less_eq_int k l;

nat_aux :: Rat.Inta -> Rat.Nat -> Rat.Nat;
nat_aux i n =
  (if Rat.less_eq_int i (Rat.Number_of_int Rat.Pls) then n
    else Rat.nat_aux (Rat.minus_int i (Rat.Number_of_int (Rat.Bit1 Rat.Pls)))
           (Rat.Suc n));

nat :: Rat.Inta -> Rat.Nat;
nat i = Rat.nat_aux i Rat.Zero_nat;

abs_int :: Rat.Inta -> Rat.Inta;
abs_int i =
  (if Rat.less_int i (Rat.Number_of_int Rat.Pls) then Rat.uminus_int i else i);

zero_int :: Rat.Inta;
zero_int = Rat.Number_of_int Rat.Pls;

one_int :: Rat.Inta;
one_int = Rat.Number_of_int (Rat.Bit1 Rat.Pls);

times_int :: Rat.Inta -> Rat.Inta -> Rat.Inta;
times_int (Rat.Number_of_int v) (Rat.Number_of_int w) =
  Rat.Number_of_int (Rat.times_int v w);
times_int (Rat.Bit1 k) l = Rat.plus_int (Rat.Bit0 (Rat.times_int k l)) l;
times_int (Rat.Bit0 k) l = Rat.Bit0 (Rat.times_int k l);
times_int Rat.Min k = Rat.uminus_int k;
times_int Rat.Pls w = Rat.Pls;

of_nat_aux :: Rat.Nat -> Inta -> Inta;
of_nat_aux (Rat.Suc n) i = Rat.of_nat_aux n (Rat.plus_int i Rat.one_int);
of_nat_aux Rat.Zero_nat i = i;

of_nat :: Rat.Nat -> Inta;
of_nat n = Rat.of_nat_aux n Rat.zero_int;

igcd :: Rat.Inta -> Rat.Inta -> Rat.Inta;
igcd i j =
  Rat.of_nat (Rat.gcda (Rat.nat (Rat.abs_int i), Rat.nat (Rat.abs_int j)));

eq_int :: Rat.Inta -> Rat.Inta -> Bool;
eq_int (Rat.Bit1 k1) (Rat.Bit1 k2) = Rat.eq_int k1 k2;
eq_int (Rat.Bit1 k1) (Rat.Bit0 k2) = False;
eq_int (Rat.Bit0 k1) (Rat.Bit1 k2) = False;
eq_int (Rat.Bit0 k1) (Rat.Bit0 k2) = Rat.eq_int k1 k2;
eq_int (Rat.Bit1 k1) Rat.Min = Rat.eq_int Rat.Min k1;
eq_int (Rat.Bit0 k1) Rat.Min = False;
eq_int (Rat.Bit1 k1) Rat.Pls = False;
eq_int (Rat.Bit0 k1) Rat.Pls = Rat.eq_int Rat.Pls k1;
eq_int Rat.Min (Rat.Bit1 k2) = Rat.eq_int Rat.Min k2;
eq_int Rat.Min (Rat.Bit0 k2) = False;
eq_int Rat.Min Rat.Min = True;
eq_int Rat.Min Rat.Pls = False;
eq_int Rat.Pls (Rat.Bit1 k2) = False;
eq_int Rat.Pls (Rat.Bit0 k2) = Rat.eq_int Rat.Pls k2;
eq_int Rat.Pls Rat.Min = False;
eq_int Rat.Pls Rat.Pls = True;
eq_int (Rat.Number_of_int k) (Rat.Number_of_int l) = Rat.eq_int k l;

adjust :: Rat.Inta -> (Rat.Inta, Rat.Inta) -> (Rat.Inta, Rat.Inta);
adjust b =
  (\ (a @ (q, r)) ->
    (if Rat.less_eq_int (Rat.Number_of_int Rat.Pls) (Rat.minus_int r b)
      then (Rat.plus_int
              (Rat.times_int (Rat.Number_of_int (Rat.Bit0 (Rat.Bit1 Rat.Pls)))
                q)
              (Rat.Number_of_int (Rat.Bit1 Rat.Pls)),
             Rat.minus_int r b)
      else (Rat.times_int (Rat.Number_of_int (Rat.Bit0 (Rat.Bit1 Rat.Pls))) q,
             r)));

negDivAlg :: Rat.Inta -> Rat.Inta -> (Rat.Inta, Rat.Inta);
negDivAlg a b =
  (if Rat.less_eq_int (Rat.Number_of_int Rat.Pls) (Rat.plus_int a b) ||
        Rat.less_eq_int b (Rat.Number_of_int Rat.Pls)
    then (Rat.Number_of_int Rat.Min, Rat.plus_int a b)
    else Rat.adjust b
           (Rat.negDivAlg a
             (Rat.times_int (Rat.Number_of_int (Rat.Bit0 (Rat.Bit1 Rat.Pls)))
               b)));

negateSnd :: (Rat.Inta, Rat.Inta) -> (Rat.Inta, Rat.Inta);
negateSnd = (\ (a @ (q, r)) -> (q, Rat.uminus_int r));

posDivAlg :: Rat.Inta -> Rat.Inta -> (Rat.Inta, Rat.Inta);
posDivAlg a b =
  (if Rat.less_int a b || Rat.less_eq_int b (Rat.Number_of_int Rat.Pls)
    then (Rat.Number_of_int Rat.Pls, a)
    else Rat.adjust b
           (Rat.posDivAlg a
             (Rat.times_int (Rat.Number_of_int (Rat.Bit0 (Rat.Bit1 Rat.Pls)))
               b)));

divAlg :: (Rat.Inta, Rat.Inta) -> (Rat.Inta, Rat.Inta);
divAlg =
  (\ (a @ (aa, b)) ->
    (if Rat.less_eq_int (Rat.Number_of_int Rat.Pls) aa
      then (if Rat.less_eq_int (Rat.Number_of_int Rat.Pls) b
             then Rat.posDivAlg aa b
             else (if Rat.eq_int aa (Rat.Number_of_int Rat.Pls)
                    then (Rat.Number_of_int Rat.Pls, Rat.Number_of_int Rat.Pls)
                    else Rat.negateSnd
                           (Rat.negDivAlg (Rat.uminus_int aa)
                             (Rat.uminus_int b))))
      else (if Rat.less_int (Rat.Number_of_int Rat.Pls) b
             then Rat.negDivAlg aa b
             else Rat.negateSnd
                    (Rat.posDivAlg (Rat.uminus_int aa) (Rat.uminus_int b)))));

{- of_int :: forall a. (Rat.Ring_1 a) => Rat.Inta -> a;
of_int k =
  (if Rat.eq_int k (Rat.Number_of_int Rat.Pls) then Rat.zero
    else (if Rat.less_int k (Rat.Number_of_int Rat.Pls)
           then Rat.uminus (Rat.of_int (Rat.uminus_int k))
           else let {
                  a = Rat.divAlg
                        (k, Rat.Number_of_int (Rat.Bit0 (Rat.Bit1 Rat.Pls)));
                  (l, m) = a;
                  l' = Rat.of_int l;
                } in (if Rat.eq_int m (Rat.Number_of_int Rat.Pls)
                       then Rat.plus l' l'
                       else Rat.plus (Rat.plus l' l') Rat.one))); -}

newtype Rat = Rationala (Rat.Inta, Rat.Inta);

div_int :: Rat.Inta -> Rat.Inta -> Rat.Inta;
div_int a b = fst (Rat.divAlg (a, b));

fract' :: Bool -> Rat.Inta -> Rat.Inta -> Rat.Rat;
fract' True k l =
  (if not (Rat.eq_int l (Rat.Number_of_int Rat.Pls)) then Rat.Rationala (k, l)
    else Rat.fract (Rat.Number_of_int (Rat.Bit1 Rat.Pls))
           (Rat.Number_of_int Rat.Pls));

fract :: Rat.Inta -> Rat.Inta -> Rat.Rat;
fract k l = Rat.fract' (not (Rat.eq_int l (Rat.Number_of_int Rat.Pls))) k l;

normNum :: (Rat.Inta, Rat.Inta) -> (Rat.Inta, Rat.Inta);
normNum =
  (\ (a @ (aa, b)) ->
    (if Rat.eq_int aa (Rat.Number_of_int Rat.Pls) ||
          Rat.eq_int b (Rat.Number_of_int Rat.Pls)
      then (Rat.Number_of_int Rat.Pls, Rat.Number_of_int Rat.Pls)
      else let {
             g = Rat.igcd aa b;
           } in (if Rat.less_int (Rat.Number_of_int Rat.Pls) b
                  then (Rat.div_int aa g, Rat.div_int b g)
                  else (Rat.uminus_int (Rat.div_int aa g),
                         Rat.uminus_int (Rat.div_int b g)))));

eq_rat :: Rat.Rat -> Rat.Rat -> Bool;
eq_rat (Rat.Rationala x) (Rat.Rationala y) = let
    (n1, d1) = Rat.normNum x
    (n2, d2) = Rat.normNum y
  in eq_int n1 n2 && eq_int d1 d2;

{-of_rat :: forall a. (Rat.Field_char_0 a) => Rat.Rat -> a;
of_rat (Rat.Rationala (k, l)) =
  (if not (Rat.eq_int l (Rat.Number_of_int Rat.Pls))
    then Rat.divide (Rat.of_int k) (Rat.of_int l) else Rat.zero);-}

nneg :: (Rat.Inta, Rat.Inta) -> (Rat.Inta, Rat.Inta);
nneg = (\ (a @ (aa, b)) -> (Rat.uminus_int aa, b));

nadd :: (Rat.Inta, Rat.Inta) -> (Rat.Inta, Rat.Inta) -> (Rat.Inta, Rat.Inta);
nadd =
  (\ (a @ (aa, b)) (c @ (a', b')) ->
    (if Rat.eq_int aa (Rat.Number_of_int Rat.Pls) ||
          Rat.eq_int b (Rat.Number_of_int Rat.Pls)
      then Rat.normNum (a', b')
      else (if Rat.eq_int a' (Rat.Number_of_int Rat.Pls) ||
                 Rat.eq_int b' (Rat.Number_of_int Rat.Pls)
             then Rat.normNum (aa, b)
             else Rat.normNum
                    (Rat.plus_int (Rat.times_int aa b') (Rat.times_int b a'),
                      Rat.times_int b b'))));

nsub :: (Rat.Inta, Rat.Inta) -> (Rat.Inta, Rat.Inta) -> (Rat.Inta, Rat.Inta);
nsub = (\ a b -> Rat.nadd a (Rat.nneg b));

nlt0 :: (Rat.Inta, Rat.Inta) -> Bool;
nlt0 = (\ (a @ (aa, b)) -> Rat.less_int aa (Rat.Number_of_int Rat.Pls));

nlt :: (Rat.Inta, Rat.Inta) -> (Rat.Inta, Rat.Inta) -> Bool;
nlt = (\ a b -> Rat.nlt0 (Rat.nsub a b));

less_rat :: Rat.Rat -> Rat.Rat -> Bool;
less_rat (Rat.Rationala x) (Rat.Rationala y) =
  Rat.nlt (Rat.normNum x) (Rat.normNum y);

nle0 :: (Rat.Inta, Rat.Inta) -> Bool;
nle0 = (\ (a @ (aa, b)) -> Rat.less_eq_int aa (Rat.Number_of_int Rat.Pls));

nle :: (Rat.Inta, Rat.Inta) -> (Rat.Inta, Rat.Inta) -> Bool;
nle = (\ a b -> Rat.nle0 (Rat.nsub a b));

less_eq_rat :: Rat.Rat -> Rat.Rat -> Bool;
less_eq_rat (Rat.Rationala x) (Rat.Rationala y) =
  Rat.nle (Rat.normNum x) (Rat.normNum y);

uminus_rat :: Rat.Rat -> Rat.Rat;
uminus_rat (Rat.Rationala x) = Rat.Rationala (Rat.nneg x);

abs_rat :: Rat.Rat -> Rat.Rat;
abs_rat q =
  (if Rat.less_rat q
        (Rat.Rationala (Rat.Number_of_int Rat.Pls, Rat.Number_of_int Rat.Pls))
    then Rat.uminus_rat q else q);

one_rat :: Rat.Rat;
one_rat =
  Rat.Rationala
    (Rat.Number_of_int (Rat.Bit1 Rat.Pls),
      Rat.Number_of_int (Rat.Bit1 Rat.Pls));

sgn_rat :: Rat.Rat -> Rat.Rat;
sgn_rat q =
  (if Rat.eq_rat q
        (Rat.Rationala (Rat.Number_of_int Rat.Pls, Rat.Number_of_int Rat.Pls))
    then Rat.Rationala (Rat.Number_of_int Rat.Pls, Rat.Number_of_int Rat.Pls)
    else (if Rat.less_rat
               (Rat.Rationala
                 (Rat.Number_of_int Rat.Pls, Rat.Number_of_int Rat.Pls))
               q
           then Rat.Rationala
                  (Rat.Number_of_int (Rat.Bit1 Rat.Pls),
                    Rat.Number_of_int (Rat.Bit1 Rat.Pls))
           else Rat.uminus_rat
                  (Rat.Rationala
                    (Rat.Number_of_int (Rat.Bit1 Rat.Pls),
                      Rat.Number_of_int (Rat.Bit1 Rat.Pls)))));

ninv :: (Rat.Inta, Rat.Inta) -> (Rat.Inta, Rat.Inta);
ninv =
  (\ (a @ (aa, b)) ->
    (if Rat.less_int aa (Rat.Number_of_int Rat.Pls)
      then (Rat.uminus_int b, Rat.abs_int aa) else (b, aa)));

nmul :: (Rat.Inta, Rat.Inta) -> (Rat.Inta, Rat.Inta) -> (Rat.Inta, Rat.Inta);
nmul =
  (\ (a @ (aa, b)) (c @ (a', b')) ->
    let {
      g = Rat.igcd (Rat.times_int aa a') (Rat.times_int b b');
    } in (Rat.div_int (Rat.times_int aa a') g,
           Rat.div_int (Rat.times_int b b') g));

ndiv :: (Rat.Inta, Rat.Inta) -> (Rat.Inta, Rat.Inta) -> (Rat.Inta, Rat.Inta);
ndiv = (\ a b -> Rat.nmul a (Rat.ninv b));

plus_rat :: Rat.Rat -> Rat.Rat -> Rat.Rat;
plus_rat (Rat.Rationala x) (Rat.Rationala y) = Rat.Rationala (Rat.nadd x y);

zero_rat :: Rat.Rat;
zero_rat = Rat.Rationala (Rat.Number_of_int Rat.Pls, Rat.Number_of_int Rat.Pls);

minus_rat :: Rat.Rat -> Rat.Rat -> Rat.Rat;
minus_rat (Rat.Rationala x) (Rat.Rationala y) = Rat.Rationala (Rat.nsub x y);

times_rat :: Rat.Rat -> Rat.Rat -> Rat.Rat;
times_rat (Rat.Rationala x) (Rat.Rationala y) = Rat.Rationala (Rat.nmul x y);

power_rat :: Rat.Rat -> Rat.Nat -> Rat.Rat;
power_rat q (Rat.Suc n) = Rat.times_rat q (Rat.power_rat q n);
power_rat q Rat.Zero_nat =
  Rat.Rationala
    (Rat.Number_of_int (Rat.Bit1 Rat.Pls),
      Rat.Number_of_int (Rat.Bit1 Rat.Pls));

divide_rat :: Rat.Rat -> Rat.Rat -> Rat.Rat;
divide_rat (Rat.Rationala x) (Rat.Rationala y) = Rat.Rationala (Rat.ndiv x y);

inverse_rat :: Rat.Rat -> Rat.Rat;
inverse_rat (Rat.Rationala x) = Rat.Rationala (Rat.ninv x);

}
