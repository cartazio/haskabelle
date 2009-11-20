module AVL where {


data Nat = Suc Nat | Zero;

data Set a = Insert a (Set a) | Empty;

data Tree a = Mkt a (Tree a) (Tree a) Nat | Et;

ht :: forall a. Tree a -> Nat;
ht (Mkt x l r h) = h;
ht Et = Zero;

bex :: forall a. Set a -> (a -> Bool) -> Bool;
bex Empty p = False;
bex (Insert a aa) p = p a || bex aa p;

data Tree_isub_0 a = MKT_isub_0 a (Tree_isub_0 a) (Tree_isub_0 a) | ET_isub_0;

erase :: forall a. Tree a -> Tree_isub_0 a;
erase (Mkt x l r h) = MKT_isub_0 x (erase l) (erase r);
erase Et = ET_isub_0;

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat (Suc m) n = less_nat m n;
less_eq_nat Zero n = True;

less_nat :: Nat -> Nat -> Bool;
less_nat m (Suc n) = less_eq_nat m n;
less_nat n Zero = False;

maxa :: Nat -> Nat -> Nat;
maxa a b = (if less_eq_nat a b then b else a);

one_nat :: Nat;
one_nat = Suc Zero;

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suc m) n = plus_nat m (Suc n);
plus_nat Zero n = n;

height :: forall a. Tree_isub_0 a -> Nat;
height (MKT_isub_0 n l r) = plus_nat one_nat (maxa (height l) (height r));
height ET_isub_0 = Zero;

eq_nat :: Nat -> Nat -> Bool;
eq_nat Zero Zero = True;
eq_nat (Suc m) (Suc n) = eq_nat m n;
eq_nat Zero (Suc a) = False;
eq_nat (Suc a) Zero = False;

hinv :: forall a. Tree a -> Bool;
hinv (Mkt x l r h) =
  eq_nat h (plus_nat one_nat (maxa (height (erase l)) (height (erase r)))) &&
    (hinv l && hinv r);
hinv Et = True;

is_bal :: forall a. Tree_isub_0 a -> Bool;
is_bal (MKT_isub_0 n l r) =
  (eq_nat (height l) (height r) ||
    (eq_nat (height l) (plus_nat one_nat (height r)) ||
      eq_nat (height r) (plus_nat one_nat (height l))))
    && (is_bal l && is_bal r);
is_bal ET_isub_0 = True;

avl :: forall a. Tree a -> Bool;
avl t = is_bal (erase t) && hinv t;

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball Empty p = True;
ball (Insert a aa) p = p a && ball aa p;

mkta :: forall a. a -> Tree a -> Tree a -> Tree a;
mkta x l r = Mkt x l r (plus_nat (maxa (ht l) (ht r)) one_nat);

member :: Nat -> Set Nat -> Bool;
member a aa = bex aa (eq_nat a);

union :: Set Nat -> Set Nat -> Set Nat;
union a Empty = a;
union Empty a = a;
union (Insert a aa) b =
  let {
    c = union aa b;
  } in (if member a b then c else Insert a c);

tree_case ::
  forall t a. t -> (a -> Tree a -> Tree a -> Nat -> t) -> Tree a -> t;
tree_case f1 f2 Et = f1;
tree_case f1 f2 (Mkt a tree1 tree2 n) = f2 a tree1 tree2 n;

r_bal :: forall a. (a, (Tree a, Tree a)) -> Tree a;
r_bal (n, (l, Mkt rn rl rr h)) =
  (if less_nat (ht rr) (ht rl)
    then (case rl of {
           Et -> Et;
           Mkt rln rll rlr ha -> mkta rln (mkta n l rll) (mkta rn rlr rr);
         })
    else mkta rn (mkta n l rl) rr);

l_bal :: forall a. (a, (Tree a, Tree a)) -> Tree a;
l_bal (n, (Mkt ln ll lr h, r)) =
  (if less_nat (ht ll) (ht lr)
    then (case lr of {
           Et -> Et;
           Mkt lrn lrl lrr lrh -> mkta lrn (mkta ln ll lrl) (mkta n lrr r);
         })
    else mkta ln ll (mkta n lr r));

insrt :: Nat -> Tree Nat -> Tree Nat;
insrt x (Mkt n l r h) =
  (if eq_nat x n then Mkt n l r h
    else (if less_nat x n
           then let {
                  l' = insrt x l;
                  hl' = ht l';
                  hr = ht r;
                } in (if eq_nat hl'
                           (plus_nat (Suc (Suc Zero)) hr)
                       then l_bal (n, (l', r))
                       else Mkt n l' r (plus_nat one_nat (maxa hl' hr)))
           else let {
                  r' = insrt x r;
                  hl = ht l;
                  hr' = ht r';
                } in (if eq_nat hr'
                           (plus_nat (Suc (Suc Zero)) hl)
                       then r_bal (n, (l, r'))
                       else Mkt n l r' (plus_nat one_nat (maxa hl hr')))));
insrt x Et = Mkt x Et Et one_nat;

is_in :: Nat -> Tree Nat -> Bool;
is_in k (Mkt n l r h) =
  (if eq_nat k n then True else (if less_nat k n then is_in k l else is_in k r));
is_in k Et = False;

set_of :: Tree_isub_0 Nat -> Set Nat;
set_of (MKT_isub_0 n l r) = Insert n (union (set_of l) (set_of r));
set_of ET_isub_0 = Empty;

is_ord :: Tree_isub_0 Nat -> Bool;
is_ord (MKT_isub_0 n l r) =
  ball (set_of l) (\ n' -> less_nat n' n) &&
    (ball (set_of r) (less_nat n) && (is_ord l && is_ord r));
is_ord ET_isub_0 = True;

-- eq_tree :: forall a. (Eq a) => Tree a -> Tree a -> Bool;
-- eq_tree Et Et = True;
-- eq_tree (Mkt a tree1 tree2 nat) (Mkt a' tree1' tree2' nat') =
--   a == a' &&
--     (eq_tree tree1 tree1' && (eq_tree tree2 tree2' && eq_nat nat nat'));
-- eq_tree Et (Mkt a b c d) = False;
-- eq_tree (Mkt a b c d) Et = False;

tree_rec ::
  forall t a. t -> (a -> Tree a -> Tree a -> Nat -> t -> t -> t) -> Tree a -> t;
tree_rec f1 f2 (Mkt a tree1 tree2 n) =
  f2 a tree1 tree2 n (tree_rec f1 f2 tree1) (tree_rec f1 f2 tree2);
tree_rec f1 f2 Et = f1;

size_tree :: forall a. Tree a -> Nat;
size_tree (Mkt a tree1 tree2 n) =
  plus_nat (plus_nat (size_tree tree1) (size_tree tree2)) (Suc Zero);
size_tree Et = Zero;

tree_size :: forall a. (a -> Nat) -> Tree a -> Nat;
tree_size fa (Mkt a tree1 tree2 n) =
  plus_nat
    (plus_nat (plus_nat (fa a) (tree_size fa tree1)) (tree_size fa tree2))
    (Suc Zero);
tree_size fa Et = Zero;

tree_isub_0_case ::
  forall t a.
    t -> (a -> Tree_isub_0 a -> Tree_isub_0 a -> t) -> Tree_isub_0 a -> t;
tree_isub_0_case f1 f2 ET_isub_0 = f1;
tree_isub_0_case f1 f2 (MKT_isub_0 a tree_isub_01 tree_isub_02) =
  f2 a tree_isub_01 tree_isub_02;

r_bal_isub_0 :: forall a. (a, (Tree_isub_0 a, Tree_isub_0 a)) -> Tree_isub_0 a;
r_bal_isub_0 (n, (l, MKT_isub_0 rn rl rr)) =
  (if less_nat (height rr) (height rl)
    then (case rl of {
           ET_isub_0 -> ET_isub_0;
           MKT_isub_0 rln rll rlr ->
             MKT_isub_0 rln (MKT_isub_0 n l rll) (MKT_isub_0 rn rlr rr);
         })
    else MKT_isub_0 rn (MKT_isub_0 n l rl) rr);

l_bal_isub_0 :: forall a. (a, (Tree_isub_0 a, Tree_isub_0 a)) -> Tree_isub_0 a;
l_bal_isub_0 (n, (MKT_isub_0 ln ll lr, r)) =
  (if less_nat (height ll) (height lr)
    then (case lr of {
           ET_isub_0 -> ET_isub_0;
           MKT_isub_0 lrn lrl lrr ->
             MKT_isub_0 lrn (MKT_isub_0 ln ll lrl) (MKT_isub_0 n lrr r);
         })
    else MKT_isub_0 ln ll (MKT_isub_0 n lr r));

insrt_isub_0 :: Nat -> Tree_isub_0 Nat -> Tree_isub_0 Nat;
insrt_isub_0 x (MKT_isub_0 n l r) =
  (if eq_nat x n then MKT_isub_0 n l r
    else (if less_nat x n
           then let {
                  l' = insrt_isub_0 x l;
                } in (if eq_nat (height l')
                           (plus_nat (Suc (Suc Zero))
                             (height r))
                       then l_bal_isub_0 (n, (l', r)) else MKT_isub_0 n l' r)
           else let {
                  r' = insrt_isub_0 x r;
                } in (if eq_nat (height r')
                           (plus_nat (Suc (Suc Zero))
                             (height l))
                       then r_bal_isub_0 (n, (l, r')) else MKT_isub_0 n l r')));
insrt_isub_0 x ET_isub_0 = MKT_isub_0 x ET_isub_0 ET_isub_0;

is_in_isub_0 :: Nat -> Tree_isub_0 Nat -> Bool;
is_in_isub_0 k (MKT_isub_0 n l r) =
  (if eq_nat k n then True
    else (if less_nat k n then is_in_isub_0 k l else is_in_isub_0 k r));
is_in_isub_0 k ET_isub_0 = False;

-- eq_tree_isub_0 :: forall a. (Eq a) => Tree_isub_0 a -> Tree_isub_0 a -> Bool;
-- eq_tree_isub_0 ET_isub_0 ET_isub_0 = True;
-- eq_tree_isub_0 (MKT_isub_0 a tree_isub_01 tree_isub_02)
--   (MKT_isub_0 a' tree_isub_01' tree_isub_02') =
--   a == a' &&
--     (eq_tree_isub_0 tree_isub_01 tree_isub_01' &&
--       eq_tree_isub_0 tree_isub_02 tree_isub_02');
-- eq_tree_isub_0 ET_isub_0 (MKT_isub_0 a b c) = False;
-- eq_tree_isub_0 (MKT_isub_0 a b c) ET_isub_0 = False;

tree_isub_0_rec ::
  forall t a.
    t -> (a -> Tree_isub_0 a -> Tree_isub_0 a -> t -> t -> t) ->
           Tree_isub_0 a -> t;
tree_isub_0_rec f1 f2 (MKT_isub_0 a tree_isub_01 tree_isub_02) =
  f2 a tree_isub_01 tree_isub_02 (tree_isub_0_rec f1 f2 tree_isub_01)
    (tree_isub_0_rec f1 f2 tree_isub_02);
tree_isub_0_rec f1 f2 ET_isub_0 = f1;

size_tree_isub_0 :: forall a. Tree_isub_0 a -> Nat;
size_tree_isub_0 (MKT_isub_0 a tree_isub_01 tree_isub_02) =
  plus_nat
    (plus_nat (size_tree_isub_0 tree_isub_01) (size_tree_isub_0 tree_isub_02))
    (Suc Zero);
size_tree_isub_0 ET_isub_0 = Zero;

tree_isub_0_size :: forall a. (a -> Nat) -> Tree_isub_0 a -> Nat;
tree_isub_0_size fa (MKT_isub_0 a tree_isub_01 tree_isub_02) =
  plus_nat
    (plus_nat (plus_nat (fa a) (tree_isub_0_size fa tree_isub_01))
      (tree_isub_0_size fa tree_isub_02))
    (Suc Zero);
tree_isub_0_size fa ET_isub_0 = Zero;

}
