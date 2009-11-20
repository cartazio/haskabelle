module Sets where {


data Nat = Suc Nat | Zero;

data Set a = Insert a (Set a) | Empty;

bex :: forall a. Set a -> (a -> Bool) -> Bool;
bex Empty p = False;
bex (Insert a aa) p = p a || bex aa p;

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball Empty p = True;
ball (Insert a aa) p = p a && ball aa p;

member :: Nat -> Set Nat -> Bool;
member a aa = bex aa (eq_nat a);

uniona :: Set Nat -> Set Nat -> Set Nat;
uniona a Empty = a;
uniona Empty a = a;
uniona (Insert a aa) b =
  let {
    c = uniona aa b;
  } in (if member a b then c else Insert a c);

union :: forall b. Set b -> (b -> Set Nat) -> Set Nat;
union Empty f = Empty;
union (Insert a aa) f = uniona (f a) (union aa f);

image :: forall b. (b -> Nat) -> Set b -> Set Nat;
image f a = union a (\ x -> Insert (f x) Empty);

intersect :: Set Nat -> Set Nat -> Set Nat;
intersect a Empty = Empty;
intersect Empty a = Empty;
intersect (Insert a aa) b =
  let {
    c = intersect aa b;
  } in (if member a b then Insert a c else c);

intera :: forall b. Set b -> (b -> Set Nat) -> Set Nat;
intera (Insert a Empty) f = f a;
intera (Insert a aa) f = intersect (f a) (intera aa f);

inter :: Set (Set Nat) -> Set Nat;
inter a = intera a (\ x -> x);

eq_nat :: Nat -> Nat -> Bool;
eq_nat Zero Zero = True;
eq_nat (Suc m) (Suc n) = eq_nat m n;
eq_nat Zero (Suc a) = False;
eq_nat (Suc a) Zero = False;

less_eq_set :: Set Nat -> Set Nat -> Bool;
less_eq_set a b = ball a (\ x -> member x b);

eq_set :: Set Nat -> Set Nat -> Bool;
eq_set a b = less_eq_set a b && less_eq_set b a;

unionb :: Set (Set Nat) -> Set Nat;
unionb a = union a (\ x -> x);

project :: (Nat -> Bool) -> Set Nat -> Set Nat;
project p a = union a (\ aa -> (if p aa then Insert aa Empty else Empty));

minus_set :: Set Nat -> Set Nat -> Set Nat;
minus_set a Empty = a;
minus_set Empty a = Empty;
minus_set (Insert a aa) b =
  let {
    c = minus_set aa b;
  } in (if member a b then c else Insert a c);

is_empty :: forall a. Set a -> Bool;
is_empty Empty = True;
is_empty (Insert a aa) = False;

less_set :: Set Nat -> Set Nat -> Bool;
less_set a b = less_eq_set a b && not (less_eq_set b a);

}
