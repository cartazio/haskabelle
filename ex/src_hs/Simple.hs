data Nat = Zero | Succ Nat

plus :: Nat -> Nat -> Nat
plus Zero n = n
plus (Succ m) n = Succ (plus m n)

mult :: Nat -> Nat -> Nat
mult Zero n = Zero
mult (Succ m) n = plus n (mult m n)

less_eq :: Nat -> Nat -> Bool
less :: Nat -> Nat -> Bool

less_eq Zero n = True
less_eq (Succ m) n = less m n
less n Zero = False
less n (Succ m) = less_eq n m

data Foo a = Tip a | Pair (Foo a) (Foo a)

size :: Foo a -> Nat
size (Tip a) = Succ Zero
size (Pair x y) = plus (size x) (size y)

cons :: a -> Foo a -> Foo a
cons x (Tip y) = Pair (Tip x) (Tip y)
cons x (Pair y z) = if less_eq (size y) (size z)
  then Pair (cons x y) z
  else Pair y (cons x z)

