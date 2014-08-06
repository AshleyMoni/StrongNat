module StrongNat

%default total

zero : Nat -> Bool
zero Z = True
zero (S _) = False

nonzero : so (not (zero Z)) -> _|_
nonzero oh impossible

pred' : (n : Nat) -> so (not (zero n)) -> Nat
pred' Z o = FalseElim (nonzero o)
pred' (S n) _ = n

(<<) : Nat -> Nat -> Bool
Z << Z = False
Z << (S _) = True
(S _) << Z = False
(S n) << (S m) = n << m

example : so (3 << 6)
example = oh

subtract : (x : Nat) -> (y : Nat) -> so (y << S x) -> Nat
subtract x Z oh = x
subtract Z (S Z) oh impossible
subtract Z (S (S Z)) oh impossible
subtract (S x) (S y) o = subtract x y o

-- *StrongNat> subtract 7 3 oh
-- 4 : Nat
