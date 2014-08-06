module StrongNat

%default total

data Unit = I

nonzero : Nat -> Type
nonzero Z = _|_
nonzero (S _) = Unit

pred' : (n : Nat) -> {default I ok : nonzero n} -> Nat
pred' Z {ok} = FalseElim ok
pred' (S n) = n

(<<) : Nat -> Nat -> Type
x << y = Exists (\d : Nat => S d + x = y)

example : 3 << 6
example = evidence 2 refl
-- 2 proves that 3 is less than 6
-- because (1+2) + 3 = 6

lt_add : (x : Nat) -> (y : Nat) -> x << S y + x
lt_add x y = evidence y refl

lt_zero_lemma : (d : Nat) -> (x : Nat) -> S d + x = 0 -> _|_
lt_zero_lemma d x refl impossible

lt_zero : (x : Nat) -> x << 0 -> _|_
lt_zero x (evidence d e) =  lt_zero_lemma d x e

exists_proof_helper : (P1 : Nat -> Type) -> (P2 : Nat -> Type) ->
                      ((d : Nat) -> P1 d -> P2 d) ->
                      Exists (\d : Nat => P1 d) -> Exists (\d : Nat => P2 d)
exists_proof_helper P1 P2 hyp (evidence d pf1) = evidence d (hyp d pf1)

lt_step_down_lemma : (d : Nat) -> S (plus d (S x)) = S y -> S (plus d x) = y
lt_step_down_lemma = ?prf0

lt_step_down : (x : Nat) -> (y : Nat) -> S x << S y -> x << y
lt_step_down x y w = exists_proof_helper _ _ lt_step_down_lemma w

subtract : (x : Nat) -> (y : Nat) -> y << x -> Nat
subtract Z y l = FalseElim (lt_zero y l)
subtract (S x) Z _ = x
subtract (S x) (S y) l = subtract x y (lt_step_down y x l)
