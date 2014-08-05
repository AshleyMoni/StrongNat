module StrongNat

%default total

-- This file demonstrates a problem with trying to do "Strong" stuff with numbers
-- in the current idris setup. You can't use the nice number syntax like "3",
-- because fromInteger doesn't reduce during typechecking.

nonzero : Nat -> Type
nonzero Z = _|_
nonzero (S _) = ()

pred' : (n : Nat) -> nonzero n -> Nat
pred' Z f = FalseElim f
pred' (S n) _ = n

{-

*StrongNat> :t pred' (S (S (S Z))) ()
pred' 3 () : Nat
*StrongNat> :t pred' 3 ()
(input):1:10:When elaborating an application of function StrongNat.pred':
        Can't unify
                Type
        with
                nonzero (fromInteger 3)
        
        Specifically:
                Can't unify
                        Type
                with
                        nonzero (fromInteger 3)

-}
