module StrongNat

%default total

-- This file demonstrates a problem with trying to do "Strong" stuff with numbers
-- in the current idris setup. You can't use the nice number syntax like "3",
-- because fromInteger doesn't reduce during typechecking.

-- UPDATE: Problem solved!

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

{-

-- Discussion in #idris about this

<christiansen> it seems to be picking the wrong ()
<christiansen> pred' 2 (the () ()) -- just fine
<vanila> thanks so much, I'm sorry! I totaly assumed this was a syntax problem with fromInteger
<christiansen> no prob :)
<vanila> that's awesome!
<edwinb> oh, the elaborator doesn't bother checking to see if it needs a type there, and it should
<edwinb> I'll update that when I'm next passing through...
<christiansen> vanila: try this signature:
<christiansen> pred' : (n : Nat) -> {default () ok : nonzero n} -> Nat

-}

{-

*StrongNat> :t pred' 3 (the () ())
pred' (fromInteger 3) (the () ()) : Nat

-}
