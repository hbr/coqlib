# Equality Proofs


In proofs involving equality we either have to use the fact that two terms are
equal or we have to prove that two terms are equal or both.

If we have a proof of the fact that two terms are equal we can do a pattern
match on the proof. E.g. if we have `p:a=b` i.e. `p` is a proof term for the
type `a=b` (or `eq a b` without notation) then we can pattern match on `p`.

    match p with
    | eq_refl => ...
    end

as shown above.

If we want to prove that two terms are equal we can introduce the equality by
`@eq_refl A a` where `A` is the type and `a` is the object which has to be
equal to something. However `@eq_refl A a` always constructs a term with type
`eq a a`. I.e. in order to prove `a = b` we have to do this in a context where
Coq can identify the left hand side and the right hand side.

You might say that this is completely useless because we can only prove
equalities of the form `a = a`. But note that the terms on both sides of the
equation need not be identical, they just have to have the same normal
form. Then using the unnormalized terms we can proceed to prove quite complex
equalities.


<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
