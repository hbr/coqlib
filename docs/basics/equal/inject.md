# Inject an Equality

We often have the problem that we want to prove an equality

    exp1 = exp2

where the left hand side and the right hand side have a different
subexpression but are identical for the rest. In this case it is always
possible to define a function `f` and express the above goal as

    f a = f b

where `a` and `b` are the different subexpressions. E.g. if the desired
equality is `n + a = n + b` then the function `f` is `fun x => n + x`. Suppose
that we have a proof `p` for the proposition `a = b` then we want to have a
theorem `inject`  such that `inject p (fun x => n + x)` generates a proof for
`n + a = n + b`.

We can create the theorem `inject` similar to the theorem `rewrite` above.

    Theorem
        inject (A B:Type) (a b: A) (p:a=b) (f:A->B): f a = f b.
    Proof
        match
            p in (_ = x)
            return f a = f x
        with
            eq_refl => eq_refl
        end.

The trick is the same above. The goal of the match expression is `f a = f b`
which is mapped via the variable `x` into the inner context to `f a = f a`
which can be proved by `eq_refl`.




<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
