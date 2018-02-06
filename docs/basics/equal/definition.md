# Definition

The standard library defines equality with an inductive type.

    Inductive eq (A:Type) (x:A): A -> Prop :=
      eq_refl: eq x x.

The inductive type `eq` has three arguments, a type, an element of this type
and another element of the same type. The term `eq A x x` is a
proposition. Note that the first argument is implicit. Therefore it has to be
written as `eq x x`. If you want to give the implicit argument as well you
have to override the implicit mechanism of Coq by writing `@eq A x x`.

The standard library declares the notation `a = b` as a shorthand for `eq a
b` and the notation `a <> b` as a shorthand for `~ a = b` (i.e. `~ eq a b`).


This time we have to differentiate between the different arguments in an
inductive definition. The type `eq` has two arguments to the left of the colon
`:` and one argument to the right of the colon. The arguments to the left of
the colon are called parameters of the inductive type. Parameters cannot
change between the different constructors. They are fixed for the specific
instantiation of the inductive type.

Parameters cannot be instantiated in pattern match expressions. I.e. it is not
possible to bind variables to the values of the parameters.

In the case of equality there is only one constructor which has no visible
arguments. It has two hidden arguments, the type and an element of that
type. These hidden arguments are hidden by the _implicit arguments_
mechanism, because they can be inferred from the proposition which the
constructor intends to construct. And since they are parameters no variables
can be bound to the hidden arguments.

If the term `p` represents a proof of `eq a b` then the pattern match looks
like

    match p with
        eq_refl => ...
    end

We can override the implicit arguments mechanism by

    match p with
        @eq_refl _ _ => ...
    end

However we have to use the wildcard `_` because the arguments are parameters
and therefore cannot be bound to variables.

If we use the constructor to create a proposition of the form `@eq A a a` then
it is sufficient to write the pure constructor `eq_refl`. In that case we can
override the implicit arguments mechanism and provide the arguments
explicitly by writing `@eq_refl A a`.

Note that the constructor `eq_refl` can only create propositions of the form
`a = a`. Equality in Coq is identity! Since Coq reduces terms to their normal
form internally different looking terms can be identical after normalization.

The terms

    (fun i => i < k) 10
    (fun x => 10 < x) k
    10 < k

are identical after normalization.


<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
