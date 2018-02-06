# Equality

## Definition

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




## Equality Proofs


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

## Dependent Pattern Match

This is a good point to introduce dependent pattern match. Dependent pattern
match is not needed for all proofs done below, but it is important to
understand the concept and be able to use it where necessary.

A pattern match inspects a term (it can be a proof term or any other term) and
does a case distinction on the possible cases how a term of the corresponding
type could have been constructed. Since practically all types in Coq are
inductive you can always do some pattern match.

The pattern match term has a required type and the different branches of the
pattern match have to provide a term which satisfies the required type. We can
always write the required type `T` explicitly.

    match exp return T
    | ...
    ...
    end

Usually we don't do that because the required type can be inferred from the
context. However the type `T` might be dependent. It could depend on some
other terms which represent objects (proofs or computations). The dependency
of the type `T` might look different for the different branches and Coq is not
always able to infer the specific type for each branch because problem is
undecidable in general.

Therefore it is possible bind some variables and let Coq compute the required
type for each branch by unification. The complete possibitlities of the
dependent pattern match are

    match exp as x in C T1 T2 ... return T
    | ...
    ...
    end

with the variables `x`, `T1`, `T2`, ... The variable `x` is bound to `exp`. `C
T1 T2 ...` must be unifiable to the type of `x` (i.e. the type of `exp` in the
outer context) and the variables can be used to express the required result
type `T` of the complete match expression.

With this information Coq is able to generate uniquely a requested type for
each branch.

This description might seem very abstract. But in the sequel we will show how
to use this construct for some equality proofs.





## Rewrite a Proposition

Lets assume we want to prove the proposition

    forall (A:Type) (a b:A) (P:A->Prop), a = b ->  P a -> P b

which states: If two objects are equal then every property satisfied the first
is satisfied by the second as well.

The proposition is a dependent product. Therefore we need a proof term which
is a function of the form

    fun A a b p_eq P pa => ...

where `pa` is a variable representing a proof of `P a` and `p_eq` is a
variable which represents a proof for the equality `a = b` (i.e. we have
`pa:Pa` and `p_eq:a=b`.

Since `p_eq` represents a proof of `a = b` (i.e. `eq a b` without the
notation) and `eq` has only one constructor we know that `p_eq` must have been
constructed by `eq_refl`.

The appropriate dependent pattern match construct looks like

    match p_eq in (_ = x) return P x with
    | eq_refl => ...
    end

We don't need a variable to represent `p_eq` here (therefore no `as ...`). The
type of `p_eq` is `a = b`. We cannot bind a variable to `a` because it is a
parameter, but we can bind a variable to `b`. We use the variable `x`
here. Now we can express the required type of the pattern match expression `P b`
with the variable `x` which is bound to `b` in the outer context. The required
type is `P x`.

As opposed to `P b` the type `P x` can be projected into the different match
cases (here there is only one). Since `eq_refl` states that `p_eq` has been
constructed by `@eq_refl A a` it must have the type `a = a`. Therefore the
variable `x` is bound to `a` in the inner context of that case. Thus the
required type of the branch is `P a` for which we have already the proof
`pa`. Therefore the complete proof is

    Theorem rewrite (A:Type) (a b:A) (p_eq:a=b) (P:A->Prop) (pa:P a): P b.
    Proof
        match
          p_eq in (_ = x)
          return P x
        with
          eq_refl => pa
        end.

We name this theorem `rewrite` because it rewrites `a` by `b` in the
proposition proved by `pa`. The proposition proved by `pa` is provided as a
function `P` which maps the term `a` to the proposition proved by `pa`.

Suppose we have a proposition of the form `n + k*i < e` and a proof `p` for
it. Furthermore we have a proof `q` for the proposition `k*i = i*k`, then the
term `rewrite p (fun x => n + x < e) q` generates a proof for `n + i*k <
e`. The application rewrites `k*i` by `i*k` in the proposition `n + k*i < e`.


## Inject an Equality

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


## Flip Equality

Equality is a symmetric relation. Therefore `a = b` implies `b = a`. Given a
proof term for an equality `a = b` we want to construct a proof term for `b =
a`.

Using the above functions it is easy. By `eq_refl` we construct `a = a` and
then we use the proof of `a = b` to rewrite the `a` on the left hand side of
`a = a` into `b`.

    Theorem
        flip (A:Type) (a b:A) (p:a=b): b=a.
    Proof
        rewrite p (fun x => x = a) eq_refl.


## Flip Inequality

We can use `flip` to prove that an inequality is symmetric as well i.e. that
we can convert any proof of `a <> b` into a proof of `b <> a`.

A proof of `b <> a` has to prove `b = a -> False` (i.e. convert a proof of `b
= a` into a proof of `False`. We have already a proof of `a <> b` which is
equivalent to `a = b -> False`. Therefore we have to flip `b = a` into `a = b`
and use the proof of `a <> b` to convert it into a proof of `False`.

    Theorem
        flip_not_equal (A:Type) (a b:A) (p:a<>b): b<>a.
    Proof
          (* p: a=b -> False
             goal: b=a -> False
           *)
        fun q:b=a => p (flip q).

## Join Equalities

Equality not only is symmetric. It is transitive as well. Having a proof for
the two equalities `a = b` and `b = c` we should be able to create a proof
term for `a = c`.

Using `rewrite` it can be done easily. W pbce use the proof of `b = c` to rewrite
`b` in `a = b` into `c`.

    Theorem
        join (A:Type) (a b:A) (pab:a=b) (pbc:b=c): a = c.
    Proof
        rewrite pbc (fun x => a = x) pab.


## Reusable Theorems

The theorems `rewrite`, `inject`, `flip`, `flip_not_equal` and `join` are
useful so that it is worthwhile to put them into a module for reuse. We add to
our `Core.v` module the following declarations.

    Module Equal.
        Theorem rewrite ...
        Theorem inject  ...
        Theorem flip    ...
        Theorem flip_not_equal  ...
        Theorem join    ...
    End Equal.

    Notation "( 'eq_chain:' x , y , .. , z )" :=
      (Equal.join .. (Equal.join x y) .. z) (at level 0): equality_scope.

We can use the content of this module in any other Coq source file by putting
`Require Import Core.` and `Open Scope equality_scope.` at the top.

We can use `Equal.rewrite ...`, `Equal.inject ...`, ... to generate proof
terms.

Furthermore the included notation allows to join an arbitrary number of proof
terms which prove `a = b`, `b = c`, ... , `y = z` by

    (eq_chain:  pab, pbc, ... , pyz)

in order to generate a proof for `a = z`.



<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
