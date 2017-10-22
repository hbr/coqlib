# Recursion

## A Term for Recursive Functions

The proof of an implication or a unversally quantified proposition is a
function. All the proofs shown up to now used functions to prove the claim
written in its type. Either anonymous functions `fun a b ... => exp` or
functions using directly the arguments of the theorem to prove.

These functions can be recursive. An anonymous function of the form `fun x =>
exp` cannot be recursive because it has no name and therefore cannot be called
inside its defining expression `exp`.

In order to declare a term as recursive we have to give the function a
temporary name which can be used inside the defining expression. A term
representing a recursive function in Coq has the form

    fix f (a:A) (b:B) ... {struct n}: return_type :=
        exp

Within `exp` we can use subterms `f x y ...` to call the function
recursively. However the compiler enforces that at least one of the arguments
of the recursive function is structurally smaller in the recursive
calls. _Structurally smaller_ means that it is the result of a pattern match
of the original argument.

The optional `{struct n}` allows you to pick one of the arguments which is
structurally smaller in all recursive calls. If you don't provide the hint
then the compiler tries to guess it and complains if it cannot find a
structurally decreasing argument.

This condition ensures that a recursive function is terminating within a
finite number of steps.

As always type annotations can be ommitted as long as the compiler can infer
them from the environment. It is recommended to provided explicit type
annotations if the type of an argument is important to understand the code.

Using the `fix` construct we can define addition for natural numbers

    Definition plus: nat -> nat -> nat :=
        fix f a b :=
            match a with
            | O => b
            | S n => S (f n b)
            end.

A definition with explicit type annotations and the declaration of the
structurally decreasing argument would look like

    fix f (a b:nat) {struct a}: nat :=
        ...

But in such simple cases the compiler can infer the missing information and
the explicit annotations are not helpful to understand the code.


## Recursive Proofs

Let's try to prove that every natural number is different from its successor
i.e. `forall n:nat,S n <> n`. The proof must be a function taking a natural
number and returning a proof that this natural number is different from its
successor. We have already a proof for the case `O` (`forall n,S n <> O` see
previous chapter). We use a recursive function to construct the general proof.

    Theorem successor_different_base:
        forall n:nat, S n <> n.
    Proof
        fix f n: S n <> n :=
            match n return S n = n -> False with
            | O =>
              fun p:S 0 = 0 => (@successor_not_zero 0) p
            | S k =>
              fun p:S (S k) = S k =>
                  ...
            end.

Since we have deconstructed `n` in the pattern match to `S k` it is guaranteed
that `k` is structurally smaller than `n`.  Therefore it is allowed to call
the recursive function `f` with the argument `k`. The term `f k` returns a
proof for `S k = k -> False`. But in this branch we need a proof for `S (S k)
= S k -> False`.

The assumption `p: S (S k) = S k` has the form `S n = S m`. The theorem
`successor_injective` of the previous chapter allows us to conclude `n = m`
i.e `S k = k` from that. The call to `f k` returns a function transforming
this into a proof of `False` and we are ready.

    Theorem successor_different_base:
        forall n:nat, S n <> n.
    Proof
        fix f n: S n <> n :=
            match n return S n = n -> False with
            | O =>
              fun p:S 0 = 0 => (@successor_not_zero 0) p
            | S k =>
              fun p:S (S k) = S k =>
                  f k (successor_injective p)
            end.

Note that it is essential to provide a return type in the pattern match
construct because it allows the compiler to infer the correct type for each of
the branches of the match construct. For the `O` case the required type is `S
0 = 0 -> False` and for the `S k` case the required type is `S (S k) = S k ->
False`. Without this piece of information the compiler would require you to
provide a term which proves `S n = n -> False` in each branch which is
impossible to prove.

A proof of the flipped version is nearly trivial.

    Theorem successor_different:
        forall n:nat, n <> S n.
    Proof
        fun n => Equal.flip_not_equal (successor_different_base n).



#### Excercises

Try to prove the following theorems with a recursive function:

    Theorem zero_right_neutral_plus: forall a:nat, a + 0 = a.
    Theorem push_successor_plus:     forall a b:nat, S (a + b) = a + S b.
    Theorem plus_commutative:        forall a b:nat, a + b = b + a.

Hint: The third needs the other two. You need `Equal.inject` for the first and
the second and `Equal.join` for the third.

If you want to learn to program with dependent types then you really should
try to solve the excercises. If you are not accustomed to dependent types then
the excercises might take you some hours.


<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
