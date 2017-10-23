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


## Proofs by Recursion

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


## Decision Procedure for Equality of `nat`

It is easy to write a boolean valued recursive function which test for
equality of two natural numbers. Just recursively strip off `S` constructors
of both until at least one of them is `O`. If both are `O` then the numbers
are equal, in all other cases both are not equal.

But as explained in the chapter [Decision Procedures](decision.md) a boolean
valued function is not usedfull unless accompanied by theorems which prove
what the result `true` and the result `false` mean in the domain of
propositions. Therefore we write a decision procedure for equality of
naturals.

    Definition is_equal: forall a b:nat, {a = b} + {a <> b} :=
      fix f a b: {a = b} + {a <> b} :=
        match a, b return {a = b} + {a <> b} with
        | O, O => left eq_refl
        | S n, O => right (@successor_not_zero n)
        | O, S n => right (Equal.flip_not_equal (@successor_not_zero n))
        | S n, S k =>
          match f n k: {n = k} + {n <> k} with
          | left p =>
            left (Equal.inject p S)
          | right p => (* p: n = k -> False *)
            right (fun q:S n = S k =>
                     p (successor_injective q:n = k))
          end
        end.

The function `is_equal` has the same structure as the boolean function we
would write in a programming language like OCaml. We just have to enrich the
different cases with a proof which states whether `a = b` or `a <> b`.

For the case `O,O` we can bild the proof by `eq_refl`. For the two cases `S
n,O` and `O, S n` we can build a proof based on `S n <> O` and for the
recursive call we have to make a case distinction whether the values `n` and
`k` are equal or not equal and inject the equality or use the fact that the
successor constructor is injective to prove the corresponding part.

We can extract the function `is_equal` to Ocaml by the command `Recursive
Extraction is_equal`.

    type nat =
    | O
    | S of nat
    type sumbool =
    | Left
    | Right

    (** val is_equal : nat -> nat -> sumbool **)
    let rec is_equal a b =
      match a with
      | O ->
        (match b with
         | O -> Left
         | S _ -> Right)
      | S n ->
        (match b with
         | O -> Right
         | S k -> is_equal n k)

You see that all proof information is stripped off and the algorithm is
exactly the same.


## Where is Induction?

You might wonder why we have not used any induction. The key point is:
Induction is _not_ anything basic in Coq. The basic things are inductive types
and recursion. With these two concepts it is possible to prove an induction
principle.

For natural numbers we expect an induction principle with the type

    forall P:nat->Prop,
        P 0 -> (forall k, P k -> P (S k)) -> forall n:nat, P n

In words: If we can prove that `0` satisfies a property and we can prove that
any number transfers the property to its successor then we can conclude that
the property is satisfied by all natural numbers.

We can prove this principle in Coq by using recursion.

    Definition nat_induction:
      forall (P:nat->Prop),
        P O -> (forall k, P k -> P (S k)) -> forall n, P n :=
      fun P p0 pstep =>
        (fix f n :=
           match n as x return P x with
           | O => p0
           | S k => pstep k (f k)
           end).

The Coq compiler generates for all inductive types an induction principle (for
naturals it is called `nat_ind`) so there is no need to prove it. All the
above proofs done by recursion can be done by using the induction principle as
well. Just define the property `P`, a proof that `0` satisfies the property
and a proof that every natural transfers the property to its successor and
then use `nat_induction P p0 pstep` to complete the proof.

It is a matter of taste which way you prefer, they are equivalent. However in
case of more than one argument like in the decision procedure for equality I
find the use of recursion more natural.


<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
