# Order Structure

## Definition

Natural numbers have an order structure. If we have one number `n`, then `n <=
n` is valid. If we have `n <= m` then we can conclude that `n <= S m` is valid
as well. These two rules are expressed in Coq with an inductive type.

    Inductive le (n : nat) : nat -> Prop :=
    | le_n : n <= n
    | le_S : forall m : nat, n <= m -> n <= S m.

`le` has the type `nat -> nat -> Prop` and is therefore a relation. Coq
provides a notation to write `n <= m` instead of `le n m`.

With `le_n n` we prove `n <= n`, and with `le_S n m p` where `n` and `m` are
two natural numbers and `p` is a proof of `n <= m` we prove `n <= S m`.

On the other hand if we have a proof of `n <= m` we can pattern match on the
proof. The case `le_n _` implies that `n = m`. The case `le_S _ k p` gives us
a number `k` whose successor is `m` and a proof `p` for `n <= k`. Note that
the variable `n` in the definition of the inductive type `le` is to the left
on the colon, i.e. it is a parameter. Therefore in the pattern match `le_n`
and `le_S` we cannot bind a variable to it, only the wildcard `_` is allowed.


## Zero and Successor

Using the inductive definition we can prove that `0 <= n` is valid for all
natural numbers `n` by a simple induction proof.

    Theorem zero_is_least:
      forall n, 0 <= n.
    Proof
      fix f n: 0 <= n :=
      match n with
      | 0 => le_n 0
      | S k => le_S 0 k (f k)
      end.

The constructor `le_n` is used to prove the base case and the constructor
`le_S` is used to map `0 <= k` to `0 <= S k`.


Next we prove that `S n <= 0` cannot be valid for any value of `n`. I.e. we
have to prove `S n <= 0 -> False` for all values of `n`.

In order to prove this fact we first prove the lemma `S n <= m -> m <> 0`. We
pattern match on a proof of `S n <= m`. In both case `m` has the form `S k`
and we can use the previous proof `successor_not_zero` to prove that `S k <>
0` is valid. The we feed the lemma with `m` substituted by `0` and get
immediately the desired result.


    Theorem successor_not_below_zero:
      forall n:nat, ~ S n <= 0  (* S n <= 0 -> False *).
    Proof
      let lemma: forall (n m:nat) (p: S n <= m), m <> 0 :=
          fun n m p =>
            match p with
            | le_n _ => @successor_not_zero n: S n <> 0
            | le_S _ k pk => @successor_not_zero k: S k <> 0
            end
      in
      fun n p => lemma n 0 p eq_refl.


Any number less or equal zero must be zero. A simple induction proves this fact.

    Theorem below_zero_is_zero:
      forall n:nat, n <= 0 -> n = 0.
    Proof
      fix f n: n <= 0 -> n = 0 :=
      match n with
      | 0 => fun p => eq_refl
      | S k =>
        (* goal S k <= 0 -> S k = 0 *)
        fun p: S k <= 0 =>
          match successor_not_below_zero p with end
      end.

## Monotonic

Now we want to verify that the successor function is monotonic with respect to
`<=` i.e. that `n <= m` implies `S n <= S m`. The prove requires an induction
on the proof of `n <= m`. The second case of the pattern match on a proof of
`n <= m` requires that `m` has the form `S k`. By recursion we get the
induction hypothesis `S n <= S k` and can use the constructor `le_S` to
construct the evidence of `S n <= S (S k)` which is the required result for
that case.

    Theorem successor_monotonic_le:
      forall (n m:nat), n <= m -> S n <= S m.
    Proof
      fix f n m (p:n<=m): S n <= S m :=
      match p with
      | le_n _ => le_n (S n)
      | le_S _ k pk => (* goal: S n <= S (S k) *)
        let hypo: S n <= S k := f n k pk in
        le_S (S n) (S k) hypo
      end.

> Note: This example shows that we can do induction on a proof of `n <= m` and
  not only on the numbers `n` or `m`. This is possible because `<=` has been
  defined inductively. I.e. a proof of `n <= m` is an object of an inductive
  type and we can do recursion on such a proof. The pattern match for the case
  `le_S` can be used to bind a variable (`pk` in the example) to a proof which
  is structurally smaller than the original proof. Therefore the structurally
  smaller variable can be used as an argument of a recursive call to construct
  an induction hypothesis.


The monotonicity holds in the other direction as well. Form `S n <= S m` we
can infer `n <= m`. In order to prove this fact we prove the lemma `n <= m ->
pred n <= pred m`.

    Theorem predecessor_monotonic_le:
      forall n m:nat, n <= m -> pred n <= pred m.
    Proof
      fix f n m p: pred n <= pred m :=
      match p with
      | le_n _ =>
        (* goal: pred n <= pred n *)
        le_n (pred n)
      | le_S _ k pk =>
        (* goal: pred n <= pred (S k),
           proof: Construct a function with type n <= k -> pred n <= pred (S k)
                  and apply it to pk which has type n <= k. The function does a
                  pattern match on k. For k=0, n has to be zero as well. For
                  k = S l use f to generate an induction hypothesis.
         *)
        (match k with
         | O =>
           fun q0:n<=0 =>
             Equal.rewrite
               (Equal.flip (below_zero_is_zero q0: n = 0))
               (fun x => pred x <= pred (S 0))
               (le_n (pred 0))
         | S l =>
           fun ql: n <= S l =>
             let hypo := f n (S l) ql: pred n <= pred (S l) (* ind hypo *)
             in
             le_S (pred n) (pred (S l)) hypo
         end) pk
      end.

> Note: In this proof we pattern match on a proof of `n <= m`. However we need
  a nested pattern match on `k` in order generate a useful induction
  hypothesis. The outer pattern match constructs a proof which is structurally
  smaller than the proof of `n <= m`. The second pattern match gives the
  environment for the recursive call of the proof generating function `f`.

With the lemma the desired proof of `S n <= S m` is trivial.

    Theorem cancel_successor_le:
      forall n m:nat, S n <= S m -> n <= m.
    Proof
      fun n m p =>
        predecessor_monotonic_le p.

This proof works because `pred (S n)` evaluates to `n` for all `n`.

## Strict Order

A number `n` is strictly less than a number `m` if the successor of `n` is
less equal `m`. In Coq the function `lt` is defined exactly in this manner.

    Definition lt (n m:nat): Prop := S n <= m.

A notation is provided to be able to write `n < m` instead of `lt n m`.

We proof some easy theorems which relation `<=`, `<` and `=`.

    Theorem lt_implies_le:
      forall (n m:nat), n < m -> n <= m.
    Proof
      fix f n m lt: n <= m :=
      match lt with
      | le_n _ => le_S n n (le_n _)
      | le_S _ k pk => le_S n k (f n k pk)
      end.

    Theorem lt_implies_ne:
      forall (n m:nat), n < m -> n <> m.
    Proof
      fun n m lt eq =>
        let n_lt_n: n < n := Equal.rewrite (Equal.flip eq) _ lt in
        successor_not_le n_lt_n.

    Theorem le_ne_implies_lt:
      forall (n m:nat), n <= m -> n <> m -> S n <= m.
    Proof
      fun n m le =>
        match le with
        | le_n _ => fun n_ne_n => match n_ne_n eq_refl with end
        | le_S _ x p => fun _ => successor_monotonic_le p
        end.

**Excercise**: Prove the following three theorems. Hint: The first needs an
induction proof. The second and third can be done without induction. Don't
introduce the last premise in the third proof too early!

    Theorem transitive:
      forall (n m k:nat), n <= m -> m <= k -> n <= k.
    Theorem lt_irreflexive:
      forall n:nat, ~ n < n.
    Theorem antisymmetric:
      forall (n m:nat), n <= m -> m <= n -> n = m.

## Decidable Order

The relation `<=` is decidable. It is easy to write a boolean valued function
which returns `true` if `n <= m` is valid and `false` if `~ n <= m` is
valid.

    Definition is_less_equal_bool: forall a b:nat, bool :=
      fix r a b: bool :=
        match a with
        | 0 => true
        | S k =>
          match b with
          | 0 => false
          | S n => r k n
          end
        end.

However as already explained, boolean functions give very little
information. We just get a value of `true` or `false`. What we really want is
a decision procedure i.e. a function which returns either a proof of `n <= m`
or a proof of `~ n <= m`.

We can use the above boolean valued function as a blueprint and instead of
returning `true` or `false` we return either `left` with a proof of `a <= b`
or `right` with a proof of `~ a <= b`.

    Definition is_less_equal: forall a b:nat, {a <= b} + {~ a <= b} :=
      fix r a b: {a <= b} + {~ a <= b} :=
        match a with
        | O => left (zero_is_least b)
        | S k =>
          match b with
          | O => right(@successor_not_below_zero k)
          | S n => (* goal: {S k <= S n} + {~ S k <= S n} *)
            match r k n: {k <= n} + {~ k <= n} with
            | left  p => left(@successor_monotonic_le k n p)
            | right p => (* p:~ k <= n *)
              right( fun q: S k <= S n =>
                       p (cancel_successor_le q: k <= n)
                   )
            end
          end
        end.

The only additional complexity is to make a case split on the recursive call
to distinguish the two possible return values and map a proof of `k <= n` of
the predecessors into a proof of `S k <= S n` and a proof of `~ k <= n` of the
predecessors into a proof of `~ S k <= S n`.




<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
