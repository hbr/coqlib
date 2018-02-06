# Basics


Natural numbers are defined in Coq as an inductive type.
```ocaml
    Inductive nat: Set :=
    | O: nat
    | S: nat -> nat.
```
The constructor `O` (note: it is the capital letter `O` an not the number `0`)
represents the number zero and the constructor `S` represents the successor
function.

The inductively defined natural numbers are a completely inefficient when used
as actual data types in a program. Then number `5` is represented as `S (S (S
(S (S 0))))`. Imagine how the number `1000000000` (one billion) is
represented. However these natural numbers are a powerful mathematical
concept. Natural numbers can be used in proofs. Since all proofs are erased
during extraction no runtime overhead is generated by using natural numbers
only in proofs.

The Coq parser has a special hack to write natural numbers conveniently. You
can write `2` and the Coq parser expands it to `S (S O)` or you can write `0`
and the Coq parser expands it to `O`.

In the following we prove some theorems about natural numbers. All the
theorems are included in the `Core.v` source file within a module `Nat` and
can be used by `Require Import Core` in any other Coq source file.

First we define a predicate describing if a number is the successor of another
number.

    Definition is_Successor (n:nat): Prop :=
      match n with
      | 0 => False
      | S _ => True
      end.

We prove that any number of the form `S n` cannot be equal to `0`.

    Theorem successor_not_zero:
      forall n:nat, S n <> 0.
    Proof
      fun n (p: S n = 0) =>
        (* Use the propositon 'is_Successor' which is trivially provable for 'S n'
         and rewrite 'S n' into '0' by using 'p' and generate a proof for
         'False'. With that we get 'S n = 0 -> False' which is the required
         result. *)
        Equal.rewrite p is_Successor I.

The predicate `is_Successor` is decidable. We can provide a decision procedure
for the predicate (or better said: for the negation of the predicate).

    Definition is_zero (n:nat): {n = 0} + {n <> 0} :=
      match n with
      | 0   => left eq_refl
      | S n => right (@successor_not_zero n)
      end.

> Note: We could have used `bool` as the return type of `is_zero` and returned
  `true` in the first case and `false` in the second case. But writing
  `is_zero` as a decision procedure is better because a pattern match on the
  result of `is_zero n` gives us a case with a proof of `n = 0` and a case
  with a proof of `n <> 0`. The proofs can be used as arguments to other
  function call in the corresponding cases.

The successor function is injective.

    Theorem successor_injective:
      forall n m:nat, S n = S m -> n = m.
    Proof
      fun n m p =>
        let f x := match x with
                     O => n
                   | S y => y end in
        Equal.inject p f.

Any number `n` is different from its successor. The proof of this property
needs an induction proof i.e. a recursive function generating the proof.

    Theorem successor_different (n:nat): n <> S n.
    Proof
      let f :=
          fix f n: S n <> n:=
            match n with
            | O =>
              fun p:S 0 = 0 => (@successor_not_zero 0) p
            | S k =>
              fun p: S (S k) = S k =>
                f k (successor_injective p: S k = k)
            end
      in
      Equal.flip_not_equal (f n).


Equality of natural numbers is decidable. We define the obvious decision
procedure.

    Definition is_equal: forall a b:nat, {a = b} + {a <> b} :=
      fix f a b: {a = b} + {a <> b} :=
        match a, b with
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

<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->