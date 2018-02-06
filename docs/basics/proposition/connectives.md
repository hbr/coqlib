# Propositional Connectives

The standard library of Coq contains the following definitions for
propositional connectives.

    Inductive and (A B:Prop): Prop :=
        conj: A -> B -> and A B.

    Inductive or (A B:Prop): Prop :=
        or_introl: A -> or A B
    |   or_intror: B -> or A B.

    Definition not (A:Prop): Prop := A -> False.

    Definition iff (A B:Prop): Prop :=
        and (A -> B) (B -> A).

In order to support better readability there are notations in Coq which allow
us to write `A /\ B` for `and A B`, `A \/ B` for `or A B`, `~ A` for `not A`
and `A <-> B` for `iff A B`. But these are just notations which can always be
replaced by the function which they denote.

Lets analyze what these definitions say.

`A /\ B` has type `Prop` i.e. is a proposition. The only way to prove it is by
applying the constructor `conj` to a proof of `A` and a proof of `B`.

`A \/ B` has type `Prop`. There are two ways to prove it. Either apply the
constructor `or_introl` to a proof of `A` or apply the constructor `or_intror`
to a proof of `B`.

In order to prove `~ A` we have to map every proof of `A` into a proof of
`False` (i.e. assuming a proof of `A` leads to inconsistency).

In order to prove `A <-> B` we have to prove `A -> B` and `B -> A` and apply
the constructor `conj` to them.

Since `A /\ B` and `A \/ B` are defined inductively we can pattern match on
proofs of them. If we have a proof of `A /\ B` i.e. a term `p` with type `A /\
B` we can extract the proofs of `A` and `B` by pattern match.

We can use these definitions to prove commutativity of `/\`.

    Goal
      forall (A B:Prop) (p:A /\ B), B /\ A.
    Proof
      fun A B p =>
        match p with
          conj a b => conj b a
        end.

In a similar manner we can prove the commutativity of `\/`.

    Goal
      forall (A B:Prop) (p:A \/ B), B \/ A.
    Proof
      fun A B p =>
        match p with
          or_introl a => or_intror a
        | or_intror b => or_introl b
        end.

Compare this proof by providing explicit proof terms with a conventional proof
by using tactics.

    Goal
      forall (A B:Prop) (p:A \/ B), B \/ A.
    Proof.
      intros A B p.
      destruct p as [a | b].
      - apply or_intror; assumption.
      - apply or_introl; assumption.
    Qed.

The `fun A B p` is equivalent to the `intros A B p`, the pattern match with
the two cases is equivalent to `destruct p as [a | b]`, `or_intror a` is
equivalent to `apply or_intror; assumption` ...

In my opinion the proof by explicit proof terms is better readable and fits
better the paradigm of functional programming. However for such trivial
examples the difference is not very significant.




<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
