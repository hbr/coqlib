# Implication and Universal Quantification

Universal quantification is built into the language. The term

    forall x:A,B

has no definition. It is the type of functions mapping objects `x` of type `A` to
objects of type `B x`. If `B` does not depend on `x` then we can write `A -> B`
as a shorthand.

In case that `A` and `B` are propositions an object of type `A -> B` is a
function which maps a proof of `A` to a proof of `B`.

This interpretation coincides with our intuition. If we have a proof for `A ->
B` and we are able to prove `A` we are willing to conclude `B`. This rule is
called the modus ponens law.

In Coq we express this law as a type

    forall (A B:Prop), A -> (A -> B) -> B

We can ask Coq what is the type of this expression by issueing

    Check forall (A B:Prop), A -> (A -> B) -> B.

and we get the answer

    forall A B : Prop, A -> (A -> B) -> B
         : Prop


i.e. the type of our expression is of type `Prop`. Expressions of type `Prop`
need a proof. A proof of the expression is a term which has the type

    forall A B : Prop, A -> (A -> B) -> B

Since our proposition which we want to prove is a dependent product we know
that a proof of this claim must be a function. According to the signature we
know that our function which is a proof for the proposition must have the form

    fun (A B:Prop) (a:A) (f:A->B) => ...

We have to design a function which returns a proof of `B` given two
propositions `A` and `B`, a proof `a` of `A` and a function which maps proofs
of `A` to proofs of `B`. Having `a` and `f` the proof is trivial.

    Goal
        forall A B : Prop, A -> (A -> B) -> B.
    Proof
        fun A B a f => f a.

> Note that it is not necessary to write `fun (A B:Prop) (a:A) (f:A->B) =>
  ...` if Coq can infer the types of the arguments from the environment. The
  stated goal provides enough environment to infer the types of the arguments.

> Note: Implication `->` is right associative.

In the same manner we can prove the transitivity of implication.

    Goal
      forall (A B C:Prop), (A -> B) -> (B -> C) -> A -> C.
    Proof
      fun A B C f1 f2 a => f2 (f1 a).

Excercise: In order to get a feeling on how to prove with proof terms it might
be good to try to prove the following propositions in the same manner.

    forall (A: Prop),      A -> A
    forall (A: Prop),      (A -> A) -> (A -> A)
    forall (A B C:Prop),   (A -> C) -> A -> B -> C
    forall (A B C:Prop),   (A -> B -> C) -> B -> A -> C
    forall (A B C D:Prop), (A -> B) -> (A -> C) -> (B -> C -> D) -> A -> D



<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
