# Propositions

## Implication and Universal Quantification

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



## True and False

In Coq `True` and `False` are defined as inductive types in the following
manner

    Inductive True: Prop := I.

    Inductive False: Prop := .

These definitions say that `True` and `False` have type `Prop` and `True` has
one constructor `I` and `False` has no constructor. There is only one way to
construct the proposition `True` by using its constructor `I` and there is no
way to construct the proposition `False` i.e. it is impossible to give a proof
for `False`.

Remember that a proof of a proposition is a term having the type of the
proposition. Since `I` is a constructor for `True` it is easy to prove `True`.

    Goal True.  Proof I.

We cannot prove `False` but we can convert a proof of `False` (which cannot
exist in the global environment, but it could exist by making some
inconsistent assumptions) into a proof of anything.

    Goal
        forall A:Prop, False -> A.
    Proof
        fun (A:Prop) (p:False) =>
            match p with
            end.

The expression

    match expr with
    | C1 a1 b1 ... => e1
    | C2 a2 b2 ... => e2
    ...
    end

is a pattern match expression which can be used if the term `expr` is of an
inductive type. It must list a case for each constructor with sufficient
formal arguments. The match expression does a case analysis on how the
expression `expr` has been constructed. The type checker of Coq checks that
each `ei` has the required type of the overall expression.

Since `False` has no constructor, the corresponding match expression does not
need any case. The type checker verifies that the cases are complete and that
for each case there is one term which has the required type. For the above
proof the type checker is completely happy. This proof expresses the fact that
from inconsistent assumptions you can conclude anything or in latin _ex falso
quodlibet_, one of the most fundamental concepts in logic.


Note that there is no built in definition of truth and falsehood. Both are
defined in the libraries which are included in any Coq source file by
default. However you are not obliged to use them if you don't want to. You can
define your own truth and falsehood.

    Inductive MyTrue: Prop := MyI.

    Inductive MyFalse: Prop := .


## Propositional Connectives

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







## Existential Quantification

As with the propositional connectives there is no built-in magic for
existential quantification. Existential quantification is defined in the Coq
library as an ordinary inductive type.

    Inductive ex (A: Type) (P:A -> Prop) : Prop :=
      ex_intro: forall (x:A), P x -> ex P.

The term `ex (fun n:nat => n > 0)` is a proposition which states that there
exists a natural number which is greater than zero.

> Note: The first argument `A` of `ex` is implicit and the libraries of Coq
  usually have the statement `Set Arguments Implicit`. This means that
  implicit arguments must not be provided. You can always override this
  locally by prefixing `@` in front of the function and provide all
  arguments. I.e. in the case of existential quantification you can write `@ex
  nat (fun n:nat => n > 0)` which states the same fact as above but is more
  verbose.

The inductive type `ex` has only one constructor `ex_intro` which needs an
object and a proof that the object satisfies the required property.

The Coq library provides a notation shorthand for existential quantification
so that the following two terms are equivalent.

    ex (fun n:nat => n > 0)

    exists n:nat, n > 0

The second form is very intuitive because it has the same form as the
dependent product `forall x:T,e` with `forall` substituted by `exists`. But
you have to realize that the dependent product is built into the language and
the existential quantification is just an inductive definition.

Now we can start to prove propositions with existential quantification. If
there exists an element which satisfies a certain property then it cannot be
the case that all objects do not satisfy this property. This proposition can
be stated in Coq as

    forall (A:Set) (P:A->Prop), (ex P) -> ~ forall x, ~ P x

Before proving this proposition we have to remember that negation has a
definition and that Coq is able to normalize terms and normalization includes
the expansion of definitions. Therefore the tail of the proposition has the
normal form

    (forall x, P x -> False) -> False

In order to prove the proposition we need a function with maps the four
arguments

- `A:Set`: a datatype
- `P:A->Prop`: a property of elements of this datatype
- `p_ex: ex P`:  a proof that there exists some element satisfying the
  property
- `f:forall x, P x -> False` a function which maps all elements `x` and proofs
  of `P x`  into a proof of `False`.

into a proof of `False`.

The proof is very easy. We just have to pull out an element satisfying the
property out of the proof `p_ex` by pattern match and then use the function
`f` to convert the element and its proof that it satisfies the property into a
proof of `False`.

    Goal
      forall (A:Set) (P:A->Prop), (ex P) -> ~ forall x, ~ P x.
    Proof
      fun A P p_ex f =>
        match p_ex with
          ex_intro _ x px => f x px
        end.

It might be instructive to compare this proof by generating directly a proof
term with a proof generated by tactics.

    Goal
      forall (A:Set) (P:A->Prop), (ex P) -> ~ forall x, ~ P x.
    Proof.
      intros A P p_ex f.
      destruct p_ex as [ x p ].
      unfold not in f.
      apply f with (x:=x).
      assumption.
    Qed.




<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
