# Basics of Inductive Types


## Parameters, Arguments and Implicits

We have already seen some inductive types which are used to define
propositions.

    Inductive and (A B:Prop): Prop :=
        conj: A -> B -> and A B.

    Inductive or (A B:Prop): Prop :=
        or_introl: A -> or A B
    |   or_intror: B -> or A B.

    Inductive ex (A: Type) (P:A -> Prop) : Prop :=
      ex_intro: forall (x:A), P x -> ex P.

    Inductive eq (A:Type) (x:A): A -> Prop :=
      eq_refl: eq x x.

We have to differentiate between the inductive type and its constructors. The
inductive type defines a type and the constructor or constructors are
functions (or constants) which define term which have the type.

The type has arguments which are separated into parameters and other
arguments. Parameters are all argument to the left of the colon. The types
`and`, `or` and `ex` have two parameters and no other arguments. The type `eq`
has two parameter and one other argument.

`and A B` or `A /\ B` is a type (because its type is `Prop`) which represents
the conjunction of the propositions `A` and `B`. The constructor `conj` needs
two arguments, one of type `A` and one of type `B`. Because `A` and `B` are
propositions the terms required by `conj` are proofs for the propositions.

The parameters of the type are mandatory arguments of all constructors unless
they can be inferred from the remaining arguments. Therfore the constructor
`conj` has four arguments, the two types `A` and `B` and the two proofs of
them. Since the proof determine uniquely the propositions they prove they must
not be supplied unless one overrides the implicit arguments mechanism by `conj
A B a b`.

The type `ex` has two parameters and the first one is implicit. The first one
is implicit, because it is completely determined by the second. The term `ex
P` is a type which represents the fact that there exists some object of type `A`
satisfying the proposition `P`. If we want to give the type `A` explicitly we
have to override the implicit arguments mechanism and write `@ex A P`.

The constructor `ex_intro` has four arguments. In full blown form one has to
write `@ex_intro A P x p` and provide the type `A` of the element which
supposedly exists, the property which is satisfied, an element which satisfies
the property and a proof which proves the fact that the element satisfies the
property. The first one is implicit. The others have to be given explicitly
(`ex_intro P x p`).

The type `eq` has two parameters and one other argument. The parameters
determine a type and an object and the other argument is an object which is
equal to the first one. The type is implicit because fully determined by the
object. The type stating equality of two objects is written `eq a b` or `@eq A
a b` or with notation `a = b`.

The constructor has two arguments, the two parameters of the type i.e. in full
form one writes `@eq_refl A a` but since both are determined by the type none
of them has to be provided. I.e. the term `eq_refl` proves any proposition of
the form `a = a`.

In patterm match constructs no variables can be bound to parameters. If the
parameters are not implicit the must be replaced in pattern match constructs
with the placeholder `_`. E.g. if you want to construct an object of type `ex
P` you have to give the provide the proposition, the witness and the
proof. However if you pattern match you can bind variables only to the witness
and the proof, but only a placeholder to the property. I.e. a valid pattern
match always looks like

    match p_exist with (* p_exist is a proof of existence *)
    |  ex_intro _ x p =>
         (* 'x' is the witness and 'p' is the proof that the witness satisfies
            the property. *)
         ...
    end



## Example Natural Numbers

Now we come to some basic techniques for proofs with inductive types. We
demonstrate these techniques on the type of natural numbers which are defined
in the standard Coq library as

    Inductive nat: Set
    |  O: nat
    |  S: nat -> nat.

Note that `O` is the letter `O` and not the number `0`. The definition of the
type has no arguments neither parameters nor others.

The first constructor is a constant which constructs the number `0`. The
second constructor uses an already constructed number and constructs the
successor of that number. The number `4` is written as `S (S (S (S O)))`. The
notations defined in the standard library of Coq allows us to write `4` which
actually means the construction `S (S (S (S O)))`.

The type `nat` is absolutely useless to be extracted to programs and doing
actual computations because the operations are tremenduously unperformant a
memory consuming. But `nat` is an important type to be used in
proofs. E.g. when it is necessary to reason about balancing a binary tree the
type `nat` can be used in proofs to represent the height of the tree.



## Inequality Proofs

We can define a predicate `Successor` which states that a number is the
successor of another number.

    Definition Successor (n:nat): Prop :=
        match n with
        | O => False
        | S _ => True
        end.

The term `Successor n` is a type because its type is a sort. The proposition
`Successor 1` needs a proof of `True` (which is trivial by the constructor `I`
of the type `True` and the proposition `Successor 0` needs a proof of `False`
which is possible only in an inconsistent state containing some contradictory
assumptions.

It is useful to define a predicate like `Successor` for all inductive types in
the sort `Set` which have more than one constructor, one for each additional
constructor. Why? Because these predicates help us to reason about inequality
of objects which have been constructed by different constructors.

For natural number we need a theorem which proves that `S n <> O` for all
numbers (this is the first peano axiom stating _Zero is not the successor of
a number_). A proof of `S n <> O` is a function converting a proof of `S n =
0` into a proof of `False` because `S n <> O` is defined as `S n = 0 ->
False`.

It is easy to proof `S n = S n` by using `eq_refl` and to proof `Successor (S
n)` by `I` (the constructor of `True`). Then we can use the former to rewrite
the proof of `Successor (S n)` into a proof of `Successor 0` which is a proof
of `False` uncovering the contradictory assumption `S n = 0`.

    Theorem successor_not_zero:
        forall n:nat, S n <> 0.
    Proof
        fun n (p:S n = 0) =>
            Equal.rewrite p Successor I.

This method can be used on any inductive type to proof that two objects
constructed with different constructors must be different.


## Injectivity Proofs

Usually we need a proof for each inductive type that two equal objects
constructed with the same constructor must have been constructed with the same
arguments.

For natural numbers we want to be able to proof `S n = S m -> n = m`. This
property is called the _injectivity_ of constructurs.

First we present the proof and then explain it.

    Theorem successor_injective:
        forall n m:nat, S n = S m -> n = m.
    Proof
        fun n m (p:S n = S m) =>
            let f x :=
                match x with
                | S k => k
                | O => n  (* value not important *)
                end
            in
            Equal.inject p f.

The inner function `f` pulls out the value used by the constructor `S` or
returns an arbitrary value in case that the object has been constructed by
`O`.

The theorem `Equal.inject` uses a proof of the equality of two objects `a` and
`b` and a function `f` to construct a proof of `f a = f b`. In the theorem `p`
is a proof of `S n = S m`. Injecting this into `f` results in a proof of `f (S
n) = f (S m)` whose normal form is `n = m`.

It is easy to see that this method can be used on any inductive type with
constructors taking arguments. Note that the value used in the inner function
`f` returned in case that the object has been constructed with some other
constructor is not important. The only important fact is that we have a value
to return. There is always a value because we want to prove the equality `n =
m` and we can always choose one of them.




<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
