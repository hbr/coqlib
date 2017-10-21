# Decision Procedures

## Booleans

The standard library defines the inductive type `bool` in the following
manner.

    Inductive bool: Set :=
    | true:  bool
    | false: bool.

The type of `bool` is `Set` (i.e. `bool:Set`). Therefore it is a datatype
which can occur in computations. Types of type `Set` can be extracted to real
programs.

Beside the type `bool` the standard library defines the functions `andb`,
`orb`, `negb` with the usual semantics.

    Definition orb (a b:bool): bool :=
        match a with
        | true  => true
        | false => b
        end.
    Definition andb (a b:bool): bool :=
        match a with
        | true  => b
        | false => false
        end.
    Definition negb (a:bool): bool :=
        match a with
        | true  => false
        | false => true
        end.

If you add `Require Import Bool.` in your source file you can write `a && b`
and `a || b` as a shorthand for `andb a b` and `orb a b`. 

Traditionally functions returning boolean values have the character `b` as the
last letter in their names.

## The Type `sumbool`

In many cases functions returning a value of type `bool` are not very
useful. They are useful only if there is some theorem that allows us to
conclude the existence of a proof for a certain proposition in case the
function returns `true` and the existence of a proof for another proposition
in case the function returns `false`.

However writing a boolean function and then proving that its value reflects
certain propositions is tedious and usually not necessary. The datatype
`sumbool` of the standard library offers a better solution. It is defined as

    Inductive sumbool (A B:Prop): Set :=
    | left:  A -> sumbool A B
    | right: B -> sumbool A B.

The Coq library defines the notation `{A} + {B}` as a shorthand for `sumbool A
B`.

If we have a proof `a` of `A` (i.e. `a:A`) then `left a` constructs an object
of type `{A} + {B}` and if we have a proof `b` of `B` then `right b`
constructs an object of the same type. An object of type `{A} + {B}` contains
either a proof of `A` or a proof of `B`.

It is interesting to note that `{A} + {B}` has type `Set` and not type
`Prop`. Having type `Set` means that it can be extracted to real
programs. Extraction erases all objects of the `Prop` sort. Therefore the only
information available in extracted programs is whether the object has been
constructed with the `left` or the `right` constructor and this is the same
information as conveyed by an object of type `bool`.

However in Coq the propositional information is accessible. On the result of
a call to a function returning an object of type `{A} + {B}` we can pattern
match and get to cases. One with a proof of `A` and one with a proof of `B`.

Therefore within Coq it is almost always better to write a function returning
an object of type `{A} + {B}` than returning an object of type `bool`. After
extraction the function will return a boolean value.


## Decision Procedure for Equality

In the previous chapter we looked into inductive type `eq` which represents
equality in Coq. This type lives in the `Prop` sort. Objects of type `eq a b`
or `a = b` (using the more readable notation) are not booleans but proves of
the corresponding equality. If we define a datatype and want to do compuations
with the type we usually need a computable functions which tells us if two
objects of the type are equal. Such a function is a decision procedure and it
has the type

    forall (A:Type) (a b:A), {a = b} + {a <> b}

Note that `a <> b` is just a notation for `~ a = b`, which is a notation for
`not (a = b)` and `not` is a function which can be expanded to `a = b ->
False`. I.e. the normal form of `a <> b` is `a = b -> False`.

We add the following defintion to the module `Equal` of the source file
`Equality_.v` in order to be able to access it from other modules by
`Equal.Decider`.

    Module Equal.
        ...
        Definition Decider (A:Type): Type :=
            forall a b:A, {a = b} + {a <> b}.
    End Equal.

We define only the type of a decision procedure for equality.

<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
