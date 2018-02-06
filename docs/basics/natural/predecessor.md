# Predecessor as Partial Function


The standard library of Coq defines the following predecessor function.

    Definition pred (n:nat): nat :=
      match n with
      | 0 => 0
      | S m => m
      end.

Since `0` has no predecessor the function cannot compute it. The function
chooses to return `0` as the predecessor of `0` in order to return something
meaningful.

But the predecessor function is partial. It is not defined for the number
`0`. Coq allows us to write partial function by using an additional argument
which proves that the argument is within the domain of the function. The
partial function should have the following signature.

    predecessor (n:nat) (p:is_Successor): nat := ...

However we can do better than that. The function should not return a natural,
it should return a number which is the predecessor of `n`. In order to specify
this exactly the Coq standard library defines the following inductive type.

    Inductive sig (A : Type) (P : A -> Prop) : Type :=
        exist : forall x : A, P x -> sig A P

The constructor `exist` makes from an object `x` of type `A` and a proof of `P
x` an object of type `@sig A P` (note: The argument `A` is implicit). I.e. an
object of type `@sig A P` contains an object of type `A` and a proof that it
satisfies the predicate `P`. By pattern matching on an object of type `@sig A
P` we can retrieve the object and the proof.

Since objects bundled with a proof of a property are used frequently, Coq
provides a notation.
```ocaml
    {x:A | P x}     (* is a notation for `@sig A P` *)
```

We can use a sig-type to specify the result of the predecessor function. The
predecessor function should have the signature

    predecessor (n:nat) (p:is_Successor): {i:nat | S i = n} := ...

The complete function looks like

    Definition predecessor (n:nat) (p:is_Successor n): {x:nat|S x = n} :=
      (match n with
      | 0 => fun p:is_Successor 0 => match p with end
      | S m => fun _ => exist _ m eq_refl
      end) p.


For the first case we need the proof `p` to derive a contradiction. For the
second case the proof is not needed. For the second case we need a number `x`
and a proof of `S x = S m`. Clearly the number `x` is the number `m` an the
proof is a trivial proof of reflexivity. The type inferer of Coq infers the
predicate `fun x => S x = S m` automatically. Therefore we can use the
wildcard `_` as the first argument of the constructor `exist`.




<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
