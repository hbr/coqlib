# Types and Terms

The terms in Coq can encode sorts, types and objects.

All terms in Coq have a type. We can always ask the question "What is the type
of a term?" by issueing the command `Check t.`.

Therefore sorts have types, types have types and objects have types. This
statements seems to contain some circularity. But Coq ensures some typing
discipline to avoid circularity.

At the bottom of the hierachy are sorts. There are 3 kind of sorts

- `Prop`
- `Set`
- `Type(i)`

where `i` is any natural number. There are the following axiomatic typing
judgements.

    Prop: Type(i)
    Set:  Type(i)
    Type(i): Type(j)             where i < j

The index of the sort `Type` is a universe index which Coq hides from its
users. Therefore in a Coq session you get the seemingly circular typing
judgement `Type: Type`. But internally Coq always keeps an index which ensures
the above conditions (i.e. the left type has an index strictly less than the
index of the right type).


A term represents a type if its type is a sort and a term represents an object
if its type is a type.

Therefore there can be terms of type `Prop`, `Set` and `Type` (index
hidden!). I.e. the typing judgements

    A: Prop
    nat: Set
    X: Type

say that the terms `A`, `nat` and `X` are types. The terms whose types are
types are objects. The following judgements

    a:A
    i:nat
    x:X

ensure that `a`, `i` and `x` are objects. There is some convention that
variables representing types are written in uppercase and variables
representing objects are written in lowercase. However this convention is not
universally used (e.g. see the type `nat` above) and not enforced by the Coq
compiler. The syntax of Coq is defined in a way that you can mix uppercase and
lowercase letters arbitrarily in identifiers.


## Propositions

If we have `A: Prop` then `A` is a type which represents propositions. The
terms of type `A` are proofs of `A`.

All propositions in Coq are types. If you can provide a term which has this
type then Coq accepts it as a proof of the proposition.


## Datatypes

If we have `T:Set` then `T` is some data type (e.g. number, tree, list,
...). The terms of type `T` are objects which can exist in a program.


## General Types

If we have `X:Type` then the term `X` represents some general type which can
be either a proposition or a datatype. There can be objects `x` of type `X`
(i.e. `x:X`) which represent either propositions (i.e. are proofs) or data
(i.e. are computations).


## Type of Functions i.e. Dependent Types

In Coq you can define functions. As you might guess functions are terms and
therefore must have a type (all terms must have a type in Coq!).

In mathematics a function maps objects of its domain to objects of its range
i.e. a function `f` is a mapping from `A` to `B` i.e. `A -> B`. If `x` is an
object of the domain `A` then `f(x)` is an object of domain `B`.

In Coq it is the same. If `A` and `B` are types then `A -> B` is a type as
well and in particular it is the type of functions mapping objects of type `A`
to objects of type `B`. Like in most functional languages Coq uses
juxtaposition to indicate function application i.e. insteat of the usual
mathematical function application `f(x)` we write just `f x` in Coq.

But in Coq things are a little more complicated in order to make it powerful
for the generation of rigid proofs. In Coq the general type of a function is

    forall x:A, B

which is called a dependent product. An object `f` of type `forall x:A,B` i.e.

    f: forall x:A,B     (* read: 'f' has type 'forall x:A,B *)

is a function mapping objects `x` of type `A` to objects of type `B x`. If `x`
does not occur in `B` then we can write

    f: A -> B

as a shorthand for `f: forall x:A,B`.

In Coq types can be functions which can be applied to objects. E.g. the
proposition `i < j` where `i` and `j` could be natural numbers clearly depends
on these numbers. For some numbers `i` and `j` the proposition `i < j` might
be provable i.e. there might be an object `p` which represents a proof which
has type `i < j` i.e. `p: i < j`.

Dependent types allow us to define a type which represents a list with a
certain length. This is not possible in conventional programming languages
where types cannot depend on the value of objects. In Haskell and ML objects
of type `list` have an arbitrary length. It is not possible in Haskell or ML
to define a type for lists with a certain length.


## Functions

We can write the term

    fun i:nat => i + 2

which is a function mapping any natural number `i` to `i + 2`. Since all Coq
terms must have types this function term has a type as well.

    (fun i:nat => i + 2): nat -> nat

which is a shorthand for

    (fun i:nat => i + 2): forall i:nat, nat

Another function term is

    (fun i j:nat => i < j)

This must have a type as well which is expressed by the following judgement

    (fun i j:nat => i < j): nat -> nat -> Prop

You can enter the command `Check fun i j:nat => i < j` in a Coq session to
verify the claim.



## Normalization

The typing discipline of Coq guarantees that all terms have a normal
form. There are 4 reductions (beta, delta, zeta, iota) which Coq does
internally.

#### Beta Reduction

Beta reduction is done according to the following scheme

    (fun x:T => e) a        ~>   e{x/a}

The left part is a reducible expression (i.e. a function term applied to an
argument) and the right part is its contractum where all occurrences of `x` in
the term `e` are substituted by the argument `a`.


#### Delta Reduction

Delta reduction is substitution a term by its definition. If the term `f` has
the definition `(fun x:T => e)` then the following reduction is applied.

    f a                     ~>  (fun x:T => e) a

Note that this delta reduction can be followed by a beta reduction.


#### Zeta Reduction

Zeta reduction is the same as beta reduction done with let expressions.

    let x:T := a in e       ~>  e{x/a}


#### Iota Reduction

Iota reduction is the computation of a recursive function i.e. a fixpoint (see
later). Note that all recursive functions in Coq are terminating. Therefore
the computation of a recursive function is guaranteed to return a result in
finite time.


<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
