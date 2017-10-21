# The Structure of a Source File

## Basic Layout

A source file has the file extension `*.v` and it is called a Coq
module. Usually file names start with an upper case letter, but this is only a
convention not enforced.

A source file contains a sequence of declarations of the form

    (* Header *)
    Require name.

    Require Import name.

    (* Type definitions *)
    Inductive name  .... see later.

    (* Axioms *)
    Parameter name: type.

    Axiom name: type.

    (* Transparent Definitions *)
    Definition name: type := definition_term.

    (* Opaque Definitons *)
    Theorem name: type. Proof proof_term.

    Lemma name: type. Proof proof_term.

    Goal type. Proof proof_term.

The header of a module declares the used modules. A use clause without
`Import` just states the module is used, but all declarations of the used
module are available via its qualified name like `M.some_function`. With
`Import` the names can be used unqualified.

The keywords `Parameter` and `Axiom` declare axioms. Axioms are declarations
without definition term i.e. they are assumptions which the system does not
(and cannot) check. The keywords `Parameter` and `Axiom` can be used
interchangeably. But the intention is to use `Parameter` for assumptions in
the `Set` sort and `Axiom` for assumptions in the `Prop` sort.

It is strongly recommended __not__ to use any axioms in the outer level of a
source file (unless you know exactly what you are doing). Axioms cannot be
checked by the system and can make your whole development inconsistent.

The keywords `Definition`, `Theorem`, `Lemma` ... (and some more) can be used
interchangeable. The names can be chose to indicate the meaning of the thing
you are defining. Usually a `Definition` defines some function and a `Theorem`
or `Lemma` makes a definition in the `Prop` sort i.e. it has some logical
content.

Transparent definitions can be expanded by the compiler (see `delta reduction`
in the previous chapter), opaque definitions cannot be expanded by the
compiler. Usually a `Definition` is transparent and a `Theorem` or `Lemma` is
opaque.

The keyword `Goal` starts an anonymous theorem (i.e. a theorem without a name)
followed by a term which proves the theorem.



## Definitions with Arguments

There are two forms of definitions.

    Definiton name: type_term := definition_term.

    Definition name (a:A) (b:B) ... : type_term := definiton term.

The second form is equivalent to

    Definition name: forall (a:A) (b:B) ... , type_term :=
        fun a b .... => definition_term.

Because we have dependent types, the argument `a` can occur in `B` and all the
following types, the argument `b` can occur in all types which follow after the
second arguments and soon.

If `b` does not occur in the subsequent types and none of the other argument
name occurs in subsequent types the definition can be rewritten to

    Definition name: forall a:A, B -> .. -> type_term :=
        fun a b .... => definition_term.

If even `a` does not occur in the subsequent types then it can be rewritten to

    Definition name: A -> B -> .. -> type_term :=
        fun a b .... => definition_term.

You can see that the arrow type `A -> B` is just a special case of the
dependent product `forall a:A, B`.

If the type of a definition is a dependent product or its specialize companion
an arrow type then the definition is a function and the term implementing the
function must be a function term (or a term whose normal form is a function
term).

Note that a term starting with `forall a:A, ...` or `A -> ...` is always a
type and a term starting with `fun x ... => ... ` is always an object.

Remember that the type of a type is a sort (either `Set` or `Prop` or `Type`)
and the type of an object is a type. Since terms can represent objects, types
and sorts it is easy to get confused. I try to name objects and functions
returning objects with lower case letters and let type names (or names of
functions returning types) start with an upper case letter. However this
convention cannot be universal because many standard types like `nat`, `list`,
`ex`, `sig`, `le` have a long history of lower case names and nobody should
change that.







## Modules and Sections

A source file can be structured into modules and sections which can be
arbitrarily nested. These are declarations of the form

    Module name.
        Declarations
        ...
    End name.

    Section name.
        Declarations
        ...
    End name.

A module defines a namespace and outside the module the names must be used
fully qualified unless the namespace of the module is `Import`ed.

A section does not define a namespace. Sections are useful to structure a
source file (see later).


## Compile a Module

The command `coqc Name.v` entered at the command line of your computer
compiles the source file `Name.v` into the compiled Coq object `Name.vo`

Compiled Coq objects can be used by other modules. The usage graph must not be
cyclic.

<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
