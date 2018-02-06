# True and False

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


<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
