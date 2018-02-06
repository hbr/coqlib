# Reusable Theorems

The theorems `rewrite`, `inject`, `flip`, `flip_not_equal` and `join` are
useful so that it is worthwhile to put them into a module for reuse. We add to
our `Core.v` module the following declarations.

    Module Equal.
        Theorem rewrite ...
        Theorem inject  ...
        Theorem flip    ...
        Theorem flip_not_equal  ...
        Theorem join    ...
    End Equal.

    Notation "( 'eq_chain:' x , y , .. , z )" :=
      (Equal.join .. (Equal.join x y) .. z) (at level 0): equality_scope.

We can use the content of this module in any other Coq source file by putting
`Require Import Core.` and `Open Scope equality_scope.` at the top.

We can use `Equal.rewrite ...`, `Equal.inject ...`, ... to generate proof
terms.

Furthermore the included notation allows to join an arbitrary number of proof
terms which prove `a = b`, `b = c`, ... , `y = z` by

    (eq_chain:  pab, pbc, ... , pyz)

in order to generate a proof for `a = z`.



<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
