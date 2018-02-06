# Dependent Pattern Match

This is a good point to introduce dependent pattern match. Dependent pattern
match is not needed for all proofs done below, but it is important to
understand the concept and be able to use it where necessary.

A pattern match inspects a term (it can be a proof term or any other term) and
does a case distinction on the possible cases how a term of the corresponding
type could have been constructed. Since practically all types in Coq are
inductive you can always do some pattern match.

The pattern match term has a required type and the different branches of the
pattern match have to provide a term which satisfies the required type. We can
always write the required type `T` explicitly.

    match exp return T
    | ...
    ...
    end

Usually we don't do that because the required type can be inferred from the
context. However the type `T` might be dependent. It could depend on some
other terms which represent objects (proofs or computations). The dependency
of the type `T` might look different for the different branches and Coq is not
always able to infer the specific type for each branch because problem is
undecidable in general.

Therefore it is possible bind some variables and let Coq compute the required
type for each branch by unification. The complete possibitlities of the
dependent pattern match are

    match exp as x in C T1 T2 ... return T
    | ...
    ...
    end

with the variables `x`, `T1`, `T2`, ... The variable `x` is bound to `exp`. `C
T1 T2 ...` must be unifiable to the type of `x` (i.e. the type of `exp` in the
outer context) and the variables can be used to express the required result
type `T` of the complete match expression.

With this information Coq is able to generate uniquely a requested type for
each branch.

This description might seem very abstract. But in the sequel we will show how
to use this construct for some equality proofs.


<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
