# Rewrite a Proposition

Lets assume we want to prove the proposition

    forall (A:Type) (a b:A) (P:A->Prop), a = b ->  P a -> P b

which states: If two objects are equal then every property satisfied the first
is satisfied by the second as well.

The proposition is a dependent product. Therefore we need a proof term which
is a function of the form

    fun A a b p_eq P pa => ...

where `pa` is a variable representing a proof of `P a` and `p_eq` is a
variable which represents a proof for the equality `a = b` (i.e. we have
`pa:Pa` and `p_eq:a=b`.

Since `p_eq` represents a proof of `a = b` (i.e. `eq a b` without the
notation) and `eq` has only one constructor we know that `p_eq` must have been
constructed by `eq_refl`.

The appropriate dependent pattern match construct looks like

    match p_eq in (_ = x) return P x with
    | eq_refl => ...
    end

We don't need a variable to represent `p_eq` here (therefore no `as ...`). The
type of `p_eq` is `a = b`. We cannot bind a variable to `a` because it is a
parameter, but we can bind a variable to `b`. We use the variable `x`
here. Now we can express the required type of the pattern match expression `P b`
with the variable `x` which is bound to `b` in the outer context. The required
type is `P x`.

As opposed to `P b` the type `P x` can be projected into the different match
cases (here there is only one). Since `eq_refl` states that `p_eq` has been
constructed by `@eq_refl A a` it must have the type `a = a`. Therefore the
variable `x` is bound to `a` in the inner context of that case. Thus the
required type of the branch is `P a` for which we have already the proof
`pa`. Therefore the complete proof is

    Theorem rewrite (A:Type) (a b:A) (p_eq:a=b) (P:A->Prop) (pa:P a): P b.
    Proof
        match
          p_eq in (_ = x)
          return P x
        with
          eq_refl => pa
        end.

We name this theorem `rewrite` because it rewrites `a` by `b` in the
proposition proved by `pa`. The proposition proved by `pa` is provided as a
function `P` which maps the term `a` to the proposition proved by `pa`.

Suppose we have a proposition of the form `n + k*i < e` and a proof `p` for
it. Furthermore we have a proof `q` for the proposition `k*i = i*k`, then the
term `rewrite p (fun x => n + x < e) q` generates a proof for `n + i*k <
e`. The application rewrites `k*i` by `i*k` in the proposition `n + k*i < e`.



<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
