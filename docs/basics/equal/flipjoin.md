# Flip and Join

## Flip Equality

Equality is a symmetric relation. Therefore `a = b` implies `b = a`. Given a
proof term for an equality `a = b` we want to construct a proof term for `b =
a`.

Using the above functions it is easy. By `eq_refl` we construct `a = a` and
then we use the proof of `a = b` to rewrite the `a` on the left hand side of
`a = a` into `b`.

    Theorem
        flip (A:Type) (a b:A) (p:a=b): b=a.
    Proof
        rewrite p (fun x => x = a) eq_refl.


## Flip Inequality

We can use `flip` to prove that an inequality is symmetric as well i.e. that
we can convert any proof of `a <> b` into a proof of `b <> a`.

A proof of `b <> a` has to prove `b = a -> False` (i.e. convert a proof of `b
= a` into a proof of `False`. We have already a proof of `a <> b` which is
equivalent to `a = b -> False`. Therefore we have to flip `b = a` into `a = b`
and use the proof of `a <> b` to convert it into a proof of `False`.

    Theorem
        flip_not_equal (A:Type) (a b:A) (p:a<>b): b<>a.
    Proof
          (* p: a=b -> False
             goal: b=a -> False
           *)
        fun q:b=a => p (flip q).

# Join Equalities

Equality not only is symmetric. It is transitive as well. Having a proof for
the two equalities `a = b` and `b = c` we should be able to create a proof
term for `a = c`.

Using `rewrite` it can be done easily. W pbce use the proof of `b = c` to rewrite
`b` in `a = b` into `c`.

    Theorem
        join (A:Type) (a b:A) (pab:a=b) (pbc:b=c): a = c.
    Proof
        rewrite pbc (fun x => a = x) pab.



<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
