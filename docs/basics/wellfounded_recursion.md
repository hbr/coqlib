# Wellfounded Recursion

## Wellfounded Relation

Coq proves the termination of structurally recursive functions by checking
that every recursive function call happens on a structurally smaller argument
than the argument of the previous call. By doing that it can guarantee that
recursion terminates.

However there is another possibility to ensure that a recursive functions
terminates. This possibility uses wellfounded relation.

A wellfounded relation is a binary relation which has no infinitely decreasing
chains. If we have two elements `x` and `y`, a binary relation `R:A->A->Prop`
and `R x y` holds we say that `x` is a predecessor of `y` with respect to the
relation `R`. A decreasing chain with respect to the relation `R` is a
sequence

    a0 a1 a2 ...

where `R aj ai` holds for `j = i+1`. `R` is wellfounded if all such chains are
finite.

Coq uses accessability to define a wellfounded relation. An element `x` is
accessible via a relation `R` if all its predecessors are accessible. This is
defined as the inductive type

    Inductive Acc (A:Type) (R: A->A->Prop) (x:A): Prop :=
        Acc_intro : (forall y:A, R y x -> Acc R y) -> Acc R x.

The type argument `A` is implicit. `Acc R a` is the proposition stating that
`a` is accessible via the relation `R`. The inductive type has only one
constructor `Acc_intro`. `Acc_intro` needs a proof that all predecessors of
`x` are accessible and provides a proof that `x` is accessible.

If `R` has no elements without predecessors then it is impossible to generate
a proof (which always must be finite) for the accessibility of any element.

An element `x` which has no predecessors is an element for which a proof of
`forall y, ~ (R y x)` exists. I.e. we can proof `forall y, R y x -> Acc R y`
by contradiction. Therefore an element without predecessors is vacuously
accessible. It is a minimal element of the relation. I.e. all minimal elements
of a relation are accessible.

Since every proof of accessibility of a certain element needs a proof of the
accessibility of all predecessors which in turn need a proof of the
accessibility of all their predecessors, any proof of the accessibility of an
element must finally in a finite number of steps use a proof of elements which
have no predecessors.

In Coq a relation over a type is wellfounded if all elements of the type are
accessible.

    Definition well_founded (A:Type) (R:A->A->Prop): Prop :=
        forall a, Acc R a.



## A Wellfounded Relation on Natural Numbers

The `<` relation on natural numbers is wellfounded. In order to prove this we
use induction.

The number 0 has no predecessors in this relation and is therefore accessible.

Let's assume that `k` is accessible. In that case we have to prove that `S k`
is accessible as well. One predecessor of `S k` is `k`, the other predecessors
are the predecessors of `k` (note that a predecessor of `S k` is a predecessor
of it with respect to the relation `<`, i.e. the predecessors of `S k` are all
numbers `j` satisfying `j < S k` or `j <= k`). In order to prove that all
predecessors `j` of `S i` are accessible we make the case split `j = k` and `j
<> k`. In both cases a proof of the accessibility of `j` is straightforward.

    Theorem lt_well_founded: well_founded lt.
    Proof
      fix f (n:nat): Acc lt n :=
      match n with
      | 0 =>
        Acc_intro
          _
          (fun j pj_lt_0 =>
             match successor_not_below_zero pj_lt_0 with end)
      | S k =>
        (* Goal: Acc lt (S k). *)
        let pk: Acc lt k := f k in
        match pk with
          Acc_intro _ p =>
          Acc_intro
            _
            (fun j (pj_lt_Sk:S j <= S k) =>
               match is_equal j k with
               | left p_eq_jk =>
                 Equal.rewrite (Equal.flip p_eq_jk) _ pk
               | right p_ne_jk =>
                 let pj_le_k: j <= k := cancel_successor_le pj_lt_Sk in
                 let pj_lt_k: j < k  := le_ne_implies_lt pj_le_k p_ne_jk in
                 p j pj_lt_k
               end)
        end
      end.



## Recursion with Wellfounded Relations

A wellfounded relation enables us to write recursive functions where the
recursive call is on an argument which is a predecessor of the original
argument. Writing such a function directly is not trivial because the
recursion has to use the accessibility predicate in a non trivial
manner. However the Coq standard libary has an object called
`well_founded_induction_type` which helps to write such general recursive
functions.

The type of `well_founded_induction_type` can be seen by issueing a `Check`
command.

    Check well_founded_induction_type.

    well_founded_induction_type
     : forall
           (A : Type)                          (* arg1 implicit *)
           (R : A -> A -> Prop),               (* arg2 implicit *)
           well_founded R ->                   (* arg3 *)
           forall T : A -> Type,               (* arg4 *)
           (forall x : A, (forall y : A, R y x -> T y) -> T x) ->  (* arg5 *)
           forall a : A, T a

This type signature looks rather complicated because it covers the most
general case of a dependent type. We will generate a simpler definition in the
following. But first let us understand the signature.

It is the type of a function which needs a type `A` which is the input type of
the generated recursive function.

Then it needs an endorelation over that type and a proof that the relation is
wellfounded. The input type `A` and the relation `R` are implicit because they
are uniquely defined by the proof term which proves `well_founded R`.

The next argument of type `forall T:A -> Type` is a function which maps an
element of the input domain to the result type of the desired
function. I.e. the result type can depend on the input value. In many cases
the result type need not be dependent and we can use a constant function of
the form `fun _ => Result_type` as the forth argument.

The fifth argument is probably the most difficult to understand. It is a
function taking 2 arguments. The first is an input value, the second is a
recursor. By using the input `x` and a recursor it must build a value of type
`T x`. We will discuss this fith argument later more in detail. It is the step
function of the recursion.

The output is a value of type `forall a:A, T a` i.e. the desired function
which maps an element of the input domain to the result type.

Before discussing the core function (arg5) we want to get rid of the dependent
type which is usually not necessary. We want an function which generates a
recursive function of type `A -> B`.

    Definition
      wf_recursion
      (A:Type)
      (B:Type)
      (R:A->A->Prop)
      (wf:well_founded R)
      (step: forall x:A, (forall y:A, R y x -> B) -> B): A -> B
      :=
        well_founded_induction_type wf (fun _ => B) step.

This function is much cleaner. The first two arguments are the input and the
output type of the desired function, the third is a relation on the input
domain, the forth a proof that the relation is wellfounded and the fifth is
the step function. The first three arguments are implicit because they can be
derived from the following arguments. Therefore the function just needs a
proof of the wellfoundedness of the relation and the step function and
produces a recursive function of type `A -> B`.

Now we look into the type of the step function. AV valid declaration looks like

    step (x:A) (fr:forall y:A, R y x -> B): B := ...

The step function takes an argument `x` of type `A` and a recursor `fr` which maps
any other value of type `A` and a proof that it is a predecessor of `x` within
the relation `R` into a value of the result type, and returns a value of the
result type.

The step function has to decide if the value `x` does not have a predecessor
in the relation `R` i.e. if `x` is minimal or if `x` has a predecessor. The
first case is the terminating case for which the step function has to generate
the result by itself. It cannot use `fr` because there is no predecessor to
give to the recursor `fr`. In the second case the step function has to find a
predecessor of `x` (and a proof that it is a predecessor) and use `fr` to
create the final value.

The recursor `fr` will call the step function recursively until the
terminating case is encountered. Due to the fact that `R` is wellfounded the
terminating case will be encountered in a finite number of steps.

In the following section we use `wf_recursion` to construct a general
recursive function.

## Mu Recursive Functions

<!--

## Details of the Wellfounded Recursion

well_founded_induction_type =
fun (A : Type) (R : A -> A -> Prop) (Rwf : well_founded R)
  (P : A -> Type) (X : forall x : A, (forall y : A, R y x -> P y) -> P x)
  (a : A) =>
Acc_rect P
  (fun (x : A) (_ : forall y : A, R y x -> Acc R y)
     (X0 : forall y : A, R y x -> P y) => X x X0) (Rwf a)
     : forall (A : Type) (R : A -> A -> Prop),
       well_founded R ->
       forall P : A -> Type,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall a : A, P a


Acc_rect =
fun (A : Type) (R : A -> A -> Prop) (P : A -> Type)
  (f : forall x : A,
       (forall y : A, R y x -> Acc R y) -> (forall y : A, R y x -> P y) -> P x) =>
fix F (x : A) (a : Acc R x) {struct a} : P x :=
  match a with
  | Acc_intro _ a0 => f x a0 (fun (y : A) (r : R y x) => F y (a0 y r))
  end
     : forall (A : Type) (R : A -> A -> Prop) (P : A -> Type),
       (forall x : A,
        (forall y : A, R y x -> Acc R y) -> (forall y : A, R y x -> P y) -> P x) ->
       forall x : A, Acc R x -> P x


-->

<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
