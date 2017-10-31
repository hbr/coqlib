Require Import Core.
Require Binary_tree.
Set Implicit Arguments.

Module Make (S0:SORTABLE) (Extra:ANY).
  Module S := Sortable_plus S0.
  Import S.Notations.

  Module BT := Binary_tree.Make S Extra.
  Include BT.
  Export  BT.

  Inductive Bounded: A -> A -> T -> Prop :=
  | singleton_bounded:
      forall a e,
        Bounded a a (node a e empty empty)
  | node_bounded:
      forall lo1 hi1 t1 lo2 hi2 t2 a e,
        Bounded lo1 hi1 t1 ->
        Bounded lo2 hi2 t2 ->
        hi1 <= a ->
        a = lo2 ->
        Bounded lo1 hi2 (node a e t1 t2).

  Inductive Sorted: T -> Prop :=
  | empty_sorted: Sorted empty
  | node_sorted:
      forall lo hi t,
        Bounded lo hi t -> Sorted t.


  Theorem least_is_leftmost:
    forall (lo hi:A) (t:T),
      Bounded lo hi t ->
      Leftmost t lo.
  Proof
    fix f lo hi t bnd :=
    match bnd in Bounded lo hi t
          return Leftmost t lo with
    | singleton_bounded a e =>
      lm_noleft a e empty
    | @node_bounded
        lo1 hi1 t1 lo2 hi2 t2 a e
        bnd1 bnd2 hi1_a a_lo2 =>
      let p: Leftmost t1 lo1 := f lo1 hi1 t1 bnd1 in
      @lm_left lo1 a e t1 t2 p
    end.

End Make.
