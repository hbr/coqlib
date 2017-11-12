Require Import Core.
Require Binary_tree.
Set Implicit Arguments.

Module Make (S0:SORTABLE) (Extra:ANY).
  Module S := Sortable_plus S0.
  Import S.Notations.

  Module BT := Binary_tree.Make S Extra.
  Include BT.
  Export  BT.

  (*====================================*)
  (** * Basic Definitions               *)
  (*====================================*)
  Inductive Bounded: A.t -> A.t -> t -> Prop :=
  | singleton_bounded:
      forall a e,
        Bounded a a (Node a e Empty Empty)
  | node_bounded:
      forall lo1 hi1 t1 lo2 hi2 t2 a e,
        Bounded lo1 hi1 t1 ->
        Bounded lo2 hi2 t2 ->
        hi1 <= a ->
        a = lo2 ->
        Bounded lo1 hi2 (Node a e t1 t2).

  Inductive Sorted: t -> Prop :=
  | empty_sorted: Sorted Empty
  | node_sorted:
      forall lo hi t_,
        Bounded lo hi t_ -> Sorted t_.


  Theorem least_is_leftmost:
    forall (lo hi:A.t) (t_:t),
      Bounded lo hi t_ ->
      Leftmost t_ lo.
  Proof
    fix f lo hi t bnd :=
    match bnd in Bounded lo hi t
          return Leftmost t lo with
    | singleton_bounded a e =>
      lm_noleft a e Empty
    | @node_bounded
        lo1 hi1 t1 lo2 hi2 t2 a e
        bnd1 bnd2 hi1_a a_lo2 =>
      let p: Leftmost t1 lo1 := f lo1 hi1 t1 bnd1 in
      @lm_left lo1 a e t1 t2 p
    end.


  (*====================================*)
  (** * Insertion                       *)
  (*====================================*)
  Section insertion.
    Inductive Inserted: A.t -> t -> t -> Prop :=
    | empty_inserted:
        forall a e, Inserted a Empty (Node a e Empty Empty)
    | left_inserted:
        forall x t11 t12 t2 a e,
          x <= a ->
          Inserted x t11 t12 ->
          Inserted x (Node a e t11 t2) (Node a e t12 t2)
    | right_inserted:
        forall x t1 t21 t22 a e,
          a <= x ->
          Inserted x t21 t22 ->
          Inserted x (Node a e t1 t21) (Node a e t1 t22).

    Theorem inserted_is_node:
      forall (x:A.t) (t1 t2:t),
        Inserted x t1 t2 ->
        is_Node t2.
    Proof
      fix f x t1 t2 ins:=
      match ins in Inserted x t1 t2
            return is_Node t2
      with
      | empty_inserted _ _ => I
      | left_inserted _ _ _ _ => I
      | right_inserted _ _ _ _ => I
      end.
(*
    Theorem inserted_is_sorted:
      forall (x:A.t) (t1 t2:T),
        Sorted t1 ->
        Inserted x t1 t2 ->
        Sorted t2.
    Proof
      fix f x t1 t2 sorted inserted:=
      let P t2 := forall x t2, Inserted x t1 t2 -> Sorted t2 in
      (match sorted in Sorted t1
            return P t2
      with
      | empty_sorted =>
        let _ := P t2 in
        _
      | node_sorted _ => _
       end
      ) x t2 inserted
    .
*)



  End insertion.
End Make.
