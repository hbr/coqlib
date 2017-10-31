Require Binary_search_tree.
Require Import Core.
Require Import Coq.Lists.List.
Import ListNotations.
Import Equal.Notations.

Set Implicit Arguments.


Module Make (S0:SORTABLE).

(*====================================*)
(** * Balance Indicator *)
(*====================================*)
  Module Balance_indicator.
    Inductive T0: Set := left: T0 | balanced: T0 | right : T0.
    Definition T:Set := T0.

    Definition Left (b:T): Prop :=
      match b with
      | left => True
      | _ => False
      end.

    Definition Right (b:T): Prop :=
      match b with
      | right => True
      | _ => False
      end.

    Definition Balanced (b:T): Prop :=
      match b with
      | balanced => True
      | _ => False
      end.

    Theorem left_not_balanced: left <> balanced.
    Proof
      fun eq => Equal.rewrite eq Left I.

    Theorem balanced_not_right: balanced <> right.
    Proof
      fun eq => Equal.rewrite eq Balanced I.

    Theorem right_not_left: right <> left.
    Proof
      fun eq => Equal.rewrite eq Right I.
  End Balance_indicator.
  Module B := Balance_indicator.



(*====================================*)
(** * Use Module 'Binary_search_tree' *)
(*====================================*)

  Include (Binary_search_tree.Make S0 B).


(*====================================*)
(** * Basic Definitions *)
(*====================================*)


  Definition Left_leaning  (t:T): Prop := Extra t B.left.
  Definition Right_leaning (t:T): Prop := Extra t B.right.
  Definition Balanced (t:T): Prop := Extra t B.balanced.


  Theorem left_leaning_is_node:
    forall (t:T), Left_leaning t -> Node t.
  Proof
    fun t ll => extra_is_node ll.

  Theorem balanced_is_node:
    forall (t:T), Balanced t -> Node t.
  Proof
    fun t bal => extra_is_node bal.

  Theorem right_leaning_is_node:
    forall (t:T), Balanced t -> Node t.
  Proof
    fun t bal => extra_is_node bal.

  Inductive Avl_height: T -> nat -> Prop :=
  | empty_avl: Avl_height empty 0
  | balanced_avl:
      forall h a t1 t2,
        Avl_height t1 h ->
        Avl_height t2 h ->
        Avl_height (node a B.balanced t1 t2) (1+h)
  | left_avl:
      forall h a t1 t2,
        Avl_height t1 (1+h) ->
        Avl_height t2 h ->
        Avl_height (node a B.left t1 t2) (2+h)
  | right_avl:
      forall h a t1 t2,
        Avl_height t1 h ->
        Avl_height t2 (1+h) ->
        Avl_height (node a B.right t1 t2) (2+h).

  Definition Avl_tree (t:T): Prop :=
    exists h, Avl_height t h.


  (*====================================*)
  (** * Rebalancing *)
  (*====================================*)

  (** An avl tree is nearly balanced if its left and right subtree differ in
      height by not more than 2. *)

  Inductive Nearly_avl_left: A -> B.T -> T -> T -> nat -> Prop :=
  | ok_nearly_left:
      forall a bal t1 t2 h,
        Avl_height (node a bal t1 t2) h ->
        Nearly_avl_left a bal t1 t2 h
  | left_nearly_left:
      forall h t1 t2 a,
        Avl_height t1 (2+h) ->
        Avl_height t2 h ->
        Nearly_avl_left  a B.left t1 t2 (3+h).

  Inductive Nearly_avl_right: T -> nat -> Prop :=
  | avl_nearly_right:
      forall t h,
        Avl_height t h ->
        Nearly_avl_right t h
  | right_nearly_right:
      forall h t1 t2 a,
        Avl_height t1 h ->
        Avl_height t2 (2+h) ->
        Nearly_avl_right (node a B.right t1 t2) (3+h).


  Inductive Rebalanced_left: A -> B.T -> T -> T -> T -> nat -> Prop :=
  | l_rebalanced:
      (* No rebalancing
       *)
      forall a bal t1 t2 h,
        Avl_height (node a bal t1 t2) h ->
        Rebalanced_left a bal t1 t2 (node a bal t1 t2) h
  | ll_rebalanced:
      (*
                    b                            a
              a          t3              t1             b
          t1     t2                      x          t2      t3
          x
       *)
      forall h t1 t2 t3 a b bal,
        Avl_height t1 (1+h) ->
        Avl_height t2 h ->
        Avl_height t3 h ->
        Rebalanced_left
          b bal (node a B.left t1 t2) t3
          (node a B.balanced t1 (node b B.balanced t2 t3))
          (2+h)
  | lrl_rebalanced:
      (*
                      c                               b
              a            t4                   a            c
          t1     b         x                 t1   t2      t3   t4
          x   t2  t3                         x    x            x
              x
       *)
      forall h t1 t2 t3 t4 a b c bal,
        Avl_height t1 (1+h) ->
        Avl_height t2 (1+h) ->
        Avl_height t3 h ->
        Avl_height t4 (1+h) ->
        Rebalanced_left
          c
          bal
          (node a B.right
                t1
                (node b B.left t2 t3))
          t4
          (node b B.balanced
                (node a B.balanced t1 t2)
                (node c B.right t3 t4))
          (3+h)
  | lrr_rebalanced:
      (*
                      c                               b
              a            t4                   a            c
          t1     b         x                 t1   t2      t3   t4
          x   t2  t3                         x            x    x
                  x
       *)
      forall h t1 t2 t3 t4 a b c bal,
        Avl_height t1 (1+h) ->
        Avl_height t2 h ->
        Avl_height t3 (1+h) ->
        Avl_height t4 (1+h) ->
        Rebalanced_left
          c
          bal
          (node a B.right
                t1
                (node b B.right t2 t3))
          t4
          (node b B.balanced
                (node a B.left t1 t2)
                (node c B.balanced t3 t4))
          (3+h).

  Theorem rebalanced_left_correct:
    forall (a:A) (bal:B.T) (t1 t2 t3:T) (h:nat),
      Rebalanced_left a bal t1 t2 t3 h ->
      Avl_height t3 h.
  Proof
    fun a bal t1 t2 t3 h rebal =>
      match rebal in Rebalanced_left a bal t1 t2 t3 h
            return Avl_height t3 h
      with
      | @l_rebalanced a bal t1 t2 h pheight =>
        pheight
      | @ll_rebalanced h t1 t2 t3 a b bal pt1 pt2 pt3 =>
        @balanced_avl
          (1+h) a t1 (node b B.balanced t2 t3)
          pt1
          (@balanced_avl h b t2 t3 pt2 pt3)
      | @lrl_rebalanced h t1 t2 t3 t4 a b c bal pt1 pt2 pt3 pt4 =>
        @balanced_avl
          (2+h) b _ _
          (@balanced_avl (1+h) a t1 t2 pt1 pt2)
          (@right_avl h c t3 t4 pt3 pt4)
      | @lrr_rebalanced h t1 t2 t3 t4 a b c bal pt1 pt2 pt3 pt4 =>
        @balanced_avl
          (2+h) b _ _
          (@left_avl h a t1 t2 pt1 pt2)
          (@balanced_avl (1+h) c t3 t4 pt3 pt4)
      end.


  Definition rebalance_left (x:A) (xbal:B.T) (u v:T): T :=
    match u with
    | node a B.left t1 t2 =>
      (* ll *)
      node a B.balanced t1 (node x B.balanced t2 v)
    | node a B.right t1 (node b B.left t2 t3) =>
      (* lrl *)
      node b B.balanced
           (node a B.balanced t1 t2)
           (node x B.right t3 v)

    | node a B.right t1 (node b B.right t2 t3) =>
      (* lrr *)
      node b B.balanced
           (node a B.left t1 t2)
           (node x B.balanced t3 v)

    | _ =>
      node x xbal u v
    end.

(*
  Theorem rebalance_left_correct:
    forall (a:A) (bal:B.T) (t1 t2 t3:T) (h:nat),
      Rebalanced_left a bal t1 t2 t3 h ->
      t3 = rebalance_left a bal t1 t2.
  Proof
    _
  .
*)





  Inductive Rebalanced_right: T -> T -> Prop :=
  | r_rebalanced:
      forall t h,
        Avl_height t h ->
        Rebalanced_right t t
  (*
              a                                     b
        t1          b                         a          t3
                 t2   t3                   t1   t2       x
                      x
   *)
  | rr_rebalanced:
      forall h t1 t2 t3 a b bal,
        Avl_height t1 h ->
        Avl_height t2 h ->
        Avl_height t3 (1+h) ->
        Rebalanced_right
          (node a bal t1 (node b B.right t2 t3))
          (node b B.balanced (node a B.balanced t1 t2) t3)
  (*
              a                                     b
        t1            c                       a            c
        x        b       t4                t1   t2      t3   t4
              t2   t3    x                 x    x            x
              x
   *)
  | rll_rebalanced:
      forall h t1 t2 t3 t4 a b c bal,
        Avl_height t1 (1+h) ->
        Avl_height t2 (1+h) ->
        Avl_height t3 h ->
        Avl_height t4 (1+h) ->
        Rebalanced_right
          (node a bal
                t1
                (node c B.left
                      (node b B.left t2 t3)
                      t4))
          (node b B.balanced
             (node a B.balanced t1 t2)
             (node c B.right t3 t4))
  (*
              a                                     b
        t1            c                       a            c
        x        b       t4                t1   t2      t3   t4
              t2   t3    x                 x            x    x
                   x
   *)
  | rlr_rebalanced:
      forall h t1 t2 t3 t4 a b c bal,
        Avl_height t1 (1+h) ->
        Avl_height t2 h ->
        Avl_height t3 (1+h) ->
        Avl_height t4 (1+h) ->
        Rebalanced_right
          (node a bal
                t1
                (node c B.left
                      (node b B.right t2 t3)
                      t4))
          (node b B.balanced
             (node a B.left t1 t2)
             (node c B.balanced t3 t4)).

End Make.




Module Make2 (S:SORTABLE).
  Import Relation.

(** * Sortable *)
(*    ======== *)
  Module S1 := Sortable_plus S.
  Section sortable.

    Definition A:Set :=  S1.T.

    Definition dichotomic := S1.dichotomic.
    Definition transitive := S1.transitive.
    Definition reflexive  := S1.reflexive.

  End sortable.
  Notation "a <= b"  := (S.Less_equal a b) (at level 70).
  Notation "a <=? b" := (S.is_less_equal a b) (at level 70).
  Notation "( 'transitivity_chain:' x , y , .. , z )" :=
    (transitive .. (transitive x y) .. z) (at level 0).


  Definition Equivalent (a b:A): Prop := a <= b /\ b <= a.



(** * List *)
(*    ==== *)
  Module List.
    Definition L: Set := list A.

    Inductive Permutation: L -> L -> Prop :=
    | perm_empty:
        Permutation [] []
    | perm_prefix:
        forall x a b, Permutation a b -> Permutation (x::a) (x::b)
    | perm_swap:
        forall x y a,  Permutation (x::y::a) (y::x::a)
    | perm_transitive:
        forall a b c,  Permutation a b -> Permutation b c -> Permutation a c.
  End List.



(** * Basic Definitions *)
(*    ================= *)
  Section basic_definitions.
    Inductive Balance: Set :=
      balanced: Balance
    | left_leaning: Balance.

    Inductive T :=
      empty: T
    | node:  Balance -> A -> T -> T -> T.

    Fixpoint height (t:T): nat :=
      match t with
      | empty => 0
      | node _ _ t1 t2 => 1 + max (height t1) (height t2)
      end.

    Definition Node (t:T): Prop :=
      match t with
      | empty => False
      | node _ _ _ _ => True
      end.

    Inductive Domain: T -> A -> Prop :=
    | domain_node:
        forall x b a t1 t2,
          x = a -> Domain (node b a t1 t2) x
    | domain_left:
        forall x a b t1 t2,
          Domain t1 x -> Domain (node b a t1 t2) x
    | domain_right:
        forall x a b t1 t2,
          Domain t2 x -> Domain (node b a t1 t2) x.


    Theorem node_not_empty:
      forall (b:Balance) (a:A) (t1 t2: T),
        node b a t1 t2 <> empty.
    Proof
      fun b a t1 t2 p =>
        Equal.rewrite p Node I.

    Definition is_node (t:T): {Node t} + {~ Node t} :=
      match t return {Node t} + {~ Node t} with
        empty => right (fun p:False => match p with end)
      | node b a t1 t2 => left I
      end.

    Definition element (t:T): Node t -> A :=
      match t return Node t -> A with
      | empty => fun p:Node empty => match p with end
      | node _ a _ _ => fun _ => a
      end.

    Definition left_son (t:T): Node t -> T :=
      match t return Node t -> T with
      | empty => fun p:Node empty => match p with end
      | node _ _ t1 _ => fun _ => t1
      end.

    Definition right_son (t:T): Node t -> T :=
      match t return Node t -> T with
      | empty => fun p:Node empty => match p with end
      | node _ _ _ t2 => fun _ => t2
      end.


    Definition balance (t:T): Balance :=
      match t with
      | empty => balanced
      | node b _ _ _ => b
      end.

    Fixpoint least (t:T): Node t -> A :=
      match t return Node t -> A with
      | empty =>
        fun p => match p with end
      | node b a t1 t2 =>
        match is_node t1 with
          left  pt1 => fun _ => least t1 pt1
        | right pt1 => fun _ => a
        end
      end.

    Fixpoint greatest (t:T): Node t -> A :=
      match t return Node t -> A with
      | empty =>
        fun p => match p with end
      | node b a t1 t2 =>
        match is_node t2 with
          left  pt2 => fun _ => greatest t2 pt2
        | right pt2 => fun _ => a
        end
      end.
  End basic_definitions.


(** * Module 'Node' Describing the Content of a Node *)
(*    ============================================== *)
  Module Node.
    Import Equal.Notations.
    Record N := make { balance:Balance; element:A; left:T; right:T}.

    Definition Tree_node (n:N) (t:T): Prop :=
      t = node n.(balance) n.(element) n.(left) n.(right).

    Definition tree_node (t:T): Node t -> {n:N | Tree_node n t} :=
      match t return Node t -> {n | Tree_node n t} with
      | empty =>
        fun p => match p with end
      | node b a t1 t2 =>
        fun _ =>
          let n := make b a t1 t2 in
          let p: Tree_node n (node b a t1 t2) :=
              (equal_arguments: eq_refl, eq_refl, eq_refl, eq_refl)
          in
          exist _ n p
      end.
  End Node.


(** * Balanced Trees *)
(*    ============== *)
  Section balanced.
    Inductive Balanced: nat -> Balance -> T -> Prop :=
      balanced_empty:
        Balanced 0 balanced empty
    | balanced_perfect:
        forall h b1 t1 b2 t2 h_new a,
          h_new = 1 + h ->
          Balanced h b1 t1 ->
          Balanced h b2 t2 ->
          Balanced h_new balanced (node balanced a t1 t2)
    | balanced_left_leaning:
        forall h1 b1 t1 h2 b2 t2 h_new a,
          h1 = 1 + h2 ->
          h_new = 2 + h2 ->
          Balanced h1 b1 t1 ->
          Balanced h2 b2 t2 ->
          Balanced h_new left_leaning (node left_leaning a t1 t2).

    Definition Balanced_tree (t:T): Prop :=
      Balanced (height t) (balance t) t.


    Inductive Balanced2: nat -> T -> Prop :=
    | bal_empty: Balanced2 0 empty
    | bal_equal: forall h t1 t2 a,
        Balanced2 h t1 ->
        Balanced2 h t2 ->
        Balanced2 (1+h) (node balanced a t1 t2)
    | bal_left: forall h t1 t2 a,
        Balanced2 (1+h) t1 ->
        Balanced2 h t2 ->
        Balanced2 (2+h) (node left_leaning a t1 t2).


    Theorem height_consistent2:
      forall (h:nat) (t:T), Balanced2 h t -> h = height t.
    Proof
      fix f h t p {struct p}: h = height t :=
      (* height (node _ _ t1 t2) = 1 + max (height t1) (height t2)
       *)
      match p in Balanced2 h t return h = height t with
      | bal_empty =>
        eq_refl
      | @bal_equal h t1 t2 a bal1 bal2 =>
        (equality_chain:
           (eq_refl: 1 + h = _)
           ,
           (let p : max h h = h := max_l h h (le_n h) in
            Equal.inject (Equal.flip p) (fun x => 1 + x)
            : _ = 1 + max h h)
           ,
           (let ht1: h = height t1 := f h t1 bal1 in
            Equal.inject ht1 (fun x => 1 + max x h)
            : _ = 1 + max (height t1) h)
           ,
           (let ht2: h = height t2 := f h t2 bal2 in
            Equal.inject ht2 (fun x => 1 + max (height t1) x)
            : _ = 1 + max (height t1) (height t2))
           ,
           (eq_refl: _ = height (node balanced a t1 t2))
        )
      | @bal_left h t1 t2 a bal1 bal2 =>
        (equality_chain:
           (eq_refl: 2 + h = _)
           ,
           (let p: max (1+h) h = 1 + h := max_l (1+h) h (le_S _ h (le_n h)) in
            Equal.inject (Equal.flip p) (fun x => 1 + x)
            : _ = 1 + max (1+h) h)
           ,
           (let ht1: 1 + h = height t1 := f (1+h) t1 bal1 in
            Equal.inject ht1 (fun x => 1 + max x h)
            : _ = 1 + max (height t1) h)
           ,
           (let ht2: h = height t2 := f h t2 bal2 in
            Equal.inject ht2 (fun x => 1 + max (height t1) x)
            : _ = 1 + max (height t1) (height t2))
           ,
           (eq_refl: _ = height (node left_leaning a t1 t2))
        )
      end.


    Theorem height_consistent:
      forall (h:nat) (b:Balance) (t:T), Balanced h b t -> h = height t.
    Proof.
      refine(
      fix f h b t p {struct p}: h = height t  :=
        match p in Balanced h b t return h = height t with
        | balanced_empty => eq_refl
        | @balanced_perfect h b1 t1 b2 t2 h_new a ph p1 p2 =>
          let pht1: h = height t1 := f h b1 t1 p1 in
          let pht2: h = height t2 := f h b2 t2 p2 in
          _
        | @balanced_left_leaning h1 b1 t1 h2 b2 t2 h_new a ph1 ph_new p1 p2 =>
          let pht1: h1 = height t1 := f h1 b1 t1 p1 in
          let pht2: h2 = height t2 := f h2 b2 t2 p2 in
          _
        end).
      - simpl. rewrite <- pht1. rewrite <- pht2.
        rewrite max_l. assumption. apply le_n.
      - simpl. rewrite <- pht1. rewrite <- pht2.
        rewrite max_l. rewrite ph_new. rewrite ph1. reflexivity.
        rewrite ph1. apply le_S. apply le_n.
    Qed.

    Theorem balanced_is_balanced_tree:
      forall (h:nat) (b:Balance) (t:T),
        Balanced h b t ->
        Balanced_tree t.
    Proof.
      refine (
          fix f h b t pbal :=
            match pbal in Balanced h b t return Balanced_tree t with
            | balanced_empty =>
              balanced_empty
            | @balanced_perfect
                h b1 t1 b2 t2 h_new a
                ph pbal1 pbal2 =>
              let ph1: h = height t1 := @height_consistent h b1 t1 pbal1 in
              let ph2: h = height t2 := @height_consistent h b2 t2 pbal2 in
              _
            | @balanced_left_leaning
                h1 b1 t1 h b2 t2 h_new a
                ph1 phnew pbal1 pbal2 =>
              let pht1: h1 = height t1 := @height_consistent h1 b1 t1 pbal1 in
              let pht2: h  = height t2 := @height_consistent h  b2 t2 pbal2 in
              _
            end).
      - unfold Balanced_tree. simpl. rewrite <- ph1. rewrite <- ph2. rewrite max_l.
        apply balanced_perfect with (h:=h)(b1:=b1)(b2:=b2).
        reflexivity. assumption. assumption. apply le_n.
      - unfold Balanced_tree.  simpl. rewrite <- pht1. rewrite <- pht2.
        rewrite max_l.
        apply balanced_left_leaning with (h1:=h1) (b1:=b1) (h2:=h) (b2:=b2).
        assumption. rewrite ph1. reflexivity. assumption. assumption.
        rewrite ph1. apply le_S. apply le_n.
    Qed.

    Theorem balanced_subtree:
      forall (b:Balance) (h:nat) (t:T),
        Balanced h b t ->
        forall p:Node t,
          Balanced_tree (left_son t p) /\
          Balanced_tree (right_son t p).
    Proof
      fun b h t pbal =>
        match pbal in Balanced h b t
              return
              forall p:Node t,
                Balanced_tree (left_son t p) /\
                Balanced_tree (right_son t p)
        with
        | balanced_empty =>
          fun pnode => match pnode with end
        | @balanced_perfect h b1 t1 b2 t2 h_new a ph pbal1 pbal2 =>
          fun pnode =>
            let lson := left_son  (node balanced a t1 t2) pnode in
            let rson := right_son (node balanced a t1 t2) pnode in
            let peq1 : t1 = lson := eq_refl in
            let peq2 : t2 = rson := eq_refl in
            let pbal_left: Balanced h b1 lson :=
                Equal.rewrite peq1 (Balanced h b1) pbal1 in
            let pbal_right: Balanced h b2 rson :=
                Equal.rewrite peq2 (Balanced h b2) pbal2 in
            conj
              (@balanced_is_balanced_tree h b1 lson pbal_left)
              (@balanced_is_balanced_tree h b2 rson pbal_right)
        | @balanced_left_leaning h1 b1 t1 h b2 t2 h_new a ph1 phnew pbal1 pbal2 =>
          fun pnode =>
            let lson := left_son  (node left_leaning a t1 t2) pnode in
            let rson := right_son (node left_leaning a t1 t2) pnode in
            let peq1 : t1 = lson := eq_refl in
            let peq2 : t2 = rson := eq_refl in
            let pbal_left: Balanced h1 b1 lson :=
                Equal.rewrite peq1 (Balanced h1 b1) pbal1 in
            let pbal_right: Balanced h b2 rson :=
                Equal.rewrite peq2 (Balanced h b2) pbal2 in
            conj
              (@balanced_is_balanced_tree h1 b1 lson pbal_left)
              (@balanced_is_balanced_tree h  b2 rson pbal_right)
        end.
  End balanced.



(** * Sorted Trees *)
(*    ============ *)
  Section sorted.
    Inductive Sorted: A -> A -> T -> Prop :=
      empty_sorted:
        forall lo hi, lo <= hi -> Sorted lo hi empty
    | node_sorted:
        forall lo1 hi1 t1 lo2 hi2 t2 b a,
          Sorted lo1 hi1 t1 ->
          Sorted lo2 hi2 t2 ->
          hi1 <= a ->
          a <= lo2 ->
          Sorted lo1 hi2 (node b a t1 t2).

    Theorem bounds_sorted:
      forall (lo hi:A) (t:T),
        Sorted lo hi t -> lo <= hi.
    Proof
      fix f lo hi t s :=
      match s in Sorted lo hi t return lo <= hi with
      | @empty_sorted lo hi p => p
      | @node_sorted lo1 hi1 t1 lo2 hi2 t2 b a s1 s2 le1 le2 =>
        let p1: lo1 <= hi1 := f lo1 hi1 t1 s1 in
        let p2: lo2 <= hi2 := f lo2 hi2 t2 s2 in
        (transitivity_chain: p1, le1, le2, p2)
      end.

    Theorem bounds_extendible:
      forall (lo lo0 hi0 hi:A) (t:T),
        Sorted lo0 hi0 t ->
        lo <= lo0 ->
        hi0 <= hi ->
        Sorted lo hi t.
    Proof
      fix f lo lo0 hi0 hi t s :=
      match s in Sorted lo0 hi0 t
            return lo <= lo0 -> hi0 <= hi -> Sorted lo hi t with
      | @empty_sorted lo0 hi0 p =>
        fun (le1:lo<=lo0) (le2:hi0<=hi) =>
          @empty_sorted
            lo hi
            (transitivity_chain: le1, p, le2)
      | @node_sorted lo1 hi1 t1 lo2 hi2 t2 b a
                     s1 s2 le_hi1_a le_a_lo2 =>
        fun (le1:lo<=lo1) (le2:hi2<=hi) =>
          let p1: Sorted lo hi1 t1 :=
              f lo lo1 hi1 hi1 t1 s1 le1 (reflexive hi1)
          in
          let p2: Sorted lo2 hi t2 :=
              f lo2 lo2 hi2 hi t2 s2 (reflexive lo2) le2
          in
          @node_sorted lo hi1 t1 lo2 hi t2 b a p1 p2 le_hi1_a le_a_lo2
      end.



    Definition Sorted_tree (t:T): Prop :=
      match is_node t with
      | left  p => (* p: Node t *)
        Sorted (least t p) (greatest t p) t
      | right p => (* p: ~ Node t *)
        True
      end.

    Definition Sorted_tree2 (t:T): Prop :=
      exists lo hi, Sorted lo hi t.

    Theorem least_is_infimum:
      forall (lo hi:A) (t:T),
        Sorted lo hi t -> forall nd:Node t, lo <= least t nd.
    Proof
      let Cond lo t nd := lo <= least t nd
      in
      fix f lo hi t sorted :=
      match sorted in Sorted lo hi t
            return forall nd, Cond lo t nd
      with
      | empty_sorted _ =>
        fun nd =>
          match nd with end
      | @node_sorted lo1 hi1 t1
                     lo2 hi2 t2
                     b a
                     s1 s2 le_l_a le_a_r =>
        fun nd =>
          (match
              t1
              return (forall nd, Cond lo1 t1 nd) ->
                     Cond lo1 (node b a t1 t2) nd
           with
           | empty =>
             fun _ =>
               Equal.rewrite
                 (eq_refl : a = least (node b a empty t2) nd)
                 (fun x => lo1 <= x)
                 ((transitivity_chain: bounds_sorted s1, le_l_a): lo1 <= a)
           | node b1 a1 t11 t12 =>
             let t_ := node b1 a1 t11 t12 in
             fun p1: forall nd1, Cond lo1 t_ nd1 =>
               p1 I
           end) (f lo1 hi1 t1 s1)
      end.

    Theorem least_is_least:
      forall (lo hi:A) (t:T),
        Sorted lo hi t ->
        forall nd:Node t,
          lo <= least t nd /\ Sorted (least t nd) hi t.
    Proof
      let Cond lo hi t nd :=
          lo <= least t nd /\ Sorted (least t nd) hi t
      in
      fix f lo hi t sorted :=
      match sorted in Sorted lo hi t
            return forall nd, Cond lo hi t nd
      with
      | empty_sorted _ =>
        fun nd =>
          match nd with end
      | @node_sorted lo1 hi1 t1
                     lo2 hi2 t2
                     b a
                     s1 s2 le_hi1_a le_a_lo2 =>
        fun nd =>
          (match
              t1
              return (forall nd, Cond lo1 hi1 t1 nd) ->
                     Cond lo1 hi2 (node b a t1 t2) nd
           with
           | empty =>
             fun p1 =>
               let t_ := node b a empty t2 in
               Equal.rewrite
                 (eq_refl : a = least t_ nd)
                 (fun x => lo1 <= x /\ Sorted x hi2 t_)
                 (conj
                    ((transitivity_chain: bounds_sorted s1, le_hi1_a):lo1 <= a)
                    (@node_sorted
                       a a empty lo2 hi2 t2 b a
                       (empty_sorted (reflexive a))
                       s2
                       (reflexive a)
                       le_a_lo2
                     : Sorted (least t_ nd) hi2 t_)
                 )
           | node b1 a1 t11 t12 =>
             let t_ := node b1 a1 t11 t12 in
             fun p1: forall nd1, Cond lo1 hi1 t_ nd1 =>
               let p11: lo1 <= least t_ I  :=
                   proj1 (p1 I) in
               let p12: Sorted (least t_ I) hi1 t_
                   := proj2 (p1 I) in
               conj
                 p11
                 (@node_sorted
                    (least t_ I) hi1 t_ lo2 hi2 t2 b a
                    p12
                    s2
                    le_hi1_a
                    le_a_lo2
                 )
            end) (f lo1 hi1 t1 s1)
      end.


    Theorem greatest_is_supremum:
      forall (lo hi:A) (t:T),
        Sorted lo hi t -> forall nd:Node t, greatest t nd <= hi.
    Proof
      let Cond hi t := forall nd:Node t, greatest t nd <= hi
      in
      fix f lo hi t sorted :=
      match sorted in Sorted lo hi t
            return Cond hi t
      with
      | empty_sorted _ =>
        fun nd =>
          match nd with end
      | @node_sorted lo1 hi1 t1
                     lo2 hi2 t2
                     b a
                     s1 s2 le_l_a le_a_r =>
        fun nd =>
          (match
              t2
              return (Cond hi2 t2) -> greatest (node b a t1 t2) nd <= hi2
           with
           | empty =>
             fun _ =>
               Equal.rewrite
                 (eq_refl : a = greatest (node b a t1 empty) nd)
                 (fun x => x <= hi2)
                 (* a <= lo2 <= hi2 *)
                 (transitivity_chain: le_a_r, bounds_sorted s2)
           | node b2 a2 t21 t22 =>
             let t := node b2 a2 t21 t22 in
             fun p1: forall nd2,
                 greatest t nd2 <= hi2 =>
               p1 I
           end) (f lo2 hi2 t2 s2)
      end.


    Theorem root_element_sorted:
      forall (t:T) (lo hi:A),
        Sorted lo hi t ->
        forall (nd:Node t),
          lo <= element t nd /\ element t nd <= hi.
    Proof
      (* match sorted:
         a) empty: by contradiction
         b) node:  lo1 <= hi1  (bounds_sorted)
                   hi1 <= a    (Sorted ...)
                   a = element t nd
                   a <= lo2    (Sorted ...)
                   lo2 <= hi2  (bounds_sorted)
       *)
      let Cond lo hi t nd :=
          lo <= element t nd /\ element t nd <= hi
      in
      fun t lo hi sorted =>
        match sorted in Sorted lo hi t
              return forall nd, Cond lo hi t nd
        with
        | empty_sorted _ =>
          fun nd =>
            match nd with end
        | @node_sorted lo1 hi1 t1
                       lo2 hi2 t2
                       b a
                       s1 s2 le_hi1_a le_a_lo2 =>
          (* goal: forall nd: Node (node b a t1 t2),
                      lo1 <= element (node b a t1 t2) nd *)
          fun nd =>
            let eq_a: a = element (node b a t1 t2) nd := eq_refl in
            conj
              (Equal.rewrite
                 eq_a
                 (fun x => lo1 <= x)
                 (transitivity_chain: bounds_sorted s1,le_hi1_a))
              (Equal.rewrite
                 eq_a
                 (fun x => x <= hi2)
                 (transitivity_chain: le_a_lo2, bounds_sorted s2))
        end.

  End sorted.

  Section draft.


    (* Replace a t1 t2: An element of 't1' equivalent to 'a' has been replaced
                        by 'a' resulting in 't2'. *)
    Inductive Replaced: A -> T -> T -> Prop :=
    | replaced_root:
        forall x a b t1 t2,
          Equivalent x a ->
          Replaced x (node b a t1 t2) (node b x t1 t2)
    | replaced_left:
        forall x t1 t2 b a t,
          Replaced x t1 t2 ->
          Replaced x (node b a t1 t) (node b a t2 t)
    | replaced_right:
        forall x t1 t2 b a t,
          Replaced x t1 t2 ->
          Replaced x (node b a t t1) (node b a t t2).

    Definition Avl (t:T): Prop :=
      match is_node t with
      | left  p => Balanced (height t) (balance t) t
                   /\
                   Sorted (least t p) (greatest t p) t
      | right _ => True
      end.

    Fixpoint inorder (t:T): List.L :=
      match t with
        empty => []
      | node b a t1 t2 => inorder t1 ++ a :: inorder t2
      end.

  End draft.
End Make2.
