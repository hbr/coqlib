Require Import Core.
Require Import Coq.Lists.List.
Import ListNotations.
Import Equal.Notations.
       
Set Implicit Arguments.

Module Make (S:SORTABLE).
  Import Relation.

(** * Sortable *)
(*    ======== *)
  Section sortable.
    Definition A:Set :=  S.T.

    Theorem transitive: Transitive S.Less_equal.
    Proof
      match S.is_linear_preorder with
        conj _ tr => tr
      end.

    Theorem reflexive: Reflexive S.Less_equal.
    Proof
      match S.is_linear_preorder with
        conj d _ =>
        dichotomic_is_reflexive d
      end.

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

    Print balance.
    Print N.
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
        Search (max _ _).
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

    Theorem guards_consistent:
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
    
    Definition Sorted_tree (t:T): Prop :=
      match is_node t with
      | left  p => (* p: Node t *)
        Sorted (least t p) (greatest t p) t
      | right p => (* p: ~ Node t *)
        True
      end.

    Definition Sorted_tree2 (t:T): Prop :=
      exists lo hi, Sorted lo hi t.
    
    Theorem least_consistent:
      forall (lo hi:A) (t:T),
        Sorted lo hi t -> forall nd:Node t, lo <= least t nd.
    Proof
      let Cond lo t := forall nd:Node t, lo <= least t nd
      in
      fix f lo hi t sorted :=
      match sorted in Sorted lo hi t
            return Cond lo t
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
              return (Cond lo1 t1) -> lo1 <= least (node b a t1 t2) nd
           with
           | empty =>
             fun _ =>
               Equal.rewrite
                 (eq_refl : a = least (node b a empty t2) nd)
                 (fun x => lo1 <= x)
                 (* lo1 <= hi1 <= a *)
                 (transitivity_chain: guards_consistent s1, le_l_a)
           | node b1 a1 t11 t12 =>
             let t := node b1 a1 t11 t12 in
             fun p1: forall nd1,
                 lo1 <= least t nd1 =>
               Equal.rewrite
                 (eq_refl (least t I))
                 (fun x => lo1 <= least t I)
                 (p1 I)
           end) (f lo1 hi1 t1 s1)
      end.


    Theorem greatest_consistent:
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
                 (transitivity_chain: le_a_r, guards_consistent s2)
           | node b2 a2 t21 t22 =>
             let t := node b2 a2 t21 t22 in
             fun p1: forall nd2,
                 greatest t nd2 <= hi2 =>
               Equal.rewrite
                 (eq_refl (greatest t I))
                 (fun x => greatest t I <= hi2)
                 (p1 I)
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
         b) node:  lo1 <= hi1  (guards_consistent)
                   hi1 <= a    (Sorted ...)
                   a = element t nd
                   a <= lo2    (Sorted ...)
                   lo2 <= hi2  (guards_consistent)
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
                 (transitivity_chain: guards_consistent s1,le_hi1_a))
              (Equal.rewrite
                 eq_a
                 (fun x => x <= hi2)
                 (transitivity_chain: le_a_lo2, guards_consistent s2))
        end.


    Theorem least_greatest_consistent:
      forall (lo hi:A) (t:T),
        Sorted lo hi t ->
        forall nd:Node t, Sorted (least t nd) (greatest t nd) t.
    Proof
      let Cond t nd: Prop := Sorted (least t nd) (greatest t nd) t
      in
      fun lo hi t sorted =>
        match sorted in Sorted lo hi t
              return forall nd, Cond t nd
        with
        | empty_sorted _ =>
          fun nd =>
            match nd with end
        | @node_sorted lo1 hi1 t1
                       lo2 hi2 t2
                       b a
                       s1 s2 le_hi1_a le_a_lo2 =>
          _
        end.
    Print ex.

    Theorem sorted_is_sorted:
      forall (t:T),
        Sorted_tree2 t ->
        forall  (nd:Node t),
          Sorted (least t nd) (greatest t nd) t.
    Proof
      let Cond t nd := Sorted (least t nd) (greatest t nd) t
      in
      fun t exist_lo_hi =>
        match exist_lo_hi with
        | ex_intro _ lo exist_hi =>
          match exist_hi with
            ex_intro _ hi sorted =>
            match sorted in Sorted lo hi t
                  return forall nd, Cond t nd
            with
            | empty_sorted _ =>
              fun nd => match nd with end
            | @node_sorted lo1 hi1 t1
                           lo2 hi2 t2
                           b a
                           s1 s2 le_hi1_a le_a_lo2 =>
              fun nd =>
                let t_ := node b a t1 t2 in
                (* goal: Sorted (least t_ nd) (greatest t_ nd) t_
                 *)
                _
            end           
          end
        end.
  End sorted.

    
  Section blabla.
    Inductive Permutation: T -> T -> Prop :=
    | perm_empty:
        Permutation empty empty
    | perm_left:
        forall b1 b2 a1 a2 t1 t2 t3,
          Permutation
            (node b1 a1 (node b2 a2 t1 t2) t3)
            (node b1 a2 (node b2 a1 t1 t2) t3)
    | perm_right:
        forall b1 b2 a1 a2 t1 t2 t3,
          Permutation
            (node b1 a1 t1 (node b2 a2 t2 t3))
            (node b1 a2 t1 (node b2 a1 t2 t3))
    | perm_root:
        forall t u v w a b,
          Permutation t u ->
          Permutation v w ->
          Permutation (node b a t v) (node b a u w)
    | perm_transitive:
        forall t1 t2 t3,
          Permutation t1 t2 -> Permutation t2 t3 -> Permutation t1 t3.


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
          Replaced x (node b a t t1) (node b a t t2)
    .

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

  End blabla.

  Theorem avl_subtree:
    forall (a:A) (b:Balance) (t1 t2:T),
      Avl (node b a t1 t2) -> Avl t1 /\ Avl t2.
  Proof.
    intros a b t1 t2 pavl. unfold Avl in pavl. unfold is_node in pavl.
    destruct pavl as [pbal psorted].
    split.
    - unfold Avl.
    -
    fun a b t1 t2 pavl =>
      match pavl with
        left p => _
                    right

      _.

  Definition add_root (a:A) (t:T): T :=
    node left_leaning a t empty.


  Definition Inserted (x:A) (t u:T): Prop :=
    List.Permutation (x :: inorder t) (inorder u).

  Definition Avl_inserted (x:A) (t u:T): Prop :=
    Avl u /\ Inserted x t u.
  Check Inserted.


  Theorem insert_empty:
    forall x:A,
      Avl_inserted x empty (node balanced x empty empty).
  Proof.
    intro x. split.
    - unfold Avl. unfold is_node. split.
      -- simpl. eapply balanced_perfect; apply balanced_empty.
      -- simpl. apply node_sorted with (hi1:=x) (lo2:=x);
                  repeat (apply empty_sorted); repeat (apply reflexive).
    - unfold Inserted. simpl. apply List.perm_prefix. apply List.perm_empty.
  Qed.

  Section insertion.
    Definition insert:
      forall (a:A) (t:T),
        Avl t ->
        Either.T {u:T | Avl_inserted a t u} {u:T | Replaced a t u}
      :=
      fix f x t :=
        match t
              return Avl t -> Either.T {u| Avl_inserted x t u} {u| Replaced x t u}
        with
        | empty =>
          fun _ =>
            let u := node balanced x empty empty in
            Either.left _ (exist _ u (insert_empty x))
        | node bal a t1 t2 =>
          fun pavl_t =>
            match x <=? a, a <=? x with
            | left p1, left p2  =>
              (* x and a are equivalent, replace *)
              let u := node bal x t1 t2 in
              let p_replace: Replaced x (node bal a t1 t2) u :=
                  @replaced_root x a bal t1 t2 (conj p1 p2)
              in
              Either.right _ (exist _ u p_replace)
            | left p1, _  =>
              (* insert into left subtree *)
              let pavl_t1: Avl t1 := _ in
              match f x t1 pavl_t1 with
              | Either.left _ sig_ins_t1 =>
                _
              | Either.right _ sig_repl_t1 =>
                _
              end
            | right p1, _  =>
              (* insert into right subtree *)
              _
            end
        end.
  End insertion.



  Section draft.
    Inductive Avl2: A -> A -> nat -> Balance -> T -> Prop :=
      avl_empty:
        forall lo hi, lo <= hi -> Avl2 lo hi 0 balanced empty
    | avl_balanced:
        forall lo1 hi1 b1 t1 lo2 hi2 b2 t2 h a,
          Avl2 lo1 hi1 h b1 t1 ->
          Avl2 lo2 hi2 h b2 t2 ->
          hi1 <= a ->
          a <= lo2 ->
          Avl2 lo1 hi2 (1+h) balanced (node balanced a t1 t2)
    | avl_left_leaning:
        forall lo1 hi1 b1 t1 lo2 hi2 b2 t2 h a,
          Avl2 lo1 hi1 (1+h) b1 t1 ->
          Avl2 lo2 hi2 h b2 t2 ->
          hi1 <= a ->
          a <= lo2 ->
          Avl2 lo1 hi2 (2+h) left_leaning (node left_leaning a t1 t2).

    Theorem extend_guards:
      forall (lo_new lo hi hi_new:A) (h:nat) (b:Balance) (t:T),
        Avl2 lo hi h b t ->
        lo_new <= lo ->
        hi <= hi_new ->
        Avl2 lo_new hi_new h b t.
    Proof
      fix f lo_new lo hi hi_new h b t p_avl:=
      match
          p_avl in Avl2 lo hi h b t
          return lo_new <= lo -> hi <= hi_new -> Avl2 lo_new hi_new h b t
      with
        @avl_empty lo hi p => (* p: lo <= hi *)
        fun (p1:lo_new<=lo) (p2:hi<=hi_new) =>
          let pguard: lo_new <= hi_new :=
              transitive (transitive p1 p) p2
          in
          @avl_empty lo_new hi_new pguard
      | @avl_balanced
          lo1 hi1 b1 t1
          lo2 hi2 b2 t2 h a
          p_avl_t1 p_avl_t2 pleft pright =>
        fun (p1:lo_new<=lo1) (p2:hi2<=hi_new) =>
          let p_avl_t1_new :=
              f lo_new lo1 hi1 hi1 h b1 t1 p_avl_t1 p1 (reflexive hi1) in
          let p_avl_t2_new :=
              f lo2 lo2 hi2 hi_new h b2 t2 p_avl_t2 (reflexive lo2) p2 in
          avl_balanced p_avl_t1_new p_avl_t2_new pleft pright
      | @avl_left_leaning
          lo1 hi1 b1 t1
          lo2 hi2 b2 t2
          h a
          p_avl_t1 p_avl_t2 pleft pright =>
        fun (p1:lo_new<=lo1) (p2:hi2<=hi_new) =>
          let p_avl_t1_new :=
              f lo_new lo1 hi1 hi1 (1+h) b1 t1 p_avl_t1 p1 (reflexive hi1) in
          let p_avl_t2_new :=
              f lo2 lo2 hi2 hi_new h b2 t2 p_avl_t2 (reflexive lo2) p2 in
          avl_left_leaning p_avl_t1_new p_avl_t2_new pleft pright
      end
    .
  End draft.
End Make.
