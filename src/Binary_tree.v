Require Import Core.
Require Import Coq.Lists.List.
Import ListNotations.
Import Equal.Notations.

Set Implicit Arguments.

Module Make (ElementM:ANY) (ExtraM:ANY).

  Definition A := ElementM.T.
  Definition E := ExtraM.T.

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




  Inductive T: Set :=
  | empty: T
  | node:  A -> E -> T -> T -> T.

  Inductive Height: T -> nat -> Prop :=
  | empty_height:
      Height empty 0
  | node_height:
      forall t1 h1 t2 h2 a i,
        Height t1 h1 ->
        Height t2 h2 ->
        Height (node a i t1 t2) (1 + max h1 h2).

  Fixpoint height (t:T): nat :=
    match t with
    | empty => 0
    | node _ _ t1 t2 =>
      1 + max (height t1) (height t2)
    end.

  Theorem height_is_height:
    forall t:T, Height t (height t).
  Proof
    fix f t :=
    match t return Height t (height t) with
    | empty =>
      empty_height
    | node a i t1 t2 =>
      @node_height t1 (height t1) t2 (height t2) a i (f t1) (f t2)
    end.

  Definition Node (t:T): Prop :=
    match t with
    | empty => False
    | node _ _ _ _ => True
    end.

  Theorem node_not_empty:
    forall(a:A) (i:E) (t1 t2: T),
      node a i t1 t2 <> empty.
  Proof
    fun a i t1 t2 p =>
      Equal.rewrite p Node I.

  Definition is_node (t:T): {Node t} + {~ Node t} :=
    match t return {Node t} + {~ Node t} with
      empty => right (fun p:False => match p with end)
    | node _ _ _ _ => left I
    end.

  Inductive Element: T -> A -> Prop :=
  | element_node:
      forall a e t1 t2, Element (node a e t1 t2) a.

  Inductive Extra: T -> E -> Prop :=
  | extra_node:
      forall a e t1 t2, Extra (node a e t1 t2) e.

  Theorem extra_is_node: forall (t:T) (e:E), Extra t e -> Node t.
  Proof
    fun t e extra =>
      match extra in Extra t _ return Node t with
      | extra_node a e t1 t2 => I
      end.

  Inductive Leftmost: T -> A -> Prop :=
  | lm_noleft:
      forall a e t2, Leftmost (node a e empty t2) a
  | lm_left:
      forall x a e t1 t2,
        Leftmost t1 x ->
        Leftmost (node a e t1 t2) x.

  Theorem leftmost_is_node:
    forall (t:T) (a:A),
      Leftmost t a -> Node t.
  Proof
    fix f t a lm :=
    match lm in Leftmost t a
          return Node t with
    | lm_noleft _ _ _ => I
    | lm_left _ _ _ _ => I
    end
  .
  Fixpoint leftmost (t:T): Node t -> A :=
    match t return Node t -> A with
    | empty =>
      fun nd => match nd with end
    | node a e t1 t2 =>
      match is_node t1 with
      | left  nd => fun _ => leftmost t1 (nd:Node t1)
      | right p  => fun _ => a
      end
    end.

  (* Inorder t xs:  'xs' is the inorder sequence of 't'.*)
  Section inorder_sequence.
    Inductive Inorder: T -> list A -> Prop :=
    | empty_inorder: Inorder empty []
    | node_inorder:
        forall t1 xs1 t2 xs2 a e,
          Inorder t1 xs1 ->
          Inorder t2 xs2 ->
          Inorder (node a e t1 t2) (xs1 ++ a :: xs2).

    Fixpoint inorder (t:T): list A :=
      match t with
      | empty => []
      | node a e t1 t2 =>
        inorder t1 ++ a :: inorder t2
      end.

    Theorem inorder_correct:
      forall (t:T) (xs:list A),
        Inorder t xs ->
        xs = inorder t.
    Proof
      fix f t xs ord :=
      match ord in Inorder t xs
            return xs = inorder t with
      | empty_inorder => eq_refl
      | @node_inorder t1 xs1 t2 xs2 a e ord1 ord2 =>
        let eq1: xs1 = inorder t1 := f t1 xs1 ord1 in
        let eq2: xs2 = inorder t2 := f t2 xs2 ord2 in
        (equality_chain:
           (eq_refl: xs1 ++ a :: xs2 = _),
           (Equal.rewrite eq1 (fun xs => _ = xs ++ a :: xs2) eq_refl
            : _ = inorder t1 ++ a :: xs2),
           (Equal.rewrite eq2 (fun xs => _ = inorder t1 ++ a :: xs) eq_refl
            : _ = inorder t1 ++ a :: inorder t2))
      end.
  End inorder_sequence.


  (*
  Theorem leftmost_is_leftmost_new:
    forall (t:T) (a:A),
      Leftmost t a ->
      forall nd:Node t, a = leftmost t nd.
  Proof
    fix f t a lm :=
    match lm in Leftmost t a
          return forall nd, a = leftmost t nd with
    | lm_noleft a e t2 =>
      fun nd => eq_refl
    | @lm_left x a1 e1 t1 t2 lm1 =>
      let nd1 := leftmost_is_node lm1 in
      let eq1: x = leftmost t1 nd1 := f t1 x lm1 nd1 in
      fun nd =>
        let f t1_: forall (nd1:Node t1_), x = leftmost (node a e1 t1_ t2) nd :=
            match t1_ with
            | empty =>
              _
            | node a1 e1 t11 t12 =>
              _
            end
        in
        _
    end.
  *)
  Theorem leftmost_is_leftmost:
    forall (t:T) (nd:Node t),
      Leftmost t (leftmost t nd).
  Proof
    let P t nd :=  Leftmost t (leftmost t nd) in
    fix f t :=
    match t return forall nd, P t nd with
    | empty =>
      fun nd => match nd with end
    | node a e t1 t2 =>
      let t_ := node a e t1 t2 in
      fun nd =>
        (match
            t1
            return (forall nd1, P t1 nd1) -> P (node a e t1 t2) nd
          with
          | empty =>
            let t_ := node a e empty t2 in
            fun _ =>
              Equal.rewrite
                (eq_refl: a = leftmost t_ nd)
                (fun x => Leftmost t_ a)
                (lm_noleft a e t2)
          | node a1 e1 t11 t12 =>
            let t1_ := node a1 e1 t11 t12 in
            fun p1: forall nd1, P t1_ nd1 =>
              let pt1: Leftmost t1_ (leftmost t1_ I) := p1 I in
              @lm_left (leftmost t1_ I) a e t1_ t2 pt1
              : Leftmost (node a e t1_ t2) (leftmost (node a e t1_ t2) nd)
          end) (f t1)
    end.
End Make.


(*
Module Make2 (S:SORTABLE).
  Notation "a <= b"  := (S.Less_equal a b) (at level 70).
  Notation "a <=? b" := (S.is_less_equal a b) (at level 70).
  Section sortable.
    Definition A:Set :=  S.T.

    Theorem transitive: Relation.Transitive S.Less_equal.
    Proof
      match S.is_linear_preorder with
        conj _ tr => tr
      end.

    Theorem reflexive: Relation.Reflexive S.Less_equal.
    Proof
      match S.is_linear_preorder with
        conj d _ =>
        Relation.dichotomic_is_reflexive d
      end.

    Definition Equivalent (a b:A): Prop := a <= b /\ b <= a.
  End sortable.


  Section basic_definitions.
    Inductive T: Set :=
    | empty: T
    | node:  A -> T -> T -> T.

    Inductive Sorted: A -> A -> T -> Prop :=
    | empty_sorted:
        forall lo hi: A,
          lo <= hi ->
          Sorted lo hi empty
    | node_sorted:
        forall lo1 hi1 t1 lo2 hi2 t2 a,
          Sorted lo1 hi1 t1 ->
          Sorted lo1 hi2 t2 ->
          hi1 <= a ->
          a <= lo2 ->
          Sorted lo1 hi2 (node a t1 t2).

    Record Guards :=
      make_guards {low_guard:A; high_guard:A}.

    Definition Sorted_tree (t:T): Prop :=
      exists g:Guards, Sorted g.(low_guard) g.(high_guard) t.
  End basic_definitions.


  Section inorder_sequence.
    Fixpoint inorder (t:T): list A :=
      match t with
      | empty => [ ]
      | node a t1 t2 => inorder t1 ++ a :: inorder t2
      end.

    Definition Same_inorder (t1 t2:T): Prop :=
      inorder t1 = inorder t2.
  End inorder_sequence.




  Section find.

    (* A 'Hole' is a partial node where either the left or the right subtree is
       missing. *)
    Inductive Hole: Set :=
    | left_hole:  A -> T -> Hole
    | right_hole: A -> T -> Hole.

    Definition Path: Set := list Hole.

    Fixpoint tree_of_path (p:list Hole) (t:T): T :=
      match p with
      | nil => t
      | left_hole a r :: holes =>
        tree_of_path holes (node a t r)
      | right_hole a l :: holes =>
        tree_of_path holes (node a l t)
      end.


    Record Focus:Set :=
      make_focus {
          path: list Hole;
          element: A;
          left: T;
          right: T}.

    Definition tree_of_focus (f:Focus): T :=
      tree_of_path f.(path) (node f.(element) f.(left) f.(right)).

    Definition Root_focus (f:Focus) (t:T): Prop :=
      tree_of_focus f = t /\ f.(path) = [].

    Definition Left_child (f g:Focus): Prop :=
      f.(path) = left_hole g.(element) g.(right) :: g.(path)
      /\
      node f.(element) f.(left) f.(right) = g.(left).

    Definition Right_child (f g:Focus): Prop :=
      f.(path) = right_hole g.(element) g.(left) :: g.(path)
      /\
      node f.(element) f.(left) f.(right) = g.(right).

    Definition Child (f g:Focus): Prop :=
      Left_child f g \/ Right_child f g.

    Definition focus_root (t:T): {f:Focus | Root_focus f t}
                                 +
                                 {t = empty} :=
      match t with
      | empty => inright (eq_refl)
      | node a t1 t2 =>
        inleft (exist
                  _
                  (make_focus [] a t1 t2)
                  (conj eq_refl eq_refl))
      end.

    Definition focus_left (f:Focus): {g:Focus| Left_child g f}
                                     +
                                     {f.(left) = empty} :=
      match f with
      | make_focus path a t1 t2 =>
        match t1 with
        | empty => inright eq_refl
        | node b u1 u2 =>
          inleft (exist
                    _
                    (make_focus
                       (left_hole a t2 :: path)
                       b u1 u2)
                    (conj eq_refl eq_refl))
        end
      end.

    Definition focus_right (f:Focus): {g:Focus| Right_child g f}
                                      +
                                      {f.(right) = empty} :=
      match f with
      | make_focus path a t1 t2 =>
        match t2 with
        | empty => inright eq_refl
        | node b u1 u2 =>
          inleft (exist
                    _
                    (make_focus
                       (right_hole a t1 :: path)
                       b u1 u2)
                    (conj eq_refl eq_refl))
        end
      end.




    Inductive Domain: T -> A -> Prop :=
    | domain_node:
        forall x a t1 t2,
          x = a -> Domain (node a t1 t2) x
    | domain_left:
        forall x a t1 t2,
          Domain t1 x -> Domain (node a t1 t2) x
    | domain_right:
        forall x a t1 t2,
          Domain t2 x -> Domain (node a t1 t2) x.

    Definition Found (a:A) (t:T): Set :=
      {f:Focus | t = tree_of_focus f /\
                 Equivalent a f.(element)}.

    Definition Not_found (a:A) (t:T): Set :=
      {p:Path  | t = tree_of_path p empty /\
                 forall x, Domain t x -> ~ Equivalent a x}.

    Definition Search_result (a:A) (t:T): Set :=
      Either.T (Found a t) (Not_found a t).

    Definition
      search (a:A) (t:T): Sorted_tree t -> Search_result a t :=
      _.

  End find.


End Make2.*)