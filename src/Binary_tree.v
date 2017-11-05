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



  (*====================================*)
  (** * Basic Definitions               *)
  (*====================================*)
  Section basic_definitions.
    Inductive T: Set :=
    | empty: T
    | node:  A -> E -> T -> T -> T.

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

    Definition left_son (t:T): Node t -> T :=
      match t with
      | empty => fun nd => match nd with end
      | node a e t1 t2 => fun _ => t1
      end.

    Definition right_son (t:T): Node t -> T :=
      match t with
      | empty => fun nd => match nd with end
      | node a e t1 t2 => fun _ => t2
      end.

    Definition element (t:T): Node t -> A :=
      match t with
      | empty => fun nd => match nd with end
      | node a e t1 t2 => fun _ => a
      end.

    Definition extra (t:T): Node t -> E :=
      match t with
      | empty => fun nd => match nd with end
      | node a e t1 t2 => fun _ => e
      end.

    Theorem left_son_correct:
      forall (a:A) (e:E) (t1 t2:T),
        t1 = left_son (node a e t1 t2) I.
    Proof
      fun a e t1 t2 => eq_refl.

    Theorem right_son_correct:
      forall (a:A) (e:E) (t1 t2:T),
        t2 = right_son (node a e t1 t2) I.
    Proof
      fun a e t1 t2 => eq_refl.

    Theorem element_correct:
      forall (a:A) (e:E) (t1 t2:T),
        a = element (node a e t1 t2) I.
    Proof
      fun a e t1 t2 => eq_refl.

    Theorem extra_correct:
      forall (a:A) (e:E) (t1 t2:T),
        e = extra (node a e t1 t2) I.
    Proof
      fun a e t1 t2 => eq_refl.

    Theorem node_injective_extra:
      forall (a1 a2:A) (e1 e2:E) (t11 t12 t21 t22:T),
        node a1 e1 t11 t12 = node a2 e2 t21 t22 ->
        e1 = e2.
    Proof
      let f e0 t :=
          match t with
          | empty => e0
          | node a e t1 t2 => e
          end
      in
      fun a1 a2 e1 e2 t11 t12 t21 t22 eq =>
        Equal.inject
          eq
          (f e1).

    Theorem node_injective_element:
      forall (a1 a2:A) (e1 e2:E) (t11 t12 t21 t22:T),
        node a1 e1 t11 t12 = node a2 e2 t21 t22 ->
        a1 = a2.
    Proof
      let f a0 t :=
          match t with
          | empty => a0
          | node a e t1 t2 => a
          end
      in
      fun a1 a2 e1 e2 t11 t12 t21 t22 eq =>
        Equal.inject
          eq
          (f a1).

    Theorem node_injective_left_son:
      forall (a1 a2:A) (e1 e2:E) (t11 t12 t21 t22:T),
        node a1 e1 t11 t12 = node a2 e2 t21 t22 ->
        t11 = t21.
    Proof
      let f t0 t :=
          match t with
          | empty => t0
          | node a e t1 t2 => t1
          end
      in
      fun a1 a2 e1 e2 t11 t12 t21 t22 eq =>
        Equal.inject
          eq
          (f t11).

    Theorem node_injective_right_son:
      forall (a1 a2:A) (e1 e2:E) (t11 t12 t21 t22:T),
        node a1 e1 t11 t12 = node a2 e2 t21 t22 ->
        t12 = t22.
    Proof
      let f t0 t :=
          match t with
          | empty => t0
          | node a e t1 t2 => t2
          end
      in
      fun a1 a2 e1 e2 t11 t12 t21 t22 eq =>
        Equal.inject
          eq
          (f t21).
  End basic_definitions.



  (*====================================*)
  (** * Height                          *)
  (*====================================*)
  Section height.
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

    Theorem height_is_only_height:
      forall (t:T) (h:nat),
        Height t h ->
        h = height t.
    Proof
      fix f t h ph :=
      match ph in Height t h
            return h = height t
      with
      | empty_height => eq_refl
      | node_height a i ph1 ph2 =>
        let p1 := f _ _ ph1 in
        let p2 := f _ _ ph2 in
        (equality_chain:
           (eq_refl: 1 + max _ _ = _ ),
           (Equal.inject p1 (fun x => 1 + max x _ )),
           (Equal.inject p2 (fun x => 1 + max _ x ))
        )
      end.

    Theorem height_is_height:
      forall t:T, Height t (height t).
    Proof
      fix f t :=
      match t return Height t (height t) with
      | empty =>
        empty_height
      | node a i t1 t2 =>
        node_height a i (f t1) (f t2)
      end.

    Theorem height_is_unique:
      forall (t:T) (h1 h2:nat),
        Height t h1 ->
        Height t h2 ->
        h1 = h2.
    Proof
      fix f t h1 h2 p1 p2 :=
      (equality_chain:
         height_is_only_height p1,
         (Equal.flip (height_is_only_height p2))).
  End height.





  (*====================================*)
  (** * Leftmost and Rightmost          *)
  (*====================================*)
  Section leftmost_and_rightmost.
    Inductive Leftmost: T -> A -> Prop :=
    | lm_noleft:
        forall a e t2, Leftmost (node a e empty t2) a
    | lm_left:
        forall x a e t1 t2,
          Leftmost t1 x ->
          Leftmost (node a e t1 t2) x.

    Inductive Rightmost: T -> A -> Prop :=
    | rm_noright:
        forall a e t1, Rightmost (node a e t1 empty) a
    | rm_right:
        forall x a e t1 t2,
          Rightmost t2 x ->
          Rightmost (node a e t1 t2) x.

    Theorem leftmost_is_node:
      forall (t:T) (a:A),
        Leftmost t a -> Node t.
    Proof
      fix f t a lm :=
      match lm in Leftmost t a
            return Node t with
      | lm_noleft _ _ _ => I
      | lm_left _ _ _ _ => I
      end.

    Theorem rightmost_is_node:
      forall (t:T) (a:A),
        Rightmost t a -> Node t.
    Proof
      fix f t a rm :=
      match rm in Rightmost t a
            return Node t with
      | rm_noright _ _ _ => I
      | rm_right _ _ _ _ => I
      end.




    Fixpoint leftmost (t:T): Node t -> A :=
      match t return Node t -> A with
      | empty =>
        fun nd => match nd with end
      | node a e t1 t2 =>
        match is_node t1 with
        | left  nd => fun _ => leftmost t1 (nd:Node t1)
        | right _  => fun _ => a
        end
      end.


    Theorem leftmost_correct:
      forall (t:T) (nd:Node t),
        Leftmost t (leftmost t nd).
    Proof
      let P t nd := Leftmost t (leftmost t nd) in
      fix f t :=
      match t return forall nd, P t nd with
      | empty => fun nd => match nd with end
      | node a e t1 t2 =>
        fun nd =>
          (match t1
                 return (forall nd1, P t1 nd1) -> P (node a e t1 t2) nd
           with
           | empty =>
             fun _ =>
               Equal.rewrite
                 (Equal.flip eq_refl: a = leftmost (node a e empty t2) I)
                 (fun x => Leftmost (node a e empty t2) x)
                 (lm_noleft a e t2)
           | node a1 e1 t11 t12 =>
             let t1_ := node a1 e1 t11 t12 in
             fun p1: forall nd1, P t1_ nd1 =>
               @lm_left (leftmost t1_ I) a e t1_ t2 (p1 I)
           end) (f t1)
      end.



    Fixpoint rightmost (t:T): Node t -> A :=
      match t return Node t -> A with
      | empty =>
        fun nd => match nd with end
      | node a e t1 t2 =>
        match is_node t2 with
        | left  nd => fun _ => rightmost t2 (nd:Node t2)
        | right p  => fun _ => a
        end
      end.

    Theorem rightmost_correct:
      forall (t:T) (nd:Node t),
        Rightmost t (rightmost t nd).
    Proof
      let P t nd := Rightmost t (rightmost t nd) in
      fix f t :=
      match t return forall nd, P t nd with
      | empty => fun nd => match nd with end
      | node a e t1 t2 =>
        fun nd =>
          (match t2
                 return (forall nd2, P t2 nd2) -> P (node a e t1 t2) nd
           with
           | empty =>
             fun _ =>
               Equal.rewrite
                 (Equal.flip eq_refl: a = rightmost (node a e t1 empty) I)
                 (fun x => Rightmost (node a e t1 empty) x)
                 (rm_noright a e t1)
           | node a2 e2 t21 t22 =>
             let t2_ := node a2 e2 t21 t22 in
             fun p2: forall nd2, P t2_ nd2 =>
               @rm_right (rightmost t2_ I) a e t1 t2_ (p2 I)
           end) (f t2)
      end.
  End leftmost_and_rightmost.






  (*====================================*)
  (** * Inorder Sequence                *)
  (*====================================*)
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
      forall t:T, Inorder t (inorder t).
    Proof
      fix f t :=
      match t return Inorder t (inorder t) with
      | empty => empty_inorder
      | node a e t1 t2 =>
        @node_inorder t1 (inorder t1) t2 (inorder t2) a e (f t1) (f t2)
      end.

    Theorem inorder_unique:
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
End Make.
