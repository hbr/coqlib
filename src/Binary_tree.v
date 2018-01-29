Require Import Core.
Require Import Coq.Lists.List.
Import ListNotations.
Import Equal.Notations.

Set Implicit Arguments.

Module Make (ElementM:ANY) (ExtraM:ANY).

  Module A := ElementM.
  Module E := ExtraM.


(** * List *)
(*    ==== *)
  Module List.
    Definition L: Set := list A.t.

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
    Inductive t: Set :=
    | Empty: t
    | Node:  A.t -> E.t -> t -> t -> t.

    Definition is_Node (t_:t): Prop :=
      match t_ with
      | Empty => False
      | Node _ _ _ _ => True
      end.

    Theorem node_not_empty:
      forall(a:A.t) (i:E.t) (t1 t2: t),
        Node a i t1 t2 <> Empty.
    Proof
      fun a i t1 t2 p =>
        Equal.rewrite p is_Node I.

    Definition is_node (t_:t): {is_Node t_} + {~ is_Node t_} :=
      match t_ return {is_Node t_} + {~ is_Node t_} with
        Empty => right (fun p:False => match p with end)
      | Node _ _ _ _ => left I
      end.

    Inductive Element: t -> A.t -> Prop :=
    | element_node:
        forall a e t1 t2, Element (Node a e t1 t2) a.

    Inductive Extra: t -> E.t -> Prop :=
    | extra_node:
        forall a e t1 t2, Extra (Node a e t1 t2) e.

    Theorem extra_is_node: forall (t_:t) (e:E.t), Extra t_ e -> is_Node t_.
    Proof
      fun t e extra =>
        match extra in Extra t _ return is_Node t with
        | extra_node a e t1 t2 => I
        end.

    Definition left_son (t_:t): is_Node t_ -> t :=
      match t_ with
      | Empty => fun nd => match nd with end
      | Node a e t1 t2 => fun _ => t1
      end.

    Definition right_son (t_:t): is_Node t_ -> t :=
      match t_ with
      | Empty => fun nd => match nd with end
      | Node a e t1 t2 => fun _ => t2
      end.

    Definition element (t_:t): is_Node t_ -> A.t :=
      match t_ with
      | Empty => fun nd => match nd with end
      | Node a e t1 t2 => fun _ => a
      end.

    Definition extra (t_:t): is_Node t_ -> E.t :=
      match t_ with
      | Empty => fun nd => match nd with end
      | Node a e t1 t2 => fun _ => e
      end.

    Theorem left_son_correct:
      forall (a:A.t) (e:E.t) (t1 t2:t),
        t1 = left_son (Node a e t1 t2) I.
    Proof
      fun a e t1 t2 => eq_refl.

    Theorem right_son_correct:
      forall (a:A.t) (e:E.t) (t1 t2:t),
        t2 = right_son (Node a e t1 t2) I.
    Proof
      fun a e t1 t2 => eq_refl.

    Theorem element_correct:
      forall (a:A.t) (e:E.t) (t1 t2:t),
        a = element (Node a e t1 t2) I.
    Proof
      fun a e t1 t2 => eq_refl.

    Theorem extra_correct:
      forall (a:A.t) (e:E.t) (t1 t2:t),
        e = extra (Node a e t1 t2) I.
    Proof
      fun a e t1 t2 => eq_refl.

    Theorem node_injective_extra:
      forall (a1 a2:A.t) (e1 e2:E.t) (t11 t12 t21 t22:t),
        Node a1 e1 t11 t12 = Node a2 e2 t21 t22 ->
        e1 = e2.
    Proof
      let f e0 t :=
          match t with
          | Empty => e0
          | Node a e t1 t2 => e
          end
      in
      fun a1 a2 e1 e2 t11 t12 t21 t22 eq =>
        Equal.inject
          eq
          (f e1).

    Theorem node_injective_element:
      forall (a1 a2:A.t) (e1 e2:E.t) (t11 t12 t21 t22:t),
        Node a1 e1 t11 t12 = Node a2 e2 t21 t22 ->
        a1 = a2.
    Proof
      let f a0 t :=
          match t with
          | Empty => a0
          | Node a e t1 t2 => a
          end
      in
      fun a1 a2 e1 e2 t11 t12 t21 t22 eq =>
        Equal.inject
          eq
          (f a1).

    Theorem node_injective_left_son:
      forall (a1 a2:A.t) (e1 e2:E.t) (t11 t12 t21 t22:t),
        Node a1 e1 t11 t12 = Node a2 e2 t21 t22 ->
        t11 = t21.
    Proof
      let f t0 t :=
          match t with
          | Empty => t0
          | Node a e t1 t2 => t1
          end
      in
      fun a1 a2 e1 e2 t11 t12 t21 t22 eq =>
        Equal.inject
          eq
          (f t11).

    Theorem node_injective_right_son:
      forall (a1 a2:A.t) (e1 e2:E.t) (t11 t12 t21 t22:t),
        Node a1 e1 t11 t12 = Node a2 e2 t21 t22 ->
        t12 = t22.
    Proof
      let f t0 t :=
          match t with
          | Empty => t0
          | Node a e t1 t2 => t2
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
    Inductive Height: t -> nat -> Prop :=
    | empty_height:
        Height Empty 0
    | node_height:
        forall t1 h1 t2 h2 a i,
          Height t1 h1 ->
          Height t2 h2 ->
          Height (Node a i t1 t2) (1 + max h1 h2).

    Fixpoint height (t_:t): nat :=
      match t_ with
      | Empty => 0
      | Node _ _ t1 t2 =>
        1 + max (height t1) (height t2)
      end.

    Theorem height_is_only_height:
      forall (t_:t) (h:nat),
        Height t_ h ->
        h = height t_.
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
      forall t_:t, Height t_ (height t_).
    Proof
      fix f t :=
      match t return Height t (height t) with
      | Empty =>
        empty_height
      | Node a i t1 t2 =>
        node_height a i (f t1) (f t2)
      end.

    Theorem height_is_unique:
      forall (t_:t) (h1 h2:nat),
        Height t_ h1 ->
        Height t_ h2 ->
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
    Inductive Leftmost: t -> A.t -> Prop :=
    | lm_noleft:
        forall a e t2, Leftmost (Node a e Empty t2) a
    | lm_left:
        forall x a e t1 t2,
          Leftmost t1 x ->
          Leftmost (Node a e t1 t2) x.

    Inductive Rightmost: t -> A.t -> Prop :=
    | rm_noright:
        forall a e t1, Rightmost (Node a e t1 Empty) a
    | rm_right:
        forall x a e t1 t2,
          Rightmost t2 x ->
          Rightmost (Node a e t1 t2) x.

    Theorem leftmost_is_node:
      forall (t_:t) (a:A.t),
        Leftmost t_ a -> is_Node t_.
    Proof
      fix f t a lm :=
      match lm in Leftmost t a
            return is_Node t with
      | lm_noleft _ _ _ => I
      | lm_left _ _ _ _ => I
      end.

    Theorem rightmost_is_node:
      forall (t_:t) (a:A.t),
        Rightmost t_ a -> is_Node t_.
    Proof
      fix f t a rm :=
      match rm in Rightmost t a
            return is_Node t with
      | rm_noright _ _ _ => I
      | rm_right _ _ _ _ => I
      end.




    Fixpoint leftmost (t_:t): is_Node t_ -> A.t :=
      match t_ return is_Node t_ -> A.t with
      | Empty =>
        fun nd => match nd with end
      | Node a e t1 t2 =>
        match is_node t1 with
        | left  nd => fun _ => leftmost t1 (nd:is_Node t1)
        | right _  => fun _ => a
        end
      end.


    Theorem leftmost_correct:
      forall (t_:t) (nd:is_Node t_),
        Leftmost t_ (leftmost t_ nd).
    Proof
      let P t nd := Leftmost t (leftmost t nd) in
      fix f t :=
      match t return forall nd, P t nd with
      | Empty => fun nd => match nd with end
      | Node a e t1 t2 =>
        fun nd =>
          (match t1
                 return (forall nd1, P t1 nd1) -> P (Node a e t1 t2) nd
           with
           | Empty =>
             fun _ =>
               Equal.rewrite
                 (Equal.flip eq_refl: a = leftmost (Node a e Empty t2) I)
                 (fun x => Leftmost (Node a e Empty t2) x)
                 (lm_noleft a e t2)
           | Node a1 e1 t11 t12 =>
             let t1_ := Node a1 e1 t11 t12 in
             fun p1: forall nd1, P t1_ nd1 =>
               @lm_left (leftmost t1_ I) a e t1_ t2 (p1 I)
           end) (f t1)
      end.



    Fixpoint rightmost (t_:t): is_Node t_ -> A.t :=
      match t_ return is_Node t_ -> A.t with
      | Empty =>
        fun nd => match nd with end
      | Node a e t1 t2 =>
        match is_node t2 with
        | left  nd => fun _ => rightmost t2 (nd:is_Node t2)
        | right p  => fun _ => a
        end
      end.

    Theorem rightmost_correct:
      forall (t_:t) (nd:is_Node t_),
        Rightmost t_ (rightmost t_ nd).
    Proof
      let P t nd := Rightmost t (rightmost t nd) in
      fix f t :=
      match t return forall nd, P t nd with
      | Empty => fun nd => match nd with end
      | Node a e t1 t2 =>
        fun nd =>
          (match t2
                 return (forall nd2, P t2 nd2) -> P (Node a e t1 t2) nd
           with
           | Empty =>
             fun _ =>
               Equal.rewrite
                 (Equal.flip eq_refl: a = rightmost (Node a e t1 Empty) I)
                 (fun x => Rightmost (Node a e t1 Empty) x)
                 (rm_noright a e t1)
           | Node a2 e2 t21 t22 =>
             let t2_ := Node a2 e2 t21 t22 in
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
    Inductive Inorder: t -> list A.t -> Prop :=
    | empty_inorder: Inorder Empty []
    | node_inorder:
        forall t1 xs1 t2 xs2 a e,
          Inorder t1 xs1 ->
          Inorder t2 xs2 ->
          Inorder (Node a e t1 t2) (xs1 ++ a :: xs2).

    Fixpoint inorder (t_:t): list A.t :=
      match t_ with
      | Empty => []
      | Node a e t1 t2 =>
        inorder t1 ++ a :: inorder t2
      end.


    Theorem inorder_correct:
      forall t_:t, Inorder t_ (inorder t_).
    Proof
      fix f t :=
      match t return Inorder t (inorder t) with
      | Empty => empty_inorder
      | Node a e t1 t2 =>
        @node_inorder t1 (inorder t1) t2 (inorder t2) a e (f t1) (f t2)
      end.

    Theorem inorder_unique:
      forall (t_:t) (xs:list A.t),
        Inorder t_ xs ->
        xs = inorder t_.
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

    Definition Same_inorder (t1 t2:t): Prop :=
      inorder t1 = inorder t2.

  End inorder_sequence.
End Make.
