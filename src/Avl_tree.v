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


    Definition Leaning (b:T): Prop :=
      match b with
      | left | right => True
      | balanced => False
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
  Section basic_definitions.

    Definition Left_leaning  (t:T): Prop := Extra t B.left.
    Definition Right_leaning (t:T): Prop := Extra t B.right.
    Definition Balanced (t:T): Prop := Extra t B.balanced.
    Definition Leaning (t:T): Prop := Left_leaning t \/ Right_leaning t.


    Theorem left_leaning_is_node:
      forall (t:T), Left_leaning t -> Node t.
    Proof
      fun t ll => extra_is_node ll.

    Theorem balanced_is_node:
      forall (t:T), Balanced t -> Node t.
    Proof
      fun t bal => extra_is_node bal.

    Theorem right_leaning_is_node:
      forall (t:T), Right_leaning t -> Node t.
    Proof
      fun t bal => extra_is_node bal.

    Theorem leaning_is_node:
      forall t:T, Leaning t -> Node t.
    Proof
      fun t leaning =>
        match leaning with
        | or_introl p => left_leaning_is_node p
        | or_intror p => right_leaning_is_node p
        end.

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

    Theorem avl_height_is_height:
      forall (t:T) (h:nat),
        Avl_height t h ->
        Height t h.
    Proof
      let maxhh  (h:nat): max h h = h := max_l h h (le_n h) in
      let maxhh1 (h:nat): max h (1+h) = 1+h := max_r _ _ (le_S _ _ (le_n _)) in
      let maxh1h (h:nat): max (1+h) h = 1+h := max_l _ _ (le_S _ _ (le_n _)) in
      fix f t h avl :=
      match avl in Avl_height t h
            return Height t h
      with
      | empty_avl => empty_height
      | balanced_avl a ph1 ph2 =>
        Equal.rewrite
          (maxhh _)
          (fun x => Height  _ (1 + x))
          (node_height a B.balanced (f _ _ ph1) (f _ _ ph2))
      | left_avl a ph1 ph2 =>
        Equal.rewrite
          (maxh1h _)
          (fun x => Height _ (1 + x))
          (node_height a B.left (f _ _ ph1) (f _ _ ph2))
      | right_avl a ph1 ph2 =>
        Equal.rewrite
          (maxhh1 _)
          (fun x => Height _ (1 + x))
          (node_height a B.right (f _ _ ph1) (f _ _ ph2))
      end.



    Definition Avl_tree (t:T): Prop :=
      Avl_height t (height t).

    Theorem avl_height_positive_is_node:
      forall (t:T) (h:nat),
        Avl_height t (S h) ->
        Node t.
    Proof
      let f t h_ (avl:Avl_height t h_): forall h, S h = h_  -> Node t :=
          (match avl in Avl_height t h_
                 return forall h, S h = h_ -> Node t with
           | empty_avl =>
             fun h eq => match Nat.successor_not_zero eq with end
           | @balanced_avl h a t1 t2 ph1 ph2 =>
             fun _ _ => I
           | @left_avl h a t1 t2 ph1 ph2 =>
             fun _ _ => I
           | @right_avl h a t1 t2 ph1 ph2 =>
             fun _ _ => I
           end)
      in
      fun t h avl => f t (S h) avl h eq_refl .
  End basic_definitions.




  (*====================================*)
  (** * Rebalancing *)
  (*====================================*)
  Section rebalancing.
    Inductive Nearly_avl_left: A -> T -> T -> Prop :=
    | lrl_nearly_avl_left:
        (* lrl:
                      c
              a            t2
          t11     b        x
          x   t121 t122
              x
         *)
        forall h t11 t121 t122 t2 a b c,
          Avl_height t11 (1+h) ->
          Avl_height t121 (1+h) ->
          Avl_height t122 h ->
          Avl_height t2 (1+h) ->
          Nearly_avl_left
            c
            (node a B.right t11 (node b B.left t121 t122))
            t2
    | lrr_nearly_avl_left:
        (* lrl:
                      c
              a            t2
          t11     b        x
          x   t121 t122
                   x
         *)
        forall h t11 t121 t122 t2 a b c,
          Avl_height t11 (1+h) ->
          Avl_height t121 h ->
          Avl_height t122 (1+h) ->
          Avl_height t2 (1+h) ->
          Nearly_avl_left
            c
            (node a B.right t11 (node b B.right t121 t122))
            t2
    | ll_nearly_avl_left:
        (* ll:
                    c
              a          t2
          t11    t12
          x
         *)
        forall h t11 t12 t2 a c,
          Avl_height t11 (1+h) ->
          Avl_height t12 h ->
          Avl_height t2  h ->
          Nearly_avl_left
            c
            (node a B.left t11 t12)
            t2.




    Definition rebalance_left (c:A) (t1 t2:T): T :=
      match t1  with
      | empty =>
        node c B.right empty t2
      | node a B.right t11 (node b B.left t121 t122) =>
        (* lrl:
                      c                               b
              a            t2                   a            c
          t11     b        x                 t11  t121   t122  t2
          x   t121 t122                      x    x            x
              x
         *)
        node
          b B.balanced
          (node a B.balanced t11 t121)
          (node c B.right t122 t2)
      | node a B.right t11 (node b B.right t121 t122) =>
        (* lrr:
                      c                               b
              a            t2                   a            c
          t11     b        x                 t11  t121   t122  t2
          x   t121 t122                      x           x     x
                   x
         *)
        node
          b B.balanced
          (node a B.left t11 t121)
          (node c B.balanced t122 t2)
      | node a bal t11 t12 =>
        (* ll:
                    c                            a
              a          t2              t11            c
          t11    t12                     x          t12   t2
          x
         *)
        node a B.balanced t11 (node c B.balanced t12 t2)
      end.


    Theorem rebalance_left_rebalances:
      forall (a:A) (t1 t2:T) (nearly:Nearly_avl_left a t1 t2),
        Avl_height (rebalance_left a t1 t2) (2 + height t2).
    Proof
      let rewrite h t1 t2 (ph1:Avl_height t1 h) (ph2:Avl_height t2 (2+h)) :=
          Equal.rewrite
            (height_is_only_height (avl_height_is_height ph1))
            (fun x => Avl_height t2 (2 + x))
            ph2
      in
      fun a t1 t2 nearly =>
        match nearly in Nearly_avl_left a t1 t2
              return Avl_height (rebalance_left a t1 t2) (2 + height t2)
        with
        | lrl_nearly_avl_left a b c ph11 ph121 ph122 ph2 =>
          let pa := balanced_avl a ph11 ph121 in
          let pc := right_avl c ph122 ph2 in
          let pb := balanced_avl b pa pc in
          rewrite _ _ _ ph2 pb
        | lrr_nearly_avl_left a b c ph11 ph121 ph122 ph2 =>
          let pa := left_avl a ph11 ph121 in
          let pc := balanced_avl c ph122 ph2 in
          let pb := balanced_avl b pa pc in
          rewrite _ _ _ ph2 pb
        | ll_nearly_avl_left a c ph11 ph12 ph2 =>
          let pc := balanced_avl c ph12 ph2 in
          let pa := balanced_avl a ph11 pc in
          rewrite _ _ _ ph2 pa
        end.


    Inductive Nearly_avl_right: A -> T -> T -> Prop :=
    | rll_nearly_avl_right:
        (* rll:
                   a
           t1               c
           x           b        t22
                   t211 t212    x
                   x
         *)
        forall h t1 t211 t212 t22 a b c,
          Avl_height t1 (1+h) ->
          Avl_height t211 (1+h) ->
          Avl_height t212 h ->
          Avl_height t22 (1+h) ->
          Nearly_avl_right
            a
            t1
            (node c B.left (node b B.left t211 t212) t22)
    | rlr_nearly_avl_right:
        (* rlr:
                   a
           t1               c
           x           b        t22
                   t211 t212    x
                         x
         *)
        forall h t1 t211 t212 t22 a b c,
          Avl_height t1 (1+h) ->
          Avl_height t211 h ->
          Avl_height t212 (1+h) ->
          Avl_height t22 (1+h) ->
          Nearly_avl_right
            a
            t1
            (node c B.left (node b B.right t211 t212) t22)
    | rr_nearly_avl_right:
        (* rr:
                   a
           t1               c
                       t21      t22
                                x
         *)
        forall h t1 t21 t22 a c,
          Avl_height t1 h ->
          Avl_height t21 h ->
          Avl_height t22 (1+h) ->
          Nearly_avl_right
            a
            t1
            (node c B.right t21 t22).



    Definition rebalance_right (a:A) (t1 t2:T): T :=
      match t2  with
      | empty =>
        node a B.left t1 empty
      | node c B.left (node b B.left t211 t212) t21 =>
        (* rll:
                   a                                  b
           t1               c                   a            c
           x           b        t21          t1  t211    t212 t21
                   t211 t212    x            x   x            x
                   x
         *)
        node
          b B.balanced
          (node a B.balanced t1 t211)
          (node c B.right t212 t21)
      | node c B.left (node b B.right t211 t212) t22 =>
        (* rlr:
                   a                                  b
           t1               c                   a            c
           x           b        t22          t1  t211    t212 t22
                   t211 t212    x            x           x    x
                        x
         *)
        node
          b B.balanced
          (node a B.left t1 t211)
          (node c B.balanced t212 t22)
      | node c bal t21 t22 =>
        (* rr:
                   a                                  c
           t1               c                   a          t22
                       t21      t22          t1  t21       x
                                x
         *)
        node c B.balanced (node a B.balanced t1 t21) t22
      end.


    Theorem rebalance_right_rebalances:
      forall (a:A) (t1 t2:T) (nearly:Nearly_avl_right a t1 t2),
        Avl_height (rebalance_right a t1 t2) (2 + height t1).
    Proof
      let rewrite h t1 t2 (ph1:Avl_height t1 h) (ph2:Avl_height t2 (2+h)) :=
          Equal.rewrite
            (height_is_only_height (avl_height_is_height ph1))
            (fun x => Avl_height t2 (2 + x))
            ph2
      in
      fun a t1 t2 nearly =>
        match nearly in Nearly_avl_right a t1 t2
              return Avl_height (rebalance_right a t1 t2) (2 + height t1)
        with
        | rll_nearly_avl_right a b c ph1 ph211 ph212 ph21 =>
          let pa := balanced_avl a ph1 ph211 in
          let pc := right_avl c ph212 ph21 in
          let pb := balanced_avl b pa pc in
          rewrite _ _ _ ph1 pb
        | rlr_nearly_avl_right a b c ph1 ph211 ph212 ph22 =>
          let pa := left_avl a ph1 ph211 in
          let pc := balanced_avl c ph212 ph22 in
          let pb := balanced_avl b pa pc in
          rewrite _ _ _ ph1 pb
        | rr_nearly_avl_right a c ph1 ph21 ph22 =>
          let pa := balanced_avl a ph1 ph21 in
          let pc := balanced_avl c pa ph22 in
          rewrite _ _ _ ph1 pc
        end.
  End rebalancing.
End Make.
