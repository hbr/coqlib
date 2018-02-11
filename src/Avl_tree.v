Require Import Core.
Require Natural.
Require Binary_search_tree.
Require Import Coq.Lists.List.
Import ListNotations.
Import Equal.Notations.

Set Implicit Arguments.

Module Nat := Natural.

Module Make (S0:SORTABLE).

(*====================================*)
(** * Balance Indicator *)
(*====================================*)
  Module Balance_indicator.
    Inductive t0: Set := Left: t0 | Balanced: t0 | Right : t0.
    Definition t:Set := t0.

    Definition is_Left (b:t): Prop :=
      match b with
      | Left => True
      | _ => False
      end.

    Definition is_Right (b:t): Prop :=
      match b with
      | Right => True
      | _ => False
      end.

    Definition is_Balanced (b:t): Prop :=
      match b with
      | Balanced => True
      | _ => False
      end.


    Definition Leaning (b:t): Prop :=
      match b with
      | Left | Right => True
      | Balanced => False
      end.

    Theorem left_not_balanced: Left <> Balanced.
    Proof
      fun eq => Equal.rewrite eq is_Left I.

    Theorem balanced_not_right: Balanced <> Right.
    Proof
      fun eq => Equal.rewrite eq is_Balanced I.

    Theorem right_not_left: Right <> Left.
    Proof
      fun eq => Equal.rewrite eq is_Right I.
  End Balance_indicator.
  Module B := Balance_indicator.



(*====================================*)
(** * Use Module 'Binary_search_tree' *)
(*====================================*)

  Include (Binary_search_tree.Make S0 B).


(*====================================*)
(** * Balance Indicator Basics        *)
(*====================================*)
  Section balance_indicator_basics.
    Definition is_Left_leaning  (t_:t): Prop := Extra t_ B.Left.
    Definition is_Right_leaning (t_:t): Prop := Extra t_ B.Right.
    Definition Balanced (t_:t): Prop := Extra t_ B.Balanced.
    Definition Leaning (t_:t): Prop := is_Left_leaning t_ \/ is_Right_leaning t_.


    Theorem left_leaning_is_node:
      forall (t_:t), is_Left_leaning t_ -> is_Node t_.
    Proof
      fun t ll => extra_is_node ll.

    Theorem balanced_is_node:
      forall (t_:t), Balanced t_ -> is_Node t_.
    Proof
      fun t bal => extra_is_node bal.

    Theorem right_leaning_is_node:
      forall (t_:t), is_Right_leaning t_ -> is_Node t_.
    Proof
      fun t bal => extra_is_node bal.

    Theorem leaning_is_node:
      forall t_:t, Leaning t_ -> is_Node t_.
    Proof
      fun t leaning =>
        match leaning with
        | or_introl p => left_leaning_is_node p
        | or_intror p => right_leaning_is_node p
        end.

    Theorem not_leaning_balanced:
      forall (a:A.t) (t1 t2:t),
        ~ Leaning (Node a B.Balanced t1 t2).
    Proof
      fun a t1 t2 leaning =>
        match leaning with
        | or_introl p =>
          (match p in Extra t bal
                 return t = Node a B.Balanced t1 t2 ->
                        bal = B.Left ->
                        False
           with
           | extra_node a bal t1 t2 =>
             fun eqt eqbal =>
               B.left_not_balanced
                 (Equal.join
                    (Equal.flip eqbal)
                    (node_injective_extra eqt))
           end) eq_refl eq_refl
        | or_intror p =>
          (match p in Extra t bal
                 return t = Node a B.Balanced t1 t2 ->
                        bal = B.Right ->
                        False
           with
           | extra_node a bal t1 t2 =>
             fun eqt eqbal =>
               B.balanced_not_right
                 (Equal.join
                    (Equal.flip (node_injective_extra eqt))
                    eqbal
                 )
           end) eq_refl eq_refl
        end.
  End balance_indicator_basics.



(*====================================*)
(** * Basic Definitions *)
(*====================================*)
  Section basic_definitions.

    Inductive Avl_height: t -> nat -> Prop :=
    | empty_avl: Avl_height Empty 0
    | balanced_avl:
        forall h a t1 t2,
          Avl_height t1 h ->
          Avl_height t2 h ->
          Avl_height (Node a B.Balanced t1 t2) (1+h)
    | left_avl:
        forall h a t1 t2,
          Avl_height t1 (1+h) ->
          Avl_height t2 h ->
          Avl_height (Node a B.Left t1 t2) (2+h)
    | right_avl:
        forall h a t1 t2,
          Avl_height t1 h ->
          Avl_height t2 (1+h) ->
          Avl_height (Node a B.Right t1 t2) (2+h).

    Theorem avl_height_is_height:
      forall (t_:t) (h:nat),
        Avl_height t_ h ->
        Height t_ h.
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
          (node_height a B.Balanced (f _ _ ph1) (f _ _ ph2))
      | left_avl a ph1 ph2 =>
        Equal.rewrite
          (maxh1h _)
          (fun x => Height _ (1 + x))
          (node_height a B.Left (f _ _ ph1) (f _ _ ph2))
      | right_avl a ph1 ph2 =>
        Equal.rewrite
          (maxhh1 _)
          (fun x => Height _ (1 + x))
          (node_height a B.Right (f _ _ ph1) (f _ _ ph2))
      end.



    Definition Avl_tree (t_:t): Prop :=
      Avl_height t_ (height t_).

    Theorem avl_height_positive_is_node:
      forall (t_:t) (h:nat),
        Avl_height t_ (S h) ->
        is_Node t_.
    Proof
      let f t h_ (avl:Avl_height t h_): forall h, S h = h_  -> is_Node t :=
          (match avl in Avl_height t h_
                 return forall h, S h = h_ -> is_Node t with
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


    Theorem avl_node_is_positive_height:
      forall (h:nat) (t_:t),
        Avl_height t_ h ->
        is_Node t_ ->
        Nat.is_Successor h.
    Proof
      fun h t_ avl =>
        match avl in Avl_height t h
        with
        | empty_avl => fun nd => match nd with end
        | left_avl a ph1 ph2 => fun nd => I
        | balanced_avl a ph1 ph2  => fun nd => I
        | right_avl a ph1 ph2 => fun nd => I
        end
      .


    Theorem left_leaning_sons_height:
      forall (h:nat) (a:A.t) (t1 t2:t),
        Avl_height (Node a B.Left t1 t2) (2+h) ->
        Avl_height t1 (1+h) /\ Avl_height t2 h.
    Proof
      fun h a t1 t2 avl =>
        (match avl in Avl_height t0 h0
               return t0 = Node a B.Left t1 t2 ->
                      h0 = 2 + h ->
                      Avl_height t1 (1 + h) /\ Avl_height t2 h
         with
         | empty_avl =>
           fun eq =>
             match
               node_not_empty (Equal.flip eq)
             with
             end
         | balanced_avl _ _ _ =>
           fun eq =>
             match
               B.left_not_balanced
                 (node_injective_extra (Equal.flip eq))
             with
             end
         | left_avl a0 avl01 avl02 =>
           fun eqt eqh_plus2 =>
             let eqt1 := node_injective_left_son eqt in
             let eqt2 := node_injective_right_son eqt in
             let eqh_plus1: 1 + _ = 1 + _ := Nat.successor_injective eqh_plus2 in
             let eqh: _ = _ := Nat.successor_injective eqh_plus1 in
             let p1 :=
                 Equal.rewrite
                   eqh_plus1
                   (fun x => Avl_height _ x)
                   (Equal.rewrite eqt1 (fun t => Avl_height t _) avl01) in
             let p2 :=
                 Equal.rewrite
                   eqh
                   (fun x => Avl_height _ x)
                   (Equal.rewrite eqt2 (fun t => Avl_height t _) avl02) in
             conj p1 p2
         | right_avl _ _ _ =>
           fun eq =>
             match
               B.right_not_left (node_injective_extra eq)
             with
             end
         end) eq_refl eq_refl.

    Theorem right_leaning_sons_height:
      forall (h:nat) (a:A.t) (t1 t2:t),
        Avl_height (Node a B.Right t1 t2) (2+h) ->
        Avl_height t1 h /\ Avl_height t2 (1+h).
    Proof
      fun h a t1 t2 avl =>
        (match avl in Avl_height t0 h0
               return t0 = Node a B.Right t1 t2 ->
                      h0 = 2 + h ->
                      Avl_height t1 h /\ Avl_height t2 (1 + h)
         with
         | empty_avl =>
           fun eq =>
             match
               node_not_empty (Equal.flip eq)
             with
             end
         | balanced_avl _ _ _ =>
           fun eq =>
             match
               B.balanced_not_right
                 (node_injective_extra eq)
             with
             end
         | left_avl _ _ _ =>
           fun eq =>
             match
               B.right_not_left
                 (node_injective_extra (Equal.flip eq))
             with
             end
         | right_avl a0 avl01 avl02 =>
           fun eqt eqh_plus2 =>
             let eqt1 := node_injective_left_son eqt in
             let eqt2 := node_injective_right_son eqt in
             let eqh_plus1: 1 + _ = 1 + _ := Nat.successor_injective eqh_plus2 in
             let eqh: _ = _ := Nat.successor_injective eqh_plus1 in
             let p1 :=
                 Equal.rewrite
                   eqh
                   (fun x => Avl_height _ x)
                   (Equal.rewrite eqt1 (fun t => Avl_height t _) avl01) in
             let p2 :=
                 Equal.rewrite
                   eqh_plus1
                   (fun x => Avl_height _ x)
                   (Equal.rewrite eqt2 (fun t => Avl_height t _) avl02) in
             conj p1 p2
         end) eq_refl eq_refl.

    Theorem balanced_sons_height:
      forall (h:nat) (a:A.t) (t1 t2:t),
        Avl_height (Node a B.Balanced t1 t2) (1+h) ->
        Avl_height t1 h /\ Avl_height t2 h.
    Proof
      fun h a t1 t2 avl =>
        (match avl in Avl_height t0 h0
               return t0 = Node a B.Balanced t1 t2 ->
                      h0 = 1 + h ->
                      Avl_height t1 h /\ Avl_height t2 h
         with
         | empty_avl =>
           fun eq =>
             match
               node_not_empty (Equal.flip eq)
             with
             end
         | left_avl _ _ _ =>
           fun eq =>
             match
               B.left_not_balanced
                 (node_injective_extra eq)
             with
             end
         | balanced_avl a0 avl01 avl02 =>
           fun eqt eqh_plus1 =>
             let eqt1 := node_injective_left_son eqt in
             let eqt2 := node_injective_right_son eqt in
             let eqh: _ = _ := Nat.successor_injective eqh_plus1 in
             let p1 :=
                 Equal.rewrite
                   eqh
                   (fun x => Avl_height _ x)
                   (Equal.rewrite eqt1 (fun t => Avl_height t _) avl01) in
             let p2 :=
                 Equal.rewrite
                   eqh
                   (fun x => Avl_height _ x)
                   (Equal.rewrite eqt2 (fun t => Avl_height t _) avl02) in
             conj p1 p2
         | right_avl _ _ _ =>
           fun eq =>
             match
               B.balanced_not_right
                 (node_injective_extra (Equal.flip eq))
             with
             end
         end) eq_refl eq_refl.

    Theorem left_leaning_height:
      forall (h:nat) (a:A.t) (t1 t2:t),
        Avl_height (Node a B.Left t1 t2) (1 + h) ->
        Nat.is_Successor h.
    Proof
      fun h a t1 t2 avl =>
        (match avl in Avl_height t_ h_
               return t_ = Node a B.Left t1 t2 ->
                      h_ = 1 + h ->
                      Nat.is_Successor h
         with
         | empty_avl =>
           fun eqt => match node_not_empty (Equal.flip eqt) with end
         | balanced_avl _ _ _ =>
           fun eqt =>
             match
               B.left_not_balanced (node_injective_extra (Equal.flip eqt))
             with end
         | left_avl a0 avl01 avl02 =>
           fun eqt eqh =>
             Equal.rewrite
               (Nat.successor_injective eqh: S _ = h)
               Nat.is_Successor
               I
         | right_avl _ _ _ =>
           fun eqt =>
             match
               B.right_not_left (node_injective_extra eqt)
             with end
         end) eq_refl eq_refl.

    Theorem right_leaning_height:
      forall (h:nat) (a:A.t) (t1 t2:t),
        Avl_height (Node a B.Right t1 t2) (1 + h) ->
        Nat.is_Successor h.
    Proof
      fun h a t1 t2 avl =>
        (match avl in Avl_height t_ h_
               return t_ = Node a B.Right t1 t2 ->
                      h_ = 1 + h ->
                      Nat.is_Successor h
         with
         | empty_avl =>
           fun eqt => match node_not_empty (Equal.flip eqt) with end
         | balanced_avl _ _ _ =>
           fun eqt =>
             match
               B.balanced_not_right (node_injective_extra eqt)
             with end
         | left_avl _ _ _ =>
           fun eqt =>
             match
               B.right_not_left (node_injective_extra (Equal.flip eqt))
             with end
         | right_avl a0 avl01 avl02 =>
           fun eqt eqh =>
             Equal.rewrite
               (Nat.successor_injective eqh: S _ = h)
               Nat.is_Successor
               I
         end) eq_refl eq_refl.
  End basic_definitions.




  (*====================================*)
  (** * Rebalancing *)
  (*====================================*)
  Section rebalancing.
    Definition Rebalance_left_result (t1 t2:t):Type :=
      let h := height t2 in
      Avl_height t1 (2 + h) ->
      Avl_height t2 h ->
      Either.t {u:t| Avl_height u (2 + h)} {u:t| Avl_height u (3 + h)}.


    Definition rebalance_left (c:A.t) (t1 t2:t): Rebalance_left_result t1 t2 :=
      let h := height t2 in
      match t1 with
      | Empty =>
        fun ph1  => match avl_height_positive_is_node ph1 with end
      | Node a B.Left t11 t12 =>
        (* left-left unbalance:
                    c                            a
              a          t2              t11            c
          t11   t12                      x          t12   t2
          x
         *)
        fun ph1 ph2  =>
          let t := Node a B.Balanced t11 (Node c B.Balanced t12 t2) in
          match left_leaning_sons_height ph1 with
          | conj ph11 ph12 =>
            let avl := balanced_avl a ph11 (balanced_avl c ph12 ph2) in
            Either.Left _ (exist _ t avl)
          end
      | Node a B.Balanced t11 t12 =>
        (* left unbalance:
                    c                            a
              a          t2              t11            c
          t11   t12                      x          t12   t2
          x     x                                   x
         *)
        fun ph1 ph2 =>
          match balanced_sons_height ph1 with
          | conj ph11 ph12 =>
            let t := Node a B.Right t11 (Node c B.Left t12 t2) in
            let ph: Avl_height t (3+h) :=
                right_avl a ph11 (left_avl c ph12 ph2) in
            Either.Right _ (exist _ t ph)
          end
      | Node a B.Right t11 t12 =>
        (* left-right unbalance:
                      c                               b
              a            t2                   a            c
          t11     b                          t11 t121    t122 t2
              t121 t122
         *)
        fun ph1 ph2 =>
          let ph_11_12 := right_leaning_sons_height ph1 in
          let ph11 := proj1 ph_11_12 in
          let ph12 := proj2 ph_11_12 in
          let f0 t h := Avl_height t h in
          let f1 t h := Avl_height t (1 + h) in
          let f2 t h := Avl_height t (1+(1+h)) in
          Either.Left
            _
            ((match
                 t12
                 return
                 forall (ph12:Avl_height t12 (1+h)),
                   {t|Avl_height t (2+h)}
               with
               | Empty =>
                 fun ph12 =>
                   match (avl_height_positive_is_node ph12) with end
               | Node b B.Left t121 t122 =>
                 fun ph12 =>
                   let predh := Nat.predecessor h (left_leaning_height ph12) in
                   let h0 := proj1_sig predh in
                   let eqh0: h = 1 + h0 := Equal.flip (proj2_sig predh) in
                   let rewrite0 t ph := Equal.rewrite eqh0 (f0 t) ph in
                   let rewrite1 t ph := Equal.rewrite eqh0 (f1 t) ph in
                   let rewrite2 t ph :=
                       Equal.rewrite (Equal.flip eqh0) (f2 t) ph in
                   let ph_121_122 := left_leaning_sons_height (rewrite1 _ ph12) in
                   match left_leaning_sons_height (rewrite1 _ ph12) with
                   | conj ph121 ph122 =>
                     exist
                       _
                       (Node b B.Balanced
                             (Node a B.Balanced t11 t121)
                             (Node c B.Right t122 t2))
                       (rewrite2
                          _
                          (balanced_avl
                             b
                             (balanced_avl
                                a (rewrite0 _ ph11) ph121)
                             (right_avl
                                c ph122 (rewrite0 _ ph2)))
                       )
                   end
               | Node b B.Balanced t121 t122 =>
                 fun ph12 =>
                   let ph_121_122 := balanced_sons_height ph12 in
                   exist _
                         (Node
                            b B.Balanced
                            (Node a B.Balanced t11 t121)
                            (Node c B.Balanced t122 t2))
                         (balanced_avl
                            b
                            (balanced_avl a ph11 (proj1 ph_121_122))
                            (balanced_avl c (proj2 ph_121_122) ph2))
               | Node b B.Right t121 t122 =>
                 fun ph12 =>
                   let predh := Nat.predecessor h (right_leaning_height ph12) in
                   let h0 := proj1_sig predh in
                   let eqh0: h = 1 + h0 := Equal.flip (proj2_sig predh) in
                   let rewrite0 t ph := Equal.rewrite eqh0 (f0 t) ph in
                   let rewrite1 t ph := Equal.rewrite eqh0 (f1 t) ph in
                   let rewrite2 t ph :=
                       Equal.rewrite (Equal.flip eqh0) (f2 t) ph in
                   match right_leaning_sons_height (rewrite1 _ ph12) with
                   | conj ph121 ph122 =>
                     exist
                       _
                       (Node b B.Balanced
                             (Node a B.Left t11 t121)
                             (Node c B.Balanced t122 t2))
                       (rewrite2
                          _
                          (balanced_avl
                             b
                             (left_avl a (rewrite0 _ ph11) ph121)
                             (balanced_avl c ph122 (rewrite0 _ ph2))))
                   end
               end) ph12)
      end.
  End rebalancing.


  (*====================================*)
  (** * Insertion *)
  (*====================================*)

  (* Insertion is done by either inserting into an empty tree (resulting in a
     balanced singleton tree) or insertion into the left or right subtree.

     Insertion into the left or right subtree might increased the height of
     the subtree by 1 or leave it at the same height as before.

     Rebalancing is necessary:

     a) left leaning, insertion into left and left subtree increases
     b) right leaning, insertion into right and right subtree increases

     Modification of balance factor from leaning to balanced:

     a) left leaning, insertion into right and right subtree increases
     b) right leaning, insertion into left and left subtree increases

     Modification of balance factor from balanced to leaning (height increase):

     a) insertion into left and left subtree increases
     b) insertion into right and right subtree increases

     No modification: Insertion into left or right and no increase in height.

*)

  Section insertion.
    Definition Put_result (x:A.t) (u:t): Type :=
      let h := height u in
      Avl_height u h ->
      Either.t {v:t | Avl_height v h} {v:t | Avl_height v (1+h)}.


    (*Fixpoint put_generic (x:A.t) (t_:t): Put_result x t_ :=
      let h := height t_ in
      match t_ with
      | Empty =>
        fun ph =>
          Either.Right
            _
            (exist
               _
               (Node x B.Balanced Empty Empty)
               (balanced_avl x ph ph))
      | Node a bal t1 t2 =>
        match S.compare x a with
        | Relation.less_than p1 notp2 =>
          match bal with
          | B.Left =>
            fun ph =>
              let v := @put_generic x t1 in
              _
          | B.Balanced => _
          | B.Right => _
          end
        | Relation.equivalent _ p2
        | Relation.greater_than _ p2 =>
          _
        end
      end.*)
  End insertion.

  (*====================================*)
  (** * Deletion *)
  (*====================================*)
  Section deletion.
  End deletion.
End Make.
