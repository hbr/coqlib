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
(** * Balance Indicator Basics        *)
(*====================================*)
  Section balance_indicator_basics.
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

    Theorem not_leaning_balanced:
      forall (a:A) (t1 t2:T),
        ~ Leaning (node a B.balanced t1 t2).
    Proof
      fun a t1 t2 leaning =>
        match leaning with
        | or_introl p =>
          (match p in Extra t bal
                 return t = node a B.balanced t1 t2 ->
                        bal = B.left ->
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
                 return t = node a B.balanced t1 t2 ->
                        bal = B.right ->
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

    Theorem left_leaning_sons_height:
      forall (h:nat) (a:A) (t1 t2:T),
        Avl_height (node a B.left t1 t2) (2+h) ->
        Avl_height t1 (1+h) /\ Avl_height t2 h.
    Proof
      fun h a t1 t2 avl =>
        (match avl in Avl_height t0 h0
               return t0 = node a B.left t1 t2 ->
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
      forall (h:nat) (a:A) (t1 t2:T),
        Avl_height (node a B.right t1 t2) (2+h) ->
        Avl_height t1 h /\ Avl_height t2 (1+h).
    Proof
      fun h a t1 t2 avl =>
        (match avl in Avl_height t0 h0
               return t0 = node a B.right t1 t2 ->
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
      forall (h:nat) (a:A) (t1 t2:T),
        Avl_height (node a B.balanced t1 t2) (1+h) ->
        Avl_height t1 h /\ Avl_height t2 h.
    Proof
      fun h a t1 t2 avl =>
        (match avl in Avl_height t0 h0
               return t0 = node a B.balanced t1 t2 ->
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
      forall (h:nat) (a:A) (t1 t2:T),
        Avl_height (node a B.left t1 t2) (1 + h) ->
        Nat.Successor h.
    Proof
      fun h a t1 t2 avl =>
        (match avl in Avl_height t_ h_
               return t_ = node a B.left t1 t2 ->
                      h_ = 1 + h ->
                      Nat.Successor h
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
               Nat.Successor
               I
         | right_avl _ _ _ =>
           fun eqt =>
             match
               B.right_not_left (node_injective_extra eqt)
             with end
         end) eq_refl eq_refl.

    Theorem right_leaning_height:
      forall (h:nat) (a:A) (t1 t2:T),
        Avl_height (node a B.right t1 t2) (1 + h) ->
        Nat.Successor h.
    Proof
      fun h a t1 t2 avl =>
        (match avl in Avl_height t_ h_
               return t_ = node a B.right t1 t2 ->
                      h_ = 1 + h ->
                      Nat.Successor h
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
               Nat.Successor
               I
         end) eq_refl eq_refl.
  End basic_definitions.




  (*====================================*)
  (** * Rebalancing *)
  (*====================================*)
  Section rebalancing.
    Definition Rebalance_left_result (t1 t2:T):Type :=
      forall h,
      Avl_height t1 (2 + h) ->
      Avl_height t2 h ->
      Either.T {t:T| Avl_height t (2 + h)} {t:T| Avl_height t (3 + h)}.


    Definition rebal_left (c:A) (t1 t2:T): Rebalance_left_result t1 t2 :=
      match t1 with
      | empty =>
        fun h ph1  => match avl_height_positive_is_node ph1 with end
      | node a B.left t11 t12 =>
        (* left-left unbalance:
                    c                            a
              a          t2              t11            c
          t11   t12                      x          t12   t2
          x
         *)
        fun h ph1 ph2  =>
          let t := node a B.balanced t11 (node c B.balanced t12 t2) in
          match left_leaning_sons_height ph1 with
          | conj ph11 ph12 =>
            let avl := balanced_avl a ph11 (balanced_avl c ph12 ph2) in
            Either.left _ (exist _ t avl)
          end
      | node a B.balanced t11 t12 =>
        (* left unbalance:
                    c                            a
              a          t2              t11            c
          t11   t12                      x          t12   t2
          x     x                                   x
         *)
        fun h ph1 ph2 =>
          match balanced_sons_height ph1 with
          | conj ph11 ph12 =>
            let t := node a B.right t11 (node c B.left t12 t2) in
            let ph: Avl_height t (3+h) :=
                right_avl a ph11 (left_avl c ph12 ph2) in
            Either.right _ (exist _ t ph)
          end
      | node a B.right t11 t12 =>
        (* left-right unbalance:
                      c                               b
              a            t2                   a            c
          t11     b                          t11 t121    t122 t2
              t121 t122
         *)
        fun h ph1 ph2 =>
          let ph_11_12 := right_leaning_sons_height ph1 in
          let ph11 := proj1 ph_11_12 in
          let ph12 := proj2 ph_11_12 in
          let f0 t h := Avl_height t h in
          let f1 t h := Avl_height t (1 + h) in
          let f2 t h := Avl_height t (1+(1+h)) in
          Either.left
            _
            ((match
                 t12
                 return
                 forall (ph12:Avl_height t12 (1+h)),
                   {t|Avl_height t (2+h)}
               with
               | empty =>
                 fun ph12 =>
                   match (avl_height_positive_is_node ph12) with end
               | node b B.left t121 t122 =>
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
                       (node b B.balanced
                             (node a B.balanced t11 t121)
                             (node c B.right t122 t2))
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
               | node b B.balanced t121 t122 =>
                 fun ph12 =>
                   let ph_121_122 := balanced_sons_height ph12 in
                   exist _
                         (node
                            b B.balanced
                            (node a B.balanced t11 t121)
                            (node c B.balanced t122 t2))
                         (balanced_avl
                            b
                            (balanced_avl a ph11 (proj1 ph_121_122))
                            (balanced_avl c (proj2 ph_121_122) ph2))
               | node b B.right t121 t122 =>
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
                       (node b B.balanced
                             (node a B.left t11 t121)
                             (node c B.balanced t122 t2))
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
  Section insertion.
    Definition Put_result (x:A) (t:T): Type :=
      forall h,
        Avl_height t h ->
        Either.T {u:T | Avl_height u h} {u:T | Avl_height u (1+h)}.

    (*Fixpoint put_generic (x:A) (t:T): Put_result x t :=
      match t with
      | empty =>
        fun h ph =>
          Either.right
            _
            (exist
               _
               (node x B.balanced empty empty)
               (balanced_avl x ph ph))
      | node a bal t1 t2 =>
        fun h ph =>
          match S.compare x a with
          | Relation.less_than  p1 notp2 =>
            _
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
