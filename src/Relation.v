Require Import Core.

Set Implicit Arguments.


Section binary_relation.
  Variables A B: Type.
  Variable R: A -> B -> Prop.

  Definition domain (a:A): Prop :=
    exists b:B, R a b.

  Definition range (b:B): Prop :=
    exists a:A, R a b.

  Definition is_left_total: Prop :=
    forall a, domain a.

  Definition is_right_total: Prop :=
    forall b, range b.

  Definition is_total: Prop :=
    is_left_total /\ is_right_total.

  Theorem total_all_in_domain:
    is_total -> forall a, domain a.
  Proof
    fun tot a =>
      match tot with
      | conj tot_l _ =>
        tot_l a
      end.

  Theorem total_all_in_range:
    is_total -> forall a, range a.
  Proof
    fun tot a =>
      match tot with
      | conj _ tot_r =>
        tot_r a
      end.
End binary_relation.


Section endorelation.
  Variable A: Type.
  Variable r: A -> A -> Prop.

  Definition carrier (a:A): Prop :=
    domain r a \/ range r a.

  Definition is_covering: Prop :=
    forall a, carrier a.

  Definition is_reflexive: Prop :=
    forall a, carrier a -> r a a.

  Definition is_dichotomic: Prop :=
    forall a b, carrier a -> carrier b -> r a b \/ r b a.

  Definition is_transitive: Prop :=
    forall a b c, r a b -> r b c -> r a c.

  Definition is_symmetric: Prop :=
    forall a b, r a b -> r b a.

  Definition is_antisymmetric: Prop :=
    forall a b, r a b -> r b a -> a = b.

  Definition is_equivalence: Prop :=
    is_reflexive /\ is_symmetric /\ is_transitive.

  Theorem left_total_is_covering:
    is_left_total r -> is_covering.
  Proof
    fun ltot a =>
      or_introl (ltot a).

  Theorem right_total_is_covering:
    is_right_total r -> is_covering.
  Proof
    fun rtot a =>
      or_intror (rtot a).


  Theorem dichotomic_is_reflexive:
    is_dichotomic -> is_reflexive.
  Proof
    fun r_dicho a a_in_carrier =>
      match r_dicho a a a_in_carrier a_in_carrier with
      | or_introl p => p
      | or_intror p => p
      end.

End endorelation.



Section order_relation.
  Variable A: Type.
  Variable r: A -> A -> Prop.

  Definition is_preorder: Prop :=
    is_reflexive r /\ is_transitive r.

  Definition is_partial_order: Prop :=
    is_reflexive r /\ is_transitive r /\ is_antisymmetric r.

  Definition is_linear_preorder: Prop :=
    is_dichotomic r /\ is_transitive r.

  Definition is_linear_order: Prop :=
    is_dichotomic r /\ is_transitive r /\ is_antisymmetric r.

  Definition is_covering_linear_order: Prop :=
    is_covering r /\
    is_dichotomic r /\
    is_transitive r /\
    is_antisymmetric r.

  Theorem linear_preorder_is_reflexive:
    is_linear_preorder -> is_reflexive r.
  Proof
    fun lpo =>
      match lpo with
      | conj di tr => dichotomic_is_reflexive di
      end.

  Theorem linear_order_is_reflexive:
    is_linear_order -> is_reflexive r.
  Proof
    fun lo =>
      match lo with
      | conj di (conj tr anti) => dichotomic_is_reflexive di
      end.

End order_relation.




Section decider.
  Variable A:Type.
  Variable r: A -> A -> Prop.

  (** Type of a decision procecure for the relation [r] *)
  Definition Decider: Type :=
    forall a b:A, {r a b} + {~ r a b}.

  (** Generate a decision procedure for equality from a decision procedure of
      a covering linear order *)
  Definition equality_decider:
    is_covering_linear_order r ->
    Decider ->
    Equal.Decider A.
  Proof
    fun lo dec a b =>
      match lo with
        conj cover (conj dicho (conj _ anti)) =>
        let refl := dichotomic_is_reflexive dicho in
        let not_r a b (p:~ r a b): a <> b :=
            fun q:a = b =>
              (Equal.rewrite q (fun x => ~ r x b) p : r b b -> False)
                ((refl b) (cover b): r b b)
        in
        match dec a b, dec b a with
        | left p1,  left p2   => left (anti _ _ p1 p2)
        | left p1,  right p2  => right (Equal.flip_not_equal (not_r b a p2))
        | right p1, _         => right (not_r a b p1)
        end
      end.
End decider.




Section example.
  Theorem th1: forall n:nat, domain le n.
  Proof. refine (
             fun n => _
           ).
         unfold domain.
         assert (H:le n n).
         - apply le_n.
         - exists n. assumption.
  Qed.
  (* fun n : nat => let H := le_n n : n <= n in ex_intro (fun b : nat => n <= b) n H
     : forall n : nat, domain le n  
   *)

  Theorem le_is_left_total: is_left_total le.
  Proof
    fun n => ex_intro (fun b => n <= b) n (le_n n).

  Theorem le_is_right_total: is_right_total le.
  Proof
    fun n => ex_intro (fun a => a <= n) n (le_n n).

  Theorem le_is_covering: is_covering le.
  Proof
    left_total_is_covering le_is_left_total.

  Theorem le_is_reflexive: is_reflexive le.
  Proof
    fun n _ => le_n n.
End example.
