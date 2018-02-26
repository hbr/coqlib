Require Extraction.
Set Implicit Arguments.



(** * Extraction of Standard Types to Ocaml *)
(*    ===================================== *)

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive sumor => option [ Some None ].
Extract Inductive unit => unit [ "()" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => option [ Some None ].
Extract Inductive prod => "( * )" [ "" ]. (* "" instead of "(,)" *)
Extract Inlined Constant andb => "(&&)".
Extract Inlined Constant orb => "(||)".


(** * Propositions *)
(*    ============ *)

Definition ex_falso {A:Type} (p:False):A :=
  match p with end.

Module And.
  Definition make3 {A B C:Prop} (a:A) (b:B) (c:C) : A /\ B /\ C :=
    conj a (conj b c).

  Definition make4 {A B C D:Prop} (a:A) (b:B) (c:C) (d:D) : A /\ B /\ C /\ D :=
    conj a (conj b (conj c d)).

  Definition use {A B C:Prop} (p:A/\B) (f:A->B->C): C :=
    match p with
      conj a b => f a b
    end.

  Definition use3 {A B C D:Prop} (p:A/\B/\C) (f:A->B->C->D): D :=
    match p with
      conj a (conj b c) => f a b c
    end.

  Definition use4 {A B C D E:Prop} (p:A/\B/\C/\D) (f:A->B->C->D->E): E :=
    match p with
      conj a (conj b (conj c d)) => f a b c d
    end.

  Definition proj1 {A B:Prop} (p:A/\B): A :=
    use p (fun a b => a).

  Definition proj2 {A B:Prop} (p:A/\B): B :=
    use p (fun a b => b).
End And.


Module Or.
  Definition use {A B C:Prop} (p:A\/B) (f:A->C) (g:B->C): C :=
    match p with
    | or_introl a => f a
    | or_intror b => g b
    end.
End Or.

Module Sigma.
  Definition value {A:Type} {P:A->Prop} (s:sig P): A :=
    match s with
      exist _ v _ => v
    end.

  Definition proof {A:Type} {P:A->Prop} (s:sig P): P (value s) :=
    match s with
      exist _ _ p => p
    end.

  Definition use {A B:Type} {P:A->Prop} (s:sig P) (f:forall a, P a -> B): B :=
    match s with
      exist _ v p => f v p
    end.

  Definition use2 {A B:Type} {P1 P2:A->Prop}
             (s:sig (fun a => P1 a /\ P2 a))
             (f:forall a, P1 a -> P2 a -> B): B :=
    match s with
      exist _ v (conj p1 p2) => f v p1 p2
    end.

  Definition use3 {A B:Type} {P1 P2 P3:A->Prop}
             (s:sig (fun a => P1 a /\ P2 a /\ P3 a))
             (f:forall a, P1 a -> P2 a -> P3 a -> B): B :=
    match s with
      exist _ v (conj p1 (conj p2 p3)) => f v p1 p2 p3
    end.

  Definition use4 {A B:Type} {P1 P2 P3 P4:A->Prop}
             (s:sig (fun a => P1 a /\ P2 a /\ P3 a /\ P4 a))
             (f:forall a, P1 a -> P2 a -> P3 a -> P4 a -> B): B :=
    match s with
      exist _ v (conj p1 (conj p2 (conj p3 p4))) => f v p1 p2 p3 p4
    end.
End Sigma.

Module Exist.
  Definition
    make2
    {A B:Type} {P:A->B->Prop} {a:A} {b:B} (p: P a b) : exists a b, P a b :=
    ex_intro _ a (ex_intro _ b p).

  Definition use {A:Type} {P:A->Prop} {B:Prop}
             (e:exists a, P a) (f:forall a, P a -> B): B :=
    match e with
      ex_intro _ v p => f v p
    end.

  Definition use2 {A B:Type} {P:A->B->Prop} {C:Prop}
             (e:exists a b, P a b) (f:forall a b, P a b -> C): C :=
    match e with
      ex_intro _ a e2 =>
      match e2 with
        ex_intro _ b p => f a b p
      end
    end.
End Exist.

(** * Equality *)
(*    ======== *)
Module Equal.
  Section equal_basics.
    Variables A B: Type.

    Theorem use {a b:A} (eq:a=b) (T:A->Type) (pa:T a): T b.
    Proof
      match eq with
        eq_refl => pa
      end.

    Theorem use2 {a1 b1:A} {a2 b2:B}
            (eq1:a1=b1) (eq2:a2=b2) (T:A->B->Type) (p: T a1 a2)
      : T b1 b2.
    Proof
      match eq1 with
        eq_refl =>
        match eq2 with
          eq_refl => p
        end
      end.

    Theorem
      rewrite0 (a b:A) (p:a = b) (P:A->Type) (pa:P a): P b.
    Proof
      match p in (_ = x) return P x with
      | eq_refl => pa
      end.

    Theorem
      rewrite {a b:A} (P:A->Type) (p:a = b) (pa:P a): P b.
    Proof
      match p in (_ = x) return P x with
      | eq_refl => pa
      end.

    Theorem
      inject {a b:A} (p:a=b) (f:A->B): f a = f b.
    Proof
      match p in (_ = x) return f a = f x with
      | eq_refl => eq_refl
      end.


    Theorem
      flip {a b:A} (p:a=b): b=a.
    Proof
      rewrite0 p (fun x => x=a) eq_refl.

    Theorem
      join (a b c:A) (pab:a=b) (pbc:b=c): a=c.
    Proof
      rewrite0 pbc (fun x => a=x) pab.

    Theorem
      flip_not_equal {a b:A} (p:a<>b): b<>a.
    Proof
      (* p: a=b -> False
         goal: b=a -> False
       *)
      fun q:b=a => p (flip q).

    Theorem use_bwd {a b:A} (eq:a=b) (T:A->Type) (pb:T b): T a.
    Proof
      use (flip eq) T pb.

    Theorem
      rewrite_bwd {a b:A} (P:A->Type) (p:a = b) (pb:P b): P a.
    Proof
      rewrite  P (flip p) pb.


    Definition Decider: Type := forall a b:A, {a = b} + {a <> b}.
  End equal_basics.

  Section application.
    Variables A B: Type.
    Theorem application:
      forall (f g: A -> B) (a b:A), f = g -> a = b -> f a = g b.
    Proof
      fun f g a b eqfg eqab =>
        join
          ((join
             (eq_refl: f a = f a)
             (inject eqab _: f a = f b)): f a = f b)
          (rewrite0 eqfg (fun g => f b = g b) eq_refl: f b = g b).
  End application.

  Module Notations.
    Notation "( 'equality_chain:' x , y , .. , z )" :=
      (Equal.join .. (Equal.join x y) .. z) (at level 0): equality_scope.

    Notation "( 'equal_arguments:' eq1 , .. , eqn )" :=
      (Equal.application .. (Equal.application eq_refl eq1) .. eqn)
        (at level 0): equality_scope.
    Open Scope equality_scope.
  End Notations.
End Equal.





(** * Predicate *)
(*    ========= *)

(** A predicate represents an arbitrary set of elements of a certain type.*)

Module Predicate.
  Section predicate_basic.
    Variable A: Type.

    Definition Decider (P:A->Prop): Type :=
      forall a:A, {P a} + {~ P a}.

    Definition Empty     (P:A->Prop): Prop := False.
    Definition Universal (P:A->Prop): Prop := True.

    Definition Add (a:A) (P:A->Prop): A->Prop :=
      fun x => x = a \/ P x.

    Definition Remove (a:A) (P:A->Prop): A->Prop :=
      fun x => x <> a /\ P x.

    Definition Union (P Q:A->Prop): A->Prop :=
      fun x => P x \/ Q x.

    Definition Intersection (P Q:A->Prop): A->Prop :=
      fun x => P x /\ Q x.

    Definition Subset (P Q:A->Prop): Prop :=
      forall x, P x -> Q x.

    Definition Not (P:A->Prop): A->Prop :=
      fun x => ~ (P x).
  End predicate_basic.
End Predicate.




(** * Relations *)
(*    ========= *)

Module Relation.
  Section binary_relation.
    Variable A B: Type.
    Variable R: A -> B -> Prop.

    Definition Decider: Type := forall (a:A) (b:B), {R a b} + {~ R a b}.

    Definition Domain (a:A): Prop :=
      exists b:B, R a b.

    Definition Range (b:B): Prop :=
      exists a:A, R a b.

    Definition Left_total: Prop :=
      forall a, Domain a.

    Definition Right_total: Prop :=
      forall b, Range b.

    Definition Total: Prop :=
      Left_total /\ Right_total.

    Theorem total_all_in_domain:
      Total -> forall a, Domain a.
    Proof
      fun total a =>
        match total with
        | conj left_total _ =>
          left_total a
        end.

    Theorem total_all_in_range:
      Total -> forall a, Range a.
    Proof
      fun total a =>
        match total with
        | conj _ right_total =>
          right_total a
        end.

    Definition Sub (S:A->B->Prop): Prop :=
      forall x y, R x y -> S x y.

  End binary_relation.



  Section endorelation.
    Variable A:Type.
    Variable R: A -> A -> Prop.

    Definition Reflexive: Prop :=
      forall a:A, R a a.

    Definition Transitive: Prop :=
      forall a b c:A, R a b -> R b c -> R a c.

    Definition Symmetric: Prop :=
      forall a b:A, R a b -> R b a.

    Definition Antisymmetric: Prop :=
      forall a b:A, R a b -> R b a -> a = b.

    Definition Complete: Prop :=
      forall a b:A, R a b \/ R b a.

    Theorem complete_is_reflexive:
      Complete -> Reflexive.
    Proof
      fun d a =>
        match d a a with
          or_introl p => p
        | or_intror p => p
        end.

    Inductive Comparison2 (a b:A): Set :=
    | less_equal:    R a b -> Comparison2 a b
    | greater_equal: R b a -> Comparison2 a b.

    Inductive Comparison3 (a b:A): Set :=
    | less_than: R a b -> Comparison3 a b
    | equivalent: R a b -> R b a  -> Comparison3 a b
    | greater_than: R b a -> Comparison3 a b.

    Definition Comparer2: Type := forall a b:A, Comparison2 a b.
    Definition Comparer3: Type := forall a b:A, Comparison3 a b.

    Theorem comparable2_is_complete:
      forall (c:Comparer2), Complete.
    Proof
      fun c a b =>
        match c a b with
        | less_equal    p => or_introl p
        | greater_equal p => or_intror p
        end.

    Theorem comparable3_is_complete:
      forall (c:Comparer3), Complete.
    Proof
      fun c a b =>
        match c a b with
        | less_than p => or_introl p
        | equivalent p1 p2 => or_introl p1
        | greater_than p => or_intror p
        end.
  End endorelation.

  Arguments less_than    [_] [_] [_] [_] _.
  Arguments equivalent   [_] [_] [_] [_] _ _.
  Arguments greater_than [_] [_] [_] [_] _.
  Arguments less_equal    [_ _ _ _]  _.
  Arguments greater_equal [_ _ _ _]  _.

  Section well_founded_relation.
    Variable A:Type.
    Variable R: A -> A -> Prop.
    Theorem wf_subrelation:
      forall (S:A->A->Prop),
        Sub S R -> well_founded R -> well_founded S.
    Proof
      fun S sub =>
        let lemma: forall x, Acc R x -> Acc S x :=
            fix f x accRx {struct accRx}: Acc S x:=
              match accRx with
                Acc_intro _ pr =>
                (* pr: forall y, R y x -> Acc R y All direct conclusions of 'pr'
                 are syntactically smaller than 'accRx', i.e. can be used to
                 recursively call 'f'.  *)
                Acc_intro
                  _
                  (fun y Syx =>
                     let Ryx: R y x := sub y x Syx in
                     let accRy: Acc R y := pr y Ryx in
                     let accSy: Acc S y := f y accRy in
                     f y accRy)
              end
        in
        fun wfR a => lemma a (wfR a).
  End well_founded_relation.

  Section order_relation.
    Variable A:Type.
    Variable R: A -> A -> Prop.

    Definition Preorder: Prop :=
      Reflexive R /\ Transitive R.

    Definition Linear_preorder: Prop :=
      Complete R /\ Transitive R.

    Definition Partial_preorder: Prop :=
      Reflexive R /\ Transitive R /\ Antisymmetric R.

    Definition Linear_order: Prop :=
      Complete R /\ Transitive R /\ Antisymmetric R.

    Definition Equivalence: Prop :=
      Reflexive R /\ Transitive R /\ Symmetric R.
  End order_relation.
End Relation.


(** * Either: Two Possible Results *)
(*    ============================ *)
Module Either.
  Inductive t (A B:Type): Type :=
  | Left:  A -> t A B
  | Right: B -> t A B.
  Arguments Left   [A] [B] _.
  Arguments Right  [A] [B] _.
End Either.




(** * Tristate: Three Possible Results *)
(*    ================================ *)
Module Tristate.
  Inductive t (A B C:Type): Type :=
  | Left:   A -> t A B C
  | Middle: B -> t A B C
  | Right:  C -> t A B C.
  Arguments Left   [A] [B] [C] _.
  Arguments Middle [A] [B] [C] _.
  Arguments Right  [A] [B] [C] _.
End Tristate.




(** * Any Type *)
(*    ======== *)
Module Type ANY.
  Parameter t: Set.
End ANY.


(** * Sortable Types *)
(*    ============== *)
Module Type SORTABLE <: ANY.
  Import Relation.

  Parameter t: Set.
  Parameter Less_equal: t -> t -> Prop.

  Axiom transitive: Transitive  Less_equal.

  Parameter compare2: Comparer2 Less_equal.
  Parameter compare3: Comparer3 Less_equal.
End SORTABLE.

Module Sortable_plus (S:SORTABLE).
  Import Relation.
  Include S.

  Definition Equivalent (a b:t): Prop := Less_equal a  b /\ Less_equal b a.

  Theorem complete: Complete Less_equal.
  Proof
    comparable2_is_complete compare2.

  Theorem reflexive: Reflexive Less_equal.
  Proof
    complete_is_reflexive complete.

  Module Notations.
    Notation "a <= b"  := (Less_equal a b) (at level 70).
    Notation "( 'transitivity_chain:' x , y , .. , z )" :=
      (transitive .. (transitive x y) .. z) (at level 0).
  End Notations.
End Sortable_plus.


(** * Finite Set *)
(*    ========== *)
Module Type FINITE_SET.
  Import Predicate.
  Parameter A: Set.
  Parameter T: Set->Set.

  Parameter Domain: T A -> A -> Prop.

  Parameter is_in:
    forall (a:A) (s:T A), {Domain s a} + {~ Domain s a}.

  Parameter empty:
    {s:T A | forall a, ~ Domain s a}.

  Parameter add:
    forall (a:A) (s:T A), {t:T A| Domain t = Add a (Domain s)}.

  Parameter remove:
    forall (a:A) (s:T A), {t:T A| Domain t = Remove a (Domain s)}.
End FINITE_SET.




(** * Finite Map *)
(*    ========== *)
Module Type FINITE_MAP.
End FINITE_MAP.
