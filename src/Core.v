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


(** * Equality *)
(*    ======== *)
Module Equal.
  Section equal_basics.
    Variables A B: Type.

    Theorem
      rewrite (a b:A) (p:a = b) (P:A->Type) (pa:P a): P b.
    Proof
      match p in (_ = x) return P x with
      | eq_refl => pa
      end.

    Theorem
      rewrite2 {a b:A} (P:A->Type) (pa:P a) (p:a = b): P b.
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
      rewrite p (fun x => x=a) eq_refl.

    Theorem
      join (a b c:A) (pab:a=b) (pbc:b=c): a=c.
    Proof
      rewrite pbc (fun x => a=x) pab.

    Theorem
      flip_not_equal {a b:A} (p:a<>b): b<>a.
    Proof
      (* p: a=b -> False
         goal: b=a -> False
       *)
      fun q:b=a => p (flip q).

    Theorem
      rewrite2_backwards {a b:A} (P:A->Type) (pb:P b) (p:a = b): P a.
    Proof
      rewrite2 P pb (flip p).


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
          (rewrite eqfg (fun g => f b = g b) eq_refl: f b = g b).
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

    Inductive Comparison (a b:A): Set :=
    | less_than: R a b -> ~ R b a -> Comparison a b
    | equivalent: R a b -> R b a  -> Comparison a b
    | greater_than: ~ R a b -> R b a -> Comparison a b.

    Definition Comparer: Type := forall a b:A, Comparison a b.

    Theorem comparable_is_complete:
      forall (c:Comparer), Complete.
    Proof
      fun c a b =>
        match c a b with
        | less_than p1 p2 => or_introl p1
        | equivalent p1 p2 => or_introl p1
        | greater_than p1 p2 => or_intror p2
      end.
  End endorelation.

  Arguments less_than    [_] [_] [_] [_] _ _.
  Arguments equivalent   [_] [_] [_] [_] _ _.
  Arguments greater_than [_] [_] [_] [_] _ _.

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

  Parameter compare: Comparer Less_equal.
End SORTABLE.

Module Sortable_plus (S:SORTABLE).
  Import Relation.
  Include S.

  Definition Equivalent (a b:t): Prop := Less_equal a  b /\ Less_equal b a.

  Theorem complete: Complete Less_equal.
  Proof
    comparable_is_complete compare.

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




