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
  Theorem make3 {A B C:Prop} (a:A) (b:B) (c:C) : A /\ B /\ C.
  Proof
    conj a (conj b c).

  Theorem make4 {A B C D:Prop} (a:A) (b:B) (c:C) (d:D) : A /\ B /\ C /\ D.
  Proof
    conj a (conj b (conj c d)).

  Theorem use {A B C:Prop} (p:A/\B) (f:A->B->C): C.
  Proof
    match p with
      conj a b => f a b
    end.

  Theorem use3 {A B C D:Prop} (p:A/\B/\C) (f:A->B->C->D): D.
  Proof
    match p with
      conj a (conj b c) => f a b c
    end.

  Theorem use4 {A B C D E:Prop} (p:A/\B/\C/\D) (f:A->B->C->D->E): E.
  Proof
    match p with
      conj a (conj b (conj c d)) => f a b c d
    end.

  Theorem use8
          {A B C D E F G H R:Prop}
          (p:A/\B/\C/\D/\E/\F/\G/\H)
          (q:A -> B -> C -> D -> E -> F -> G -> H -> R) : R.
  Proof
    match p with
      conj a (conj b (conj c (conj d (conj e (conj f (conj g h)))))) =>
      q a b c d e f g h
    end.

  Theorem use9
          {A B C D E F G H K R:Prop}
          (p:A/\B/\C/\D/\E/\F/\G/\H/\K)
          (q:A -> B -> C -> D -> E -> F -> G -> H -> K -> R) : R.
  Proof
    match p with
      conj a (conj b (conj c (conj d (conj e (conj f (conj g (conj h k))))))) =>
      q a b c d e f g h k
    end.

  Theorem proj1 {A B:Prop} (p:A/\B): A.
  Proof
    use p (fun a b => a).

  Theorem proj2 {A B:Prop} (p:A/\B): B.
  Proof
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
    Variables A B C: Type.

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

    Theorem use3 {a1 b1:A} {a2 b2:B} {a3 b3:C}
            (eq1:a1=b1) (eq2:a2=b2) (eq3:a3=b3) (T:A->B->C->Type) (p: T a1 a2 a3)
      : T b1 b2 b3.
    Proof
      match eq1 with
        eq_refl =>
        match eq2 with
          eq_refl =>
          match eq3 with
            eq_refl => p
          end
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

    Theorem inject2 {a1 a2:A} {b1 b2:B}
            (pa:a1=a2) (pb:b1=b2) (f:A->B->C): f a1 b1 = f a2 b2.
    Proof
      match pa in (_ = x), pb in (_ = y) return f a1 b1 = f x y with
        eq_refl, eq_refl => eq_refl
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

    Definition Empty     (P:A->Prop): Prop := forall x, ~ P x.
    Definition Universal (P:A->Prop): Prop := forall x, P x.

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
  Section basics.
    Definition Binary (A:Type) (B:Type):Type := A -> B -> Prop.
    Definition Endo   (A:Type) :Type := A -> A -> Prop.
  End basics.

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

    Definition is_Partial_function: Prop :=
      forall x y z,
        R x y ->
        R x z ->
        y = z.
  End binary_relation.



  Section endorelation.
    Variable A:Type.

    Definition Reflexive (R:Endo A): Prop :=
      forall a:A, R a a.

    Definition Transitive (R:Endo A): Prop :=
      forall a b c:A, R a b -> R b c -> R a c.

    Definition Symmetric (R:Endo A): Prop :=
      forall a b:A, R a b -> R b a.

    Definition Antisymmetric (R:Endo A): Prop :=
      forall a b:A, R a b -> R b a -> a = b.

    Definition Complete (R:Endo A): Prop :=
      forall a b:A, R a b \/ R b a.

    Theorem complete_is_reflexive:
      forall (R:Endo A), Complete R -> Reflexive R.
    Proof
      fun R d a =>
        match d a a with
          or_introl p => p
        | or_intror p => p
        end.

    Inductive Comparison2 (R:Endo A) (a b:A): Set :=
    | LE:  R a b -> Comparison2 R a b
    | GE:  R b a -> Comparison2 R a b.

    Inductive Comparison3 (R:Endo A) (a b:A): Set :=
    | LT:  R a b -> ~ R b a -> Comparison3 R a b
    | EQV: R a b -> R b a   -> Comparison3 R a b
    | GT:  R b a -> ~ R a b -> Comparison3 R a b.

    Definition Comparer2 (R:Endo A): Type :=
      forall a b:A, Comparison2 R a b.

    Definition Comparer3 (R:Endo A): Type :=
      forall a b:A, Comparison3 R a b.

    Theorem comparable2_is_complete:
      forall (R:Endo A) (c:Comparer2 R), Complete R.
    Proof
      fun R c a b =>
        match c a b with
        | LE _ _ _ p => or_introl p
        | GE _ _ _ p => or_intror p
        end.

    Theorem comparable3_is_complete:
      forall (R:Endo A) (c:Comparer3 R), Complete R.
    Proof
      fun R c a b =>
        match c a b with
        | LT  _ _ _ p _   => or_introl p
        | EQV _ _ _ p1 p2 => or_introl p1
        | GT  _ _ _ p _   => or_intror p
        end.

    Section closures.
      Inductive Plus (R:Endo A): Endo A :=
      | plus_start: forall x y, R x y -> Plus R x y
      | plus_next:  forall x y z, Plus R x y -> R y z -> Plus R x z.
      Arguments plus_start   [_ _ _] _.
      Arguments plus_next    [_ _ _ _] _ _.


      Theorem use_plus:
        forall {R:Endo A} {x y:A} (p:Plus R x y) (P: Endo A),
          (forall x y, R x y -> P x y)
          -> (forall x y z, Plus R x y -> R y z -> P x y -> P x z)
          -> P x y.
      Proof
        fix f R x y pxy P :=
        match pxy with
        | plus_start rab => fun f1 f2 => f1 _ _ rab
        | plus_next  pab rbc =>
          fun f1 f2 =>
            f2 _ _ _ pab rbc
               (f _ _ _ pab P f1 f2)
        end.

      Theorem plus_transitive:
        forall (R:Endo A), Transitive (Plus R).
      Proof
        fun R a b c plus_ab plus_bc =>
          let P b c := forall a, Plus R a b -> Plus R a c in
          (use_plus
             plus_bc
             P
             (fun b c rbc a plus_ab => plus_next plus_ab rbc)
             (fun b c d plus_bc (rcd: R c d)
                  (ihbc:forall a, Plus R a b -> Plus R a c)
                  a
                  (plus_ab: Plus R a b) =>
                plus_next (ihbc a plus_ab) rcd)
           :P b c) a plus_ab.



      Inductive Star (R:Endo A): Endo A :=
      | star_start: forall x, Star R x x
      | star_next:  forall x y z, Star R x y -> R y z -> Star R x z.
      Arguments star_start   [_] _.
      Arguments star_next    [_ _ _ _] _ _.

      Theorem use_star:
        forall {R:Endo A} {x y:A} (p:Star R x y) (P: Endo A),
          (forall x, P x x)
          -> (forall x y z, Star R x y -> R y z -> P x y -> P x z)
          -> P x y.
      Proof
        fix f R x y xy P :=
        match xy with
        | star_start a => fun f1 f2 => f1 a
        | star_next  pab rbc =>
          fun f1 f2 =>
            f2 _ _ _ pab rbc
               (f R _ _ pab P f1 f2)
        end.

      Theorem star_transitive:
        forall (R:Endo A), Transitive (Star R).
      Proof
        fun R a b c star_ab star_bc =>
          let P b c := forall a, Star R a b -> Star R a c in
          (use_star
             star_bc
             P
             (fun x _ p => p)
             (fun b c d star_bc rcd ih_bc a star_ab =>
                star_next (ih_bc a star_ab) rcd)
           :P b c) a star_ab.



      Inductive Equi_close (R:A -> A -> Prop): A -> A -> Prop :=
      | equi_start: forall x, Equi_close R x x
      | equi_fwd:   forall x y z, Equi_close R x y -> R y z -> Equi_close R x z
      | equi_bwd:   forall x y z, Equi_close R x y -> R z y -> Equi_close R x z.
      Arguments equi_start   [_] _.
      Arguments equi_fwd    [_ _ _ _] _ _.
      Arguments equi_bwd    [_ _ _ _] _ _.

      Theorem use_equi_close:
        forall {R:Endo A} {x y} (p:Equi_close R x y) (P:Endo A),
          (forall x, P x x)
          -> (forall x y z, R y z -> P x y -> P x z)
          -> (forall x y z, R z y -> P x y -> P x z)
          -> P x y.
      Proof
        fix f R x y xy P :=
        match xy with
        | equi_start a => fun f1 f2 f3 => f1 a
        | equi_fwd pab rbc =>
          fun f1 f2 f3 =>
            f2 _ _ _ rbc (f R _ _ pab P f1 f2 f3)
        | equi_bwd pab rcb =>
          fun f1 f2 f3 =>
            f3 _ _ _ rcb (f R _ _ pab P f1 f2 f3)
        end.

      Theorem equi_close_transitive:
        forall (R:Endo A), Transitive (Equi_close R).
      Proof
        fun R a b c eab ebc =>
          let P b c := forall a, Equi_close R a b -> Equi_close R a c
          in
          (use_equi_close
             ebc
             P
             (fun x c p => p)
             (fun b c d rcd pbc a eab =>
                equi_fwd (pbc a eab: Equi_close R a c) (rcd: R c d))
             (fun b c d rdc pbc a eab =>
                equi_bwd (pbc a eab: Equi_close R a c) (rdc: R d c))
          ) a eab.

      Theorem equi_close_symmetric:
        forall (R:Endo A), Symmetric (Equi_close R).
      Proof
        fun R =>
          let lemma1 a b (rab:R a b): Equi_close R a b :=
              equi_fwd (equi_start a) rab
          in
          let lemma2 a b (rab:R a b): Equi_close R b a :=
              equi_bwd (equi_start b) rab
          in
          fun a b equi_ab =>
            let P a b := Equi_close R b a in
            use_equi_close
              equi_ab
              (fun a b => Equi_close R b a)
              (fun x => equi_start x)
              (fun x y z ryz (ihxy: Equi_close R y x) =>
                 equi_close_transitive
                   (lemma2 y z ryz:Equi_close R z y)
                   (ihxy:Equi_close R y x)
                 :Equi_close R z x)
              (fun x y z rzy (ihxy: Equi_close R y x) =>
                 equi_close_transitive
                   (lemma1 z y rzy:Equi_close R z y)
                   (ihxy:Equi_close R y x)
                 :Equi_close R z x)
              .
    End closures.
  End endorelation.

  Arguments LT    [_] [_] [_] [_] _.
  Arguments EQV   [_] [_] [_] [_] _ _.
  Arguments GT    [_] [_] [_] [_] _.
  Arguments LE    [_ _ _ _]  _.
  Arguments GE    [_ _ _ _]  _.

  Arguments star_start   [_ _] _.
  Arguments star_next    [_ _ _ _ _] _ _.

  Section well_founded_relation.
    Variable A:Type.
    Variable R: A -> A -> Prop.

    Variable P: A -> Prop.

    Theorem accessible_induction:
      (forall x, Acc R x -> (forall y, R y x ->  P y) -> P x)
      ->
      forall x, Acc R x -> P x.
    Proof
      fun hypo =>
        (fix f x acc_x :=
           match acc_x with
             Acc_intro _ h =>
             hypo x acc_x (fun y Ryx => f y (h y Ryx))
           end
        )
    .


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

  Section diamond.
    Variable A:Type.

    Definition Diamond (R:Endo A): Prop :=
      forall a b c, R a b -> R a c -> exists d, R b d /\ R c d.

    Theorem use_diamond
            {R:Endo A}
            (dia:Diamond R) (a b c:A) (rab:R a b) (rac:R a c)
            (P:Prop)
            (f:forall d, R b d -> R c d -> P): P.
    Proof
      match dia a b c rab rac with
      | ex_intro _ d (conj rbd rcd) =>
        f d rbd rcd
      end.

    Definition Confluent (R:Endo A): Prop :=
      Diamond (Star R).


    Theorem use_confluent
            {R:Endo A}
            (confl:Confluent R) (a b c:A) (sab: Star R a b) (sac: Star R a c)
            (P: Prop)
            (f: forall d, Star R b d -> Star R c d -> P): P.
    Proof
      use_diamond confl a b c sab sac f.

    Theorem confluent_equivalent_meet:
      forall {R:Endo A} {a b:A},
        Confluent R ->
        Equi_close R a b ->
        exists c, Star R a c /\ Star R b c.
    Proof
      fun R a b confl e_ab =>
        let P a b := exists c, Star R a c /\ Star R b c in
        let useP a b (pab:P a b)
                 (B:Prop) (f:forall c, Star R a c -> Star R b c -> B): B :=
            match pab with
            | ex_intro _ c (conj sac sbc) =>
              f c sac sbc
            end
        in
        use_equi_close
          e_ab
          P
          (fun x =>
             let star_xx: Star R x x := star_start x in
             ex_intro _ x (conj star_xx star_xx))
          (fun a b c rbc ih_ab =>
             (* a  ->eq   b     ->     c
                  \       |            |
                   \*     v*           v*
                    >  some d  ->*   some e

                 d exists by induction hypothesis
                 e exists by confluence
              *)
             useP _ _ ih_ab _
                  (fun d star_ad star_bd =>
                     use_confluent
                       confl
                       (star_next (star_start b) rbc)
                       star_bd
                       (fun e star_ce star_de =>
                          ex_intro
                            _ e
                            (conj (star_transitive star_ad  star_de) star_ce))
                  ))
          (fun a b c rcb ih_ab =>
             (* a  ->eq   b     <-     c
                  \       |            |
                   \*     v*           v*
                    >  some d  ->*   some e

                 d exists by induction hypothesis
                 e exists by confluence
              *)
             useP _ _ ih_ab _
                  (fun d star_ad star_bd =>
                     use_confluent
                       confl
                       (star_start c)
                       (star_transitive
                          (star_next (star_start c) rcb)
                          star_bd)
                       (fun e star_ce star_de =>
                          ex_intro
                            _ e
                            (conj (star_transitive star_ad  star_de) star_ce)))
          ).
  End diamond.
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
  Parameter t: Type.
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

  Import Notations.

  Definition max (a b:t): {m:t | a <= m /\ b <= m /\ (m = a \/ m = b)}.
  Proof.
    exact(
        match compare2 a b with
        | LE le =>
          exist _ b (And.make3 le (reflexive b) (or_intror eq_refl))
        | GE ge =>
          exist _ a (And.make3 (reflexive a) ge (or_introl eq_refl))
        end
      ).
  Defined.

  Definition min (a b:t): {m:t | m <= a /\ m <= b /\ (m = a \/ m = b)}.
  Proof.
    exact(
        match compare2 a b with
        | LE le =>
          exist _ a (And.make3 (reflexive a) le (or_introl eq_refl))
        | GE ge =>
          exist _ b (And.make3 ge (reflexive b) (or_intror eq_refl))
        end
      ).
  Defined.
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
    {s:T A | Empty (Domain s)}.

  Parameter add:
    forall (a:A) (s:T A), {t:T A| Domain t = Add a (Domain s)}.

  Parameter remove:
    forall (a:A) (s:T A), {t:T A| Domain t = Remove a (Domain s)}.
End FINITE_SET.




(** * Finite Map *)
(*    ========== *)
Module Type FINITE_MAP.
  Parameter Key: Set.
  Parameter Value: Type.
  Parameter T: Type.
  Parameter empty: T.
  Parameter find: forall (e:Key) (m:T), option Value.
  Parameter add:  forall (e:Key) (v:Value) (m:T), T.
  Axiom empty_is_empty: forall k, find k empty = None.
  Axiom add_is_in:
    forall k v m, find k (add k v m) = Some v.
  Axiom add_others_unchanged:
    forall k1 k2 v m,
      k1 <> k2 ->
      find k2 (add k1 v m) = find k2 m.
End FINITE_MAP.
