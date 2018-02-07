Set Implicit Arguments.

(** * Axioms *)
(*    ====== *)
Section axioms.
  Section axiom_definitions.
    Axiom excluded_middle:
      forall A:Prop, A \/ ~ A.

    Axiom proof_irrelevance:
      forall (A:Prop) (p q:A), p = q.

    Axiom dependent_function_equality:
      forall (A:Type) (B:A->Type) (f g: forall x, B x),
        (forall x, f x = g x) -> f = g.
  End axiom_definitions.

  Section axiom_consequences.
    Theorem function_equality:
      forall (A B:Type) (f g:A->B),
        (forall x, f x = g x) -> f = g.
    Proof
      fun A B f g p =>
        dependent_function_equality (fun _ => B) f g p.
  End axiom_consequences.
End axioms.




(** * Standard Types *)
(*    ============== *)

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].


(** * Equality *)
(*    ======== *)
Module Equal.
  Section equal_basics.
    Variables A B: Type.

    Theorem
      rewrite (a b:A) (p:a = b) (P:A->Prop) (pa:P a): P b.
    Proof
      match p in (_ = x) return P x with
      | eq_refl => pa
      end.

    Theorem
      inject (a b:A) (p:a=b) (f:A->B): f a = f b.
    Proof
      match p in (_ = x) return f a = f x with
      | eq_refl => eq_refl
      end.


    Theorem
      flip (a b:A) (p:a=b): b=a.
    Proof
      rewrite p (fun x => x=a) eq_refl.

    Theorem
      join (a b c:A) (pab:a=b) (pbc:b=c): a=c.
    Proof
      rewrite pbc (fun x => a=x) pab.

    Theorem
      flip_not_equal (a b:A) (p:a<>b): b<>a.
    Proof
      (* p: a=b -> False
         goal: b=a -> False
       *)
      fun q:b=a => p (flip q).


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
  | left:  forall a:A, t A B
  | right: forall b:B, t A B.
End Either.




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



(** * Natural Numbers *)
(*    ================ *)

Module Nat.
  (** ** Basic Facts about Natural Numbers *)
  (*     ================================= *)
  Section nat_basics.
    Definition is_Successor (n:nat): Prop :=
      match n with
      | 0 => False
      | S _ => True
      end.

    Definition predecessor (n:nat) (p:is_Successor n): {x:nat|S x = n} :=
      (match n with
      | 0 => fun p:is_Successor 0 => match p with end
      | S m => fun _ => exist _ m eq_refl
      end) p.


    Theorem successor_not_zero:
      forall n:nat, S n <> 0.
    Proof
      fun n (p: S n = 0) =>
        (* Use the propositon 'is_Successor' which is trivially provable for 'S n'
         and rewrite 'S n' into '0' by using 'p' and generate a proof for
         'False'. With that we get 'S n = 0 -> False' which is the required
         result. *)
        Equal.rewrite p is_Successor I.


    Definition is_zero (n:nat): {n = 0} + {n <> 0} :=
      match n with
      | 0   => left eq_refl
      | S n => right (@successor_not_zero n)
      end.

    Theorem successor_injective:
      forall n m:nat, S n = S m -> n = m.
    Proof
      fun n m p =>
        let f x := match x with
                     O => n
                   | S y => y end in
        Equal.inject p f.



    Theorem
      successor_different (n:nat): n <> S n.
    Proof
      let f :=
          fix f n: S n <> n:=
            match n with
            | O =>
              fun p:S 0 = 0 => (@successor_not_zero 0) p
            | S k =>
              fun p: S (S k) = S k =>
                f k (successor_injective p: S k = k)
            end
      in
      Equal.flip_not_equal (f n).

    Definition is_equal: forall a b:nat, {a = b} + {a <> b} :=
      fix f a b: {a = b} + {a <> b} :=
        match a, b with
        | O, O => left eq_refl
        | S n, O => right (@successor_not_zero n)
        | O, S n => right (Equal.flip_not_equal (@successor_not_zero n))
        | S n, S k =>
          match f n k: {n = k} + {n <> k} with
          | left p =>
            left (Equal.inject p S)
          | right p => (* p: n = k -> False *)
            right (fun q:S n = S k =>
                     p (successor_injective q:n = k))
          end
        end.
  End nat_basics.





  (** ** Order Structure of Natural Numbers *)
  (*     ================================== *)
  Section nat_order.

    Theorem zero_is_least:
      forall n, 0 <= n.
    Proof
      fix f n: 0 <= n :=
      match n with
      | 0 => le_n 0
      | S k => le_S 0 k (f k)
      end.


    Theorem successor_not_below_zero:
      forall n:nat, ~ S n <= 0  (* S n <= 0 -> False *).
    Proof
      let f: forall (n m:nat) (p: S n <= m), m <> 0 :=
          fun n m p =>
            match p with
            | le_n _ => @successor_not_zero n: S n <> 0
            | le_S _ k pk => @successor_not_zero k: S k <> 0
            end
      in
      fun n p => f n 0 p eq_refl.


    Theorem below_zero_is_zero:
      forall n:nat, n <= 0 -> n = 0.
    Proof
      fix f n: n <= 0 -> n = 0 :=
      match n with
      | 0 => fun p => eq_refl
      | S k =>
        (* goal S k <= 0 -> S k = 0 *)
        fun p: S k <= 0 =>
          match successor_not_below_zero p with end
      end.



    Theorem successor_monotonic_le:
      forall (n m:nat), n <= m -> S n <= S m.
    Proof
      fix f n m (p:n<=m): S n <= S m :=
      match p with
      | le_n _ => le_n (S n)
      | le_S _ k pk => (* goal: S n <= S (S k) *)
        let hypo: S n <= S k := f n k pk in
        le_S (S n) (S k) hypo
      end.


    Theorem predecessor_monotonic_le:
      forall n m:nat, n <= m -> pred n <= pred m.
    Proof
      fix f n m p: pred n <= pred m :=
      match p with
      | le_n _ =>
        (* goal: pred n <= pred n *)
        le_n (pred n)
      | le_S _ k pk =>
        (* goal: pred n <= pred (S k),
           proof: Construct a function with type n <= k -> pred n <= pred (S k)
                  and apply it to pk which has type n <= k. The function does a
                  pattern match on k. For k=0, n has to be zero as well. For
                  k = S l use f to generate an induction hypothesis.
         *)
        (match k with
         | O =>
           fun q0:n<=0 =>
             Equal.rewrite
               (Equal.flip (below_zero_is_zero q0: n = 0))
               (fun x => pred x <= pred (S 0))
               (le_n (pred 0))
         | S l =>
           fun ql: n <= S l =>
             let hypo := f n (S l) ql: pred n <= pred (S l) (* ind hypo *)
             in
             le_S (pred n) (pred (S l)) hypo
         end) pk
      end.


    Theorem cancel_successor_le:
      forall n m:nat, S n <= S m -> n <= m.
    Proof
      fun n m p =>
        predecessor_monotonic_le p.



    Theorem successor_not_le:
      forall (n:nat), ~ S n <= n.
    Proof
      fix f n: ~S n <= n :=
      match n with
      | 0 => @successor_not_below_zero 0
      | S k => fun p => f k (cancel_successor_le p)
      end.



    Theorem lt_implies_le:
      forall (n m:nat), n < m -> n <= m.
    Proof
      fix f n m lt: n <= m :=
      match lt with
      | le_n _ => le_S n n (le_n _)
      | le_S _ k pk => le_S n k (f n k pk)
      end.


    Theorem lt_implies_ne:
      forall (n m:nat), n < m -> n <> m.
    Proof
      fun n m lt eq =>
        let n_lt_n: n < n := Equal.rewrite (Equal.flip eq) _ lt in
        successor_not_le n_lt_n.



    Theorem le_ne_implies_lt:
      forall (n m:nat), n <= m -> n <> m -> S n <= m.
    Proof
      fun n m le =>
        match le with
        | le_n _ => fun n_ne_n => match n_ne_n eq_refl with end
        | le_S _ x p => fun _ => successor_monotonic_le p
        end.


    Theorem transitive:
      forall (n m k:nat), n <= m -> m <= k -> n <= k.
    Proof
      fix f n m k nm mk: n <= k :=
      match mk with
      | le_n _ => nm
      | le_S _ l ml =>
        let nl: n <= l := f n m l nm ml in
        le_S n l nl
      end.


    Theorem lt_irreflexive:
      forall n:nat, ~ n < n.
    Proof
      fun n (nn: n < n) =>
        lt_implies_ne nn eq_refl.


    Theorem antisymmetric:
      forall (n m:nat), n <= m -> m <= n -> n = m.
    Proof
      fun n m nm =>
      match nm with
      | le_n _ => fun _ => eq_refl
      | le_S _ k nk =>
        fun Skn: S k <= n =>
          let Skk: k < k := transitive Skn nk in
          match lt_irreflexive Skk with end
      end.

    Definition is_less_equal_bool: forall a b:nat, bool :=
      fix r a b: bool :=
        match a with
        | 0 => true
        | S k =>
          match b with
          | 0 => false
          | S n => r k n
          end
        end.


    Definition is_less_equal: forall a b:nat, {a <= b} + {~ a <= b} :=
      fix r a b: {a <= b} + {~ a <= b} :=
        match a with
        | O => left (zero_is_least b)
        | S k =>
          match b with
          | O => right(@successor_not_below_zero k)
          | S n => (* goal: {S k <= S n} + {~ S k <= S n} *)
            match r k n: {k <= n} + {~ k <= n} with
            | left  p => left(@successor_monotonic_le k n p)
            | right p => (* p:~ k <= n *)
              right( fun q: S k <= S n =>
                       p (cancel_successor_le q: k <= n)
                   )
            end
          end
        end.
  End nat_order.



  (** ** Order Predicates *)
  (*     ================= *)
  Section nat_order_predicates.
    Definition Lower_bound (P:nat->Prop): nat->Prop :=
      fun n => forall m, P m -> n <= m.

    Definition Strict_lower_bound (P:nat->Prop): nat->Prop :=
      fun n => Lower_bound P n /\ ~ P n.

    Definition Upper_bound (P:nat->Prop): nat->Prop :=
      fun n => forall m, P m -> m <= n.

    Definition Strict_upper_bound (P:nat->Prop): nat->Prop :=
      fun n => Upper_bound P n /\ ~ P n.

    Definition Least (P:nat->Prop): nat->Prop :=
      fun n => P n /\ Lower_bound P n.

    Definition Greatest (P:nat->Prop): nat->Prop :=
      fun n => P n /\ Upper_bound P n.

    Definition Supremum (P:nat->Prop): nat->Prop :=
      fun n => Least (Upper_bound P) n.

    Definition Infimum (P:nat->Prop): nat->Prop :=
      fun n => Greatest (Lower_bound P) n.

    Theorem successor_strict_lower_bound:
      forall (n:nat) (P:nat->Prop) (slb:Strict_lower_bound P n),
        Lower_bound P (S n).
    Proof
      fun n P slb =>
        (* goal: Lower_bound P (S n)
           Expanded goal: forall m, P m -> S n <= m
           S n <= m is by definition equivalent to n < m.
           We know forall m, P m -> n <= m and ~ (P n). We have to prove that
           S n <= m is valid as well. If P m is valid then m must be different
           from n because n does not satisfy the predicate. I.e. we have n <= m
           and n <> m which is sufficient to prove S n <= m.
         *)
        match slb with
          conj lb pnot =>
          fun m mP =>
            let n_ne_m: n <> m :=
                fun n_eq_m =>
                  match pnot (Equal.rewrite (Equal.flip n_eq_m)  _ mP)
                  with end
            in
            le_ne_implies_lt (lb m mP)  n_ne_m
        end.
  End nat_order_predicates.



  (** ** Wellfounded Relation: lt *)
  (*     ======================== *)
  Section nat_wellfounded.
    Theorem well_founded_lt: well_founded lt.
    Proof
      fix f (n:nat): Acc lt n :=
      match n with
      | 0 =>
        (* i < j is defined as (S i) <= j. A predecessor of 0 must satisfy i <
           0, i.e. (S i) <= 0 which is impossible because of
           'successor_not_below_zero' *)
        Acc_intro
          _
          (fun j pj_lt_0 =>
             match Nat.successor_not_below_zero pj_lt_0 with end)
      | S k =>
        (* Goal: Acc lt (S k). S k must be accessible. In order to prove that
           we have to prove that all predecessors of S k are accessible. The
           predecessors of S k are k and all predecessors of k. By calling f k
           we get a proof that all k is accessible which we can pattern match
           to get a proof that all predecessors of k are accessible as well.
         *)
        let pk: Acc lt k := f k in
        match pk with
          Acc_intro _ p =>
          Acc_intro
            _
            (fun j (pj_lt_Sk:S j <= S k) =>
               match Nat.is_equal j k with
               | left p_eq_jk =>
                 Equal.rewrite (Equal.flip p_eq_jk) _ pk
               | right p_ne_jk =>
                 let pj_le_k: j <= k := Nat.cancel_successor_le pj_lt_Sk in
                 let pj_lt_k: j < k  := Nat.le_ne_implies_lt pj_le_k p_ne_jk in
                 p j pj_lt_k
               end)
        end
      end.
  End nat_wellfounded.





  (** ** Arithmetic *)
  (*     ========== *)
  Section nat_arithmetic.
    Theorem successor_into_plus:
      forall (n m:nat), S (n + m) = n + S m.
    Proof
      fix f n: forall m, S (n + m) = n + S m :=
      match n with
      | 0 =>
        fun m =>
          let p: S (0 + m) = 0 + S m := Equal.inject (eq_refl:0 + m = m) S in
          p
      | S k =>
        fun m => Equal.inject (f k m) S

      end.

    Theorem n_plus_zero_eq_n:
      forall (n:nat), n + 0 = n.
    Proof
      fix f n: n + 0 = n :=
      match n with
      | 0 => eq_refl
      | S k =>
        (* goal S k + 0 = S k,
       hypo k + 0   = k *)
        Equal.inject (f k) S
      end.
  End nat_arithmetic.

  (** ** Element Search *)
  (*     ============== *)
  Section nat_search.
    Definition
      search_below (P:nat->Prop) (n:nat) (d:Predicate.Decider P)
    : sig (Least P) + {Lower_bound P n}
      :=
        let LB := Lower_bound P in
        let Fail := LB n in
        let OK := sig (Least P) in
        (fix f i: forall k (p:i+k=n) (lbk:LB k), OK + {Fail} :=
           match i with
           | 0 => fun k (eqkn:0+k=n) lbk =>
                    inright (Equal.rewrite eqkn LB lbk)
           | S j =>
             fun k (eqSjkn:S j + k = n) lbk =>
               match d k with
               | left pk => (* found least element k satisfying P *)
                 inleft (exist _ k (conj pk lbk))
               | right notpk =>
                 let SLB := Strict_lower_bound P in
                 let slbk : SLB k := conj lbk notpk in
                 let lbSk: LB (S k) := successor_strict_lower_bound slbk in
                 let eqjSkn: j + S k = n :=
                     Equal.rewrite
                       (successor_into_plus j k)
                       (fun x => x = n)
                       eqSjkn
                 in
                 f j (S k) eqjSkn lbSk
               end
           end
        )
          n 0 (n_plus_zero_eq_n n) (fun x _ => zero_is_least x).
  End nat_search.

  Module Notations.
    Notation "x =? y" :=
      (is_equal x y) (at level 70, no associativity) : nat_scope.
    Open Scope nat_scope.
    Notation "x <=? y" :=
      (is_less_equal x y) (at level 70, no associativity) : nat_scope.
    Open Scope nat_scope.
  End Notations.
End Nat.
