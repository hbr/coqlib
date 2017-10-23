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


(** * Equality *)
(*    ======== *)
Module Equal.
  Section equal.
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
  End equal.
End Equal.


Notation "( 'eq_chain:' x , y , .. , z )" :=
  (Equal.join .. (Equal.join x y) .. z) (at level 0): equality_scope.

Section examples.
  Open Scope equality_scope.
  Theorem transfer_equal_notation:
    forall (A:Type) (a b c d:A), a=b -> b=c -> c=d -> a=d.
  Proof
    fun A a b c d pab pbc pcd =>
      (eq_chain:
         pab,
         pbc,
         pcd).
End examples.




(** * Natural Numbers *)
(*    ================ *)

Module Nat.
  (** ** Basic Facts about Natural Numbers *)
  (*     ================================= *)
  Section nat_basics.
    Definition Successor (n:nat): Prop :=
      match n with
      | 0 => False
      | S _ => True
      end.

    Definition predecessor (n:nat): Successor n -> {x:nat|S x = n} :=
      match n return Successor n -> {x:nat|S x = n} with
      | 0 => fun p:Successor 0 =>
               match p with end
      | S m => fun _ => exist (fun x => S x = S m) m eq_refl
      end.


    Theorem successor_not_zero:
      forall n:nat, S n <> 0.
    Proof
      fun n (p: S n = 0) =>
        (* Use the propositon 'Successor' which is trivially provable for 'S n'
         and rewrite 'S n' into '0' by using 'p' and generate a proof for
         'False'. With that we get 'S n = 0 -> False' which is the required
         result. *)
        Equal.rewrite p Successor I.


    Definition is_zero (n:nat): {n = 0} + {n <> 0} :=
      match n as x return {x = 0} + {x <> 0} with
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
            match n return S n <> n with
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
        match a, b return {a = b} + {a <> b} with
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
      fun n =>
        let P k := 0 <= k in
        let p0: 0 <= 0 := le_n 0 in
        let pstep k (pk: 0 <= k): 0 <= S k :=
            (le_S 0) k pk in
        nat_rect P p0 pstep n.

    Theorem successor_not_below_zero:
      forall n:nat, ~ S n <= 0  (* S n <= 0 -> False *).
    Proof
      fun n (p: S n <= 0) =>
        let make_false: 0 = 0 -> False :=
            (match
                p in (_ <= x)         (* p: S n <= 0, therefore x is bound to 0  *)
                return x = 0 -> False (* 0 = 0 -> False, because x is bound to 0 *)
              with
              | le_n _ =>
                (* le_n (S n): S n <= S n *)
                @successor_not_zero n: S n = 0 -> False
              | le_S _ m _ =>
                (* le_S (S n) m pm: S n <= S m *)
                @successor_not_zero m: S m = 0 -> False
              end) in
        make_false eq_refl (* eq_refl proves 0 = 0 *).


    Theorem below_zero_is_zero:
      forall n:nat, n <= 0 -> n = 0.
    Proof
      let P k := k <= 0 -> k = 0 in
      let p0: P 0 :=
          fun _ => eq_refl in
      let p_step k (p:P k): P (S k) :=
          fun q: S k <= 0 =>
            match (successor_not_below_zero q:False) with end
      in
      nat_rect P p0 p_step.


    Theorem successor_monotonic_le:
      forall (n m:nat), n <= m -> S n <= S m.
    Proof
      fix f n m (p:n<=m): S n <= S m :=
      match p in (_ <= x)
            return S n <= S x
      with
      | le_n _ => le_n (S n)
      | le_S _ k pk => (* goal: S n <= S (S k) *)
        let hypo: S n <= S k := f n k pk in
        le_S (S n) (S k) hypo
      end.


    Theorem predecessor_monotonic_le:
      forall a b:nat, a <= b -> pred a <= pred b.
    Proof
      fix f a b p: pred a <= pred b :=
      match p in (_ <= x)
            return pred a <= pred x
      with
      | le_n _ =>
        (* goal: pred a <= pred a *)
        le_n (pred a)
      | le_S _ m pm =>
        (* goal: pred a <= pred (S m),
           proof: Construct a function with type a <= m -> pred a <= pred (S m)
                  and apply it to pm which has type a <= m. The function does a
                  pattern match on m. For m=0, a has to be zero as well. For
                  m = S k use f to generate an induction hypothesis.
         *)
        (match m return a <= m -> pred a <= pred (S m) with
         | O =>
           fun q0:a<=0 =>
             Equal.rewrite
               (Equal.flip (below_zero_is_zero q0: a = 0))
               (fun x => pred x <= pred (S 0))
               (le_n (pred 0))
         | S k =>
           fun qk: a <= S k =>
             let hypo := f a (S k) qk: pred a <= pred (S k) (* ind hypo *)
             in
             le_S (pred a) (pred (S k)) hypo
         end) pm
      end.


    Theorem cancel_successor_le:
      forall a b:nat, S a <= S b -> a <= b.
    Proof
      fun a b p =>
        predecessor_monotonic_le p.


    Definition is_less_equal: forall a b:nat, {a <= b} + {~ a <= b} :=
      fix r a b: {a <= b} + {~ a <= b} :=
        match a as n return {n <= b} + {~ n <= b} with
        | O => left (zero_is_least b)
        | S k =>
          match b return {S k <= b} + {~ S k <= b} with
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
End Nat.


(** * Predicate *)
(*    ========= *)

(** A predicate represents an arbitrary set of elements of a certain type.*)

Module Predicate.
  Section predicate_basic.
    Variable A: Type.

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

    Definition Equivalent (P Q:A->Prop): Prop :=
      Subset P Q /\ Subset Q P.
  End predicate_basic.
End Predicate.


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
    forall (a:A) (s:T A), {t:T A|Equivalent (Domain t) (Add a (Domain s))}.

  Parameter remove:
    forall (a:A) (s:T A), {t:T A|Equivalent (Domain t) (Remove a (Domain s))}.
End FINITE_SET.




(** * Finite Map *)
(*    ========== *)
Module Type FINITE_MAP.
End FINITE_MAP.
