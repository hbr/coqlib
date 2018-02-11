Require Import Core.

Set Implicit Arguments.

(** * Basic Facts about Natural Numbers *)
(*    ================================= *)
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





(** * Arithmetic *)
(*    ========== *)
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


(** * Order Structure of Natural Numbers *)
(*    ================================== *)
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


  Theorem le_transitive:
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


  Theorem le_antisymmetric:
    forall (n m:nat), n <= m -> m <= n -> n = m.
  Proof
    fun n m nm =>
      match nm with
      | le_n _ => fun _ => eq_refl
      | le_S _ k nk =>
        fun Skn: S k <= n =>
          let Skk: k < k := le_transitive Skn nk in
          match lt_irreflexive Skk with end
      end.

  Theorem lt_le_transitive:
    forall (n m k:nat), n < m -> m <= k -> n < k.
  Proof
    fun n m k (le_Snm: S n <= m) le_mk =>
      le_transitive le_Snm le_mk.

  Theorem le_lt_transitive:
    forall (n m k:nat), n <= m -> m < k -> n < k.
  Proof
    fun n m k le_nm (le_Smk: S m <= k) =>
      le_transitive (successor_monotonic_le le_nm) le_Smk.

  Theorem lt_transitive:
    forall (n m k:nat), n < m -> m < k -> n < k.
  Proof
    fun n m k (lt_nm: S n <= m) lt_mk =>
      lt_implies_le (le_lt_transitive lt_nm lt_mk) : S n <= k.

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



(** * Order Predicates *)
(*    ================= *)
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


  Theorem lower_bound_transitive:
    forall (P:nat->Prop) (n m:nat),
      n <= m -> Lower_bound P m -> Lower_bound P n.
  Proof
    fun P n m le_nm lbm k pk =>
      let le_mk: m <= k := lbm k pk in
      le_transitive le_nm le_mk.


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



(** * Wellfounded Relation: lt *)
(*    ======================== *)
Section nat_wellfounded.
  Theorem lt_well_founded: well_founded lt.
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
           match successor_not_below_zero pj_lt_0 with end)
    | S k =>
      (* Goal: Acc lt (S k). S k must be accessible. In order to prove that
           we have to prove that all predecessors of S k are accessible. The
           predecessors of S k are k and all predecessors of k. By calling f k
           we get a proof that all k is accessible which we can pattern match
           to get a proof that all predecessors of k are accessible as well.
       *)
      let hypo_k: Acc lt k := f k in
      match hypo_k with
        Acc_intro _ p =>
        Acc_intro
          _
          (fun j (pj_lt_Sk:S j <= S k) =>
             match is_equal j k with
             | left p_eq_jk =>
               Equal.rewrite (Equal.flip p_eq_jk) _ hypo_k
             | right p_ne_jk =>
               let pj_le_k: j <= k := cancel_successor_le pj_lt_Sk in
               let pj_lt_k: j < k  := le_ne_implies_lt pj_le_k p_ne_jk in
               p j pj_lt_k
             end)
      end
    end.
End nat_wellfounded.




(** * Element Search *)
(*    ============== *)
Section nat_search.
  Definition
    find_below (P:nat->Prop) (n:nat) (d:Predicate.Decider P)
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


  Definition
    find_existing_below
    (P:nat->Prop)
    (n:nat)
    (d:Predicate.Decider P)
    (e: exists x, x < n /\ P x)
    : sig (Least P) :=
    match find_below n d with
    | inleft least => least
    | inright lbn =>
      let contra: False :=
          match e with
            ex_intro _ x q =>
            match q with
              conj lt_xn px => (* S x <= n, P x *)
              let le_nx: n <= x := lbn x px in
              successor_not_le (le_transitive lt_xn le_nx: S x <= x)
            end
          end in
      match contra with end
    end.


End nat_search.

Module Notations.
  Notation "x =? y" :=
    (is_equal x y) (at level 70, no associativity) : nat_scope.
  Open Scope nat_scope.
  Notation "x <=? y" :=
    (is_less_equal x y) (at level 70, no associativity) : nat_scope.
  Open Scope nat_scope.
End Notations.
