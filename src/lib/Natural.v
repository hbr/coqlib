Require Import Core.
Import Equal.Notations.

Set Implicit Arguments.
Set Warnings "-extraction-opaque-accessed".

(** * Basic Facts *)
(*    =========== *)
Section nat_basics.
  Definition is_Successor (n:nat): Prop :=
    match n with
    | 0 => False
    | S _ => True
    end.

  Fact predecessor0 (n:nat) (p:is_Successor n): {x:nat|S x = n}.
  Proof
    (match n with
     | 0 => fun p:is_Successor 0 => ex_falso p
     | S m => fun _ => exist _ m eq_refl
     end) p.

  Fact is_successor (n:nat): {x:nat|S x = n} + {n = 0}.
  Proof
    match n with
    | 0 => inright eq_refl
    | S x => inleft (exist _ x eq_refl)
    end.

  Fact predecessor (n:nat) (p:is_Successor n): {x:nat|S x = n}.
  Proof
    match is_successor n with
    | inleft p => p
    | inright neq0 => ex_falso (Equal.rewrite is_Successor neq0 p)
    end.


  Theorem successor_not_zero:
    forall n:nat, S n <> 0.
  Proof
    fun n (p: S n = 0) =>
      (* Use the propositon 'is_Successor' which is trivially provable for 'S n'
         and rewrite 'S n' into '0' by using 'p' and generate a proof for
         'False'. With that we get 'S n = 0 -> False' which is the required
         result. *)
      Equal.rewrite is_Successor p I.

  Theorem successor_equal_zero {A:Prop}:
    forall (n:nat), S n = 0 -> A.
  Proof
    fun n eq => ex_falso (successor_not_zero eq).

  Theorem zero_equal_successor {A:Prop}:
    forall (n:nat), 0 = S n -> A.
  Proof
    fun n eq => successor_equal_zero (Equal.flip eq).


  Theorem pred_correct:
    forall (n:nat),
      is_Successor n ->
      S (pred n) = n.
  Proof
    fun n =>
      match is_successor n with
      | inleft x =>
        fun p =>
          let q x: S (pred (S x)) = S x := eq_refl in
          Sigma.use
            x
            (fun x (px:S x = n) =>
               Equal.rewrite (fun z => S (pred z) = z) px (q x)
            )
      | inright p =>
        let Q n := is_Successor n -> S (Nat.pred n) = n in
        let q: Q 0 := ex_falso in
        Equal.rewrite_bwd Q (p:n=0) q
      end.

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
  Theorem push_successor_plus:
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


  Theorem pull_successor_plus:
    forall (n m:nat), n + S m = S (n + m).
  Proof
    fun n m =>
      Equal.flip (push_successor_plus n m).

  Theorem cancel_plus_zero:
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

  Theorem plus_commutative:
    forall (n m:nat), n + m = m + n.
  Proof
    fix f n: forall m, n + m = m + n :=
    match n with
    | 0 =>
      fun m =>
        let p: m + 0 = m := cancel_plus_zero m in
        let q: 0 + m = m + 0 := Equal.flip p in
        q
    | S k =>
      fun m =>
        let hypo := f k m in
        let p: S k + m = S m + k := Equal.inject hypo S in
        Equal.join p (push_successor_plus m k)
    end.

  Theorem zero_sum1:
    forall (n m:nat), n + m = 0 -> n = 0.
  Proof
    fun n =>
      match n return forall m (p:n+m=0), n = 0
      with
      | 0 => fun _ _ => eq_refl
      | S k =>
        fun m (eq0: S (k + m) = 0) =>
          match successor_not_zero eq0 with end
      end.

  Theorem zero_sum2:
    forall (n m:nat), n + m = 0 -> m = 0.
  Proof
    fun n m eq =>
      let p: m + n = 0 :=
          Equal.join (plus_commutative m n) eq in
      zero_sum1 m n p.

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


  Theorem predecessor_decreasing_le:
    forall n m:nat, n <= m -> pred n <= m.
  Proof
    fix f n m p {struct p} :=
    match p with
    | le_n _ =>
      (* goal: pred n <= n *)
      match n with
      | 0 => le_n 0
      | S k =>
        (* goal: pred (S k) <= S k *)
        le_S _ k (le_n k)
      end
    | le_S _ k pk =>
      (* goal: pred n <= S k *)
      le_S _ k (f n k pk: pred n <= k)
    end.



  Theorem predecessor_monotonic_le:
    forall n m:nat, n <= m -> pred n <= pred m.
  Proof
    fun n m p =>
      match p with
      | le_n _ =>
        (* goal: pred n <= pred n *)
        le_n (pred n)
      | le_S _ k pk =>
        (* goal: pred n <= pred (S k), i.e. pred n <= k *)
        predecessor_decreasing_le pk
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


  Theorem eq_to_le:
    forall (n m:nat), n = m -> n <= m.
  Proof
    fun n m eq =>
      Equal.rewrite _ eq (le_n n).


  Theorem lt_to_le:
    forall (n m:nat), n < m -> n <= m.
  Proof
    fix f n m lt: n <= m :=
    match lt with
    | le_n _ => le_S n n (le_n _)
    | le_S _ k pk => le_S n k (f n k pk)
    end.


  Theorem lt_to_neq:
    forall (n m:nat), n < m -> n <> m.
  Proof
    fun n m lt eq =>
      let n_lt_n: n < n := Equal.rewrite_bwd _  eq lt in
      successor_not_le n_lt_n.



  Theorem le_neq_to_lt:
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
      lt_to_neq nn eq_refl.


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

  Theorem le_eq_transitive:
    forall (n m k:nat), n <= m -> m = k -> n <= k.
  Proof
    fun n m k le eq =>
      Equal.rewrite (fun x => n <= x) eq le.

  Theorem lt_eq_transitive:
    forall (n m k:nat), n < m -> m = k -> n < k.
  Proof
    fun n m k lt eq =>
      Equal.rewrite (fun x => n < x) eq lt.

  Theorem lt_transitive:
    forall (n m k:nat), n < m -> m < k -> n < k.
  Proof
    fun n m k (lt_nm: S n <= m) lt_mk =>
      lt_to_le (le_lt_transitive lt_nm lt_mk) : S n <= k.



  Theorem le_contradicts_lt:
    forall (n m:nat), n <= m -> m < n -> False.
  Proof
    fun n m le lt =>
      lt_irreflexive (le_lt_transitive le lt:n < n).


  Theorem plus_increases1:
    forall (n m:nat), n <= n + m.
  Proof
    fix f n: forall m, n <= n + m :=
    match n with
    | 0 => fun m => zero_is_least (0 + m)
    | S k =>
      fun m =>
        let p: k <= k + m := f k m in
        successor_monotonic_le p
    end.

  Theorem plus_increases2:
    forall (n m:nat), m <= n + m.
  Proof
    fun n m =>
      let p: m + n = n + m := plus_commutative m n in
      Equal.rewrite (fun x => m <= x) p (plus_increases1 m n).

  Theorem left_summand_to_le:
    forall (n m k:nat), n + m = k -> n <= k.
  Proof
    fun n m k eq =>
      le_eq_transitive (plus_increases1 n m) eq.

  Theorem right_summand_to_le:
    forall (n m k:nat), n + m = k -> m <= k.
  Proof
    fun n m k eq =>
      le_eq_transitive (plus_increases2 n m) eq.
End nat_order.






(** * Decidable Order of Natural Numbers *)
(*    ================================== *)
Section decidable_order.
(** It is easy to write a recursive boolean function which compares two
    natural numbers. *)

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

(* However it is much more effective to write a decision procedure which not
   only returns a boolean value but a proof as well. *)

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
End decidable_order.



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


  Theorem zero_lower_bound:
    forall (P:nat->Prop), Lower_bound P 0.
  Proof
    fun P n _ => zero_is_least n.


  Theorem predecessor_lower_bound:
    forall (P:nat->Prop) (n:nat),
      Lower_bound P (S n) -> Lower_bound P n.
  Proof
    fun P n lbSn =>
      lower_bound_transitive (le_S n n (le_n n)) lbSn.



  Theorem successor_not_lower_bound:
    forall (P:nat->Prop) (n:nat), P n -> ~ Lower_bound P (S n).
  Proof
    fun P n pn lbsn =>
      ex_falso
        (successor_not_le (lbsn n pn: S n <= n)).


  Theorem successor_lower_bound:
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
                match
                  pnot (Equal.rewrite_bwd _ n_eq_m mP)
                with
                end
          in
          le_neq_to_lt (lb m mP)  n_ne_m
      end.
End nat_order_predicates.



(** * Comparison *)
(*    ========== *)
Section comparison.
  Definition Comparison3 (n m:nat): Type :=
    Tristate.t {d| S n + d = m} (n=m) {d| S m + d = n}.

  Definition compare3 (n m:nat): Comparison3 n m :=
    (fix f n m: Comparison3 n m :=
       match n, m with
       | 0, 0 =>
         Tristate.Middle eq_refl
       | 0, S j =>
         Tristate.Left (exist _ j eq_refl)
       | S i, 0 =>
         Tristate.Right (exist _ i eq_refl)
       | S i, S j =>
         match f i j with
         | Tristate.Left p =>
           match p with
             exist _ d eq =>
             Tristate.Left (exist _ d (Equal.inject eq S))
           end
         | Tristate.Middle p =>
           Tristate.Middle (Equal.inject p S)
         | Tristate.Right p =>
           match p with
             exist _ d eq =>
             Tristate.Right (exist _ d (Equal.inject eq S))
           end
         end
       end) n m.

  Definition difference2 (n m:nat): Either.t {d|n + d = m} {d|S m + d = n} :=
    match compare3 n m with
    | Tristate.Left x =>
      match x with
        exist _ d p =>
        let q: n + S d = m :=
            Equal.join
              (pull_successor_plus n d: n + S d = _)
              (p: S n + d = m)
        in
        Either.Left (exist _ (S d) q)
      end
    | Tristate.Middle p =>
      let q: n + 0 = n := cancel_plus_zero n in
      Either.Left (exist _ 0 (Equal.join q p))
    | Tristate.Right p =>
      Either.Right p
    end.
End comparison.



(** * More Arithmetic       *)
(*    ===================== *)
Section more_arithmetic.
  Definition half (n:nat): Either.t {x| x + x = n} {x| S(x + x) = n} :=
    let RT n := Either.t {x| x + x = n} {x| S(x + x) = n} in
    (fix f m: forall k, k + k + m = n ->  RT n :=
       match m with
       | 0 =>
         fun k inv =>
           let p: k + k = n :=
               Equal.join
                 (Equal.flip (cancel_plus_zero (k+k)): k + k = k + k + 0)
                 (inv: _ = n)
           in
           Either.Left (exist _ k p)
       | S 0 =>
         fun k inv =>
           let p: S (k + k) = n :=
               Equal.rewrite
                 (fun x => x = n)
                 (plus_commutative (k + k) 1: k + k + 1 = 1 + (k + k))
                 inv
           in
           Either.Right (exist _ k p)
       | S (S i) =>
         fun k inv =>
           let p := push_successor_plus (S i) (k + k) in
           let q := push_successor_plus i (S (k + k)) in
           let r: S (k + k) = k + S k := push_successor_plus k k in
           let eq: (S k) + (S k) + i = n :=
               (equality_chain:
                  (Equal.inject
                     (pull_successor_plus (S k) k)
                     (fun x => x + i)
                   : S k + S k + i = _),
                  (push_successor_plus (S (k + k)) i: S (S (k + k)) + i = _),
                  (push_successor_plus (k + k) (S i): S (k + k) + S i = _),
                  (inv: k + k + S (S i) = n))
           in
           f i (S k) eq
       end)
      n 0 eq_refl.
End more_arithmetic.



Section downward_induction.
  Theorem downward_induction:
    forall (m:nat) (P: nat -> Prop),
      P m ->
      (forall n, P (S n) -> P n) ->
      forall n, n <= m -> P n.
  Proof
    fun m P pm hypo n n_le_m =>
      match difference2 n m with
      | Either.Left p =>
        match p with
          exist _ d n_plus_d_eq_m =>
          let d_plus_n_eq_m: d + n = m :=
              Equal.rewrite
                (fun x => x = m)
                (plus_commutative n d)
                n_plus_d_eq_m in
          let q: forall d n, d + n = m -> P n :=
              fix f d :=
                match d with
                | O =>
                  fun n n_eq_m =>
                    Equal.rewrite_bwd P (n_eq_m: 0 + n = m) pm
                | S d =>
                  fun n Sd_n_eq_m =>
                    let pSn: P (S n) :=
                        f d (S n)
                          (Equal.rewrite_bwd
                             (fun x => x = m)
                             (pull_successor_plus d n)
                             Sd_n_eq_m
                          ) in
                    hypo n pSn
                end
          in
          q d n d_plus_n_eq_m
        end
      | Either.Right q (* {d| S m + d = n} *) =>
        (* q implies m < n which contradicts n <= m *)
        let m_lt_n: m < n :=
            match q with
              exist _ d Sm_plus_d_eq_n =>
              @left_summand_to_le _ _ _ Sm_plus_d_eq_n
            end
        in
        ex_falso
          (le_contradicts_lt n_le_m m_lt_n)
      end.
End downward_induction.






(** * Wellfounded Relations *)
(*    ===================== *)
Section wellfounded.
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
               Equal.rewrite_bwd _ p_eq_jk  hypo_k
             | right p_ne_jk =>
               let pj_le_k: j <= k := cancel_successor_le pj_lt_Sk in
               let pj_lt_k: j < k  := le_neq_to_lt pj_le_k p_ne_jk in
               p j pj_lt_k
             end)
      end
    end.

End wellfounded.






(** * Element Search *)
(*    ============== *)
Section bounded_search.
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
                  inright (Equal.rewrite LB eqkn lbk)
         | S j =>
           fun k (eqSjkn:S j + k = n) lbk =>
             match d k with
             | left pk => (* found least element k satisfying P *)
               inleft (exist _ k (conj pk lbk))
             | right notpk =>
               let SLB := Strict_lower_bound P in
               let slbk : SLB k := conj lbk notpk in
               let lbSk: LB (S k) := successor_lower_bound slbk in
               let eqjSkn: j + S k = n :=
                   Equal.rewrite
                     (fun x => x = n)
                     (push_successor_plus j k)
                     eqSjkn
               in
               f j (S k) eqjSkn lbSk
             end
         end
      )
        n 0 (cancel_plus_zero n) (fun x _ => zero_is_least x).


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

  Theorem exist_least:
    forall (P:nat->Prop),
      Predicate.Decider P ->
      (exists x, P x) ->
      exists x, Least P x.
  Proof
    fun P d e =>
      match e with
      | ex_intro _ x p =>
        let e: exists y, y < S x /\ P y :=
            ex_intro _ x (conj (le_n (S x)) p)
        in
        let least := @find_existing_below P (S x) d e in
        match least with
        | exist _ x p =>
          ex_intro _ x p
        end
      end.
End bounded_search.




Section unbounded_search.
  Variable P: nat -> Prop.
  Variable n: nat.
  Variable d: Predicate.Decider P.
  Variable e: exists x, P x.

  Let LB := Lower_bound P.

  Let R (y x:nat): Prop :=
    y = S x /\ LB y /\ LB x.

  Let predecessor_accessible (x:nat) (acc_Sx: Acc R (S x)): Acc R x :=
    Acc_intro
      _
      (fun y Ryx =>
         match Ryx with
           conj yeqSx (conj _ _) =>
           Equal.rewrite_bwd (fun x => Acc R x) yeqSx acc_Sx
         end).

  Let least_accessible (x:nat) (least:Least P x): Acc R x :=
    match least with
      conj px lb =>
      Acc_intro
        _
        (fun y Ryx =>
           match Ryx with
             conj y_eq_Sx (conj lby lbx) =>
             ex_falso
               (successor_not_lower_bound
                  px
                  (Equal.rewrite LB y_eq_Sx lby: LB (S x)))
           end
        )
    end.

  Let lb_accessible (x:nat) (lbx:LB x): Acc R x :=
    match exist_least d e with
      ex_intro _ y least_y =>
      match least_y with
        conj py lby =>
        @downward_induction
          y
          (Acc R)
          (least_accessible least_y)
          predecessor_accessible
          x
          (lbx y py )
      end
    end.


  Definition least: sig (Least P) :=
    let least_above:
          forall k, LB k -> Acc R k -> sig (Least P) :=
        fix f k lb_k acc_k :=
          match d k with
          | left pk =>
            exist _ k (conj pk lb_k)
          | right not_pk =>
            match acc_k with
            | Acc_intro _ h =>
              (* use h to extract a proof of Acc R (S k) which is structurally
                 smaller than acc_k *)
              let lb_Sk: LB (S k) :=
                  successor_lower_bound (conj lb_k not_pk) in
              let RSkk: R (S k) k :=
                  conj eq_refl (conj lb_Sk lb_k): S k = S k /\ LB (S k) /\ LB k
              in
              f (S k) lb_Sk (h (S k) RSkk)
         end
       end
    in
    let lb0: LB 0 := zero_lower_bound P in
    least_above 0 lb0 (lb_accessible lb0).
End unbounded_search.







Module Notations.
  Notation "x =? y" :=
    (is_equal x y) (at level 70, no associativity) : nat_scope.
  Open Scope nat_scope.
  Notation "x <=? y" :=
    (is_less_equal x y) (at level 70, no associativity) : nat_scope.
  Open Scope nat_scope.
End Notations.
