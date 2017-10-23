Set Implicit Arguments.


Module Equal.
  Section sec1.
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
  End sec1.
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

Module Nat.
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
  End nat_basics.

  Section nat_recursive.
    Theorem successor_different (n:nat): n <> S n.
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
  End nat_recursive.
  
  
  Section nat_order.
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
            match (@successor_not_below_zero k q:False) with end
      in
      nat_rect P p0 p_step.
  End nat_order.
End Nat.
