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
  End nat_recursive.
  
  
  Section nat_order.
  End nat_order.
End Nat.