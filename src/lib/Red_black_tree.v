Require Import Core.
Require Natural.
Require Import Coq.Lists.List.
Import ListNotations.

Set Implicit Arguments.

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



(* Invariant:
   1. The black depth in both subtrees is the same.
   2. A red parent has two black sons.
 *)


(* Insertion:

Rule: We always maintain the black-depth invariant, we temporarily violate the
no-red-red invariant.

Elementary case: Insert into an empty tree. A singleton red tree with two
empty leaves. If we put the singleton red tree as a subtree into another node
we might violate the no-red-red invariant in case that the parent node is
red).

Recursive case: Insert into a nonempty tree. We insert into the left or right
son which might turn the son into a tree which has a no-red-red violation at
the top.

Insertion into a tree with a black root node never violates the no-red-red
invariant because we can always rebalance and get a new tree with a red root.

A tree with a red root node has two black sons. Insertion in one of the two
might paint it red which causes a no-red-red violation.


*)

(****** Okasaki ***********)
Module RB_Tree_nat.
  Import Natural.
  Inductive Color: Set := Red | Black.
  Inductive Tree (A:Type): Type :=
  | Leaf: Tree A
  | Node: Color -> Tree A -> A -> Tree A -> Tree A.
  Arguments Leaf [A].
  Arguments Node [A] _ _ _ _.




  Definition insert (x:nat) (a:Tree nat): Tree nat :=
    let balance c t1 z t2 :=
        let common a x b y c z d :=
            Node Red (Node Black a x b) y (Node Black c z d)
        in
        match c with
        | Red => Node c t1 z t2
        | Black =>
          match t1, t2 with
          | Node Red (Node Red a x b) y c, t2 =>
            common a x b y c z t2
          | Node Red a x (Node Red b y c), t2 =>
            common a x b y c z t2
          | t1, Node Red (Node Red b y c) z d =>
            common t1 x b y c z d
          | t2, Node Red b y (Node Red c z d) =>
            common t1 x b y c z d
          | _, _ =>
            Node c t1 z t2
          end
        end
    in
    let ins: Tree nat -> Tree nat :=
        fix f a :=
          match a with
          | Leaf => Node Red Leaf x Leaf
          | Node c t1 y t2 =>
            match compare3 x y with
            | Tristate.Left _ =>
              balance c (f t1) y t2
            | Tristate.Middle _ =>
              Node c t1 y t2
            | Tristate.Right _ =>
              balance c t1 y (f t2)
            end
          end
    in
    let make_black a :=
        match a with
        | Leaf => Leaf
        | Node c e t1 t2 => Node Black e t1 t2
        end
    in
    make_black (ins a).

End RB_Tree_nat.







Module M1 (S0: SORTABLE).
  Module S := Sortable_plus S0.
  Import S.Notations.


  Inductive Color: Set := Red | Black.

  Inductive tree: Type :=
  | Leaf: tree
  | Node: Color -> tree -> S.t -> tree -> tree.

  Definition is_Node (t:tree): Prop :=
    match t with
    | Leaf => False
    | Node _ _ _ _ => True
    end.

  Definition is_node (t:tree): {is_Node t} + {~ is_Node t} :=
    match t with
    | Leaf => right (fun nd:False => ex_falso nd)
    | Node c t1 x t2 =>
      left I
    end.

  Theorem leaf_ne_node:
    forall (c:Color) (x:S.t) (u v:tree),
      Leaf <> Node c u x v.
  Proof.
    intros c x u v eq. inversion eq.
  Qed.
  
  Theorem node_injective:
    forall (c1 c2:Color) (x1 x2:S.t) (t1 t2 u1 u2:tree),
      Node c1 t1 x1 u1 = Node c2 t2 x2 u2 ->
      c1 = c2 /\ x1 = x2 /\ t1 = t2 /\ u1 = u2.
  Proof.
    intros c1 c2 x1 x2 t1 t2 u1 u2 eq.
    inversion eq.
    split. reflexivity. split. reflexivity. split;reflexivity.
  Qed.
  
  Inductive Domain: tree -> S.t -> Prop :=
  | dom_singleton:
      forall c x,
        Domain (Node c Leaf x Leaf) x
  | dom_left:
      forall x c t y u,
        Domain t x -> Domain (Node c t y u) x
  | dom_right:
      forall x c t y u,
        Domain u x -> Domain (Node c t y u) x
  | dom_root:
      forall x c t y u,
        x = y  -> Domain (Node c t y u) x.

  
  Inductive RB_inv: nat -> Color -> tree -> Prop :=
  | rb_leaf: RB_inv 0 Black Leaf
  | rb_red:
      forall n t1 x t2,
        RB_inv n Black t1 ->
        RB_inv n Black t2 ->
        RB_inv n Red (Node Red t1 x t2)
  | rb_black:
      forall n c1 t1 x c2 t2,
        RB_inv n c1 t1 ->
        RB_inv n c2 t2 ->
        RB_inv (S n) Black (Node Black t1 x t2).


  Definition color (t:tree): Color :=
    match t with
    | Leaf => Black
    | Node c _ _ _ => c
    end.

  Fixpoint black_height (t:tree): nat :=
    match t with
    | Leaf => 0
    | Node Red t1 x t2 => black_height t1
    | Node Black t1 x t2 => S (black_height t1)
    end.

  Theorem black_height_correct:
    forall (h:nat) (c:Color) (t:tree),
      RB_inv h c t -> h = black_height t.
  Proof
    fix f h c t rb :=
      match rb with
      | rb_leaf => eq_refl
      | rb_red x rb1 rb2   => f _ _ _ rb1
      | rb_black x rb1 rb2 => Equal.inject (f _ _ _ rb1) S
      end.

  Definition Same_black (t1 t2:tree): Prop :=
    black_height t1 = black_height t2.

  Definition Red_black (t:tree): Prop :=
    exists h, RB_inv h (color t) t.

  Inductive RB_nearly_inv: nat -> tree -> Prop :=
    nearly:
      forall n c1 t1 x c2 t2 c3,
        RB_inv n c1 t1 ->
        RB_inv n c2 t2 ->
        RB_nearly_inv n (Node c3 t1 x t2).

  Definition RB_nearly (t:tree): Prop :=
    exists h, RB_nearly_inv h t.

  Theorem singleton_nearly:
    forall (c:Color) (x:S.t), RB_nearly_inv 0 (Node c Leaf x Leaf).
  Proof
        fun c x =>
          let t := Node c Leaf x Leaf in
          nearly x c rb_leaf rb_leaf.


  Inductive Rotation: tree -> tree -> Prop :=
  | rot_left:
      forall c1 c2 c3 c4 a x b y c,
        Rotation
          (Node c3 a x (Node c4 b y c))
          (Node c1 (Node c2 a x b) y c)
  | rot_right:
      forall c1 c2 c3 c4 a x b y c,
        Rotation
          (Node c1 (Node c2 a x b) y c)
          (Node c3 a x (Node c4 b y c))
  | rot_leaf:
      Rotation Leaf Leaf
  | rot_node:
      forall c1 c2 x t11 t12 t21 t22,
        Rotation t11 t12 ->
        Rotation t21 t22 ->
        Rotation (Node c1 t11 x t21) (Node c2 t12 x t22)
  | rot_trans:
      forall t1 t2 t3,
        Rotation t1 t2 -> Rotation t2 t3 -> Rotation t1 t3.

  Theorem rotation_reflexive:
    forall (t:tree), Rotation t t.
  Proof
    fix f t :=
    match t with
    | Leaf => rot_leaf
    | Node c t1 x t2 =>
      let r1 := f t1 in
      let r2 := f t2 in
      rot_node c c x r1 r2
    end.


  Inductive Bounded: S.t -> tree -> S.t -> Prop :=
  | leaf_bounded:
      forall lo hi,
        lo <= hi ->
        Bounded  lo Leaf hi
  | node_bounded:
      forall lo1 hi1 t1 lo2 hi2 t2 c x,
        Bounded lo1 t1 hi1 ->
        Bounded lo2 t2 hi2 ->
        hi1 <= x ->
        x <= lo2 ->
        Bounded lo1 (Node c t1 x t2) hi2.

  Theorem bounds_le:
    forall (lo hi:S.t) (t:tree),
      Bounded lo t hi ->
      lo <= hi.
  Proof
    fix f lo hi t bnd:=
      match bnd with
      | leaf_bounded le => le
      | @node_bounded lo1 hi1 t1 lo2 hi2 t2 c x b1 b2 le1 le2 =>
        (transitivity_chain:
           (f lo1 hi1 t1 b1:  lo1 <= hi1),
           (le1:  hi1 <= x ),
           (le2:  x <= lo2 ),
           (f lo2 hi2 t2 b2:  lo2 <= hi2))
          end.



  Theorem bounded_left_transitive:
    forall (x lo hi:S.t) (t:tree),
      Bounded lo t hi ->
      x <= lo ->
      Bounded x t hi.
  Proof
    fix f x lo hi t bnd:=
      match bnd with
      | leaf_bounded le_lo_hi =>
        fun le_x_lo =>
          leaf_bounded (S.transitive le_x_lo le_lo_hi)
      | node_bounded c bnd1 bnd2 le1 le2 =>
        fun le_x_lo1 =>
          node_bounded
            c (f _ _ _ _ bnd1 le_x_lo1)
            bnd2 le1 le2
      end.

  Theorem leaf_bounded_forall:
      forall (x y:S.t),
        x <= y ->
        Bounded x Leaf y.
  Proof
    let f:
          forall (t:tree) (x y:S.t),
            x <= y -> ~ is_Node t -> Bounded x t y :=
        fun t x y le =>
          match t return ~ is_Node t -> Bounded x t y with
          | Leaf => fun _ => leaf_bounded le
          | Node _ _ _ _ =>
            fun notnd =>
              ex_falso (notnd I)
          end
    in
    fun x y le =>
      f Leaf x y le (fun nd => match nd with end).





  Theorem bounded_right_transitive:
    forall (x lo hi:S.t) (t:tree),
      Bounded lo t hi ->
      hi <= x ->
      Bounded lo t x.
  Proof
    fix f x lo hi t bnd:=
      match bnd with
      | leaf_bounded le_lo_hi =>
        fun le_hi_x =>
          leaf_bounded (S.transitive le_lo_hi le_hi_x)
      | node_bounded c bnd1 bnd2 le1 le2 =>
        fun le_hi2_x =>
          node_bounded
            c bnd1
            (f _ _ _ _ bnd2 le_hi2_x)
            le1 le2
      end.



    

  Definition Sorted (t:tree): Prop :=
    is_Node t -> exists lo hi, Bounded lo t hi.


  Definition RB_sorted (t:tree): Prop := Red_black t /\ Sorted t.

  Definition RB_nearly_sorted (t:tree): Prop := RB_nearly t /\ Sorted t.

  Theorem singleton_sorted:
    forall (c:Color) (x:S.t), Sorted (Node c Leaf x Leaf).
  Proof
    fun c x node =>
      let le_xx: x <= x := S.reflexive x in
      let leafb: Bounded x Leaf x := leaf_bounded le_xx in
      let t := Node c Leaf x Leaf in
      let b: Bounded x t x :=
          node_bounded c leafb leafb le_xx le_xx
      in
      Exist.make2 b.


  Definition Lower_bound (t:tree) (lo:S.t): Prop :=
    exists hi, Bounded lo t hi.

  Definition Upper_bound (t:tree) (hi:S.t): Prop :=
    exists lo, Bounded lo t hi.

  Theorem lower_bound_to_sorted:
    forall (t:tree) (lo:S.t),
      Lower_bound t lo ->
      Sorted t.
  Proof
    fun t lo lb nd =>
      Exist.use lb (fun hi bnd => Exist.make2 bnd).

  Theorem upper_bound_to_sorted:
    forall (t:tree) (hi:S.t),
      Upper_bound t hi ->
      Sorted t.
  Proof
    fun t hi hb nd =>
      Exist.use hb (fun ls bnd => Exist.make2 bnd).




  Theorem sons_bounded:
    forall (c:Color) (lo hi x:S.t) (u v:tree),
      Bounded lo (Node c u x v) hi ->
      Bounded lo u x /\ Bounded x v hi.
  Proof.
    refine(
        fun c lo hi x u v b => _
      ).
    inversion b as [| lo1 hi1 u1 lo2 hi2 u2 c1 y b1 b2 hi1x xlo2 eqlo1lo].
    split.
    - apply bounded_right_transitive with (hi:=hi1); assumption.
    - apply bounded_left_transitive with (lo:=lo2); assumption.
  Qed.

  Theorem sons_sorted:
    forall (c:Color) (x:S.t) (t u:tree),
      Sorted (Node c t x u) ->
      Sorted t /\ Sorted u.
  Proof
    fun c x t u sort =>
      match is_node (Node c t x u) with
      | left p =>
        Exist.use2
          (sort p)
          (fun lo hi b =>
             And.use
               (sons_bounded b)
               (fun b1 b2 =>
                  (conj
                     (fun _ => Exist.make2 b1)
                     (fun _ => Exist.make2 b2) )))
      | right p => ex_falso (p I)
      end.

  Theorem lower_upper_to_bounded:
    forall (lo hi:S.t) (t:tree),
      Lower_bound t lo ->
      Upper_bound t hi ->
      Bounded lo t hi.
  Proof.
    refine (
        fun lo hi t lb ub =>
          Exist.use
            lb
            (fun x1 (b1: Bounded lo t x1) =>
               Exist.use
                 ub
                 (fun x2 (b2: Bounded x2 t hi) =>
                    _))
      ).



  Theorem node_sorted:
    forall (c:Color) (t1:tree) (x:S.t) (t2:tree),
      Upper_bound t1 x ->
      Lower_bound t2 x ->
      Sorted (Node c t1 x t2).
  Proof
    fun c t1 x t2 hb lb nd =>
      let le_xx: x <= x := S.reflexive x in
      Exist.use
        hb
        (fun lo1 bnd1 =>
           Exist.use
             lb
             (fun hi2 bnd2 =>
                Exist.make2 (node_bounded c bnd1 bnd2 le_xx le_xx)
             )
        ).




  Theorem domain_bounded:
    forall (z:S.t) (t:tree),
      Domain t z ->
      forall (lo hi:S.t),
        Bounded lo t hi ->
        lo <= z /\ z <= hi.
  Proof.
    refine(
        fix f z t dom :=
          match dom with
          | @dom_singleton c x =>
            fun lo hi b =>
              And.use
                (sons_bounded b)
                (fun b1 b2 =>
                   conj (bounds_le b1) (bounds_le b2))
          | @dom_left x c t y u dom =>
            fun lo hi b =>
              And.use
                (sons_bounded b)
                (fun b1 b2 =>
                   And.use
                     (f x t dom lo y b1)
                     (fun p1 p2 =>
                        conj
                          p1
                          (S.transitive p2 (bounds_le b2))
                     )
                )
          | @dom_right x c t y u dom =>
            fun lo hi b =>
              And.use
                (sons_bounded b)
                (fun b1 b2 =>
                   And.use
                     (f x u dom y hi b2)
                     (fun p1 p2 =>
                        conj
                          (S.transitive (bounds_le b1) p1)
                          p2
                     )
                )
          | @dom_root x c t y u eq =>
            fun lo hi b =>
              And.use
                (sons_bounded b)
                (fun b1 b2 =>
                   Equal.rewrite_bwd
                     (fun z => lo <= z /\ z <= hi)
                     (conj (bounds_le b1) (bounds_le b2))
                     eq
                )
          end
      ).
  Qed.





  (*
  Theorem sons_sorted0:
    forall (t:tree),
      Sorted t ->
      forall (c:Color) (t1:tree) (x:S.t) (t2:tree),
        t = Node c t1 x t2 ->
      Sorted t1 /\ Sorted t2 /\ High_bound t1 x /\ Low_bound x t2.
  Proof.
    refine (
        fun t sort =>
          Or.use
            sort
            (fun eq_leaf =>
               fun c t1 x t2 eq =>
                 let eq_contra := Equal.join (Equal.flip eq_leaf) eq in
                 _)
            (fun exist_lo_hi =>
               Exist.use2
                  exist_lo_hi
                  (fun lo hi bnd =>
                     match bnd with
                     | leaf_bounded le => _
                     | node_bounded c bnd1 bnd2 le1 le2 => _
                     end)
            )
      ).
    inversion eq_contra.
  Qed.
*)


  Inductive Insert: S.t -> tree -> tree -> Prop :=
  | ins_leaf:
      forall c x, Insert x Leaf (Node c Leaf x Leaf)
  | ins_left:
      forall c x y t1 t1new t2,
        x <= y ->
        Insert x t1 t1new ->
        Insert x (Node c t1 y t2) (Node c t1new y t2)
  | ins_right:
      forall c x y t1 t2 t2new,
        y <= x ->
        Insert x t2 t2new ->
        Insert x (Node c t1 y t2) (Node c t1 y t2new)
  | ins_replace:
      forall c x y t1 t2,
        S.Equivalent x y ->
        Insert x (Node c t1 y t2) (Node c t1 x t2)
  | ins_rotation:
      forall x t1 t2 t3,
        Insert x t1 t2 ->
        Rotation t2 t3 ->
        Insert x t1 t3.


  (* Theorem nearly complete, only the rotation part is missing
     ----------------------------------------------------------
  Theorem insert_left:
    forall (x:S.t) (t u:tree),
      Insert x t u ->
      forall lo hi,
        lo <= x ->
        x <= hi ->
        Bounded lo t hi ->
        Bounded lo u hi.
  Proof.
    refine (
        let refl := S.reflexive in
        fix f x t u ins :=
          match ins with
          | @ins_leaf c z =>
            fun lo hi le1 le2 b  =>
              node_bounded c
                           (leaf_bounded (refl _)) (leaf_bounded (refl _))
                           le1 le2 
          | @ins_left c x z t1 u1 t2 le_xz ins =>
            fun lo hi le1 le2 b  =>
              And.use
                (sons_bounded b)
                (fun b1 b2 =>
                   node_bounded
                     c
                     (f x t1 u1 ins lo z le1 le_xz b1)
                     b2 (refl _) (refl _)
                )
          | @ins_right c x z t1 t2 v2 le_zx ins =>
            fun lo hi le1 le2 b  =>
              And.use
                (sons_bounded b)
                (fun b1 b2 =>
                   node_bounded
                     c b1
                     (f x t2 v2 ins z hi le_zx le2 b2)
                     (refl _) (refl _)
                )
          | @ins_replace c x z t1 t2 eqv =>
            And.use
              eqv
              (fun xz zx =>
                 fun lo hi le1 le2 b =>
                   And.use
                     (sons_bounded b)
                     (fun b1 b2 => node_bounded c b1 b2 zx xz)
              )
              | @ins_rotation z t1 t2 t3 ins rot =>
                fun lo hi le1 le2 b =>
                  _
          end
      ).
    Qed.*)
  



  Inductive Inorder: list S.t -> tree -> Prop :=
  | inorder_leaf: Inorder [] Leaf
  | inorder_node:
      forall c l1 t1 x l2 t2,
        Inorder l1 t1 ->
        Inorder l2 t2 ->
        Inorder (l1 ++ x :: l2) (Node c t1 x t2).


  (* Theorem is proven as text, but not yet done formally
     ----------------------------------------------------
  Theorem insert_to_sorted:
    forall (x:S.t) (t1 t2:tree),
      Insert x t1 t2 ->
      Sorted t1 ->
      Sorted t2.
  (* Analyze Insert x t1 t2. The case that t1 = Leaf generates a singleton
     which is trivially sorted.

     Assume that t1 has the form Node c u1 y u2. The insertion either happens
     on u1 or u2 or it replaces y. t1 is sorted which implies that u1 and u2
     are sorted and y is a highbound for u1 and a lowbound for u2.

     A recursive call returns Insert x u1 u1new -> Sorted u1new and Insert x
     u2 u2new -> Sorted u2new. Now we have to see that y is still a bound for
     u1new or u2new. I.e. we need theorems of the form

         x <= y -> Low_bound y u1 -> Insert x u1 u1new -> Low_bound y u1new

     In order to stick the inserted subtrees together we need a theorem of the
     form

        node_sorted: High_bound y u1 -> Low_bound y u2 -> Sorted (Node c u1 y u2)
 *)
  Proof.
    refine (
        fix f x t1 t2 ins :=
          match ins with
          | ins_leaf c x =>
            fun _ => @singleton_sorted c x
          | @ins_left c x y t1 t1new t2 le ins =>
            fun sort nd => _
          | ins_right c t2 le ins =>
            fun sort nd => _
          | ins_replace c t1 t2 eqv => _
          | ins_rotation ins rot => _
          end
      ).
    Qed.*)

  Definition RBT: Type := {t:tree | Red_black t}.

  Definition RBN: Type := {t:tree | exists h, RB_nearly_inv h t}.

  Theorem nearly_leaf_to_absurd:
    forall (h:nat), RB_nearly_inv h Leaf -> False.
  Proof.
    refine (
      let f: forall h t, RB_nearly_inv h t -> t = Leaf -> False :=
          fun _ _ nrb =>
            match nrb with
              nearly _ _ _ _ =>
              fun eq: Node _ _ _ _ = Leaf =>
                _ (* inversion leads to contradiction *)
            end
      in
      fun h nrb => f h Leaf nrb eq_refl
    ).
    inversion eq.
  Qed.

  Theorem nearly_node_to_rb:
    forall (h:nat) (c:Color) (t1:tree) (x:S.t) (t2:tree),
      RB_nearly_inv h (Node c t1 x t2) ->
      RB_inv (S h) Black (Node Black t1 x t2).
  Proof.
    refine (
        let f: forall h t c t1 x t2,
            RB_nearly_inv h t -> t = Node c t1 x t2 ->
            RB_inv (S h) Black (Node Black t1 x t2) :=
            fun h t c t1 x t2 nrb =>
              match nrb with
                @nearly h2 ca ta z cb tb c3 rba rbb =>
                fun eq => _
          end
        in
        fun h c t1 x t2 nrb => f h (Node c t1 x t2) c t1 x t2 nrb eq_refl
      ).
    inversion eq as [ (eqc,eqt1,eqx,eqt2) ].
    apply rb_black with (c1:=ca) (c2:=cb).
    - rewrite <- eqt1; assumption.
    - rewrite <- eqt2; assumption.
  Qed.


  Definition make_black (t:RBN): RBT.
    refine (
        match t with
          exist _ t rbn =>
          (match t with
           | Leaf =>
             let f: forall t, (exists h,RB_nearly_inv h t) -> t = Leaf -> False :=
                 fun t rbn =>
                   match rbn with
                     ex_intro _ h nrb =>
                     match nrb with
                       nearly x c3 rb1 rb2 =>
                       fun eq => _ (* inversion leads to contradiction *)
                     end
                   end
             in
             fun rbn => match f Leaf rbn eq_refl with end
           | Node c t1 x t2 =>
             fun rbn =>
               let t := Node Black t1 x t2 in
               let rbt: exists h, RB_inv h Black t :=
                   match rbn with
                     ex_intro _ h rb =>
                     let q := @nearly_node_to_rb h c t1 x t2 rb in
                     ex_intro _ (S h) q
                   end
               in
               exist _ t rbt
           end) rbn
        end).
    inversion eq.
  Defined.




  Definition make_black2 (t:tree): RB_nearly t -> RBT.
    refine (
        match t with
        | Leaf =>
          let f: forall t, (exists h,RB_nearly_inv h t) -> t = Leaf -> False :=
              fun t rbn =>
                match rbn with
                  ex_intro _ h nrb =>
                  match nrb with
                    nearly x c3 rb1 rb2 =>
                    fun eq => _ (* inversion leads to contradiction *)
                  end
                end
          in
          fun rbn => match f Leaf rbn eq_refl with end
        | Node c t1 x t2 =>
          fun rbn =>
            let t := Node Black t1 x t2 in
            let rbt: exists h, RB_inv h Black t :=
                match rbn with
                  ex_intro _ h rb =>
                  let q := @nearly_node_to_rb h c t1 x t2 rb in
                  ex_intro _ (S h) q
                end
            in
            exist _ t rbt
        end
      ).
    inversion eq.
  Defined.

  Definition Insert_result (x:S.t) (t:tree): Type :=
    {u:tree | Red_black u /\ Insert x t u}.

  Import Relation.

  Definition insert
             (x:S.t) (t:tree) (rb:Red_black t) (s:Sorted t)
    : Insert_result x t :=
    let Res0 t :=
        {u | RB_nearly u /\ Insert x t u} in
    let Res t  := Insert_result x t in
    let ins: forall t, Red_black t -> Sorted t ->  Res0 t :=
        fix f t :=
          match t with
          | Leaf =>
            fun _ _ =>
              exist
                _ (Node Red Leaf x Leaf)
                (conj
                   (ex_intro _ 0 (singleton_nearly Red x))
                   (ins_leaf Red x)
                )
          | Node c t1 y t2 =>
            fun rb sort =>
              match S.compare3 x y with
              | less_than xy =>
                let ssons := sons_sorted sort in
                _
                (*Sigma.use
                  (f t1 _)
                  (fun t1a
                       (rbn1:RB_nearly t1a)
                       (i:Insert x t1 t1a) sb =>
                     _)*)
              | equivalent xy zx =>
                _
              | greater_than yx =>
                _
              end
          end
    in
    let mblack t: Res0 t -> Insert_result x t := _ in
    _.


  Definition insert (x:S.t) (t:RBT): RBT :=
    let bd t := black_depth (Sigma.value t) in
    let ins: forall t:RBT, RBN (bd t) := _
    in
    let make_black (u:RBN (bd t)): RBT := _ in
    make_black (ins t).
End M1.







(* ************* cpdt chlipala **************)
Module Make (S0:SORTABLE).
  Module S := Sortable_plus S0.
  Import S.Notations.

  Module Color.
    Inductive t: Set := Red | Black.
  End Color.

  (* Invariant:
     1. The black depth in both subtrees is the same.
     2. A red parent has two black sons.
   *)



  Inductive t : Color.t -> nat -> Set :=
  | Leaf :
      t Color.Black 0
  | Red_node :
      forall n,
        t Color.Black n ->
        S.t ->
        t Color.Black n ->
        t Color.Red n
  | Black_node :
      forall c1 c2 n,
        t c1 n ->
        S.t ->
        t c2 n ->
        t Color.Black (S n).


  Extraction t.
  (* A nearly red black tree might have a root node with arbitrary colored
     sons. The black-height invariant is valid and the sons are valid red
     black trees of the same black depth. *)
  Inductive nearly: nat -> Set :=
  | Nearly:
      forall c1 c2 n,
        t c1 n ->
        S.t ->
        t c2 n ->
        nearly n.


  (*
    Inductive sigT (A : Type) (T : A -> Type) : Type :=
    | existT :
        forall x : A,
            T x ->
            {x : A & T x}.

     T is a dependend type. It maps a value of type A into the type T a.

     {x: A & T} is a notation for sigT (fun x : A => T)
   *)
  (*Definition balance1
             (n:nat) (a:nearly n)
             (e:S.t) (c2:Color.t)
             (b:t c2 n)
    : {c:Color.t & t c (S n)} :=
    _.*)

End Make.
