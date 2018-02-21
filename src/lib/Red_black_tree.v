Require Import Core.
Require Natural.
Require Import Coq.Lists.List.
Import ListNotations.

Set Implicit Arguments.


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

  Definition color (t:tree): Color :=
    match t with
    | Leaf => Black
    | Node c _ _ _ => c
    end.

  Theorem invert_tree:
    forall {A:Type} {c:Color} {x:S.t} {u v:tree},
      Leaf = Node c u x v -> A.
  Proof.
    refine (
        fun A c x u v eq =>
          let p := Equal.rewrite_bwd is_Node eq I in
          match p with end
      ).
  Qed.

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

  Theorem rb_inv_leaf:
    forall (h:nat) (c:Color),
      RB_inv h c Leaf ->
      h = 0 /\ c = Black.
  Proof.
    refine(
        fun h c rb =>
          _
      ).
    inversion rb.
    split; reflexivity.
  Qed.

  Theorem rb_inv_color:
    forall (h:nat) (c:Color) (t:tree),
      RB_inv h c t ->
      RB_inv h (color t) t.
  Proof.
    intros h c t rb.
    inversion rb as [ | | n c1 t1 x c2 t2 ].
    - apply rb_leaf.
    - simpl. apply rb_red;assumption.
    - simpl. apply rb_black with (c1:=c1) (c2:=c2);assumption.
  Qed.

  Theorem use_rb_leaf:
    forall (h:nat) (c:Color),
      RB_inv h c Leaf ->
      forall (P:nat->Color->Prop),
        P 0 Black ->
        P h c.
  Proof.
    refine(
      fun h c inv =>
        _
      ).
    inversion inv. intros P p. assumption.
  Qed.


  Theorem use_rb_red:
    forall (h:nat) (x:S.t) (t1 t2:tree),
      RB_inv h Red (Node Red t1 x t2) ->
      forall P:nat->tree->S.t->tree->Prop,
        (RB_inv h Black t1 -> RB_inv h Black t2 -> P h t1 x t2) ->
        P h t1 x t2.
  Proof.
    refine (
        fun h x t1 t2 inv =>
          _
      ).
    inversion inv. intros P impl. apply impl; assumption.
  Qed.


  Theorem use_rb_black:
    forall (h:nat) (x:S.t) (t1 t2:tree),
      RB_inv h Black (Node Black t1 x t2) ->
      forall (P:nat->tree->S.t->tree->Prop),
        (
         RB_inv (pred h) (color t1) t1 ->
         RB_inv (pred h) (color t2) t2 ->
         P h t1 x t2) ->
        P h t1 x t2.
  Proof.
    refine (
        fun h x t1 t2 inv =>
          _
      ).
    inversion inv as [| | n d1 u1 y d2 u2 rb1 rb2 ].
    intros P impl. apply impl.
    - apply rb_inv_color with (c:=d1);assumption.
    - apply rb_inv_color with (c:=d2);assumption.
  Qed.


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
        Bounded lo Leaf hi
  | node_bounded:
      forall lo t1 x t2 hi c,
        Bounded lo t1 x ->
        Bounded x t2 hi ->
        Bounded lo (Node c t1 x t2) hi.

  Theorem use_leaf_bounded:
    forall (lo hi:S.t),
      Bounded lo Leaf hi ->
      forall (A:Prop) (P:lo<=hi->A), A.
  Proof.
    intros lo hi b.
    inversion b. intros A impl. apply impl. assumption.
  Qed.

  Theorem use_node_bounded:
    forall (c:Color) (lo x hi:S.t) (t1 t2:tree),
      Bounded lo (Node c t1 x t2) hi ->
      forall (A:Prop) (P:Bounded lo t1 x -> Bounded x t2 hi -> A),
        A.
  Proof.
    intros c lo x hi t1 t2 b.
    inversion b.
    intros A impl. apply impl;assumption.
  Qed.


  Theorem bounds_le:
    forall (lo hi:S.t) (t:tree),
      Bounded lo t hi ->
      lo <= hi.
  Proof
    fix f lo hi t bnd:=
      match bnd with
      | leaf_bounded le => le
      | @node_bounded lo t1 x t2 hi c b1 b2 =>
        S.transitive
          (f lo x t1 b1)
          (f x hi t2 b2)
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
      | node_bounded c bnd1 bnd2 =>
        fun le_x_lo1 =>
          node_bounded
            c (f _ _ _ _ bnd1 le_x_lo1)
            bnd2
      end.

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
      | node_bounded c bnd1 bnd2 =>
        fun le_hi2_x =>
          node_bounded
            c bnd1
            (f _ _ _ _ bnd2 le_hi2_x)
      end.

  Theorem rotation_bounded:
    forall (t u:tree),
      Rotation t u ->
      forall (lo hi:S.t),
        Bounded lo t hi ->
        Bounded lo u hi.
  Proof
    fix f t u rot :=
    match rot with
    | @rot_left c1 c2 c3 c4 a x b y c =>
      fun lo hi bnd =>
        use_node_bounded
          bnd
          (fun bnd1 bnd2 =>
             use_node_bounded
               bnd2
               (fun bnd2a bnd2b =>
                  node_bounded c1 (node_bounded c2 bnd1 bnd2a) bnd2b
               )
          )
    | @rot_right c1 c2 c3 c4 a x b y c =>
      fun lo hi bnd =>
        use_node_bounded
          bnd
          (fun bnd1 bnd2 =>
             use_node_bounded
               bnd1
               (fun bnd1a bnd1b =>
                  node_bounded c3 bnd1a (node_bounded c4 bnd1b bnd2)
               )
          )
    | rot_leaf =>
      fun _ _ b => b
    | @rot_node c1 c2 x u1 u2 v1 v2 ru rv =>
      fun lo hi bnd =>
        use_node_bounded
          bnd
          (fun bnd1 bnd2 =>
             let b1new := f u1 u2 ru lo x bnd1 in
             let b2new := f v1 v2 rv x hi bnd2 in
             node_bounded c2 b1new b2new
          )
    | @rot_trans t u v tu uv =>
      fun lo hi bnd =>
        f u v uv lo hi (f t u tu lo hi bnd)
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
          node_bounded c leafb leafb
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
  Proof
    fun c lo hi x u v b =>
      use_node_bounded
        b
        (fun b1 b2 => conj b1 b2).

  (*
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
*)
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
                Exist.make2 (node_bounded c bnd1 bnd2)
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
                     eq
                     (conj (bounds_le b1) (bounds_le b2))
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





  Inductive Inorder: list S.t -> tree -> Prop :=
  | inorder_leaf: Inorder [] Leaf
  | inorder_node:
      forall c l1 t1 x l2 t2,
        Inorder l1 t1 ->
        Inorder l2 t2 ->
        Inorder (l1 ++ x :: l2) (Node c t1 x t2).

  Theorem insert_to_bounded:
    forall (x:S.t) (t1 t2:tree),
      Insert x t1 t2 ->
      forall lo hi,
        lo <= x ->
        x <= hi ->
        Bounded lo t1 hi ->
        Bounded lo t2 hi.
  Proof
    fix f x t1 t2 ins :=
    match ins with
    | ins_leaf c x =>
      fun lo hi lox xhi b =>
        node_bounded c (leaf_bounded lox) (leaf_bounded xhi)
    | @ins_left c x y t1 t1new t2 xy ins =>
      fun lo hi lox xhi b =>
        use_node_bounded
          b
          (fun b1 b2 =>
             let loy := bounds_le b1 in
             let yhi := bounds_le b2 in
             let bnew := f x t1 t1new ins lo y lox xy b1 in
             node_bounded c bnew b2
          )
    | @ins_right c x y t1 t2 t2new yx ins =>
      fun lo hi lox xhi b =>
        use_node_bounded
          b
          (fun b1 b2 =>
             let loy := bounds_le b1 in
             let yhi := bounds_le b2 in
             let bnew := f x t2 t2new ins y hi yx xhi b2 in
             node_bounded c b1 bnew
          )
    | @ins_replace c x y t1 t2 eqv =>
      fun _ _ _ _ b =>
        use_node_bounded
          b
          (fun b1 b2 =>
             And.use
               eqv
               (fun xy yx  =>
                  node_bounded
                    c
                    (bounded_right_transitive b1 yx)
                    (bounded_left_transitive b2 xy)
               )
          )
    | @ins_rotation x t1 t2 t3 ins rot =>
      fun lo hi lox xhi b =>
        rotation_bounded
          rot
          (f x t1 t2 ins lo hi lox xhi b)
    end.





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
    {u:tree | Red_black t -> Sorted t -> Red_black u /\ Insert x t u}.

  Import Relation.

  Definition insert
             (x:S.t) (t:tree): Insert_result x t :=
    let Res0 t :=
        {u |
         forall lo hi h c,
           Bounded lo t hi ->
           RB_inv h c t ->
           RB_nearly_inv h u /\ Insert x t u} in
    let bal_left c t1 (r1:Res0 t1) z t2: Res0 (Node c t1 z t2) :=
        Sigma.use
          r1
          (fun u1 p1 =>
             match c return Res0 (Node c t1 z t2) with
             | Red => _
             | Black =>
               match u1 with
               | Node Red (Node Red a x b) y c => _
               | Node Red a x (Node Red b y c) => _
               | _ => _
               end
             end
          )
    in
    let bal_right c t1 y t2  (r2:Res0 t2): Res0 (Node c t1 y t2) :=
        _
    in
    let sub c t1 y t2 (xy:x<=y) (yx:y<=x): Res0 (Node c t1 y t2) :=
        _
    in
    let ins: forall t,  Res0 t :=
        fix f t :=
          match t with
          | Leaf =>
            let u := Node Red Leaf x Leaf in
            exist
              _ u
              (fun lo hi h c b rb =>
                 conj
                   (Equal.rewrite_bwd
                      (fun h => _ )
                      (And.proj1 (rb_inv_leaf rb):h = 0)
                      (singleton_nearly Red x))
                   (ins_leaf Red x:Insert x Leaf u))
          | Node c t1 y t2 =>
            match S.compare3 x y with
            | less_than xy => bal_left c t1 (f t1) y t2
            | equivalent xy yx => sub c t1 y t2 xy yx
            | greater_than yx => bal_right c t1 y t2 (f t2)
            end
          end
    in
    let mblack: Res0 t -> Insert_result x t := _ in
    mblack (ins t).







  Definition Insert_result (x:S.t) (t:tree): Type :=
    {u:tree | Red_black u /\ Insert x t u}.

  Definition insert
             (x:S.t) (t:tree) (rb:Red_black t) (s:Sorted t)
    : Insert_result x t :=
    let Res00 t :=
        {u |
         forall lo hi h c,
           Bounded0 lo t hi ->
           RB_inv h c t ->
           RB_nearly_inv h u /\ Insert x t u} in
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
                let s1 := And.proj1 (sons_sorted sort) in
                let s2 := And.proj2 (sons_sorted sort) in
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
