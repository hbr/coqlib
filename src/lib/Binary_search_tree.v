Require Import Core.
Require Binary_tree.

Set Implicit Arguments.

Module Make (S0:SORTABLE) (E:ANY).
  Module S := Sortable_plus S0.
  Import S.Notations.

  Module BT := Binary_tree.Make S E.
  Import BT.

  (*====================================*)
  (** * Sorted Binary Tree              *)
  (*====================================*)
  Module Sorted.
    (** [R lo t hi] means [t] is sorted and all elements are between [lo] and
    [hi].*)
    Inductive R: S.t -> Tree.t -> S.t -> Prop :=
    | leaf:
        forall lo hi,
          lo <= hi ->
          R lo Tree.Leaf hi
    | node:
        forall lo t1 x t2 hi c,
          R lo t1 x ->
          R x t2 hi ->
          R lo (Tree.Node c t1 x t2) hi.

    (** [P t] means [t] is a sorted tree. *)
    Inductive P (t:Tree.t): Prop :=
      make:
        forall lo hi,
          R lo t hi ->
          P t.

    Theorem use_leaf0:
      forall (A:Prop) (lo hi:S.t) (t:Tree.t),
        R lo t hi ->
        t = Tree.Leaf ->
        (lo <= hi -> A) ->
        A.
    Proof
      fun A lo hi t b =>
        match b with
        | leaf lo_hi =>
          fun _ f => f lo_hi
        | node x b1 b2 =>
          fun eq => Tree.node_equal_leaf eq
        end.

    Theorem use_leaf:
      forall (A:Prop) (lo hi:S.t),
        R lo Tree.Leaf hi ->
        (lo <= hi -> A) ->
        A.
    Proof
      fun A lo hi b =>
        use_leaf0 b eq_refl.

    Theorem use_node0:
      forall (A:Prop) (e:E.t) (lo x hi:S.t) (t u v:Tree.t),
        R lo t hi ->
        t = Tree.Node e u x v ->
        (R lo u x -> R x v hi -> A) ->
        A.
    Proof
      fun A e lo x hi t u v b =>
        match b with
        | leaf lo_hi =>
          fun eq => Tree.leaf_equal_node eq
        | node e0 b1 b2 =>
          fun eq f =>
            Tree.use_node_equal
              eq
              (fun eeq xeq t1eq t2eq =>
                 f (Equal.use2 t1eq xeq (fun t1 x => R _ t1 x) b1)
                   (Equal.use2 t2eq xeq (fun t2 x => R x t2 _) b2))
        end.

    Theorem use_node:
      forall (A:Prop) (e:E.t) (lo x hi:S.t) (u v:Tree.t),
        R lo (Tree.Node e u x v) hi ->
        (R lo u x -> R x v hi -> A) ->
        A.
    Proof
      fun A e lo x hi u v b =>
        use_node0 b eq_refl.


    Theorem ignore_rotation:
      forall (t u: Tree.t),
        Rotation.R t u ->
        forall (lo hi:S.t),
          R lo t hi ->
          R lo u hi.
    Proof
      fix f t u rot :=
      match rot with
      | Rotation.leaf =>
        fun _ _ b => b
      | Rotation.left c1 c2 c3 c4 a x b y c =>
        fun lo hi bnd =>
          use_node
            bnd
            (fun s1 s2 =>
               use_node
                 s2
                 (fun s2a s2b =>
                    node c3 (node c4 s1 s2a) s2b
                 )
            )
      | Rotation.right c1 c2 c3 c4 a x b y c =>
        fun lo hi bnd =>
          use_node
            bnd
            (fun s1 s2 =>
               use_node
                 s1
                 (fun s1a s1b =>
                    node c3 s1a (node c4 s1b s2)
                 )
            )
      | @Rotation.node c1 c2 x _ _ _ _ ru rv =>
        fun lo hi bnd =>
          use_node
            bnd
            (fun s1 s2 =>
               node c2
                    (f _ _ ru lo x s1)
                    (f _ _ rv x hi s2)
            )
      | Rotation.transitive tu uv =>
        fun lo hi s =>
          f _ _ uv lo hi (f _ _ tu lo hi s)
      end.
  End Sorted.


  (*====================================*)
  (** * Insertion into a Sorted Tree    *)
  (*====================================*)
  Module Inserted.
    (** [R x u v] means [x] inserted into the sorted tree [u] results in the
    sorted tree [v]. *)
    Inductive R: S.t -> Tree.t -> Tree.t -> Prop :=
    | leaf:
        forall c x, R x Tree.Leaf (Tree.Node c Tree.Leaf x Tree.Leaf)
    | left:
        forall lo x y hi c1 t1 t1new c2 t2,
          lo <= x ->
          x <= y ->
          Sorted.R lo t1 y ->
          Sorted.R y t2 hi ->
          R x t1 t1new ->
          R x (Tree.Node c1 t1 y t2) (Tree.Node c2 t1new y t2)
    | right:
        forall lo x y hi c1 t1 c2 t2 t2new,
          y <= x ->
          x <= hi ->
          Sorted.R lo t1 y ->
          Sorted.R y t2 hi ->
          R x t2 t2new ->
          R x (Tree.Node c1 t1 y t2) (Tree.Node c2 t1 y t2new)
    | replace:
        forall lo x y hi c1 t1 c2 t2,
          lo <= x ->
          y <= hi ->
          S.Equivalent x y ->
          Sorted.R lo t1 y ->
          Sorted.R y t2 hi ->
          R x (Tree.Node c1 t1 y t2) (Tree.Node c2 t1 x t2)
    | rotation:
        forall x t1 t2 t3,
          R x t1 t2 ->
          Rotation.R t2 t3 ->
          R x t1 t3.
  End Inserted.
End Make.
