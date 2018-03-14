Require Import Core.
Require Binary_tree.

Set Implicit Arguments.

Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-inside-module".
Unset Elimination Schemes.


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

    Theorem less_equal_lo_hi:
      forall lo hi t,
        R lo t hi ->
        lo <= hi.
    Proof
      fix f lo hi t s:=
      match s with
      | leaf le => le
      | node c s1 s2 =>
        S.transitive
          (f _ _ _ s1)
          (f _ _ _ s2)
      end.

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
        (lo <= x -> x <= hi -> R lo u x -> R x v hi -> A) ->
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
                 let b1a := Equal.use2 t1eq xeq (fun t1 x => R _ t1 x) b1 in
                 let b2a := Equal.use2 t2eq xeq (fun t2 x => R x t2 _) b2 in
                 f (less_equal_lo_hi b1a)
                   (less_equal_lo_hi b2a)
                   b1a b2a)
        end.

    Theorem use_node:
      forall (A:Prop) (e:E.t) (lo x hi:S.t) (u v:Tree.t),
        R lo (Tree.Node e u x v) hi ->
        (lo <= x -> x <= hi -> R lo u x -> R x v hi -> A) ->
        A.
    Proof
      fun A e lo x hi u v b =>
        use_node0 b eq_refl.


    Theorem use_node_P0:
      forall (A:Prop) e x u v,
        P (Tree.Node e u x v) ->
        (forall lo hi,
            lo <= x -> x <= hi -> R lo u x -> R x v hi -> A) ->
        A.
    Proof
      fun A e x u v p =>
        match p with
        | make s =>
          use_node
            s
            (fun lox xhi s1 s2 f =>
               f _ _ lox xhi s1 s2)
        end.

    Theorem use_node_P:
      forall (A:Prop) e x u v,
        P (Tree.Node e u x v) ->
        (P u -> P v -> A) ->
        A.
    Proof
      fun A e x u v p =>
        use_node_P0
          p
          (fun lo hi lox xhi s1 s2 f =>
             f (make s1) (make s2)).


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
            (fun _ _ s1 s2 =>
               use_node
                 s2
                 (fun _ _ s2a s2b =>
                    node c3 (node c4 s1 s2a) s2b
                 )
            )
      | Rotation.right c1 c2 c3 c4 a x b y c =>
        fun lo hi bnd =>
          use_node
            bnd
            (fun _ _ s1 s2 =>
               use_node
                 s1
                 (fun _ _ s1a s1b =>
                    node c3 s1a (node c4 s1b s2)
                 )
            )
      | @Rotation.node c1 c2 x _ _ _ _ ru rv =>
        fun lo hi bnd =>
          use_node
            bnd
            (fun _ _ s1 s2 =>
               node c2
                    (f _ _ ru lo x s1)
                    (f _ _ rv x hi s2)
            )
      | Rotation.transitive tu uv =>
        fun lo hi s =>
          f _ _ uv lo hi (f _ _ tu lo hi s)
      end.

    Theorem change_extra:
      forall e lo t hi,
        R lo t hi ->
        R lo (Tree.change_extra e t) hi.
    Proof
      fun e lo t hi b =>
        ignore_rotation
          (Rotation.change_extra e (Rotation.reflexive t))
          b.

    (** All elements are within the bounds. *)
    Theorem use_elements_bounded:
      forall (A:Prop) x lo t hi,
        R lo t hi ->
        Domain.R t x ->
        (lo <= x -> x <= hi -> A) ->
        A.
    Proof
      fix f A x lo t hi s :=
      match s with
      | leaf le =>
        fun has =>
          ex_falso ((@Domain.leaf_empty x) has)
      | node e s1 s2 =>
        fun dom =>
          let p := f A x _ _ _ s1 in
          let q := f A x _ _ _ s2 in
          Domain.use_node
            dom
            (fun eq g =>
               g (Equal.use_bwd eq (fun z => _ <= z) (less_equal_lo_hi s1))
                 (Equal.use_bwd eq (fun z => z <= _) (less_equal_lo_hi s2)))
            (fun dom1 g =>
               (f A x _ _ _ s1  dom1)
                 (fun lox xy =>
                    g lox (S.transitive xy (less_equal_lo_hi s2)))
               )
            (fun dom2 g =>
               (f A x _ _ _ s2 dom2)
                 (fun yx xhi =>
                    g (S.transitive (less_equal_lo_hi s1) yx)
                      xhi))
      end.
  End Sorted.




  (*====================================*)
  (** * Searching Elements              *)
  (*====================================*)
  Module Search.
    (** [search x t s] searches for an element equivalent to [x] in the sorted
    tree [t] where [s] is a proof that [t] is sorted. It returns either an
    element of the tree [t] equivalent to [x] or a proof that no element in
    the tree [t] is equivalent to [x].*)
    Fact search:
      forall (x:S.t) (t:Tree.t),
        Sorted.P t ->
        {e:S.t | Domain.R t e /\ S.Equivalent e x} +
        {forall e, Domain.R t e -> ~ S.Equivalent e x}.
    Proof
      fix f x t :=
      match t with
      | Tree.Leaf =>
        fun s  =>
          inright ( fun e dom => ex_falso (Domain.leaf_empty dom) )
      | Tree.Node _ u y v =>
        match S.compare3 x y with

        | Relation.LT xy not_yx=>

          fun s =>
            match f x u (Sorted.use_node_P s (fun s1 _ => s1)) with
            | inleft p =>
              match p with
              | exist _ z (conj dom1 eqv) =>
                inleft (exist _ z (conj (Domain.left _ _ _ dom1) eqv))
              end
            | inright q =>
              inright
                (fun e dom =>
                   Domain.use_node
                     dom
                     (fun eq_e_y eqv_e_x =>
                        match eqv_e_x with
                        | conj ex xe =>
                            not_yx (Equal.use eq_e_y (fun e => e <= x) ex)
                        end)
                     (q e)
                     (Sorted.use_node_P0
                        s
                        (fun lo hi lox xhi s1 s2 domv =>
                           (Sorted.use_elements_bounded
                              s2 domv
                              (fun y_e e_hi eqv =>
                                 match eqv with
                                 | conj e_x x_e =>
                                   not_yx (S.transitive y_e e_x)
                                 end)
                        ))
                     )
                )
            end

        | Relation.EQV xy yx =>

          fun s =>
            inleft (exist _ y (conj (Domain.root _ u y v) (conj yx xy)))

        | Relation.GT yx not_xy =>

          fun s =>
            match f x v (Sorted.use_node_P s (fun _ s2 => s2)) with
            | inleft p =>
              match p with
              | exist _ z (conj dom2 eqv) =>
                inleft (exist _ z (conj (Domain.right _ _ _ dom2) eqv))
              end
            | inright q =>
              inright
                (fun e dom =>
                   Domain.use_node
                     dom
                     (fun eq_e_y eqv_e_x =>
                        match eqv_e_x with
                        | conj ex xe =>
                          not_xy (Equal.use eq_e_y (fun e => x <= e) xe)
                        end)
                     (Sorted.use_node_P0
                        s
                        (fun lo hi lox xhi s1 s2 domu =>
                           (Sorted.use_elements_bounded
                              s1 domu
                              (fun loe ey eqv =>
                                 match eqv with
                                 | conj ex xe =>
                                   not_xy (S.transitive xe ey)
                                 end)
                              )))
                     (q e)
                )
            end
        end
      end.
  End Search.


  (*====================================*)
  (** * Insertion into a Sorted Tree    *)
  (*====================================*)
  Module Inserted.
    (** [R x r u v] means [x] inserted into the sorted tree [u] or replaced an
     equivalent element depending on the replace flag [r] results in the
     sorted tree [v]. *)
    Inductive R: S.t -> bool -> Tree.t -> Tree.t -> Prop :=
    | leaf:
        forall c x r, R x r Tree.Leaf (Tree.Node c Tree.Leaf x Tree.Leaf)
    | left:
        forall lo x r y hi c1 c2 t1 t1new t2,
          x <= y ->
          (y <= x -> r = false) ->
          Sorted.R lo t1 y ->
          Sorted.R y t2 hi ->
          R x r t1 t1new ->
          R x r (Tree.Node c1 t1 y t2) (Tree.Node c2 t1new y t2)
    | right:
        forall lo x r y hi c1 c2 t1 t2 t2new,
          y <= x ->
          (x <= y -> r = false) ->
          Sorted.R lo t1 y ->
          Sorted.R y t2 hi ->
          R x r t2 t2new ->
          R x r (Tree.Node c1 t1 y t2) (Tree.Node c2 t1 y t2new)
    | replace:
        forall lo x r y hi c1 c2 t1 t2,
          S.Equivalent x y ->
          r = true ->
          Sorted.R lo t1 y ->
          Sorted.R y t2 hi ->
          R x r (Tree.Node c1 t1 y t2) (Tree.Node c2 t1 x t2)
    | rotation:
        forall x r t1 t2 t3,
          R x r t1 t2 ->
          Rotation.R t2 t3 ->
          R x r t1 t3.

    Theorem rotate_left:
      forall (e1 e2:E.t) (r:bool) (xi x y:S.t) (t a b c:Tree.t),
        R xi r t (Tree.Node e1 a x (Tree.Node e2 b y c)) ->
        R xi r t (Tree.Node e2 (Tree.Node e1 a x b) y c).
    Proof
      fun e1 e2 r xi x y t a b c ins =>
        rotation ins (Rotation.left e1 e2 e2 e1 a x b y c).

    Theorem rotate_right:
      forall (e1 e2:E.t) (r:bool) (xi x y:S.t) (t a b c:Tree.t),
        R xi r t (Tree.Node e1 (Tree.Node e2 a x b) y c) ->
        R xi r t (Tree.Node e2 a x (Tree.Node e1 b y c)).
    Proof
      fun e1 e2 r xi x y t a b c ins =>
        rotation ins (Rotation.right e1 e2 e2 e1 a x b y c).

    Theorem change_extra0:
      forall (e:E.t) (r:bool) (x:S.t) (t u:Tree.t),
        R x r t u ->
        R x r t (Tree.change_extra e u).
    Proof
      fix f e r x t u ins :=
      match ins with
      | leaf e0 x r =>
        leaf e x r
      | left e1 e2 r xy s1 s2 ins =>
        left e1 e r xy s1 s2 ins
      | right e1 e2 r yx s1 s2 ins =>
        right e1 e r yx s1 s2 ins
      | replace e1 e2 r eqv s1 s2 =>
        replace e1 e  r eqv s1 s2
      | rotation ins12 rot23 =>
        rotation ins12 (Rotation.change_extra e rot23)
      end.

    Theorem change_extra:
      forall (e1 e2:E.t) (r:bool) (x y:S.t) (t u v:Tree.t),
        R x r t (Tree.Node e1 u y v) ->
        R x r t (Tree.Node e2 u y v).
    Proof
      fun e1 e2 r x y t u v ins =>
        change_extra0 e2 ins.

    Theorem change_left_extra:
      forall (e e1 e2:E.t) (r:bool) (x y z:S.t) (t u v w:Tree.t),
        R x r t (Tree.Node e1 (Tree.Node e2 u y v) z w) ->
        R x r t (Tree.Node e1 (Tree.Node e  u y v) z w).
    Proof
      fun e e1 e2 r x y z t u v w ins =>
        rotate_left (change_extra e (rotate_right ins)).

    Theorem change_right_extra:
      forall (e1 e2 e3:E.t) (r:bool) (x y z:S.t) (t u v w:Tree.t),
        R x r t (Tree.Node e1 u y (Tree.Node e2 v z w)) ->
        R x r t (Tree.Node e1 u y (Tree.Node e3 v z w)).
    Proof
      fun e1 e2 e3 r x y z t u v w ins =>
        rotate_right (change_extra e3 (rotate_left ins)).
  End Inserted.
End Make.
