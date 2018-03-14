Require Import Core.
Require Natural.
Require List.
Require Binary_search_tree.

Import List.Notations.
Import Equal.Notations.

Set Implicit Arguments.
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-inside-module".
Unset Elimination Schemes.



Module Make (S0:SORTABLE).
  Module S := Sortable_plus S0.
  Import S.Notations.


  (** * Node Colors *)
  (*  ------------- *)
  Module Color.
    Inductive t0: Set := Red | Black.

    Definition t := t0.

    Definition is_Red (c:t): Prop :=
      match c with
      | Red => True
      | Black => False
      end.

    Definition is_Black (c:t): Prop :=
      match c with
      | Red => False
      | Black => True
      end.

    Theorem red_equal_black {A:Type} (eq:Red=Black): A.
    Proof
      ex_falso (Equal.use eq is_Red I).

    Theorem black_equal_red {A:Type} (eq:Black=Red): A.
    Proof
      red_equal_black (Equal.flip eq).
  End Color.





  (** * Use Binary_search_tree *)
  (*  ------------------------ *)
  Module BST := Binary_search_tree.Make S Color.
  Import BST.
  Import BST.BT.

  Definition color (t:Tree.t): Color.t :=
    match t with
    | Tree.Leaf => Color.Black
    | Tree.Node c _ _ _ => c
    end.





  (** * Red Black Invariant *)
  (*  --------------------- *)
  (** A valid red black tree must satisfy the following two invariants:

      - A red node has only black sons (an empty tree is considered as black).

      - The number of black nodes of any path from the root to a leaf must be
        equal.
   *)
  Module Red_black.
    (** [R h c t] means that [t] is a valid red black tree with black height
    [h] and color [c]. *)
    Inductive R: nat -> Color.t -> Tree.t -> Prop :=
    | leaf: R 0 Color.Black Tree.Leaf
    | red:
        forall h t1 x t2,
          R h Color.Black t1 ->
          R h Color.Black t2 ->
          R h Color.Red (Tree.Node Color.Red t1 x t2)
    | black:
        forall h c1 t1 x c2 t2,
          R h c1 t1 ->
          R h c2 t2 ->
          R (S h) Color.Black (Tree.Node Color.Black t1 x t2).


    (** [P t] means that [t] is a valid red black tree. *)
    Inductive P (t:Tree.t): Prop :=
      make: forall h c, R h c t -> P t.


    Theorem color_correct {h:nat} {c:Color.t} {t:Tree.t} (rb:R h c t)
      : c = color t.
    Proof
      match rb in R h c t return c = color t with
      | leaf => eq_refl
      | red x rb1 rb2 => eq_refl
      | black x rb1 rb2 => eq_refl
      end.

    Theorem color_unique {h1 h2:nat} {c1 c2:Color.t} {t:Tree.t}
            (rb1:R h1 c1 t) (rb2:R h2 c2 t): c1 = c2.
    Proof
      Equal.join (color_correct rb1) (Equal.flip (color_correct rb2)).



    Theorem pull_color:
      forall (h:nat) (c1 c2:Color.t) (x:S.t) (u v:Tree.t),
        R h c1 (Tree.Node c2 u x v) ->
        R h c2 (Tree.Node c2 u x v).
    Proof
      fun h c1 c2 x u v rb =>
        Equal.use
          (color_correct rb: c1 = c2)
          (fun c => R _ c _)
          rb.


    Fixpoint black_height (t:Tree.t): nat :=
      match t with
      | Tree.Leaf => 0
      | Tree.Node Color.Black t1 _ _ => S (black_height t1)
      | Tree.Node Color.Red t1 _ _  => black_height t1
      end.

    Theorem black_height_correct:
        forall (h:nat) (c:Color.t) (t:Tree.t),
          R h c t ->
          h = black_height t.
    Proof
      fix f h c t rb :=
      match rb with
      | leaf => eq_refl
      | red x rb1 rb2 =>
        f _ _ _ rb1
      | black x rb1 rb2 =>
        Equal.inject (f _ _ _ rb1) S
      end.

    Theorem black_height_unique:
      forall (h1 h2:nat) (c1 c2:Color.t) (t:Tree.t),
        R h1 c1 t ->
        R h2 c2 t ->
        h1 = h2.
    Proof
      fun h1 h2 c1 c2 t rb1 rb2 =>
        Equal.join
          (black_height_correct rb1)
          (Equal.flip (black_height_correct rb2)).


    Theorem use_red_node0:
      forall (A:Prop) h t u x v,
        R h Color.Red t ->
        t = Tree.Node Color.Red u x v ->
        (R h Color.Black u ->
         R h Color.Black v ->
         R h Color.Red (Tree.Node Color.Red u x v) ->
         A) ->
        A.
    Proof
      fix f A h t u x v rb :=
      match rb with
      | leaf =>
        fun eq =>
          Tree.leaf_equal_node eq
      | red x rb1 rb2 =>
        fun eq f =>
          Tree.use_node_equal
            eq
            (fun ceq xeq ueq veq =>
               let rbu := Equal.use ueq _ rb1 in
               let rbv := Equal.use veq _ rb2 in
               let rbt :=
                   Equal.use xeq (fun x => R _ _ (Tree.Node _ _ x _))
                             (red x rbu rbv) in
               f rbu rbv rbt)
      | black x rb1 rb2 =>
        fun eq f =>
          Tree.use_node_equal
            eq
            (fun ceq _ _ _ => Color.black_equal_red ceq)
      end.


    Theorem use_black_node0:
      forall (A:Prop) h t u x v,
        R h Color.Black t ->
        t = Tree.Node Color.Black u x v ->
        (forall h cu cv,
            R h cu u ->
            R h cv v ->
            R (S h) Color.Black (Tree.Node Color.Black u x v) ->
            A) ->
        A.
    Proof
      fix f A h t u x v rb :=
      match rb with
      | leaf =>
        fun eq => Tree.leaf_equal_node eq
      | red x rb1 rb2 =>
        fun eq f =>
          Tree.use_node_equal
            eq
            (fun ceq _ _ _ => Color.red_equal_black ceq)
      | black x rb1 rb2 =>
        fun eq f =>
          Tree.use_node_equal
            eq
            (fun ceq xeq ueq veq =>
               let rbu := Equal.use ueq _ rb1 in
               let rbv := Equal.use veq _ rb2 in
               let rbt :=
                   Equal.use xeq (fun x => R _ _ (Tree.Node _ _ x _))
                             (black x rbu rbv) in
               f _ _ _ rbu rbv rbt)

      end.


    Theorem use_red_node:
      forall (A:Prop) h u x v,
        R h Color.Red (Tree.Node Color.Red u x v) ->
        (R h Color.Black u ->
         R h Color.Black v ->
         R h Color.Red (Tree.Node Color.Red u x v) ->
         A) ->
        A.
    Proof
      fun A h u x v rbt f =>
        use_red_node0 rbt eq_refl f.



    Theorem use_black_node:
      forall (A:Prop) h u x v,
        R h Color.Black (Tree.Node Color.Black u x v) ->
        (forall h cu cv,
            R h cu u ->
            R h cv v ->
            R (S h) Color.Black (Tree.Node Color.Black u x v) ->
            A) ->
        A.
    Proof
      fun A h u x v rbt f =>
        use_black_node0 rbt eq_refl f.

    Theorem use_left_red0:
      forall (A:Prop) h h0 c t u x v,
        R h c t ->
        t = Tree.Node c u x v ->
        R h0 Color.Red u ->
        (forall h cv,
            R h Color.Red u ->
            R h cv v ->
            R (S h) c (Tree.Node c u x v) ->
            A) ->
        A.
    Proof
      fun A h h0 c t u x v rbt =>
        match rbt with
        | leaf =>
          fun eq => Tree.leaf_equal_node eq
        | red x rb1 rb2 =>
          fun eq rbu f =>
            Tree.use_node_equal
              eq
              (fun eqc eqx eq1 eq2 =>
                 let rb1 := Equal.use eq1 (Red_black.R _ _) rb1 in
                 Color.black_equal_red (color_unique rb1 rbu))
        | black x rb1 rb2 =>
          fun eq rbu f =>
            Tree.use_node_equal
              eq
              (fun eqc eqx eq1 eq2 =>
                 let rb1 := Equal.use eq1 (Red_black.R _ _) rb1 in
                 let heq: _ = h0 := black_height_unique rb1 rbu in
                 let rbv :=
                     Equal.use2 heq eq2 (fun h t => Red_black.R h _ t) rb2 in
                 f _ _ rbu rbv
                   (Equal.use
                      eqx (fun x => R _ _ (Tree.Node _ _ x _))
                      (black x rbu rbv)))
        end.


    Theorem use_right_red0:
      forall (A:Prop) h h0 c t u x v,
        R h c t ->
        t = Tree.Node c u x v ->
        R h0 Color.Red v ->
        (forall h cu,
            R h cu u ->
            R h Color.Red v ->
            R (S h) c (Tree.Node c u x v) ->
            A) ->
        A.
    Proof
      fun A h h0 c t u x v rbt =>
        match rbt with
        | leaf =>
          fun eq => Tree.leaf_equal_node eq
        | red x rb1 rb2 =>
          fun eq rbv f =>
            Tree.use_node_equal
              eq
              (fun eqc eqx eq1 eq2 =>
                 let rb2 := Equal.use eq2 (Red_black.R _ _) rb2 in
                 Color.black_equal_red (color_unique rb2 rbv))
        | black x rb1 rb2 =>
          fun eq rbv f =>
            Tree.use_node_equal
              eq
              (fun eqc eqx eq1 eq2 =>
                 let rb2 := Equal.use eq2 (Red_black.R _ _) rb2 in
                 let heq: _ = h0 := black_height_unique rb2 rbv in
                 let rbu :=
                     Equal.use2 heq eq1 (fun h t => Red_black.R h _ t) rb1 in
                 f _ _ rbu rbv
                   (Equal.use
                      eqx (fun x => R _ _ (Tree.Node _ _ x _))
                      (black x rbu rbv)))
        end.


    Theorem use_left_red:
      forall (A:Prop) h h0 c1 c2 u x v,
        R h c1 (Tree.Node c2 u x v) ->
        R h0 Color.Red u ->
        (forall h cv,
            R h Color.Red u ->
            R h cv v ->
            R (S h) c2 (Tree.Node c2 u x v) ->
            A) ->
        A.
    Proof
      fun A h h0 c1 c2 u x v rbt rbu f =>
        let rbt := pull_color rbt in
        use_left_red0 rbt eq_refl rbu f.

    Theorem use_right_red:
      forall (A:Prop) h h0 c1 c2 u x v,
        R h c1 (Tree.Node c2 u x v) ->
        R h0 Color.Red v ->
        (forall h cu,
            R h cu u ->
            R h Color.Red v ->
            R (S h) c2 (Tree.Node c2 u x v) ->
            A) ->
        A.
    Proof
      fun A h h0 c1 c2 u x v rbt rbv f =>
        let rbt := pull_color rbt in
        use_right_red0 rbt eq_refl rbv f.
  End Red_black.





  (** * Sorted Red Black Trees *)
  (*  ------------------------ *)

  (** A sorted red black tree is a tree which is sorted as defined in the
  module [Binary_search_tree] and satisfies the red black invariant. *)
  Module Red_black_sorted.
    (** [P t] means that [t] is a sorted red black tree. *)
    Inductive P (t:Tree.t): Prop :=
      make:
        forall h c lo hi,
          Red_black.R h c t ->
          Sorted.R lo t hi ->
          P t.


    Theorem use_black_node:
      forall (A:Prop) (x:S.t) (u v: Tree.t),
        P (Tree.Node Color.Black u x v) ->
        (forall h cu cv lo hi,
            Red_black.R h cu u ->
            Red_black.R h cv v ->
            Red_black.R (S h) Color.Black (Tree.Node Color.Black u x v) ->
            lo <= x ->
            x <= hi ->
            Sorted.R lo u x ->
            Sorted.R x  v hi ->
            Sorted.R lo (Tree.Node Color.Black u x v) hi ->
            A) ->
        A.
    Proof
      fun A x u v p =>
        match p with
          make rbt st =>
          Red_black.use_black_node
            (Red_black.pull_color rbt)
            (fun h cu cv rbu rbv rbt f =>
               Sorted.use_node
                 st
                 (fun lox xhi su sv =>
                    f h cu cv _ _ rbu rbv rbt lox xhi su sv st))
        end.


    Theorem use_red_node:
      forall (A:Prop) (x:S.t) (u v: Tree.t),
        P (Tree.Node Color.Red u x v) ->
        (forall h lo hi,
            Red_black.R h Color.Black u ->
            Red_black.R h Color.Black v ->
            Red_black.R h Color.Red (Tree.Node Color.Red u x v) ->
            lo <= x ->
            x <= hi ->
            Sorted.R lo u x ->
            Sorted.R x v hi ->
            Sorted.R lo (Tree.Node Color.Red u x v) hi ->
            A) ->
        A.
    Proof
      fun A x u v p =>
        match p with
          make rbt st =>
          Red_black.use_red_node
            (Red_black.pull_color rbt)
            (fun rbu rbv rbt f =>
               Sorted.use_node
                 st
                 (fun lox xhi su sv =>
                    f _ _ _ rbu rbv rbt lox xhi su sv st))
        end.



    Theorem use_node:
      forall (A:Prop) c u x v,
        P (Tree.Node c u x v) ->
        (forall h h0 cu cv lo hi,
            Red_black.R h0 cu u ->
            Red_black.R h0 cv v ->
            Red_black.R h c (Tree.Node c u x v) ->
            lo <= x ->
            x <= hi ->
            Sorted.R lo u x ->
            Sorted.R x v hi ->
            Sorted.R lo (Tree.Node c u x v) hi ->
            A) ->
        A.
    Proof
      fun A c =>
        match c with
        | Color.Red =>
          fun u x v p f =>
            use_red_node
              p
              (fun h lo hi rbu rbv rbt lox xhi su sv st =>
                 f _ _ _ _ _ _ rbu rbv rbt lox xhi su sv st)
        | Color.Black =>
          fun u x v p f =>
            use_black_node
              p
              (fun h cu cv lo hi rbu rbv rbt lox xhi su sv st =>
                 f _ _ _ _ _ _ rbu rbv rbt lox xhi su sv st)
        end.



    Theorem use_node1:
      forall (A:Prop) (c:Color.t) (x:S.t) (u v:Tree.t),
        P (Tree.Node c u x v) ->
        (P u -> P v -> A) ->
        A.
    Proof
      fun A c x u v p =>
        use_node
          p
          (fun h h0 cu cv lo hi rbu rbv rbt lox xhi su sv st f =>
             f (make rbu su) (make rbv sv)).


    Theorem left_son:
      forall (c:Color.t) (x:S.t) (u v:Tree.t),
        P (Tree.Node c u x v) -> P u.
    Proof
      fun c x u v p =>
        use_node1
          p
          (fun pu pv => pu).


    Theorem right_son:
      forall (c:Color.t) (x:S.t) (u v:Tree.t),
        P (Tree.Node c u x v) -> P v.
    Proof
      fun c x u v p =>
        use_node1
          p
          (fun pu pv => pv).



    Theorem use_left_red:
      forall (A:Prop) (h:nat) (c:Color.t) (x:S.t) (u v: Tree.t),
        P (Tree.Node c u x v) ->
        Red_black.R h Color.Red u ->
        (forall h cv lo hi,
            Red_black.R h Color.Red u ->
            Red_black.R h cv v ->
            Red_black.R (S h) c (Tree.Node c u x v) ->
            lo <= x ->
            x <= hi ->
            Sorted.R lo u x ->
            Sorted.R x v hi ->
            Sorted.R lo (Tree.Node Color.Black u x v) hi ->
            A) ->
        A.
    Proof
      fun A h c x u v rbst =>
        match rbst with
          make rbt_0 st =>
          fun rbu f =>
            Red_black.use_left_red
              (Red_black.pull_color rbt_0) rbu
              (fun h cv rbu rbv rbt =>
                 let st := Sorted.change_extra Color.Black st in
                 Sorted.use_node
                   st
                   (fun lox xhi s1 s2 =>
                      f _ _ _ _ rbu rbv rbt lox xhi s1 s2 st))
        end.

    Theorem use_right_red:
      forall (A:Prop) (h:nat) (c:Color.t) (x:S.t) (u v: Tree.t),
        P (Tree.Node c u x v) ->
        Red_black.R h Color.Red v ->
        (forall h cu lo hi,
            Red_black.R h cu u ->
            Red_black.R h Color.Red v ->
            Red_black.R (S h) c (Tree.Node c u x v) ->
            lo <= x ->
            x <= hi ->
            Sorted.R lo u x ->
            Sorted.R x v hi ->
            Sorted.R lo (Tree.Node Color.Black u x v) hi ->
            A) ->
        A.
    Proof
      fun A h c x u v rbst =>
        match rbst with
          make rbt_0 st =>
          fun rbu f =>
            Red_black.use_right_red
              (Red_black.pull_color rbt_0) rbu
              (fun h cv rbu rbv rbt =>
                 let st := Sorted.change_extra Color.Black st in
                 Sorted.use_node
                   st
                   (fun lox xhi s1 s2 =>
                      f _ _ _ _ rbu rbv rbt lox xhi s1 s2 st))
        end.
  End Red_black_sorted.









  (** * Insertion into a Sorted Red Black Tree *)
  (*  ---------------------------------------- *)
  Module Insertion.
    Module Red_black_inserted.
      (** [R e r t u] means that the element [e] has been inserted into the
      tree [t] or has replaced an equivalent (depending on the replace flag
      [r]) resulting in the red black tree [u]. Note that both [t] and [u]
      must be sorted because of the definition of the [Inserted.R] relation of
      the module [Binary_search_tree]. *)
      Inductive R (e:S.t) (r:bool) (t u: Tree.t): Prop :=
        make:
          forall h c,
            Red_black.R h c u ->
            Inserted.R e r t u ->
            R e r t u.
    End Red_black_inserted.


    (** Result type of the insertion function. *)
    Definition result (e:S.t) (r:bool) (t:Tree.t): Type :=
      {u:Tree.t | Red_black_inserted.R e r t u}.


    (** Insertion always starts at a leaf node. An insertion into a leaf node
    results in a red singleton node. If the insertion happens below a red node
    we get a red red violation because a red node must not have any red son.*)

    (** The red red violation can be resolved at the level of the grandparent
    of the inserted node which must be black (otherwise the original tree
    would not satisfy the red black invariant) by pulling its blackness one
    level down. This might create a new red red violation which can bubble up
    to the root. At the root a red red violation can be resolved by painting
    the root node black. *)

    (** We define several propositions which describe the intermediate states
    of the insertion process.*)

    Module Red_red.
    (** [Red_red.R e r t a x b y c] means that [e] has been inserted into the
      valid red black tree [t] (or has replaced an equivalent) but the result
      has a red red violation. The trees [a], [b] and [c] are black and have
      the same black height as the original tree [t]. Such a violation can
      occur only if the original tree [t] is red.*)(**<<
                yR
             xR    c
           a    b
>>*)
      Inductive R
                (e:S.t) (r:bool) (t:Tree.t)
                (a:Tree.t) (x:S.t) (b:Tree.t) (y:S.t) (c:Tree.t): Prop :=
        make:
        forall h,
          Red_black.R h Color.Red t ->
          Red_black.R h Color.Black a ->
          Red_black.R h Color.Black b ->
          Red_black.R h Color.Black c ->
          Inserted.R e r t (Tree.Node Color.Red (Tree.Node Color.Red a x b) y c) ->
          R e r t a x b y c.
    End Red_red.

    Module Red.
    (** [Red.R e r t a x b] means that [e] has been inserted into the valid
      red black tree [t] (or has replaced an equivalent element) and the
      result is a red tree. The trees [a] and [b] are black and have the same
      black height as the original tree [t]. The original tree [t] can have
      any color.*)
(**<<
             xR
           a    b
>>*)
      Inductive R (e:S.t) (r:bool) (t:Tree.t)
                (a:Tree.t) (x:S.t) (b:Tree.t): Prop :=
        make:
          forall h c,
            Red_black.R h c t ->
            Red_black.R h Color.Black a ->
            Red_black.R h Color.Black b ->
            Inserted.R e r t (Tree.Node Color.Red a x b) ->
            R e r t a x b.
    End Red.

    Module Black.
    (** [Black.R e r t a x b] means that [e] has been inserted into the valid
      red black tree [t] (or has replaced an equivalent element) and the
      result is a black tree. The trees [a] and [b] are black and a black
      height one less than the original tree [t]. The original tree [t] must
      be black. Insertion into a red tree cannot result in a black tree
      without breaking the black height invariant.*)
(**<<
             xB
           a    b
>>*)
      Inductive R (e:S.t) (r:bool) (t:Tree.t)
                (a:Tree.t) (x:S.t) (b:Tree.t): Prop :=
        make:
          forall h ca cb,
            Red_black.R (S h) Color.Black t ->
            Red_black.R h ca a ->
            Red_black.R h cb b ->
            Inserted.R e r t (Tree.Node Color.Black a x b) ->
            R e r t a x b.
    End Black.

    (** The intermediate results with a red red violation or a valid red or a
    valid black tree can easily be turned into a final result at the root
    level.*)

    (** If we have a red red violation we just repaint the root node black. *)
(**<<
                yR                                    yB
            xR                                    xR
         a     b    c                          a     b    c
>>*)
    Theorem inserted_of_red_red:
      forall e r t  a x b y c,
        Red_red.R e r t a x b y c ->
        Red_black_inserted.R
          e r t
          (Tree.Node
             Color.Black
             (Tree.Node Color.Red a x b)
             y
             c).
    Proof
      fun e r t a x b y c rr =>
        match rr with
          Red_red.make rbt rba rbb rbc ins =>
          Red_black_inserted.make
            (Red_black.black y (Red_black.red x rba rbb) rbc)
            (Inserted.change_extra Color.Black ins)
        end.

    (** A red node is already valid. Nothing to be done. *)
    Theorem inserted_of_red:
      forall e r t a x b,
        Red.R e r t a x b ->
        Red_black_inserted.R
          e r t
          (Tree.Node Color.Red a x b).
    Proof
      fun e r t a x b r =>
        match r with
          Red.make _ rba rbb ins =>
          Red_black_inserted.make (Red_black.red _ rba rbb) ins
        end.

    (** A black node is already valid. Nothing to be done. *)
    Theorem inserted_of_black:
      forall e r t a x b,
        Black.R e r t a x b ->
        Red_black_inserted.R
          e r t
          (Tree.Node Color.Black a x b).
    Proof
      fun e r t a x b black =>
        match black with
          Black.make _ rba rbb ins =>
          Red_black_inserted.make (Red_black.black _ rba rbb) ins
        end.

    (** Intermediate results can be turned into intermediate results one level
    higher.*)


    (** If the insertion into a red left subtree results in a red red
    violation we use the blackness of the root and turn the tree into a valid
    red tree. *)
(**<<
            ynB       insertion              yR
        t1R   t2      into t1             xR     c
                                        a    b
    which we insert as the new left subtree
          ynB                                 yR
       yR     t2     rotate right         xB     ynB
     xR   c          repaint x           a  b   c  t2
    a  b
>>*)
    (** t2 has the same black height as [a,b,c]. The parent of t1 and t2 must
    be black because t1 is red. Therefore the resulting tree can have one
    black height level more than t1, a, b and c.*)
    Theorem red_of_left_red_red:
      forall e r cn t1 yn t2 a x b y c,
        Red_black_sorted.P (Tree.Node cn t1 yn t2) ->
        e <= yn ->
        (yn <= e -> r = false) ->
        Red_red.R e r t1 a x b y c ->
        Red.R e r
              (Tree.Node cn t1 yn t2)
              (Tree.Node Color.Black a x b)
              y
              (Tree.Node Color.Black c yn t2).
    Proof
      fun e r cn t1 yn t2 a x b y c rbs eyn yner rr =>
        match rr with
          Red_red.make rbt1_0 rba rbb rbc ins1 =>
          Red_black_sorted.use_left_red
            rbs
            rbt1_0
            (fun h ct2 lo hi rbt1 rbt2 rbt lo_yn yn_hi st1 st2 st =>
               let insu :=
                   Inserted.change_left_extra
                     Color.Black
                     (Inserted.rotate_right
                        (Inserted.left
                           cn Color.Black eyn yner st1 st2 ins1))
               in
               let heq: _ = h := Red_black.black_height_unique rbt1_0 rbt1 in
               let P t h := Red_black.R h _ t in
               Red.make
                 rbt
                 (Red_black.black
                    x
                    (Equal.use heq (P a) rba)
                    (Equal.use heq (P b) rbb))
                 (Red_black.black
                    yn
                    (Equal.use heq (P c) rbc)
                    rbt2)
                 insu)
        end.

    (** Same situation after insertion into the right subtree. *)
(**<<
            ynB        insertion             yR
         t1   t2R      into t2            xR     c
                                        a    b
    which we rotate right and insert as the new right subtree
          ynB                                 xR
       t1     xR     rotate left          ynB     yB
            a    yR  repaint y           t1  a   b  c
                b  c
>>*)
    Theorem red_of_right_red_red:
      forall e r cn t1 yn t2 a x b y c,
        Red_black_sorted.P (Tree.Node cn t1 yn t2) ->
        yn <= e ->
        (e <= yn -> r = false) ->
        Red_red.R e r t2 a x b y c ->
        Red.R e r
              (Tree.Node cn t1 yn t2)
              (Tree.Node Color.Black t1 yn a)
              x
              (Tree.Node Color.Black b y c).
    Proof
      fun e r cn t1 yn t2 a x b y c rbs yne eynr rr =>
        match rr with
          Red_red.make rbt2_0 rba rbb rbc ins2 =>
          Red_black_sorted.use_right_red
            rbs
            rbt2_0
            (fun h ct2 lo hi rbt1 rbt2 rbt lo_yn yn_hi st1 st2 st =>
               let insv :=
                   Inserted.change_right_extra
                     Color.Black
                     (Inserted.rotate_left
                        (Inserted.right
                           cn Color.Black yne eynr st1 st2
                           (Inserted.rotate_right ins2))) in
               let heq: _ = h := Red_black.black_height_unique rbt2_0 rbt2 in
               let P t h := Red_black.R h _ t in
               Red.make
                 rbt
                 (Red_black.black
                    yn
                    rbt1
                    (Equal.use heq (P a) rba))
                 (Red_black.black
                    y
                    (Equal.use heq (P b) rbb)
                    (Equal.use heq (P c) rbc))
                 insv)
        end.

    (** If insertion into the left subtree results in a red tree and the root
    is already red we get a red red violation.*)
(*<<
           ynR           insertion        xR
         t1   t2         into t1        a    b

           ynR
        xR    t2
       a  b
>>*)
    Theorem red_red_of_left_red:
      forall e r t1 yn t2 a x b,
        Red_black_sorted.P (Tree.Node Color.Red t1 yn t2) ->
        e <= yn ->
        (yn <= e -> r = false) ->
        Red.R e r t1 a x b ->
        Red_red.R
          e r (Tree.Node Color.Red t1 yn t2)
          a x b yn t2.
    Proof
      fun e r t1 yn t2 a x b rbst e_yn yn_e_r r =>
        match r with
          Red.make rbt1_0 rba rbb ins1 =>
          Red_black_sorted.use_red_node
            rbst
            (fun h lo hi rbt1 rbt2 rbt lo_yn yn_hi st1 st2 st =>
               let insu :=
                   Inserted.left
                     Color.Red Color.Red e_yn yn_e_r st1 st2 ins1 in
               let heq: _ = h := Red_black.black_height_unique rbt1_0 rbt1 in
               let P t h := Red_black.R h Color.Black t in
               Red_red.make
                 rbt
                 (Equal.use heq (P a) rba)
                 (Equal.use heq (P b) rbb)
                 rbt2
                 insu)
        end.

    (** Symmetrical situation for insertion into the right subtree.*)
(*<<
           ynR           insertion        xR
         t1   t2         into t2        a    b

           ynR           left             xR
         t1    xR        rotation      ynR   b
              a  b                   t1   a
>>*)
    Theorem red_red_of_right_red:
      forall e r t1 yn t2 a x b,
        Red_black_sorted.P (Tree.Node Color.Red t1 yn t2) ->
        yn <= e ->
        (e <= yn -> r = false) ->
        Red.R e r t2 a x b ->
        Red_red.R
          e r (Tree.Node Color.Red t1 yn t2)
          t1 yn a x b.
    Proof
      fun e r t1 yn t2 a x b rbst yn_e e_yn_r r =>
        match r with
          Red.make rbt2_0 rba rbb ins2 =>
          Red_black_sorted.use_red_node
            rbst
            (fun h lo hi rbt1 rbt2 rbt lo_yn yn_hi st1 st2 st =>
               let insv :=
                   Inserted.rotate_left
                     (Inserted.right
                        Color.Red Color.Red yn_e e_yn_r st1 st2 ins2) in
               let heq: _ = h := Red_black.black_height_unique rbt2_0 rbt2 in
               let P t h := Red_black.R h Color.Black t in
               Red_red.make
                 rbt
                 rbt1
                 (Equal.use heq (P a) rba)
                 (Equal.use heq (P b) rbb)
                 insv)
        end.



    (** Insertion into the left red subtree might result in a new red
    subtree. The left subtree can be red only if the root is black. Because
    the root is black we can insert the new left subtree into the original
    tree without violation. *)
(*<<
           ynB           insertion        xR
         t1R  t2         into t1        a    b

           ynB
        xR    t2
       a  b
>>*)
    Theorem black_of_left_red:
      forall e r t1 yn t2 a x b,
        Red_black_sorted.P (Tree.Node Color.Black t1 yn t2) ->
        e <= yn ->
        (yn <= e -> r = false) ->
        Red.R e r t1 a x b ->
        Black.R
          e r (Tree.Node Color.Black t1 yn t2)
          (Tree.Node Color.Red a x b)
          yn
          t2.
    Proof
      fun e r t1 yn t2 a x b rbst e_yn yn_e_r red =>
        match red with
          Red.make rbt1_0 rba rbb ins1 =>
          Red_black_sorted.use_black_node
            rbst
            (fun h ct1 ct2 lo hi rbt1 rbt2 rbt lo_yn yn_hi st1 st2 st =>
               let heq: _ = h := Red_black.black_height_unique rbt1_0 rbt1 in
               let P t h := Red_black.R h _ t in
               Black.make
                 rbt
                 (Red_black.red
                    x
                    (Equal.use heq (P a) rba)
                    (Equal.use heq (P b) rbb))
                 rbt2
                 (Inserted.left
                    Color.Black Color.Black e_yn yn_e_r st1 st2 ins1)
            )
        end.

    (** Symmetrical situtation for insertion into the right subtree. *)
    Theorem black_of_right_red:
      forall e r t1 yn t2 a x b,
        Red_black_sorted.P (Tree.Node Color.Black t1 yn t2) ->
        yn <= e ->
        (e <= yn -> r = false) ->
        Red.R e r t2 a x b ->
        Black.R
          e r (Tree.Node Color.Black t1 yn t2)
          t1
          yn
          (Tree.Node Color.Red a x b).
    Proof
      fun e r t1 yn t2 a x b rbst yn_e e_yn_r red =>
        match red with
          Red.make rbt2_0 rba rbb ins2 =>
          Red_black_sorted.use_black_node
            rbst
            (fun h ct1 ct2 lo hi rbt1 rbt2 rbt lo_yn yn_hi st1 st2 st =>
               let heq: _ = h := Red_black.black_height_unique rbt2_0 rbt2 in
               let P t h := Red_black.R h _ t in
               Black.make
                 rbt
                 rbt1
                 (Red_black.red
                    x
                    (Equal.use heq (P a) rba)
                    (Equal.use heq (P b) rbb))
                 (Inserted.right
                    Color.Black Color.Black yn_e e_yn_r st1 st2 ins2)
            )
        end.

    (** Insertion into the black left subtree might result in a new black left
    subtree. If the original root is black we can insert the new left black
    subtree.*)
    Theorem black_of_left_black:
      forall e r t1 yn t2 a x b,
        Red_black_sorted.P (Tree.Node Color.Black t1 yn t2) ->
        e <= yn ->
        (yn <= e -> r = false) ->
        Black.R e r t1 a x b ->
        Black.R
          e r (Tree.Node Color.Black t1 yn t2)
          (Tree.Node Color.Black a x b)
          yn
          t2.
    Proof
      fun e r t1 yn t2 a x b rbst e_yn yn_e_r black =>
        match black with
          Black.make rbt1_0 rba rbb ins1 =>
          Red_black_sorted.use_black_node
            rbst
            (fun h ct1 ct2 lo hi rbt1 rbt2 rbt lo_yn yn_hi st1 st2 st =>
               let heq: _ = h := Red_black.black_height_unique rbt1_0 rbt1 in
               Black.make
                 rbt
                 (Equal.use
                    heq (fun h => Red_black.R h _ _)
                    (Red_black.black x rba rbb))
                 rbt2
                 (Inserted.left Color.Black Color.Black e_yn yn_e_r st1 st2 ins1)
            )
        end.



    (** Symmetrical situtation for insertion into the right subtree. *)
    Theorem black_of_right_black:
      forall e r t1 yn t2 a x b,
        Red_black_sorted.P (Tree.Node Color.Black t1 yn t2) ->
        yn <= e ->
        (e <= yn -> r = false) ->
        Black.R e r t2 a x b ->
        Black.R
          e r (Tree.Node Color.Black t1 yn t2)
          t1
          yn
          (Tree.Node Color.Black a x b).
    Proof
      fun e r t1 yn t2 a x b rbst yn_e e_yn_r black =>
        match black with
          Black.make rbt2_0 rba rbb ins2 =>
          Red_black_sorted.use_black_node
            rbst
            (fun h ct1 ct2 lo hi rbt1 rbt2 rbt lo_yn yn_hi st1 st2 st =>
               let heq: _ = h := Red_black.black_height_unique rbt2_0 rbt2 in
               Black.make
                 rbt
                 rbt1
                 (Equal.use
                    heq (fun h => Red_black.R h _ _)
                    (Red_black.black x rba rbb))
                 (Inserted.right Color.Black Color.Black yn_e e_yn_r st1 st2 ins2)
            )
        end.



    (** Insertion into the black left subtree might result in a new black left
    subtree. If the original root is red we can insert the new left black
    subtree and the resulting tree stays red. *)
    Theorem red_of_left_black:
      forall e r t1 yn t2 a x b,
        Red_black_sorted.P (Tree.Node Color.Red t1 yn t2) ->
        e <= yn ->
        (yn <= e -> r = false) ->
        Black.R e r t1 a x b ->
        Red.R
          e r (Tree.Node Color.Red t1 yn t2)
          (Tree.Node Color.Black a x b)
          yn
          t2.
    Proof
      fun e r t1 yn t2 a x b rbst e_yn yn_e_r black =>
        match black with
          Black.make rbt1_0 rba rbb ins1 =>
          Red_black_sorted.use_red_node
            rbst
            (fun h lo hi rbt1 rbt2 rbt lo_yn yn_hi st1 st2 st =>
               let heq: _ = h := Red_black.black_height_unique rbt1_0 rbt1 in
               Red.make
                 rbt
                 (Equal.use
                    heq (fun h => Red_black.R h _ _)
                    (Red_black.black x rba rbb))
                 rbt2
                 (Inserted.left Color.Red Color.Red e_yn yn_e_r st1 st2 ins1)
            )
        end.


    (** Symmetrical situtation for insertion into the right subtree. *)
    Theorem red_of_right_black:
      forall e r t1 yn t2 a x b,
        Red_black_sorted.P (Tree.Node Color.Red t1 yn t2) ->
        yn <= e ->
        (e <= yn -> r = false) ->
        Black.R e r t2 a x b ->
        Red.R
          e r (Tree.Node Color.Red t1 yn t2)
          t1
          yn
          (Tree.Node Color.Black a x b).
    Proof
      fun e r t1 yn t2 a x b rbst yn_e e_yn_r black =>
        match black with
        | Black.make rbt2_0 rba rbb ins2 =>
          Red_black_sorted.use_red_node
            rbst
            (fun h lo hi rbt1 rbt2 rbt lo_yn yn_hi st1 st2 st =>
               let heq: _ = h := Red_black.black_height_unique rbt2_0 rbt2 in
               Red.make
                 rbt
                 rbt1
                 (Equal.use
                    heq (fun h => Red_black.R h _ _)
                    (Red_black.black x rba rbb))
                 (Inserted.right Color.Red Color.Red yn_e e_yn_r st1 st2 ins2)
            )
        end.



    (** An intermediate insert result is either a red red violation or a valid
    red tree or a valid black tree.*)
    Inductive result0 (e:S.t) (r:bool) (t:Tree.t): Type :=
    | Red_red:
        forall a x b y c,
          Red_red.R e r t a x b y c ->
          result0 e r t
    | Red:
        forall a x b,
          Red.R e r t a x b ->
          result0 e r t
    | Black:
        forall a x b,
          Black.R e r t a x b ->
          result0 e r t.

    (** Insertion of a new element [e] into a sorted red black tree [t].*)
    Fact insert (e:S.t) (r:bool) (t:Tree.t)
         (rbs:Red_black_sorted.P t): result e r t.
    Proof
      let insert0:
            forall r t,
              Red_black_sorted.P t -> result0 e r t :=
          fix insert0 r t :=
            match t with

            | Tree.Leaf =>
              fun _ =>
                let rbl := Red_black.leaf in
                Red (Red.make rbl rbl rbl (Inserted.leaf Color.Red e r))

            | Tree.Node cn t1 yn t2 =>

              let insert_left r e_yn (yn_e_r: yn <= e -> r = false) rbs :=
                  (match insert0 r t1 (Red_black_sorted.left_son rbs), cn with
                   | Red_red red_red, _ =>

                     fun _ => Red (red_of_left_red_red rbs e_yn yn_e_r red_red)

                   | Red red, Color.Red =>

                     fun rbs => Red_red (red_red_of_left_red rbs e_yn yn_e_r red)

                   | Red red, Color.Black =>

                     fun rbs => Black (black_of_left_red rbs e_yn yn_e_r red)

                   | Black black, Color.Black =>

                     fun rbs => Black (black_of_left_black rbs e_yn yn_e_r black)

                   | Black black, Color.Red =>

                     fun rbs => Red (red_of_left_black rbs e_yn yn_e_r black)
                  end) rbs
              in
              let insert_right r yn_e (e_yn_r:e <= yn -> r = false) rbs :=
                  (match insert0 r t2 (Red_black_sorted.right_son rbs), cn with
                   | Red_red red_red, _ =>

                     fun _ =>
                       Red (red_of_right_red_red rbs yn_e e_yn_r red_red)

                   | Red red, Color.Red =>

                     fun rbs => Red_red (red_red_of_right_red rbs yn_e e_yn_r red)

                   | Red red, Color.Black =>

                     fun rbs => Black (black_of_right_red rbs yn_e e_yn_r red)

                   | Black black, Color.Red =>

                     fun rbs =>  Red (red_of_right_black rbs yn_e e_yn_r black)

                   | Black black, Color.Black =>

                     fun rbs => Black (black_of_right_black rbs yn_e e_yn_r black)
                  end) rbs
              in
              let replace r (rtrue:r = true) e_yn yn_e rbst :=
                  match cn with

                  | Color.Red =>
                    fun rbst =>
                      let red :=
                          Red_black_sorted.use_red_node
                            rbst
                            (fun h lo hi rbt1 rbt2 rbt lo_yn yn_hi st1 st2 st =>
                               Red.make
                                 rbt rbt1 rbt2
                                 (Inserted.replace
                                    Color.Red Color.Red
                                    (conj e_yn yn_e) rtrue st1 st2))
                      in
                      Red red
                  | Color.Black =>

                    fun rbst =>
                      let black :=
                          Red_black_sorted.use_black_node
                            rbst
                            (fun h ct1 ct2 lo hi rbt1 rbt2 rbt
                                 lo_yn yn_hi st1 st2 st =>
                               Black.make
                                 rbt rbt1 rbt2
                                 (Inserted.replace
                                    Color.Black Color.Black
                                    (conj e_yn yn_e) rtrue st1 st2))
                      in
                      Black black
                  end
              in

              match S.compare3 e yn with

              | Relation.LT e_yn not_yn_e =>

                let yn_e_r: yn <= e -> r = false :=
                    fun yn_e => ex_falso (not_yn_e yn_e) in
                insert_left r e_yn yn_e_r

              | Relation.EQV e_yn yn_e =>

                match r with
                | true =>
                  replace true eq_refl e_yn yn_e rbs
                | false =>
                  insert_right false yn_e (fun _ => eq_refl)
                end

              | Relation.GT yn_e not_e_yn =>

                let e_yn_r: e <= yn -> r = false :=
                    fun e_yn => ex_falso (not_e_yn e_yn) in
                insert_right r yn_e e_yn_r
              end
            end
      in
      match insert0 r t rbs with
      | Red_red rr =>
        exist _ _ (inserted_of_red_red rr)
      | Red r =>
        exist _ _ (inserted_of_red r)
      | Black b =>
        exist _ _ (inserted_of_black b)
      end.
  End Insertion.
End Make.
