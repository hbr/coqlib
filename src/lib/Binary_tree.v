Require Import Core.
Require List.
Require Import Coq.Lists.List.
Import ListNotations.
Import Equal.Notations.

Set Implicit Arguments.

Module Make
       (A:ANY)  (* Elements *)
       (E:ANY). (* Extra Info *)


(** * List *)
(*    ==== *)
  Module List.
    Definition L: Type := list A.t.

    Inductive Permutation: L -> L -> Prop :=
    | perm_empty:
        Permutation [] []
    | perm_prefix:
        forall x a b, Permutation a b -> Permutation (x::a) (x::b)
    | perm_swap:
        forall x y a,  Permutation (x::y::a) (y::x::a)
    | perm_transitive:
        forall a b c,  Permutation a b -> Permutation b c -> Permutation a c.
  End List.


  (*====================================*)
  (** * Tree                            *)
  (*====================================*)
  Module Tree.
    Inductive t: Type :=
    | Leaf: t
    | Node: E.t -> t -> A.t -> t -> t.

    Definition is_Node (a:t): Prop :=
      match a with
      | Leaf => False
      | Node _ _ _ _ => True
      end.

    Definition is_Leaf (a:t): Prop :=
      match a with
      | Leaf => True
      | Node _ _ _ _ => False
      end.

    Definition extra (a:t): is_Node a -> E.t :=
      match a with
      | Leaf =>
        fun nd => ex_falso nd
      | Node e _ _ _ =>
        fun _ => e
      end.

    Definition change_extra (e:E.t) (a:t): t :=
      match a with
      | Leaf => Leaf
      | Node _ t1 x t2 => Node e t1 x t2
      end.

    Theorem node_equal_leaf
            {A:Type} {e:E.t} {x:A.t} {u v:t}
            (eq:Node e u x v = Leaf): A.
    Proof
      ex_falso (Equal.use eq is_Node I).

    Theorem leaf_equal_node
            {A:Type} {e:E.t} {x:A.t} {u v:t}
            (eq:Leaf = Node e u x v): A.
    Proof
      node_equal_leaf (Equal.flip eq).

  Theorem use_node_equal:
    forall {A:Prop} (e1 e2:E.t) (x1 x2:A.t) (t1 t2 u1 u2:t),
      Node e1 t1 x1 u1 = Node e2 t2 x2 u2 ->
      (e1=e2 -> x1=x2 -> t1=t2 -> u1=u2 -> A)
      -> A.
  Proof
    fun A e1 e2 x1 x2 t1 t2 u1 u2 eq P =>
      let extra t :=
          match t with
          | Leaf => e1
          | Node e _ _ _  => e
          end in
      let elem t :=
          match t with
          | Leaf => x1
          | Node c t x u => x
          end in
      let left t :=
          match t with
          | Leaf => t1
          | Node c t x u => t
          end in
      let right t :=
          match t with
          | Leaf => t2
          | Node c t x u => u
          end in
      P (Equal.inject eq extra)
        (Equal.inject eq elem)
        (Equal.inject eq left)
        (Equal.inject eq right).
  End Tree.


  (*====================================*)
  (** * Elements of the Tree            *)
  (*====================================*)
  Module Domain.
    (** [Domain.R t x] means that the tree [t] has at least one node with
    the element [x].*)
    Inductive R: Tree.t -> A.t -> Prop :=
    | left:
        forall e u x y v,
            R u x ->
            R (Tree.Node e u y v) x
    | root:
        forall e u x v,
            R (Tree.Node e u x v) x
    | right:
        forall e u x y v,
            R v x ->
            R (Tree.Node e u y v) x.

    (** A leaf does not have any elements.*)
    Theorem leaf_empty:
      forall x, ~ R Tree.Leaf x.
    Proof
      let lemma:
            forall x t, R t x -> t <> Tree.Leaf :=
          fix f x t r :=
            match r with
            | left e y v ru =>
              fun eq => Tree.node_equal_leaf eq
            | root eqv e u v =>
              fun eq => Tree.node_equal_leaf eq
            | right e u y rv =>
              fun eq => Tree.node_equal_leaf eq
            end in
      fun x rt => lemma x Tree.Leaf rt eq_refl.

    Theorem use_node:
      forall (A:Prop) x e u y v,
        R (Tree.Node e u y v) x ->
        (x = y -> A) ->
        (R u x -> A) ->
        (R v x -> A) ->
        A.
    Proof
      fun A x e u y v dom feq f1 f2 =>
        let lemma:
              forall e x t u y v,
                R t x ->
                t = Tree.Node e u y v ->
              _ -> _ -> _ -> A :=
            fun e x t u y v dom =>
              match dom with
              | left e y v domu =>
                fun eq =>
                  Tree.use_node_equal
                    eq
                    (fun eeq xeq ueq veq feq fu fv =>
                       fu (Equal.use ueq (fun u => R u _) domu))
              | root e u x v =>
                fun eq =>
                  Tree.use_node_equal
                    eq
                    (fun eeq xeq ueq veq feq fu fv =>
                       feq xeq)
              | right e u y domv =>
                fun eq =>
                  Tree.use_node_equal
                    eq
                    (fun eeq xeq ueq veq feq fu fv =>
                       fv (Equal.use veq (fun v => R v _) domv))
              end
        in
        lemma e x (Tree.Node e u y v) u y v dom eq_refl feq f1 f2.
  End Domain.




  (*====================================*)
  (** * Inorder Sequence                *)
  (*====================================*)
  Module Inorder.
    Inductive R: Tree.t -> list A.t -> Prop :=
    | leaf: R Tree.Leaf []
    | node:
        forall c t1 l1 x t2 l2,
          R t1 l1 ->
          R t2 l2 ->
          R (Tree.Node c t1 x t2) (l1 ++ x :: l2).

    Fixpoint make (t:Tree.t): list A.t :=
      match t with
      | Tree.Leaf => []
      | Tree.Node c t x u => make t ++ x :: (make u)
      end.

    Theorem of_list:
      forall (t:Tree.t) (l:list A.t),
        l = make t ->
        R t l.
    Proof
      fix f t :=
      match t with
      | Tree.Leaf =>
        fun l (eq: l = make Tree.Leaf) =>
          let p := leaf in
          Equal.use
            (Equal.flip eq)
            (fun l => R Tree.Leaf l)
            leaf
      | Tree.Node c u x v =>
        fun l (eq: l = make (Tree.Node c u x v)) =>
          Equal.use
            (Equal.flip eq)
            (fun l => R _ l)
            (node c x (f u (make u) eq_refl) (f v (make v) eq_refl))
      end.


    Theorem to_list:
      forall (t:Tree.t) (l:list A.t),
        R t l ->
        l = make t.
    Proof
      fix f t l r {struct r}:=
      match r with
      | leaf =>
        eq_refl: [] = make Tree.Leaf
      | node c x r1 r2 =>
        Equal.use2
           (Equal.flip (f _ _ r1) : make _ = _)
           (Equal.flip (f _ _ r2) : make _ = _)
           (fun a b => a ++ x :: b = _)
           eq_refl
        : _ ++ x :: _ = make (Tree.Node c _ x _)
      end.


    Theorem make_correct (t:Tree.t): R t (make t).
    Proof
      (fix f t :=
      match t with
      | Tree.Leaf => leaf:R Tree.Leaf (make Tree.Leaf)
      | Tree.Node c t x u =>
        node c x (f t) (f u) : R _ (make (Tree.Node c t x u))
      end) t.

    Theorem unique:
      forall (t:Tree.t) (a b:list A.t),
        R t a ->
        R t b ->
        a = b.
    Proof
      fun t a b r1 r2 =>
        let p := to_list r1 in
        Equal.join (to_list r1) (Equal.flip (to_list r2)).
  End Inorder.




  (*====================================*)
  (** * Rotations                       *)
  (*====================================*)
  Module Rotation.
    Inductive R: Tree.t -> Tree.t -> Prop :=
    | leaf:
        R Tree.Leaf Tree.Leaf
    | left:
        forall c1 c2 c3 c4 a x b y c,
          R (Tree.Node c1 a x (Tree.Node c2 b y c))
            (Tree.Node c3 (Tree.Node c4 a x b) y c)
    | right:
        forall c1 c2 c3 c4 a x b y c,
          R (Tree.Node c1 (Tree.Node c2 a x b) y c)
            (Tree.Node c3 a x (Tree.Node c4 b y c))
    | node:
        forall c1 c2 x t11 t12 t21 t22,
          R t11 t12 ->
          R t21 t22 ->
          R (Tree.Node c1 t11 x t21) (Tree.Node c2 t12 x t22)
    | transitive:
        forall t1 t2 t3,
          R t1 t2 -> R t2 t3 -> R t1 t3.

  Theorem reflexive:
    forall (t:Tree.t), R t t.
  Proof
    fix f t :=
    match t with
    | Tree.Leaf => leaf
    | Tree.Node c t1 x t2 =>
      let r1 := f t1 in
      let r2 := f t2 in
      node c c x r1 r2
    end.

  Theorem to_node:
    forall (u v:Tree.t),
      R u v ->
      Tree.is_Node u ->
      Tree.is_Node v.
  Proof
    fix f u v rot :=
    match rot with
    | leaf =>
    fun nd => ex_falso nd
    | left c1 c2 c3 c4 a x b y c =>
      fun nd => I
    | right c1 c2 c3 c4 a x b y c =>
      fun nd => I
    | node  c1 c2 x rt ru =>
      fun nd => I
    | transitive ruv rvw =>
      fun ndu => f _ _ rvw (f _ _ ruv ndu)
    end.


  Theorem symmetric:
    forall (u v:Tree.t),
      R u v ->
      R v u.
  Proof
    fix f u v rot :=
    match rot with
    | leaf =>
      leaf
    | left c1 c2 c3 c4 a x b y c =>
      right c3 c4 c1 c2 a x b y c
    | right c1 c2 c3 c4 a x b y c =>
      left c3 c4 c1 c2 a x b y c
    | node c1 c2 x rt ru =>
      node c2 c1 x (f _ _ rt) (f _ _ ru)
    | transitive ruv rvw =>
      transitive (f _ _ rvw) (f _ _ ruv)
    end.


  Theorem change_extra:
    forall (e:E.t) (u v:Tree.t),
      R u v ->
      R u (Tree.change_extra e v).
  Proof
    fix f cnew u v rot :=
    match rot with
    | leaf => leaf
    | left c1 c2 c3 c4 a x b y c =>
      left c1 c2 cnew c4 a x b y c
    | right c1 c2 c3 c4 a x b y c =>
      right c1 c2 cnew c4 a x b y c
    | node c1 c2 x r1 r2 =>
      node c1 cnew x r1 r2
    | transitive r12 r23 =>
      transitive r12 (f _ _ _ r23)
    end.

  Theorem change_extra1:
    forall (e:E.t) (u v w:Tree.t),
      R u v ->
      w = Tree.change_extra e v ->
      R u w.
  Proof
    fun e u v w rot eq =>
      Equal.use_bwd eq _ (change_extra e rot).





  (** Rotations keep the inorder sequence. The proof recurses over all
  constructors of a rotation.

  The left and right rotation use the associativity of list append.

  The node construction uses the fact that rotations of the sons keep their
  inorder sequence. Using this we can transform an inorder sequence of the
  node before the rotation into the same inorder sequence of the node after
  rotation.

  Transitivity is a simple application of two rotations keeping the inorder
  sequence.*)
  Theorem keep_inorder:
    forall (t u:Tree.t),
      R t u ->
      forall l,
        Inorder.R t l ->
        Inorder.R u l.
  Proof
    fix f t u rot:=
    match rot with
    | leaf =>
      fun l ord => ord
    | @left c1 c2 c3 c4 a x b y c =>
      fun l inord =>
        let t := Tree.Node c1 a x (Tree.Node c2 b y c) in
        let u := Tree.Node c3 (Tree.Node c4 a x b) y c in
        let eq: l = Inorder.make u :=
            Equal.join
               (Inorder.to_list inord
                : l = _ ++ x :: _ ++ y :: _)
               (Equal.flip (List.app_associative _ (x::_) (y::_))
                : _ = (_ ++ x :: _) ++ y :: _)
        in
        Inorder.of_list u eq
        : Inorder.R u l
    | @right c1 c2 c3 c4 a x b y c =>
      fun l inord =>
        let t := Tree.Node c1 (Tree.Node c2 a x b) y c in
        let u := Tree.Node c3 a x (Tree.Node c4 b y c) in
        let eq : l = Inorder.make u :=
            Equal.join
               (Inorder.to_list inord: l = (_ ++ x :: _) ++ y :: _)
               (List.app_associative _ (x::_) (y::_)
                : _ = _ ++ x :: _ ++ y :: _)
        in
        Inorder.of_list u eq: Inorder.R u l
    | @node c1 c2 x t1 t2 u1 u2 rt ru =>
      fun l ord =>
        let t := Tree.Node c1 t1 x u1 in
        let u := Tree.Node c2 t2 x u2 in
        let eq: l = Inorder.make u :=
            (equality_chain:
               (Inorder.to_list ord
                : l = Inorder.make t1 ++ x :: Inorder.make u1),
               (
                Equal.use2
                  (Inorder.to_list (f _ _ rt _ (Inorder.make_correct t1))
                   : Inorder.make t1 = Inorder.make t2)
                  (Inorder.to_list (f _ _ ru _ (Inorder.make_correct u1))
                   : Inorder.make u1 = Inorder.make u2)
                  (fun a b => _ = a ++ x :: b)
                  eq_refl
                : _ = Inorder.make t2 ++ x :: Inorder.make u2)
            )
        in
        Inorder.of_list u eq : Inorder.R u l
    | @transitive u v w ruv rvw =>
      fun l ord_ul =>
        f v w rvw l (f u v ruv  l ord_ul)
    end.
  End Rotation.





  (*====================================*)
  (** * Basic Definitions               *)
  (*====================================*)
  Section basic_definitions.
    Inductive tree: Type :=
    | Empty: tree
    | Node:  E.t -> tree -> A.t ->  tree -> tree.

    Definition is_Node (t:tree): Prop :=
      match t with
      | Empty => False
      | Node _ _ _ _ => True
      end.

    Theorem node_not_empty:
      forall(a:A.t) (i:E.t) (t1 t2: tree),
        Node i t1 a t2 <> Empty.
    Proof
      fun a i t1 t2 p =>
        Equal.rewrite is_Node p I.

    Definition is_node (t:tree): {is_Node t} + {~ is_Node t} :=
      match t return {is_Node t} + {~ is_Node t} with
        Empty => right (fun p:False => match p with end)
      | Node _ _ _ _ => left I
      end.

    Inductive Element: tree -> A.t -> Prop :=
    | element_node:
        forall a e t1 t2, Element (Node e t1 a t2) a.

    Inductive Extra: tree -> E.t -> Prop :=
    | extra_node:
        forall e t1 a t2, Extra (Node e t1 a t2) e.

    Theorem extra_is_node: forall (t:tree) (e:E.t), Extra t e -> is_Node t.
    Proof
      fun t e extra =>
        match extra in Extra t _ return is_Node t with
        | extra_node a e t1 t2 => I
        end.

    Definition left_son (t_:tree): is_Node t_ -> tree :=
      match t_ with
      | Empty => fun nd => match nd with end
      | Node e t1 a t2 => fun _ => t1
      end.

    Definition right_son (t_:tree): is_Node t_ -> tree :=
      match t_ with
      | Empty => fun nd => match nd with end
      | Node a e t1 t2 => fun _ => t2
      end.

    Definition element (t_:tree): is_Node t_ -> A.t :=
      match t_ with
      | Empty => fun nd => match nd with end
      | Node e t1 a t2 => fun _ => a
      end.

    Definition extra (t_:tree): is_Node t_ -> E.t :=
      match t_ with
      | Empty => fun nd => match nd with end
      | Node e t1 a t2 => fun _ => e
      end.

    Theorem left_son_correct:
      forall (a:A.t) (e:E.t) (t1 t2:tree),
        t1 = left_son (Node e t1 a t2) I.
    Proof
      fun a e t1 t2 => eq_refl.

    Theorem right_son_correct:
      forall (a:A.t) (e:E.t) (t1 t2:tree),
        t2 = right_son (Node e t1 a t2) I.
    Proof
      fun a e t1 t2 => eq_refl.

    Theorem element_correct:
      forall (a:A.t) (e:E.t) (t1 t2:tree),
        a = element (Node e t1 a t2) I.
    Proof
      fun a e t1 t2 => eq_refl.

    Theorem extra_correct:
      forall (a:A.t) (e:E.t) (t1 t2:tree),
        e = extra (Node e t1 a t2) I.
    Proof
      fun a e t1 t2 => eq_refl.

    Theorem node_injective_extra:
      forall (a1 a2:A.t) (e1 e2:E.t) (t11 t12 t21 t22:tree),
        Node e1 t11 a1 t12 = Node e2 t21 a2 t22 ->
        e1 = e2.
    Proof
      let f e0 t :=
          match t with
          | Empty => e0
          | Node e t1 a t2 => e
          end
      in
      fun a1 a2 e1 e2 t11 t12 t21 t22 eq =>
        Equal.inject
          eq
          (f e1).

    Theorem node_injective_element:
      forall (a1 a2:A.t) (e1 e2:E.t) (t11 t12 t21 t22:tree),
        Node e1 t11 a1 t12 = Node e2 t21 a2 t22 ->
        a1 = a2.
    Proof
      let f a0 t :=
          match t with
          | Empty => a0
          | Node e t1 a t2 => a
          end
      in
      fun a1 a2 e1 e2 t11 t12 t21 t22 eq =>
        Equal.inject
          eq
          (f a1).

    Theorem node_injective_left_son:
      forall (a1 a2:A.t) (e1 e2:E.t) (t11 t12 t21 t22:tree),
        Node e1 t11 a1 t12 = Node e2 t21 a2 t22 ->
        t11 = t21.
    Proof
      let f t0 t :=
          match t with
          | Empty => t0
          | Node e t1 a t2 => t1
          end
      in
      fun a1 a2 e1 e2 t11 t12 t21 t22 eq =>
        Equal.inject
          eq
          (f t11).

    Theorem node_injective_right_son:
      forall (a1 a2:A.t) (e1 e2:E.t) (t11 t12 t21 t22:tree),
        Node e1 t11 a1 t12 = Node e2 t21 a2 t22 ->
        t12 = t22.
    Proof
      let f t0 t :=
          match t with
          | Empty => t0
          | Node a e t1 t2 => t2
          end
      in
      fun a1 a2 e1 e2 t11 t12 t21 t22 eq =>
        Equal.inject
          eq
          (f t21).
  End basic_definitions.



  (*====================================*)
  (** * Height                          *)
  (*====================================*)
  Section height.
    Inductive Height: tree -> nat -> Prop :=
    | empty_height:
        Height Empty 0
    | node_height:
        forall t1 h1 t2 h2 a i,
          Height t1 h1 ->
          Height t2 h2 ->
          Height (Node i t1 a t2) (1 + max h1 h2).

    Fixpoint height (t_:tree): nat :=
      match t_ with
      | Empty => 0
      | Node _ t1 _ t2 =>
        1 + max (height t1) (height t2)
      end.

    Theorem height_is_only_height:
      forall (t_:tree) (h:nat),
        Height t_ h ->
        h = height t_.
    Proof
      fix f t h ph :=
      match ph in Height t h
            return h = height t
      with
      | empty_height => eq_refl
      | node_height a i ph1 ph2 =>
        let p1 := f _ _ ph1 in
        let p2 := f _ _ ph2 in
        (equality_chain:
           (eq_refl: 1 + max _ _ = _ ),
           (Equal.inject p1 (fun x => 1 + max x _ )),
           (Equal.inject p2 (fun x => 1 + max _ x ))
        )
      end.

    Theorem height_is_height:
      forall t_:tree, Height t_ (height t_).
    Proof
      fix f t :=
      match t return Height t (height t) with
      | Empty =>
        empty_height
      | Node i t1 a t2 =>
        node_height a i (f t1) (f t2)
      end.

    Theorem height_is_unique:
      forall (t_:tree) (h1 h2:nat),
        Height t_ h1 ->
        Height t_ h2 ->
        h1 = h2.
    Proof
      fix f t h1 h2 p1 p2 :=
      (equality_chain:
         height_is_only_height p1,
         (Equal.flip (height_is_only_height p2))).
  End height.





  (*====================================*)
  (** * Leftmost and Rightmost          *)
  (*====================================*)
  Section leftmost_and_rightmost.
    Inductive Leftmost: tree -> A.t -> Prop :=
    | lm_noleft:
        forall a e t2, Leftmost (Node e Empty a t2) a
    | lm_left:
        forall x a e t1 t2,
          Leftmost t1 x ->
          Leftmost (Node e t1 a t2) x.

    Inductive Rightmost: tree -> A.t -> Prop :=
    | rm_noright:
        forall a e t1, Rightmost (Node e t1 a Empty) a
    | rm_right:
        forall x a e t1 t2,
          Rightmost t2 x ->
          Rightmost (Node e t1 a t2) x.

    Theorem leftmost_is_node:
      forall (t_:tree) (a:A.t),
        Leftmost t_ a -> is_Node t_.
    Proof
      fix f t a lm :=
      match lm in Leftmost t a
            return is_Node t with
      | lm_noleft _ _ _ => I
      | lm_left _ _ _ _ => I
      end.

    Theorem rightmost_is_node:
      forall (t_:tree) (a:A.t),
        Rightmost t_ a -> is_Node t_.
    Proof
      fix f t a rm :=
      match rm in Rightmost t a
            return is_Node t with
      | rm_noright _ _ _ => I
      | rm_right _ _ _ _ => I
      end.




    Fixpoint leftmost (t_:tree): is_Node t_ -> A.t :=
      match t_ return is_Node t_ -> A.t with
      | Empty =>
        fun nd => match nd with end
      | Node e t1 a t2 =>
        match is_node t1 with
        | left  nd => fun _ => leftmost t1 (nd:is_Node t1)
        | right _  => fun _ => a
        end
      end.


    Theorem leftmost_correct:
      forall (t_:tree) (nd:is_Node t_),
        Leftmost t_ (leftmost t_ nd).
    Proof
      let P t nd := Leftmost t (leftmost t nd) in
      fix f t :=
      match t return forall nd, P t nd with
      | Empty => fun nd => match nd with end
      | Node e t1 a t2 =>
        fun nd =>
          (match t1
                 return (forall nd1, P t1 nd1) -> P (Node e t1 a t2) nd
           with
           | Empty =>
             fun _ =>
               Equal.rewrite_bwd
                 (fun x => Leftmost _ x)
                 (eq_refl: leftmost (Node e Empty a t2) I = a)
                 (lm_noleft a e t2)
           | Node a1 e1 t11 t12 =>
             let t1_ := Node a1 e1 t11 t12 in
             fun p1: forall nd1, P t1_ nd1 =>
               @lm_left (leftmost t1_ I) a e t1_ t2 (p1 I)
           end) (f t1)
      end.



    Fixpoint rightmost (t_:tree): is_Node t_ -> A.t :=
      match t_ return is_Node t_ -> A.t with
      | Empty =>
        fun nd => match nd with end
      | Node e t1 a t2 =>
        match is_node t2 with
        | left  nd => fun _ => rightmost t2 (nd:is_Node t2)
        | right p  => fun _ => a
        end
      end.

    Theorem rightmost_correct:
      forall (t_:tree) (nd:is_Node t_),
        Rightmost t_ (rightmost t_ nd).
    Proof
      let P t nd := Rightmost t (rightmost t nd) in
      fix f t :=
      match t return forall nd, P t nd with
      | Empty => fun nd => match nd with end
      | Node e t1 a t2 =>
        fun nd =>
          (match t2
                 return (forall nd2, P t2 nd2) -> P (Node e t1 a t2) nd
           with
           | Empty =>
             fun _ =>
               Equal.rewrite
                 (fun x => Rightmost _ x)
                 (Equal.flip eq_refl: a = rightmost (Node e t1 a Empty) I)
                 (rm_noright a e t1)
           | Node e2 t21 a2 t22 =>
             let t2_ := Node e2 t21 a2 t22 in
             fun p2: forall nd2, P t2_ nd2 =>
               @rm_right (rightmost t2_ I) a e t1 t2_ (p2 I)
           end) (f t2)
      end.
  End leftmost_and_rightmost.






  (*====================================*)
  (** * Inorder Sequence                *)
  (*====================================*)
  (* Inorder t xs:  'xs' is the inorder sequence of 't'.*)
  Section inorder_sequence.
    Inductive Inorder: tree -> list A.t -> Prop :=
    | empty_inorder: Inorder Empty []
    | node_inorder:
        forall t1 xs1 t2 xs2 a e,
          Inorder t1 xs1 ->
          Inorder t2 xs2 ->
          Inorder (Node e t1 a t2) (xs1 ++ a :: xs2).

    Fixpoint inorder (t_:tree): list A.t :=
      match t_ with
      | Empty => []
      | Node e t1 a t2 =>
        inorder t1 ++ a :: inorder t2
      end.


    Theorem inorder_correct:
      forall t_:tree, Inorder t_ (inorder t_).
    Proof
      fix f t :=
      match t return Inorder t (inorder t) with
      | Empty => empty_inorder
      | Node e t1 a t2 =>
        @node_inorder t1 (inorder t1) t2 (inorder t2) a e (f t1) (f t2)
      end.

    Theorem inorder_unique:
      forall (t_:tree) (xs:list A.t),
        Inorder t_ xs ->
        xs = inorder t_.
    Proof
      fix f t xs ord :=
      match ord in Inorder t xs
            return xs = inorder t with
      | empty_inorder => eq_refl
      | @node_inorder t1 xs1 t2 xs2 a e ord1 ord2 =>
        let eq1: xs1 = inorder t1 := f t1 xs1 ord1 in
        let eq2: xs2 = inorder t2 := f t2 xs2 ord2 in
        (equality_chain:
           (eq_refl: xs1 ++ a :: xs2 = _),
           (Equal.rewrite0 eq1 (fun xs => _ = xs ++ a :: xs2) eq_refl
            : _ = inorder t1 ++ a :: xs2),
           (Equal.rewrite0 eq2 (fun xs => _ = inorder t1 ++ a :: xs) eq_refl
            : _ = inorder t1 ++ a :: inorder t2))
      end.

    Definition Same_inorder (t1 t2:tree): Prop :=
      inorder t1 = inorder t2.

  End inorder_sequence.
End Make.
