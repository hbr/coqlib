Require Import Core.

Set Implicit Arguments.
Set Warnings "-extraction-opaque-accessed".

Module Notations.
  Notation "[ ]" := nil (format "[ ]") : list_scope.
  Notation "[ x ]" := (cons x nil) : list_scope.
  Notation "[ x ; y ; .. ; z ]" :=
    (cons x (cons y .. (cons z nil) ..)) : list_scope.
  Open Scope list.
End Notations.

Import Notations.
Import Equal.Notations.

(** * Append and Reverse *)
(*  -------------------- *)

Section app_rev.
  Variable A: Type.

  (** The standard library of Coq defines the function [app] in the form [[
      Fixpoint app a b :=
        match a with
        | [] => b
        | x::xs => x :: (app xs b)
        end.]]
   and introduces the notation [a ++ b]  for [app a b].*)

  (** This recursive definition is not tail recursive but its time complexity
  is linear with the size of the first list. In this section we derive some
  properties about list appending.  *)

  Theorem app_associative:
    forall a b c: list A,
      (a ++ b) ++ c = a ++ b ++ c.  (* '++' is right associative *)
  Proof
    fix f a b c :=
    match a with
    | [] => eq_refl
    | x :: a => Equal.inject (f a b c) (fun l => x :: l)
    end.



  Theorem app_nil_right_neutral:
    forall a: list A,
      a ++ [] = a.
  Proof
    fix f a :=
    match a with
    | [] => eq_refl
    | x :: a => Equal.inject (f a) (fun l => x :: l)
    end.



  (** For list reversal we define a straightforward recursive function which
  is neither tail recursive nor linear. *)

  Fixpoint rev (a:list A): list A :=
    match a with
    | [] => []
    | x :: a => rev a ++ [x]
    end.

  Theorem rev_distributes_app:
    forall a b: list A,
      rev (a ++ b) = rev b ++ rev a.
  Proof
    fix f a b :=
    match a with
    | [] => Equal.use_bwd
              (app_nil_right_neutral (rev b))
              (fun l => _ = l)
              eq_refl
    | x :: a =>
      (equality_chain:
         (eq_refl: rev ((x::a)++b) = rev (x::(a++b))),
         (eq_refl: _ = rev (a++b) ++ [x]),
         (Equal.inject (f a b) (fun l => l ++ _): _ = (rev b ++ rev a) ++ [x]),
         (app_associative (rev b) (rev a) [x]:  _ = rev b ++ rev a ++ [x]),
         (eq_refl: _ = rev b ++ rev (x::a)))
    end.


  Theorem rev_involutive:
    forall a: list A,
      rev (rev a) = a.
  Proof
    fix f a :=
    match a with
    | [] => eq_refl
    | x :: a =>
      (equality_chain:
         (eq_refl : rev (rev (x :: a)) = rev (rev a ++ [x])),
         (rev_distributes_app _ _ : _ = rev [x] ++  rev (rev a)),
         (Equal.use_bwd (f a) (fun l => rev [x] ++ l = x :: a) eq_refl
           :  _ = x :: a))
    end.

End app_rev.



(** * Fast Append and Reverse *)
(*  ------------------------- *)
Section fast_app_rev.
  Variable A: Type.

  (** This section defines functions for efficient list reversal and list
  append. The functions are tail recursive and perform in linear time. *)

  Fact reverse_append (xs ys:list A): {b:list A | b = rev xs ++ ys}.
  Proof
    (fix f a b: rev a ++ b = rev xs ++ ys ->
                {b | b = rev xs ++ ys} :=
       match a with
       | [] =>
         fun inv =>
           exist
             _ b
             inv
       | x :: tl =>
         fun inv =>
           f tl (x::b)
             (equality_chain:
                (Equal.flip (app_associative (rev tl) [x] b)
                 : rev tl ++ x :: b  =  (rev tl ++ [x]) ++ b),
                (eq_refl: _ = rev (x :: tl) ++ b),
                (inv: _ = rev xs ++ ys))
       end
    ) xs ys eq_refl.

  Fact reverse (a:list A):  {b:list A | b = rev a}.
  Proof
    match reverse_append a [] with
    | exist _ b eq =>
      exist _ b
            (Equal.join eq (app_nil_right_neutral _))
    end.

  Fact append (a b:list A): {c:list A | c = a ++ b}.
  Proof
    match (reverse a) with
    | exist _ ra pa =>
      match reverse_append ra b with
      | exist _ c pc =>
        exist
          _ c
          ((equality_chain:
              (pc: c = rev ra ++ b),
              (Equal.use
                 pa
                 (fun x => _ = rev x ++ b)
                 eq_refl
               : _ = rev (rev a) ++ b),
              (
                Equal.use_bwd
                  (rev_involutive a)
                  (fun x => x ++ b = a ++ b)
                  eq_refl
               : _ = a ++ b)
           )
           : c = a ++ b)
      end
    end.
End fast_app_rev.
