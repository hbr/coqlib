Require Import Core.
Require Import String_.

Parameter int:Set.
Parameter zero:int.
Parameter one:int.
Parameter  int_plus: int -> int -> int.
Extract Inlined Constant int  => "int".
Extract Inlined Constant zero => "0".
Extract Inlined Constant one  => "1".
Extract Inlined Constant int_plus => "(+)".

Parameter ocaml_exit: int -> unit.
Extract Constant ocaml_exit => "exit".

Module Character.
  Definition newline:ascii := "010"%char.
End Character.

Module String_.
  Definition newline:string := String Character.newline EmptyString.
  Parameter normal: string -> string.
  Extract Constant normal =>
  "(fun (p,s) -> if p=0 then (p,s) else 0,String.(sub s p (length s - p)))".
End String_.

Inductive Result (A B:Type): Type :=
| Ok:    A -> Result A B
| Error: B -> Result A B.
Arguments Ok [A B] _.
Arguments Error [A B] _.



Inductive with_exit (A:Type): Type :=
| Normal: A -> with_exit A
| Exit: int -> with_exit A.
Arguments Normal [A] _.

Module Type IO_TYPE.
  Parameter t: Type -> Type.
  Parameter bind: forall {A B:Type}, t A -> (A -> t B) -> t B.
  Parameter map:  forall {A B:Type}, (A->B) -> t A -> t B.
  Parameter exit: int -> t (with_exit unit).
  Parameter execute: t (with_exit unit) -> unit.

  Parameter ocaml_put_string: string -> t unit.
  Parameter ocaml_put_line: string -> t unit.
  Parameter get_line: t (option string).
  Parameter put_string: string -> t unit.
  Parameter put_newline: t unit.
  Parameter put_line: string -> t unit.

  Parameter iterate:
    forall (A S:Type), t A -> S -> (A->S->t unit*S) -> (S->bool) -> t unit * S.
  Parameter interactive:
    (string -> option string) -> t (with_exit unit).
End IO_TYPE.

Module IO: IO_TYPE.
  Section basics.
    Definition t (A:Type): Type := unit -> A.
    Definition make {A:Type} (a:A): t A := fun _ => a.
    Definition bind {A B:Type} (m:t A) (f:A -> t B): t B :=
      f (m tt).
    Definition map {A B:Type} (f:A->B) (m:t A): t B :=
      bind m (fun a => make (f a)).
    Definition join {A:Type} (m: t (t A)): t A :=
      bind m (fun m_inner => m_inner).
    Definition exit (code:int): t (with_exit unit) := make (Exit _ code).
    Definition execute (m: t (with_exit unit)): unit :=
      match m tt with
      | Normal _ => ocaml_exit zero
      | Exit _ code => ocaml_exit code
      end.
  End basics.

  Parameter get_line: t (option string).

  Parameter ocaml_put_string: string -> t unit.

  Parameter ocaml_put_line: string -> t unit.

  Definition put_string (s:string): t unit :=
    ocaml_put_string (String_.normal s).

  Parameter put_newline: t unit.

  Definition put_line (s:string): t unit :=
    ocaml_put_line (String_.normal s).


  Parameter iterate:
    forall {B S:Type} (action: t B)
            (start:S) (f:B->S->t unit*S) (d:S->bool),
      t unit*S.


  Definition interactive (f:string -> option string): t (with_exit unit) :=
    let (m,s) :=
        iterate
          get_line
          true
          (fun s_opt _ =>
             match s_opt with
             | None =>
               (make tt, false)
             | Some s =>
               (put_line s, true)
             end)
          (fun x => x)
    in
    map (fun _ => Exit _ zero) m.

End IO.

Extract Constant IO.get_line =>
"fun _ -> try Some (0,Pervasives.read_line ()) with End_of_file -> None".

Extract Constant IO.ocaml_put_string =>
"fun (p,s) _ -> Pervasives.print_string s".

Extract Constant IO.ocaml_put_line =>
"fun (p,s) _ -> Pervasives.print_endline s".

Extract Constant IO.put_newline => "Pervasives.print_newline".

Extract Constant IO.iterate =>
  "fun (a:'b t) (s:'s) (f:'b->'s->(unit t)*'s) (d:'s->bool) ->
       let rec iter (s:'s): unit t*'s =
         if d s then
           let m,s = bind a (fun b -> f b s) in
           (m (); iter s) (* evalute the last action *)
         else make (),s
       in
       iter s".


(*
Module Process.
    Inductive with_exit (A:Type): Type :=
    | Normal: A -> with_exit A
    | Exit: int -> with_exit A.
    Arguments Normal [A] _.
    Arguments Exit   [A] _.

    CoInductive stream (A:Type): Type :=
    | Cons: A -> stream A -> stream A.
    Arguments Cons [A] _ _.

    CoFixpoint zeroes : stream nat := Cons 0 zeroes.
    CoFixpoint from (n:int): stream int := Cons n (from (int_plus n one)).

    Recursive Extraction from.
    (*
        type 'a stream = 'a __stream Lazy.t
        and 'a __stream =
        | Cons of 'a * 'a stream

        (** val from : int -> int stream **)

        let rec from n =
          lazy (Cons (n, (from ((+) n one))))
     *)
End Process.
*)
