Require Import Core.
Require Binary_tree.
Require Import List.
Set Implicit Arguments.

Module Make (S0:SORTABLE) (Extra:ANY).
  Module S := Sortable_plus S0.
  Import S.Notations.

  Module BT := Binary_tree.Make S Extra.
  Include BT.
  Export  BT.

  (*====================================*)
  (** * Basic Definitions               *)
  (*====================================*)
End Make.
