From Stdlib Require Import Utf8 String.

Set Primitive Projections.

(** Universe level *)
Definition level := nat.

Inductive sort :=
| S_Typ
| S_PTyp.
