(** * Interface instantiation *)

From Stdlib Require Import Utf8 List.
From LocalComp.autosubst Require Import AST SubstNotations RAsimpl AST_rasimpl.
From LocalComp Require Import Util BasicAST Env.
Import ListNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.

(** ** Unrelated utility

  TODO MOVE

*)

(** n-ary application *)

Fixpoint apps (u : term) (l : list term) :=
  match l with
  | [] => u
  | v :: l => apps (app u v) l
  end.

(** Substitution lifting *)

Fixpoint ups n σ :=
  match n with
  | 0 => σ
  | S n => up_term (ups n σ)
  end.
