(** * Environments

  We have three kinds of environments:
  - Σ the global signature, containing definitions and interfaces.
  - Ξ the extension environment.
  - Γ the local environment.

*)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import AST SubstNotations RAsimpl AST_rasimpl.
From LocalComp Require Import Util BasicAST.

Import ListNotations.

(** Local environment, a list of types *)
Definition ctx := list term.

(** ** Custom computation rule

  We consider them as definitional equalities which might be nonlinear.
  For implementation purposes however, it's better to have a linear version
  (as well as pattern syntax) so we consider the left-hand side as the result of
  applying a "forcing" substitution.

  To make the inlining proof easier and more general, we will consider an
  equation proxy where the substitution is already applied.

  Fields are
  - [cr_env]: the environment of the rule [Θ]
  - [cr_pat]: the "pattern" for the left-hand side [p]
  - [cr_sub]: the "forcing" substitution [ρ] to go from [p] to the actual lhs
  - [cr_rep]: the replacing term [r]
  - [cr_typ]: the type for both sides [A]

  This represents the following (typed) definitional equality:
  [Θ ⊢ l <[ρ] ≡ r : A]

*)
Record crule := {
  cr_env : ctx ;
  cr_pat : term ;
  cr_sub : nat → term ;
  cr_rep : term ;
  cr_typ : term
}.

Record equation := {
  eq_env : ctx ;
  eq_lhs : term ;
  eq_rhs : term ;
  eq_typ : term
}.

Definition crule_eq rule : equation := {|
  eq_env := rule.(cr_env) ;
  (* eq_lhs := rule.(cr_pat) <[ rule.(cr_sub) ] ; *)
  eq_lhs := subst_term rule.(cr_sub) rule.(cr_pat) ;
  eq_rhs := rule.(cr_rep) ;
  eq_typ := rule.(cr_typ)
|}.

(** ** Notations *)

Notation "'∙'" :=
  (@nil term).

Notation "Γ ,, d" :=
  (@cons term d Γ) (at level 20, d at next level).

Notation "Γ ,,, Δ" :=
  (@List.app term Δ Γ) (at level 25, Δ at next level, left associativity).
