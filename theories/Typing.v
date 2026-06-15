(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool.
From LocalComp.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.

Notation Typ := (Sort S_Typ).
Notation PTyp := (Sort S_PTyp).

(** ** Closedness property *)

Fixpoint scoped n t :=
  match t with
  | var m => m <? n
  | Sort _ _ => true
                
  | Pi A B => scoped n A && scoped (S n) B
  | lam A t => scoped n A && scoped (S n) t
  | app u v => scoped n u && scoped n v

  end.

Notation closed t := (scoped 0 t).

Notation scoped_instance k ξ :=
  (forallb (λ t, onSomeb (scoped k) t) ξ).

Notation closed_instance ξ :=
  (scoped_instance 0 ξ).

Reserved Notation "Γ ⊢ t : A"
  (at level 80, t, A at next level).

Reserved Notation "Γ ⊨ t : A"
  (at level 80, t, A at next level).

Reserved Notation "u ≡ v"
  (at level 80).

Inductive conversion : term → term → Prop :=

(** Computation rules *)

| conv_beta :
    ∀ A t u,
      app (lam A t) u ≡ t <[ u .. ]

(** Congruence rules *)

| cong_Pi :
    ∀ A A' B B',
      A ≡ A' →
      B ≡ B' →
      Pi A B ≡ Pi A' B'

| cong_lam :
    ∀ A A' t t',
      A ≡ A' →
      t ≡ t' →
      lam A t ≡ lam A' t'

| cong_app :
    ∀ u u' v v',
      u ≡ u' →
      v ≡ v' →
      app u v ≡ app u' v'

(** Structural rules *)

| conv_refl :
    ∀ u,
      u ≡ u

| conv_sym :
    ∀ u v,
      u ≡ v →
      v ≡ u

| conv_trans :
    ∀ u v w,
      u ≡ v →
      v ≡ w →
      u ≡ w

where "u ≡ v" := (conversion u v).

Inductive styping (Γ : ctx) : term → term → Prop :=

| stype_var :
    ∀ x A,
      nth_error Γ x = Some A →
      Γ ⊢ var x : (plus (S x)) ⋅ A

| stype_sort :
    ∀ s i,
      Γ ⊢ Sort s i : Sort s (S i)

| stype_pi :
    ∀ s s' i j A B,
      Γ ⊢ A : Sort s i →
      Γ ,, A ⊢ B : Sort s' j →
      Γ ⊢ Pi A B : Sort s' (max i j)
                        
| stype_lam :
    ∀ s s' i j A B t,
      Γ ⊢ A : Sort s i →
      Γ ,, A ⊢ B : Sort s' j →
      Γ ,, A ⊢ t : B →
      Γ ⊢ lam A t : Pi A B

| stype_app :
    ∀ s s' i j A B t u,
      Γ ⊢ t : Pi A B →
      Γ ⊢ u : A →
      Γ ⊢ A : Sort s i →
      Γ ,, A ⊢ B : Sort s' j →
      Γ ⊢ app t u : B <[ u .. ]

| stype_conv :
    ∀ s i A B t,
      Γ ⊢ t : A →
      A ≡ B →
      Γ ⊢ B : Sort s i →
      Γ ⊢ t : B

where "Γ ⊢ t : A" := (styping Γ t A).

Inductive ttyping (Γ : ctx) : term → term → Prop :=

| ttype_var :
    ∀ x A,
      nth_error Γ x = Some A →
      Γ ⊨ var x : (plus (S x)) ⋅ A

| ttype_typ :
    ∀ i,
      Γ ⊨ Typ i : Typ (S i)
                      
| ttype_pi :
    ∀ i j A B,
      Γ ⊨ A : Typ i →
      Γ ,, A ⊨ B : Typ j →
      Γ ⊨ Pi A B : Typ (max i j)
                        
| ttype_lam :
    ∀ i j A B t,
      Γ ⊨ A : Typ i →
      Γ ,, A ⊨ B : Typ j →
      Γ ,, A ⊨ t : B →
      Γ ⊨ lam A t : Pi A B

| ttype_app :
    ∀ i j A B t u,
      Γ ⊨ t : Pi A B →
      Γ ⊨ u : A →
      Γ ⊨ A : Typ i →
      Γ ,, A ⊨ B : Typ j →
      Γ ⊨ app t u : B <[ u .. ]

| ttype_conv :
    ∀ i A B t,
      Γ ⊨ t : A →
      A ≡ B →
      Γ ⊨ B : Typ i →
      Γ ⊨ t : B

where "Γ ⊨ t : A" := (ttyping Γ t A).

(** ** Context formation *)

Inductive wf : ctx → Prop :=
| wf_nil : wf ∙
| wf_cons :
    ∀ Γ s i A,
      wf Γ →
      Γ ⊢ A : Sort s i →
      wf (Γ ,, A).

(** Automation *)

Create HintDb conv discriminated.
Create HintDb type discriminated.

Hint Resolve conv_beta cong_Pi cong_lam cong_app conv_refl
: conv.

Hint Resolve stype_var stype_sort stype_pi
  stype_lam stype_app
  : type.

Hint Resolve ttype_var ttype_typ ttype_pi ttype_lam ttype_app
: type.

Ltac ttconv :=
  unshelve typeclasses eauto with conv shelvedb ; shelve_unifiable.

Ltac tttype :=
  unshelve typeclasses eauto with type shelvedb ; shelve_unifiable.
