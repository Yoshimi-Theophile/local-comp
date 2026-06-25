(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool.
From LocalComp.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From LocalComp Require Import Util BasicAST.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.

(* Contexts *)

Notation sctx := (list (sort * term)).
Notation scope := (list sort).

Notation tctx := (list term).

Definition sc (Γ : sctx) : scope :=
  map fst Γ.
  
Notation "'∙s'" :=
  (@nil (sort * term)).

Notation "Γ ,,s d" :=
  (@cons (sort * term) d Γ) (at level 20, d at next level).

Notation "Γ ,,,s Δ" :=
  (@List.app (sort * term) Δ Γ) (at level 25, Δ at next level, left associativity).

Notation "'∙t'" :=
  (@nil term).

Notation "Γ ,,t d" :=
  (@cons term d Γ) (at level 20, d at next level).

Notation "Γ ,,,t Δ" :=
  (@List.app term Δ Γ) (at level 25, Δ at next level, left associativity).

(* Typing Notation *)

Notation Typ := (Sort S_Typ).
Notation PTyp := (Sort S_PTyp).

Notation Pi_T := (Pi S_Typ S_Typ).
Notation Pi_P := (Pi S_PTyp S_PTyp).
Notation Pi_PT := (Pi S_PTyp S_Typ).
Notation Pi_TP := (Pi S_Typ S_PTyp).

Notation lam_T := (lam S_Typ S_Typ).
Notation lam_P := (lam S_PTyp S_PTyp).
Notation lam_PT := (lam S_PTyp S_Typ).
Notation lam_TP := (lam S_Typ S_PTyp).

Notation app_T := (app S_Typ S_Typ).
Notation app_P := (app S_PTyp S_PTyp).
Notation app_PT := (app S_PTyp S_Typ).
Notation app_TP := (app S_Typ S_PTyp).

(* Scoping *)

Inductive scoping (Γ : scope) : term → sort → Prop :=

| scope_var :
    ∀ x s,
      nth_error Γ x = Some s →
      scoping Γ (var x) s

| scope_sort :
    ∀ s i,
      scoping Γ (Sort s i) s

| scope_pi :
    ∀ i j s s' A B,
      scoping Γ A s →
      scoping (s :: Γ) B s' →
      scoping Γ (Pi s s' i j A B) s'

| scope_lam :
    ∀ s s' A t,
      scoping Γ A s →
      scoping (s :: Γ) t s' →
      scoping Γ (lam s s' A t) s'

| scope_app :
    ∀ s s' t u,
      scoping Γ t s' →
      scoping Γ u s →
      scoping Γ (app s s' t u) s'.

Notation cscoping Γ := (scoping (sc Γ)).

Definition st (Γ : scope) (t : term) : sort :=
  match t with
  | var x => List.nth x Γ S_Typ
  | Sort s l => s
  | Pi _ s' _ _ _ _  => s'
  | lam _ s' _ _ => s'
  | app _ s' _ _ => s'
  | _ => S_Typ
  end.

Notation stc Γ t := (st (sc Γ) t).

Lemma scoping_md :
  ∀ Γ t m,
    scoping Γ t m →
    st Γ t = m.
Proof.
  intros Γ t m h.
  induction h. all: try reflexivity.
  now apply nth_error_nth.
Qed.

(* Typing Notation *)

Reserved Notation "Γ ⊢ t : A"
  (at level 80, t, A at next level).

Reserved Notation "Γ ⊨ t : A"
  (at level 80, t, A at next level).

Reserved Notation "u ≡ v"
  (at level 80).

Inductive conversion : term → term → Prop :=

(** Computation rules *)

| conv_beta :
    ∀ s s' A t u,
      app s s' (lam s s' A t) u ≡ t <[ u .. ]

(** Congruence rules *)

| cong_Pi :
    ∀ s s' i j A A' B B',
      A ≡ A' →
      B ≡ B' →
      Pi s s' i j A B ≡ Pi s s' i j A' B'

| cong_lam :
    ∀ s s' A A' t t',
      A ≡ A' →
      t ≡ t' →
      lam s s' A t ≡ lam s s' A' t'

| cong_app :
    ∀ s s' u u' v v',
      u ≡ u' →
      v ≡ v' →
      app s s' u v ≡ app s s' u' v'

| cong_Sigma :
  ∀ A A' B B',
    A ≡ A' →
    B ≡ B' →
    Sigma A B ≡ Sigma A' B'

| cong_sig :
  ∀ t t' u u',
    t ≡ t' →
    u ≡ u' →
    sig t u ≡ sig t' u'

| cong_pi1 :
  ∀ t t',
    t ≡ t' →
    pi1 t ≡ pi1 t'

| cong_pi2 :
  ∀ t t',
    t ≡ t' →
    pi2 t ≡ pi2 t'

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

Inductive styping (Γ : sctx) : term → term → Prop :=

| stype_var :
    ∀ x A s,
      nth_error Γ x = Some (s, A) →
      Γ ⊢ var x : (plus (S x)) ⋅ A

| stype_sort :
    ∀ s i,
      Γ ⊢ Sort s i : Sort s (S i)

| stype_Pi :
    ∀ s s' i j A B,
      Γ ⊢ A : Sort s i →
      Γ ,,s (s, A) ⊢ B : Sort s' j →
      Γ ⊢ Pi s s' i j A B : Sort s' (max i j)
                        
| stype_lam :
    ∀ s s' i j A B t,
      Γ ⊢ A : Sort s i →
      Γ ,,s (s, A) ⊢ B : Sort s' j →
      Γ ,,s (s, A) ⊢ t : B →
      Γ ⊢ lam s s' A t : Pi s s' i j A B

| stype_app :
    ∀ s s' i j A B t u,
      Γ ⊢ t : Pi s s' i j A B →
      Γ ⊢ u : A →
      Γ ⊢ A : Sort s i →
      Γ ,,s (s, A) ⊢ B : Sort s' j →
      Γ ⊢ app s s' t u : B <[ u .. ]

| stype_conv :
    ∀ s i A B t,
      Γ ⊢ t : A →
      A ≡ B →
      Γ ⊢ B : Sort s i →
      Γ ⊢ t : B

where "Γ ⊢ t : A" := (styping Γ t A).

Inductive ttyping (Γ : tctx) : term → term → Prop :=

| ttype_var :
    ∀ x A,
      nth_error Γ x = Some A →
      Γ ⊨ var x : (plus (S x)) ⋅ A

| ttype_typ :
    ∀ i,
      Γ ⊨ Typ i : Typ (S i)
                      
| ttype_Pi :
    ∀ i j A B,
      Γ ⊨ A : Typ i →
      Γ ,,t A ⊨ B : Typ j →
      Γ ⊨ Pi_T i j A B : Typ (max i j)
                        
| ttype_lam :
    ∀ i j A B t,
      Γ ⊨ A : Typ i →
      Γ ,,t A ⊨ B : Typ j →
      Γ ,,t A ⊨ t : B →
      Γ ⊨ lam_T A t : Pi_T i j A B

| ttype_app :
    ∀ i j A B t u,
      Γ ⊨ t : Pi_T i j A B →
      Γ ⊨ u : A →
      Γ ⊨ A : Typ i →
      Γ ,,t A ⊨ B : Typ j →
      Γ ⊨ app_T t u : B <[ u .. ]

| ttype_unit :
    ∀ i, Γ ⊨ unit : Typ i

| ttype_tt :
    Γ ⊨ tt : unit

| ttype_Sigma :
    ∀ i j A B,
      Γ ⊨ A : Typ i →
      Γ ,,t A ⊨ B : Typ j →
      Γ ⊨ Sigma A B : Typ (max i j)
                         
| ttype_sig :
    ∀ i j A B t u,
      Γ ⊨ A : Typ i → 
      Γ ⊨ t : A →
      Γ ,,t A ⊨ B : Typ j →
      Γ ,,t A ⊨ u : B →
      Γ ⊨ sig t u : Sigma A B

| ttype_pi1 :
    ∀ i j A B t,
      Γ ⊨ A : Typ i →
      Γ ,,t A ⊨ B : Typ j →
      Γ ⊨ t : Sigma A B →
      Γ ⊨ pi1 t : A

| ttype_pi2 :
    ∀ i j A B t,
      Γ ⊨ A : Typ i →
      Γ ,,t A ⊨ B : Typ j →
      Γ ⊨ t : Sigma A B →
      Γ ⊨ pi2 t : B <[ (pi1 t) .. ]
                    
| ttype_conv :
    ∀ i A B t,
      Γ ⊨ t : A →
      A ≡ B →
      Γ ⊨ B : Typ i →
      Γ ⊨ t : B

where "Γ ⊨ t : A" := (ttyping Γ t A).

(** ** Context formation *)

Inductive swf : sctx → Prop :=
| swf_nil : swf ∙s
| swf_cons :
    ∀ Γ s i A,
      swf Γ →
      Γ ⊢ A : Sort s i →
      swf (Γ ,,s (s, A)).

Inductive twf : tctx → Prop :=
| wf_nil : twf ∙t
| wf_cons :
    ∀ Γ i A,
      twf Γ →
      Γ ⊨ A : Typ i →
      twf (Γ ,,t A).

(** Automation *)

Create HintDb conv discriminated.
Create HintDb type discriminated.

Hint Resolve conv_beta cong_Pi cong_lam cong_app conv_refl
: conv.

Hint Resolve stype_var stype_sort stype_Pi stype_lam stype_app
  : type.

Hint Resolve ttype_var ttype_typ ttype_Pi ttype_lam ttype_app
             ttype_unit ttype_tt ttype_Sigma ttype_sig ttype_pi1 ttype_pi2
: type.

Ltac ttconv :=
  unshelve typeclasses eauto with conv shelvedb ; shelve_unifiable.

Ltac tttype :=
  unshelve typeclasses eauto with type shelvedb ; shelve_unifiable.
