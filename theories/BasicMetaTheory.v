(** Basic meta-theory *)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Typing.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Require Import Equations.Prop.DepElim.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

(** Scoping Lemmas, taken from GhostTT *)

(** Substitution preserves modes **)

Definition rscoping (Γ : scope) (ρ : nat → nat) (Δ : scope) : Prop :=
  ∀ x m,
    nth_error Δ x = Some m →
    nth_error Γ (ρ x) = Some m.

Inductive σscoping (Γ : scope) (σ : nat → term) : scope → Prop :=
| scope_nil : σscoping Γ σ []
| scope_cons :
    ∀ Δ s,
      σscoping Γ (↑ >> σ) Δ →
      scoping Γ (σ var_zero) s →
      σscoping Γ σ (s :: Δ).

Lemma rscoping_S Γ s :
    rscoping (s :: Γ) S Γ.
Proof.
  intros x s' e.
  cbn. assumption.
Qed.

Lemma rscoping_shift Γ Δ ρ s :
    rscoping Γ ρ Δ →
    rscoping (s :: Γ) (0 .: ρ >> S) (s :: Δ).
Proof.
  intros h' y s' e.
  destruct y.
  - simpl in *. assumption.
  - simpl in *. apply h'. assumption.
Qed.

Lemma scoping_ren Γ Δ ρ t s :
    rscoping Γ ρ Δ →
    scoping Δ t s →
    scoping Γ (ren_term ρ t) s.
Proof.
  intros hρ ht.
  pose proof rscoping_shift as lem.
  induction ht in Γ, ρ, hρ, lem |- *.
  all: solve [ rasimpl ; econstructor ; eauto ].
Qed.

Lemma σscoping_weak Γ Δ σ s :
    σscoping Γ σ Δ →
    σscoping (s :: Γ) (σ >> ren_term ↑) Δ.
Proof.
  intros h.
  induction h.
  - constructor.
  - constructor.
    + assumption.
    + rasimpl. eapply scoping_ren. 2: eassumption.
      apply rscoping_S.
Qed.

Lemma scoping_subst Γ Δ σ t s :
    σscoping Γ σ Δ →
    scoping Δ t s →
    scoping Γ (t <[ σ ]) s.
Proof.
  intros hσ ht.
  induction ht in Γ, σ, hσ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto ].
  - rename H into hx, Γ0 into Δ.
    rasimpl. induction hσ in x, hx |- *. 1: destruct x ; discriminate.
    destruct x.
    + simpl in *. inversion hx. subst. assumption.
    + apply IHhσ. simpl in hx. assumption.
  - rasimpl. constructor.
    + eauto.
    + apply IHht2. constructor.
      * rasimpl. apply σscoping_weak. assumption.
      * rasimpl. constructor. reflexivity.
  - rasimpl. constructor.
    + eauto.
    + apply IHht2. constructor.
      * rasimpl. apply σscoping_weak. assumption.
      * rasimpl. constructor. reflexivity.
Qed.

Lemma σscoping_shift Γ Δ s σ :
    σscoping Γ σ Δ →
    σscoping (s :: Γ) (var 0 .: σ >> ren1 S) (s :: Δ).
Proof.
  intros h.
  constructor.
  - rasimpl. apply σscoping_weak. assumption.
  - rasimpl. constructor. reflexivity.
Qed.

#[export] Instance rscoping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) rscoping.
Proof.
  intros Γ ? <- ρ ρ' e Δ ? <-.
  revert ρ ρ' e. wlog_iff. intros ρ ρ' e h.
  intros n m en. rewrite <- e. apply h. assumption.
Qed.

Lemma autosubst_simpl_rscoping Γ Δ r s :
    RenSimplification r s →
    rscoping Γ r Δ ↔ rscoping Γ s Δ.
Proof.
  intros H.
  apply rscoping_morphism. 1,3: auto.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_rscoping : rasimpl_outermost.

#[export] Instance σscoping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) σscoping.
Proof.
  intros Γ ? <- σ σ' e Δ ? <-.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  induction h as [| ? ? ? ? ih ] in σ', e |- *.
  - constructor.
  - constructor.
    + apply ih. intros n. apply e.
    + rewrite <- e. assumption.
Qed.

Lemma autosubst_simpl_σscoping Γ Δ r s :
    SubstSimplification r s →
    σscoping Γ r Δ ↔ σscoping Γ s Δ.
Proof.
  intros H.
  apply σscoping_morphism. 1,3: auto.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_σscoping : rasimpl_outermost.

Lemma σscoping_ids Γ :
    σscoping Γ ids Γ.
Proof.
  induction Γ as [| s Γ ih].
  - constructor.
  - constructor.
    + eapply σscoping_weak with (s := s) in ih. rasimpl in ih. assumption.
    + constructor. reflexivity.
Qed.

Lemma σscoping_one Γ u s :
    scoping Γ u s →
    σscoping Γ u.. (s :: Γ).
Proof.
  intros h.
  constructor.
  - rasimpl. apply σscoping_ids.
  - rasimpl. assumption.
Qed.

(** Conversion entails mode equality **)

Definition rscoping_comp (Γ : scope) ρ (Δ : scope) :=
  ∀ x,
    nth_error Δ x = None →
    nth_error Γ (ρ x) = None.

Definition σscoping_comp (Γ : scope) σ (Δ : scope) :=
  ∀ n,
    nth_error Δ n = None →
    ∃ s,
      σ n = var s ∧
      nth_error Γ s = None.

Lemma σscoping_comp_shift Γ Δ σ s :
    σscoping_comp Γ σ Δ →
    σscoping_comp (s :: Γ) (up_term σ) (s :: Δ).
Proof.
  intros h n e.
  destruct n.
  - cbn in e. discriminate.
  - cbn in e. cbn.
    eapply h in e as e'. destruct e' as [m [e1 e2]].
    unfold core.funcomp. exists (S m). intuition eauto.
    rewrite e1. rasimpl. reflexivity.
Qed.

Lemma rscoping_comp_S Γ s :
    rscoping_comp (s :: Γ) S Γ.
Proof.
  intros n e. cbn. assumption.
Qed.

Lemma nth_nth_error :
  ∀ A (l : list A) (d : A) n,
    nth n l d = match nth_error l n with Some x => x | None => d end.
Proof.
  intros A l d n.
  induction l in n |- *.
  - cbn. destruct n. all: reflexivity.
  - cbn. destruct n.
    + cbn. reflexivity.
    + cbn. apply IHl.
Qed.

Lemma rscoping_comp_upren Γ Δ s ρ :
    rscoping_comp Γ ρ Δ →
    rscoping_comp (s :: Γ) (up_ren ρ) (s :: Δ).
Proof.
  intros h x e.
  destruct x.
  - cbn in *. assumption.
  - cbn in *. apply h. assumption.
Qed.

Lemma st_ren Γ Δ ρ t :
    rscoping Γ ρ Δ →
    rscoping_comp Γ ρ Δ →
    st Γ (ρ ⋅ t) = st Δ t.
Proof.
  intros hρ hcρ.
  induction t in Γ, Δ, ρ, hρ, hcρ |- *.
  all: try reflexivity.
  all: try solve [ cbn ; eauto ].
  - cbn. rewrite 2!nth_nth_error.
    destruct (nth_error Δ n) eqn:e.
    + eapply hρ in e. rewrite e. reflexivity.
    + eapply hcρ in e. rewrite e. reflexivity.
      (*
  - cbn. eapply IHt2.
    + eapply rscoping_shift. assumption.
    + eapply rscoping_comp_upren. assumption.
*)
Qed.

Lemma st_subst Γ Δ σ t :
    σscoping Γ σ Δ →
    σscoping_comp Γ σ Δ →
    st Γ (t <[ σ ]) = st Δ t.
Proof.
  intros hσ hcσ.
  induction t in Γ, Δ, σ, hσ, hcσ |- *.
  all: try reflexivity.
  all: try solve [ cbn ; eauto ].
  - cbn. rewrite nth_nth_error.
    destruct (nth_error Δ n) eqn:e.
    + clear hcσ. induction hσ as [| σ Δ mx hσ ih hm] in n, s, e |- *.
      1: destruct n ; discriminate.
      destruct n.
      * cbn in *. noconf e.
        erewrite scoping_st. 2: eassumption. reflexivity.
      * cbn in e. eapply ih. assumption.
    + eapply hcσ in e. destruct e as [m [e1 e2]].
      rewrite e1. cbn. rewrite nth_nth_error. rewrite e2. reflexivity.
(*
  - cbn. eapply IHt2.
    + eapply σscoping_shift. assumption.
    + eapply σscoping_comp_shift. assumption.
*)
Qed.

Lemma σscoping_comp_one :
  ∀ Γ u mx,
    σscoping_comp Γ u.. (mx :: Γ).
Proof.
  intros Γ u mx. intros n e.
  destruct n.
  - cbn in e. discriminate.
  - cbn in e. cbn. eexists. intuition eauto.
Qed.

Lemma conv_st Γ u v s :
    u ≡ v →
    scoping Γ u s ↔ scoping Γ v s.
Proof.
  intros h.
  induction h in s |- *.
  - split; intros h.
    + inversion h; subst.
      inversion H4; subst.
      apply (scoping_subst _ (s0 :: Γ)).
      1: now apply σscoping_one.
      assumption.
    + admit.
  - 
Admitted.

(** Better induction principle for [styping] *)

Lemma styping_ind :
  ∀ (P : sctx → term → term → Prop),
    (∀ Γ x A s, nth_error Γ x = Some (s, A) → P Γ (var x) (Nat.add (S x) ⋅ A)) →
    (∀ Γ s i, P Γ (Sort s i) (Sort s (S i))) →
    (∀ Γ s s' i j A B,
      Γ ⊢ A : Sort s i → P Γ A (Sort s i) →
      Γ,,s (s, A) ⊢ B : Sort s' j → P (Γ,,s (s, A)) B (Sort s' j) →
      P Γ (Pi s s' i j A B) (Sort s' (Nat.max i j))
    ) →
    (∀ Γ s s' i j A B t,
      Γ ⊢ A : Sort s i → P Γ A (Sort s i) →
      Γ,,s (s, A) ⊢ B : Sort s' j → P (Γ,,s (s, A)) B (Sort s' j) →
      Γ,,s (s, A) ⊢ t : B → P (Γ,,s (s, A)) t B →
      P Γ (lam s s' A t) (Pi s s' i j A B)
    ) →
    (∀ Γ s s' i j A B t u,
      Γ ⊢ t : Pi s s' i j A B → P Γ t (Pi s s' i j A B) →
      Γ ⊢ u : A → P Γ u A →
      Γ ⊢ A : Sort s i → P Γ A (Sort s i) →
      Γ,,s (s, A) ⊢ B : Sort s' j → P (Γ,,s (s, A)) B (Sort s' j) →
      P Γ (app s s' t u) (B <[ u..])
    ) →
    (∀ Γ s i A B t,
      Γ ⊢ t : A → P Γ t A → A ≡ B →
      Γ ⊢ B : Sort s i → P Γ B (Sort s i) →
      P Γ t B
    ) →
    ∀ Γ t A, Γ ⊢ t : A → P Γ t A.
Proof.
  intros P hvar hsort hpi hlam happ hconv.
  fix aux 4. move aux at top.
  intros Γ t A h.
  destruct h as [| | | | |].
  all: try solve [eauto].
  apply (happ _ _ _ i j A).
  all: try solve [eauto].
Qed.

(** Better induction principle for [ttyping] *)

Lemma ttyping_ind :
  ∀ (P : tctx → term → term → Prop),
    (∀ Γ x A, nth_error Γ x = Some A → P Γ (var x) (Nat.add (S x) ⋅ A)) →
    (∀ Γ i, P Γ (Typ i) (Typ (S i))) →
    (∀ Γ i j A B,
      Γ ⊨ A : Typ i → P Γ A (Typ i) →
      Γ,,t A ⊨ B : Typ j → P (Γ,,t A) B (Typ j) →
      P Γ (Pi_T i j A B) (Typ (Nat.max i j))
    ) →
    (∀ Γ i j A B t,
      Γ ⊨ A : Typ i → P Γ A (Typ i) →
      Γ,,t A ⊨ B : Typ j → P (Γ,,t A) B (Typ j) →
      Γ,,t A ⊨ t : B → P (Γ,,t A) t B →
      P Γ (lam_T A t) (Pi_T i j A B)
    ) →
    (∀ Γ i j A B t u,
      Γ ⊨ t : Pi_T i j A B → P Γ t (Pi_T i j A B) →
      Γ ⊨ u : A → P Γ u A →
      Γ ⊨ A : Typ i → P Γ A (Typ i) →
      Γ,,t A ⊨ B : Typ j → P (Γ,,t A) B (Typ j) →
      P Γ (app_T t u) (B <[ u..])
    ) →
    (∀ Γ i, P Γ unit (Typ i)) →
    (∀ Γ , P Γ tt unit) →
    (∀ Γ i j A B,
      Γ ⊨ A : Typ i →
      P Γ A (Typ i) →
      Γ,,t A ⊨ B : Typ j →
      P (Γ,,t A) B (Typ j) →
      P Γ (Sigma A B) (Typ (Nat.max i j))
    ) →
    (∀ Γ i j A B t u,
      Γ ⊨ A : Typ i →
      P Γ A (Typ i) →
      Γ ⊨ t : A →
      P Γ t A →
      Γ,,t A ⊨ B : Typ j →
      P (Γ,,t A) B (Typ j) →
      Γ,,t A ⊨ u : B →
      P (Γ,,t A) u B →
      P Γ (sig t u) (Sigma A B)
    ) →
    (∀ Γ i j A B t,
      Γ ⊨ A : Typ i →
      P Γ A (Typ i) →
      Γ,,t A ⊨ B : Typ j →
      P (Γ,,t A) B (Typ j) →
      Γ ⊨ t : Sigma A B →
      P Γ t (Sigma A B) →
      P Γ (pi1 t) A
    ) →
    (∀ Γ i j A B t,
      Γ ⊨ A : Typ i →
      P Γ A (Typ i) →
      Γ,,t A ⊨ B : Typ j →
      P (Γ,,t A) B (Typ j) →
      Γ ⊨ t : Sigma A B →
      P Γ t (Sigma A B) →
      P Γ (pi2 t) (B <[ (pi1 t)..])
    ) →
    (∀ Γ i A B t,
      Γ ⊨ t : A → P Γ t A → A ≡ B →
      Γ ⊨ B : Typ i → P Γ B (Typ i) →
      P Γ t B
    ) →
    ∀ Γ t A, Γ ⊨ t : A → P Γ t A.
Proof.
  intros P hvar htyp hpi hlam happ hunit htt hSigma hsig hpi1 hpi2 hconv.
  fix aux 4. move aux at top.
  intros Γ t A h.
  destruct h as [| | | | | | | | | | |].
  all: try solve [eauto].
  - apply (happ _ i j A).
    all: try solve [eauto].
  - apply (hsig _ i j).
    all: try solve [eauto].
Qed.

(** Renaming preserves typing *)

Definition rstyping (Γ : sctx) (ρ : nat → nat) (Δ : sctx) : Prop :=
  ∀ x A s,
    nth_error Δ x = Some (s, A) →
    ∃ B,
      nth_error Γ (ρ x) = Some (s, B) ∧
      (plus (S x) >> ρ) ⋅ A = (plus (S (ρ x))) ⋅ B.

#[export] Instance rstyping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) rstyping.
Proof.
  intros Γ ? <- ρ ρ' e Δ ? <-.
  revert ρ ρ' e. wlog_iff. intros ρ ρ' e h.
  intros n A s en. rewrite <- e.
  eapply h in en as [B [en eB]].
  eexists. split. 1: eassumption.
  rasimpl. rasimpl in eB. rewrite <- eB.
  apply extRen_term. intro x. cbn. core.unfold_funcomp.
  rewrite <- e. reflexivity.
Qed.

Definition rttyping (Γ : tctx) (ρ : nat → nat) (Δ : tctx) : Prop :=
  ∀ x A,
    nth_error Δ x = Some A →
    ∃ B,
      nth_error Γ (ρ x) = Some B ∧
      (plus (S x) >> ρ) ⋅ A = (plus (S (ρ x))) ⋅ B.

#[export] Instance rttyping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) rttyping.
Proof.
  intros Γ ? <- ρ ρ' e Δ ? <-.
  revert ρ ρ' e. wlog_iff. intros ρ ρ' e h.
  intros n A en. rewrite <- e.
  eapply h in en as [B [en eB]].
  eexists. split. 1: eassumption.
  rasimpl. rasimpl in eB. rewrite <- eB.
  apply extRen_term. intro x. cbn. core.unfold_funcomp.
  rewrite <- e. reflexivity.
Qed.

Lemma autosubst_simpl_rstyping :
  ∀ Γ Δ r s,
    RenSimplification r s →
    rstyping Γ r Δ ↔ rstyping Γ s Δ.
Proof.
  intros Γ Δ r s H.
  apply rstyping_morphism. 1,3: auto.
  apply H.
Qed.

Lemma autosubst_simpl_rttyping :
  ∀ Γ Δ r s,
    RenSimplification r s →
    rttyping Γ r Δ ↔ rttyping Γ s Δ.
Proof.
  intros Γ Δ r s H.
  apply rttyping_morphism. 1,3: auto.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_rstyping : rasimpl_outermost.
#[export] Hint Rewrite -> autosubst_simpl_rttyping : rasimpl_outermost.

Lemma rstyping_up :
  ∀ Γ Δ A ρ s,
    rstyping Γ ρ Δ →
    rstyping (Γ ,,s (s, ρ ⋅ A)) (upRen_term_term ρ) (Δ,,s (s, A)).
Proof.
  intros Γ Δ A ρ s hρ.
  intros y B s' hy.
  destruct y.
  - cbn in *. inversion hy. eexists.
    split. 1: reflexivity.
    rasimpl. reflexivity.
  - cbn in *. eapply hρ in hy. destruct hy as [C [en eC]].
    eexists. split. 1: eassumption.
    rasimpl.
    apply (f_equal (λ t, S ⋅ t)) in eC. rasimpl in eC.
    assumption.
Qed.

Lemma rstyping_S :
  ∀ Γ A s,
    rstyping (Γ ,,s (s, A)) S Γ.
Proof.
  intros Γ A. intros x B e.
  simpl. rasimpl.
  eexists. split. 1: eassumption.
  rasimpl. reflexivity.
Qed.

Lemma rttyping_up :
  ∀ Γ Δ A ρ,
    rttyping Γ ρ Δ →
    rttyping (Γ ,,t (ρ ⋅ A)) (upRen_term_term ρ) (Δ,,t A).
Proof.
  intros Γ Δ A ρ hρ.
  intros y B hy.
  destruct y.
  - cbn in *. inversion hy. eexists.
    split. 1: reflexivity.
    rasimpl. reflexivity.
  - cbn in *. eapply hρ in hy. destruct hy as [C [en eC]].
    eexists. split. 1: eassumption.
    rasimpl.
    apply (f_equal (λ t, S ⋅ t)) in eC. rasimpl in eC.
    assumption.
Qed.

Lemma rttyping_S :
  ∀ Γ A,
    rttyping (Γ ,,t A) S Γ.
Proof.
  intros Γ A. intros x B e.
  simpl. rasimpl.
  eexists. split. 1: eassumption.
  rasimpl. reflexivity.
Qed.

(* unused *)
Lemma rstyping_comp Γ Δ Θ ρ ρ' :
  rstyping Δ ρ Θ →
  rstyping Γ ρ' Δ →
  rstyping Γ (ρ >> ρ') Θ.
Proof.
  intros hρ hρ'. intros x A s e.
  simpl. rasimpl.
  eapply hρ in e as [B [e h]].
  eapply hρ' in e as [C [e h']].
  exists C. split. 1: assumption.
  apply (f_equal (λ t, ρ' ⋅ t)) in h. rasimpl in h.
  rasimpl in h'. rewrite h' in h.
  etransitivity. 1: exact h.
  reflexivity.
Qed.

(* unused *)
Lemma rstyping_add Γ Δ :
  rstyping (Γ ,,,s Δ) (plus (length Δ)) Γ.
Proof.
  intros x A s e.
  exists A. split.
  - rewrite nth_error_app2. 2: lia.
    rewrite <- e. f_equal. lia.
  - apply extRen_term. intro. core.unfold_funcomp. lia.
Qed.

Lemma conv_ren ρ u v :
  u ≡ v →
  ρ ⋅ u ≡ ρ ⋅ v.
Proof.
  intros h.
  induction h in ρ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto ].  
  rasimpl. apply (conv_trans _ (((0 .: ρ >> S) ⋅ t) <[ (ρ ⋅ u)..])).
  - constructor.
  - rasimpl. constructor.
Qed.

Lemma styping_ren :
  ∀ Γ Δ ρ t A,
    rstyping Δ ρ Γ →
    Γ ⊢ t : A →
    Δ ⊢ ρ ⋅ t : ρ ⋅ A.
Proof.
  intros Γ Δ ρ t A hρ ht.
  induction ht using styping_ind in Δ, ρ, hρ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto using rstyping_up ].
  all: rasimpl.
  - eapply hρ in H as [B [? eB]].
    rewrite eB. econstructor. apply H.
  - rasimpl in IHht1; rasimpl in IHht4.
    assert (((0 .: ρ >> S) ⋅ B) <[ (ρ ⋅ u)..] = B <[ ρ ⋅ u .: ρ >> var])
      as <- by now rasimpl.
    econstructor. all: eauto.
    eauto using rstyping_up.
  - rasimpl in IHht2.
    econstructor. all: eauto.
    now apply conv_ren.
Qed.

Lemma ttyping_ren :
  ∀ Γ Δ ρ t A,
    rttyping Δ ρ Γ →
    Γ ⊨ t : A →
    Δ ⊨ ρ ⋅ t : ρ ⋅ A.
Proof.
  intros Γ Δ ρ t A hρ ht.
  induction ht using ttyping_ind in Δ, ρ, hρ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto using rttyping_up ].
  all: rasimpl.
  - eapply hρ in H as [B [? eB]].
    rewrite eB. now econstructor.
  - rasimpl in IHht1; rasimpl in IHht4.
    assert (((0 .: ρ >> S) ⋅ B) <[ (ρ ⋅ u)..] = B <[ ρ ⋅ u .: ρ >> var])
      as <- by now rasimpl.
    econstructor. all: eauto.
    eauto using rttyping_up.
  - rasimpl in IHht3.
    assert (((0 .: ρ >> S) ⋅ B) <[ (pi1 (t <[ ρ >> var]))..] =
              B <[ pi1 (t <[ ρ >> var]) .: ρ >> var]) as <- by now rasimpl.
    assert (ρ ⋅ t = t <[ ρ >> var]) as <- by now rasimpl.
    econstructor. all: eauto.
    eauto using rttyping_up.
  - rasimpl in IHht2.
    econstructor. all: eauto.
    now apply conv_ren.
Qed.

(** Substitution preserves typing *)

Inductive σstyping (Γ : sctx) (σ : nat → term) : sctx → Prop :=
| stype_nil : σstyping Γ σ ∙s
| stype_cons Δ A s :
    σstyping Γ (S >> σ) Δ →
    cscoping Γ (σ 0) s →
    styping Γ (σ 0) (A <[ S >> σ ]) →
    σstyping Γ σ (Δ ,,s (s, A)).

#[export] Instance σstyping_morphism :
Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) σstyping.
Proof.
  intros Γ ? <- σ σ' e Δ ? <-.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  induction h as [| ? ? ? ? ? ih ? ] in σ', e |- *.
  - constructor.
  - constructor.
    + apply ih. intros n. apply e.
    + now rewrite <- e.
    + rewrite <- e.
      assert (A <[ S >> σ] = A <[ S >> σ']) as <-.
      { apply ext_term. intro. apply e. }
      assumption.
Qed.

Inductive σttyping (Γ : tctx) (σ : nat → term) : tctx → Prop :=
| ttype_nil : σttyping Γ σ ∙t
| ttype_cons Δ A :
    σttyping Γ (S >> σ) Δ →
    ttyping Γ (σ 0) (A <[ S >> σ ]) →
    σttyping Γ σ (Δ ,,t A).

#[export] Instance σttyping_morphism :
Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) σttyping.
Proof.
  intros Γ ? <- σ σ' e Δ ? <-.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  induction h as [| ? ? ? ? ih ? ] in σ', e |- *.
  - constructor.
  - constructor.
    + apply ih. intros n. apply e.
    + rewrite <- e.
      assert (A <[ S >> σ] = A <[ S >> σ']) as <-.
      { apply ext_term. intro. apply e. }
      assumption.
Qed.

Lemma autosubst_simpl_σstyping :
  ∀ Γ Δ r s,
    SubstSimplification r s →
    σstyping Γ r Δ ↔ σstyping Γ s Δ.
Proof.
  intros Γ Δ r s H.
  apply σstyping_morphism.
  1,3: reflexivity.
  apply H.
Qed.

Lemma autosubst_simpl_σttyping :
  ∀ Γ Δ r s,
    SubstSimplification r s →
    σttyping Γ r Δ ↔ σttyping Γ s Δ.
Proof.
  intros Γ Δ r s H.
  apply σttyping_morphism.
  1,3: reflexivity.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_σstyping : rasimpl_outermost.
#[export] Hint Rewrite -> autosubst_simpl_σttyping : rasimpl_outermost.

Lemma styping_scoping Γ Δ σ :
    σstyping Γ σ Δ →
    σscoping (sc Γ) σ (sc Δ).
Proof.
  intros h. induction h.
  - constructor.
  - cbn. constructor. all: assumption.
Qed.

Lemma σstyping_weak Γ Δ σ A s :
  σstyping Γ σ Δ →
  σstyping (Γ,,s (s, A)) (σ >> ren_term S) Δ.
Proof.
  intros h.
  induction h.
  - constructor.
  - constructor.
    1: assumption.
    + eapply scoping_ren. 2: eassumption.
      apply rscoping_S.
    + assert (S ⋅ A0 <[ S >> σ] = A0 <[ S >> (σ >> ren_term S)]) as <- by now rasimpl.
      eapply styping_ren. 2: eassumption.
      apply rstyping_S.
Qed.

Lemma σstyping_up Γ Δ A σ s :
  σstyping Γ σ Δ →
  σstyping (Γ ,,s (s, A <[ σ ])) (up_term σ) (Δ,,s (s, A)).
Proof.
  intros h.
  constructor.
  - rasimpl. now apply σstyping_weak.
  - admit.
  - rasimpl.
    assert (Init.Nat.add 1 ⋅ A <[ σ] = A <[ σ >> ren_term S]) as <- by now rasimpl.
    now econstructor.
Admitted.

Lemma σttyping_weak Γ Δ σ A :
  σttyping Γ σ Δ →
  σttyping (Γ,,t A) (σ >> ren_term S) Δ.
Proof.
  intros h.
  induction h.
  - constructor.
  - constructor.
    1: assumption.
    assert (S ⋅ A0 <[ S >> σ] = A0 <[ S >> (σ >> ren_term S)]) as <- by now rasimpl.
    eapply ttyping_ren. 2: eassumption.
    apply rttyping_S.
Qed.

Lemma σttyping_up Γ Δ A σ :
  σttyping Γ σ Δ →
  σttyping (Γ ,,t A <[ σ ]) (up_term σ) (Δ,,t A).
Proof.
  intros h.
  constructor.
  - rasimpl. now apply σttyping_weak.
  - rasimpl.
    assert (Init.Nat.add 1 ⋅ A <[ σ] = A <[ σ >> ren_term S]) as <- by now rasimpl.
    now econstructor.
Qed.

Lemma conv_subst σ u v :
  u ≡ v →
  u <[ σ ] ≡ v <[ σ ].
Proof.
  intros h.
  induction h using conversion_ind in σ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto ].
  - assert ((t <[ (var 0) .: σ >> ren_term S]) <[ (u <[ σ])..] = (t <[ u..]) <[ σ])
      as <- by now rasimpl.
    econstructor.
Qed.

Lemma styping_subst Γ Δ σ t A :
  σstyping Δ σ Γ →
  Γ ⊢ t : A →
  Δ ⊢ t <[ σ ] : A <[ σ ].
Proof.
  intros hσ ht.
  induction ht using styping_ind in Δ, σ, hσ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto using σstyping_up ].
  - rasimpl.
    induction hσ in x, H |- *. 1: destruct x ; discriminate.
    destruct x.
    + cbn in H. inversion H. subst. assumption.
    + apply IHhσ. assumption.
  - assert ((B <[ up_term_term σ]) <[ (u <[ σ])..] = (B <[ u..]) <[ σ])
      as <- by now rasimpl.
    cbn in *. econstructor ; eauto using σstyping_up.
  - econstructor. 1,3: eauto.
    eapply conv_subst. eassumption.
Qed.

Lemma ttyping_subst Γ Δ σ t A :
  σttyping Δ σ Γ →
  Γ ⊨ t : A →
  Δ ⊨ t <[ σ ] : A <[ σ ].
Proof.
  intros hσ ht.
  induction ht using ttyping_ind in Δ, σ, hσ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto using σttyping_up ].
  - rasimpl.
    induction hσ in x, H |- *. 1: destruct x ; discriminate.
    destruct x.
    + cbn in H. inversion H. subst. assumption.
    + apply IHhσ. assumption.
  - assert ((B <[ up_term_term σ]) <[ (u <[ σ])..] = (B <[ u..]) <[ σ])
      as <- by now rasimpl.
    cbn in *. econstructor ; eauto using σttyping_up.
  - assert ((B <[ up_term_term σ]) <[ ((pi1 t) <[ σ])..] = (B <[ (pi1 t)..]) <[ σ])
      as <- by now rasimpl.
    econstructor ; eauto using σttyping_up.
  - econstructor. 1,3: eauto.
    eapply conv_subst. eassumption.
Qed.

(** Validity (or presupposition) *)

Lemma σstyping_ids Γ :
  σstyping Γ ids Γ.
Proof.
  induction Γ as [| [s A] Γ ih].
  - constructor.
  - constructor.
    + eapply σstyping_weak with (s := s) (A := A) in ih.
      assumption.
    + now constructor.
    + assert (Init.Nat.add 1 ⋅ A = A <[ S >> ids]) as <- by now rasimpl; substify.
      now econstructor.
Qed.

Lemma σstyping_one Γ A u s :
  cscoping Γ u s →
  Γ ⊢ u : A →
  σstyping Γ u.. (Γ ,,s (s, A)).
Proof.
  intros h.
  constructor. all: rasimpl. 2,3: auto.
  erewrite autosubst_simpl_σstyping. 2: exact _. (* Somehow rasimpl doesn't work *)
  apply σstyping_ids.
Qed.

Lemma σttyping_ids Γ :
  σttyping Γ ids Γ.
Proof.
  induction Γ as [| A Γ ih].
  - constructor.
  - constructor.
    + eapply σttyping_weak with (A := A) in ih.
      assumption.
    + assert (Init.Nat.add 1 ⋅ A = A <[ S >> ids]) as <- by now rasimpl; substify.
      now econstructor.
Qed.

Lemma σttyping_one Γ A u :
  Γ ⊨ u : A →
  σttyping Γ u.. (Γ ,,t A).
Proof.
  intros h.
  constructor. all: rasimpl. 2: auto.
  erewrite autosubst_simpl_σttyping. 2: exact _. (* Somehow rasimpl doesn't work *)
  apply σttyping_ids.
Qed.

Lemma valid_swf Γ x A s :
  swf Γ →
  nth_error Γ x = Some (s, A) →
  ∃ i, Γ ⊢ (plus (S x)) ⋅ A : Sort s i.
Proof.
  intros hΓ h.
  induction hΓ as [| Γ s' i B hΓ ih hB] in x, h |- *.
  1: destruct x ; discriminate.
  destruct x.
  - cbn in *. inversion h. subst.
    exists i. rasimpl.
    assert (S ⋅ Sort s i = Sort s i) as <- by easy.
    eapply styping_ren. 1: eapply rstyping_S.
    assumption.
  - cbn in h. eapply ih in h as [j h]. exists j.
    eapply styping_ren in h. 2: eapply rstyping_S.
    rasimpl in h. eassumption.
Qed.

Lemma valid_twf Γ x A :
  twf Γ →
  nth_error Γ x = Some A →
  ∃ i, Γ ⊨ (plus (S x)) ⋅ A : Typ i.
Proof.
  intros hΓ h.
  induction hΓ as [| Γ i B hΓ ih hB] in x, h |- *.
  1: destruct x ; discriminate.
  destruct x.
  - cbn in *. inversion h. subst.
    exists i. rasimpl.
    assert (S ⋅ Typ i = Typ i) as <- by easy.
    eapply ttyping_ren. 1: eapply rttyping_S.
    assumption.
  - cbn in h. eapply ih in h as [j h]. exists j.
    eapply ttyping_ren in h. 2: eapply rttyping_S.
    rasimpl in h. eassumption.
Qed.

Lemma svalidity Γ t A :
  swf Γ →
  Γ ⊢ t : A →
  cscoping Γ t (stc Γ t) ∧
  ∃ i, Γ ⊢ A : Sort (stc Γ t) i.
Proof.
  intros hΓ h.
  induction h using styping_ind in hΓ |- *.
  (*
  all: try solve [ eexists ; econstructor ; intuition eauto using styping ].
  - apply valid_swf. all: assumption.
  - exists s', j.
    assert (Sort s' j <[ u..] = Sort s' j) as <- by easy.
    apply (styping_subst (Γ,,A)).
    + now apply σstyping_one.
    + assumption.
*)
Admitted.

Lemma tvalidity Γ t A :
  twf Γ →
  Γ ⊨ t : A →
  ∃ i, Γ ⊨ A : Typ i.
Proof.
  intros hΓ h.
  induction h using ttyping_ind in hΓ |- *.
  7: exists 0; constructor.
  all: try solve [ eexists ; econstructor ; intuition eauto using ttyping ].
  - apply valid_twf. all: assumption.
  - exists j.
    assert (Typ j <[ u..] = Typ j) as <- by easy.
    apply (ttyping_subst (Γ,,t A)).
    + now apply σttyping_one.
    + assumption.
  - eauto.
  - exists j.
    assert (Typ j <[ (pi1 t)..] = Typ j) as <- by easy.
    apply (ttyping_subst (Γ,,t A)).
    + apply σttyping_one.
      econstructor. all: eauto.
    + assumption.
  - eauto. 
Qed.

(*
(** * Context conversion *)

Notation ctx_conv Γ Δ := (Forall2 conversion Γ Δ).

Lemma ctx_conv_cons_same Γ Δ A :
  ctx_conv Γ Δ →
  ctx_conv (Γ ,,s A) (Δ ,,s A).
Proof.
  intros h.
  constructor.
  - apply conv_refl.
  - assumption.
Qed.

Lemma ctx_conv_refl Γ :
  ctx_conv Γ Γ.
Proof.
  apply Forall2_diag. apply Forall_forall.
  auto using conv_refl.
Qed.

Lemma ctx_conv_cons_same_ctx Γ A B :
  A ≡ B →
  ctx_conv (Γ ,, A) (Γ ,, B).
Proof.
  intros h.
  constructor.
  - assumption.
  - apply ctx_conv_refl.
Qed.

Inductive swf_ctx_conv : ctx → ctx → Prop :=
| swf_conv_nil : swf_ctx_conv ∙ ∙
| swf_conv_cons Γ Δ s i A B :
    swf_ctx_conv Γ Δ →
    Δ ⊢ A : Sort s i →
    A ≡ B →
    swf_ctx_conv (Γ ,, A) (Δ ,, B).

Inductive twf_ctx_conv : ctx → ctx → Prop :=
| twf_conv_nil : twf_ctx_conv ∙ ∙
| twf_conv_cons Γ Δ i A B :
    twf_ctx_conv Γ Δ →
    Δ ⊨ A : Typ i →
    A ≡ B →
    twf_ctx_conv (Γ ,, A) (Δ ,, B).

Lemma swf_ctx_conv_nth_error_l Γ Δ x A :
  swf_ctx_conv Γ Δ →
  nth_error Γ x = Some A →
  ∃ s i B,
    nth_error Δ x = Some B ∧
    A ≡ B ∧
    (Δ ⊢ (plus (S x)) ⋅ A : Sort s i).
Proof.
  intros hctx h.
  induction hctx as [| Γ Δ s i B C hctx ih hB he] in x, h |- *.
  1: destruct x ; discriminate.
  destruct x.
  - simpl in *. inversion h. subst.
    exists s, i, C. rasimpl. intuition auto.
    assert (S ⋅ Sort s i = Sort s i) as <- by easy.
    eapply styping_ren. 1: eapply rtyping_S.
    eassumption.
  - cbn in h. eapply ih in h as (s' & j & D & ? & ? & h).
    exists s', j, D. cbn. intuition auto.
    eapply styping_ren in h. 2: eapply rtyping_S.
    rasimpl in h. eassumption.
Qed.

Lemma twf_ctx_conv_nth_error_l Γ Δ x A :
  twf_ctx_conv Γ Δ →
  nth_error Γ x = Some A →
  ∃ i B,
    nth_error Δ x = Some B ∧
    A ≡ B ∧
    (Δ ⊨ (plus (S x)) ⋅ A : Typ i).
Proof.
  intros hctx h.
  induction hctx as [| Γ Δ i B C hctx ih hB he] in x, h |- *.
  1: destruct x ; discriminate.
  destruct x.
  - simpl in *. inversion h. subst.
    exists i, C. rasimpl. intuition auto.
    assert (S ⋅ Typ i = Typ i) as <- by easy.
    eapply ttyping_ren. 1: eapply rtyping_S.
    eassumption.
  - cbn in h. eapply ih in h as (j & D & ? & ? & h).
    exists j, D. cbn. intuition auto.
    eapply ttyping_ren in h. 2: eapply rtyping_S.
    rasimpl in h. eassumption.
Qed.

Lemma styping_ctx_conv_gen (Γ Δ : ctx) t A :
  swf_ctx_conv Γ Δ →
  Γ ⊢ t : A →
  Δ ⊢ t : A.
Proof.
  intros hctx h.
  induction h in Δ, hctx |- * using styping_ind.
  all: try solve [ econstructor ; eauto using swf_conv_cons, conv_refl ].
  eapply swf_ctx_conv_nth_error_l in hctx as h. 2: eassumption.
  destruct h as (s & i & B & e & hc & h).
  eapply stype_conv.
  - econstructor. eassumption.
  - apply conv_sym. apply conv_ren. assumption.
  - eassumption.
Qed.

Lemma ttyping_ctx_conv_gen (Γ Δ : ctx) t A :
  twf_ctx_conv Γ Δ →
  Γ ⊨ t : A →
  Δ ⊨ t : A.
Proof.
  intros hctx h.
  induction h in Δ, hctx |- * using ttyping_ind.
  all: try solve [ econstructor ; eauto using twf_conv_cons, conv_refl ].
  eapply twf_ctx_conv_nth_error_l in hctx as h. 2: eassumption.
  destruct h as (i & B & e & hc & h).
  eapply ttype_conv.
  - econstructor. eassumption.
  - apply conv_sym. apply conv_ren. assumption.
  - eassumption.
Qed.
  
Lemma styping_ctx_conv (Γ Δ : ctx) t A :
  Γ ⊢ t : A →
  swf Γ →
  ctx_conv Γ Δ →
  Δ ⊢ t : A.
Proof.
  intros ht hΓ hctx.
  eapply styping_ctx_conv_gen. 2: eassumption.
  clear ht. induction hΓ in Δ, hctx |- *.
  - inversion hctx. constructor.
  - inversion hctx. subst.
    econstructor. 1,3: eauto.
    eauto using styping_ctx_conv_gen.
Qed.

Lemma ttyping_ctx_conv (Γ Δ : ctx) t A :
  Γ ⊨ t : A →
  twf Γ →
  ctx_conv Γ Δ →
  Δ ⊨ t : A.
Proof.
  intros ht hΓ hctx.
  eapply ttyping_ctx_conv_gen. 2: eassumption.
  clear ht. induction hΓ in Δ, hctx |- *.
  - inversion hctx. constructor.
  - inversion hctx. subst.
    econstructor. 1,3: eauto.
    eauto using ttyping_ctx_conv_gen.
Qed.

(** Congruence of substitution *)

Lemma conv_substs_up σ σ' :
  (∀ x, σ x ≡ σ' x) →
  (∀ x, up_term σ x ≡ up_term σ' x).
Proof.
  intros h x.
  destruct x.
  - cbn. ttconv.
  - cbn. unfold core.funcomp. apply conv_ren. auto.
Qed.

Lemma conv_substs σ σ' t :
  (∀ x, σ x ≡ σ' x) →
  t <[ σ ] ≡ t <[ σ' ].
Proof.
  intros h.
  induction t using term_rect in σ, σ', h |- *.
  all: try solve [ rasimpl ; econstructor ; eauto using conv_substs_up ].
  eauto.
Qed.

(* Some other lemmas *)

Definition σtyping_alt (jmt : ctx → term → term → Prop)
  (Γ : ctx) (σ : nat → term) (Δ : ctx) :=
  ∀ x A,
    nth_error Δ x = Some A →
    jmt Γ (σ x) (((plus (S x)) ⋅ A) <[ σ ]).

Lemma σtyping_alt_equiv jmt Γ σ Δ :
  σtyping jmt Γ σ Δ ↔ σtyping_alt jmt Γ σ Δ.
Proof.
  split.
  - intro h. induction h as [| ???? ih].
    + intros x A e. destruct x. all: discriminate.
    + intros [] B e.
      * rasimpl. cbn in e. inversion e. subst.
        assumption.
      * cbn in e. rasimpl. eapply ih in e. rasimpl in e.
        exact e.
  - intro h. induction Δ as [| A Δ ih] in σ, h |- *.
    1: constructor.
    econstructor.
    + eapply ih.
      intros x B e. rasimpl.
      core.unfold_funcomp.
      specialize (h (S x) _ e). rasimpl in h.
      assumption.
    + specialize (h 0 _ eq_refl). rasimpl in h.
      assumption.
Qed.
*)
