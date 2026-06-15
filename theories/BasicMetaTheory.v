(** Basic meta-theory *)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Require Import Equations.Prop.DepElim.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

(** Better induction principle for [typing] *)

Lemma styping_ind :
  ∀ (P : ctx → term → term → Prop),
    (∀ Γ x A, nth_error Γ x = Some A → P Γ (var x) (Nat.add (S x) ⋅ A)) →
    (∀ Γ s i, P Γ (Sort s i) (Sort s (S i))) →
    
    (∀ Γ s s' i j A B,
      Γ ⊢ A : Sort s i → P Γ A (Sort s i) →
      Γ,, A ⊢ B : Sort s' j → P (Γ,, A) B (Sort s' j) →
      P Γ (Pi A B) (Sort s' (Nat.max i j))
    ) →
    
    (∀ Γ s s' i j A B t,
      Γ ⊢ A : Sort s i → P Γ A (Sort s i) →
      Γ,, A ⊢ B : Sort s' j → P (Γ,, A) B (Sort s' j) →
      Γ,, A ⊢ t : B → P (Γ,, A) t B →
      P Γ (lam A t) (Pi A B)
    ) →
    
    (∀ Γ s s' i j A B t u,
      Γ ⊢ t : Pi A B → P Γ t (Pi A B) →
      Γ ⊢ u : A → P Γ u A →
      Γ ⊢ A : Sort s i → P Γ A (Sort s i) →
      Γ,, A ⊢ B : Sort s' j → P (Γ,, A) B (Sort s' j) →
      P Γ (app t u) (B <[ u..])
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
  apply (happ _ s s' i j A).
  all: try solve [eauto].
Qed.

(** Typing implies scoping *)

Lemma styping_scoped Γ t A :
  Γ ⊢ t : A →
  scoped (length Γ) t = true.
Proof.
  intro h.
  induction h using styping_ind.
  all: try solve [ cbn - ["<?"] in * ; eauto ].
  all: try solve [
    cbn - ["<?"] in * ;
    rewrite Bool.andb_true_iff in * ;
    intuition eauto
  ].
  simpl. rewrite Nat.ltb_lt, <-nth_error_Some.
  congruence.
Qed. 

Lemma styping_closed t A :
  ∙ ⊢ t : A →
  closed t = true.
Proof.
  intros h.
  eapply styping_scoped with (Γ := ∙).
  eassumption.
Qed.

(** Renaming preserves typing *)

Definition rtyping (Γ : ctx) (ρ : nat → nat) (Δ : ctx) : Prop :=
  ∀ x A,
    nth_error Δ x = Some A →
    ∃ B,
      nth_error Γ (ρ x) = Some B ∧
      (plus (S x) >> ρ) ⋅ A = (plus (S (ρ x))) ⋅ B.

#[export] Instance rtyping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) rtyping.
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

Lemma autosubst_simpl_rtyping :
  ∀ Γ Δ r s,
    RenSimplification r s →
    rtyping Γ r Δ ↔ rtyping Γ s Δ.
Proof.
  intros Γ Δ r s H.
  apply rtyping_morphism. 1,3: auto.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_rtyping : rasimpl_outermost.

Lemma rtyping_up :
  ∀ Γ Δ A ρ,
    rtyping Γ ρ Δ →
    rtyping (Γ ,, (ρ ⋅ A)) (upRen_term_term ρ) (Δ,, A).
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

Lemma rtyping_S :
  ∀ Γ A,
    rtyping (Γ ,, A) S Γ.
Proof.
  intros Γ A. intros x B e.
  simpl. rasimpl.
  eexists. split. 1: eassumption.
  rasimpl. reflexivity.
Qed.

Lemma rtyping_comp Γ Δ Θ ρ ρ' :
  rtyping Δ ρ Θ →
  rtyping Γ ρ' Δ →
  rtyping Γ (ρ >> ρ') Θ.
Proof.
  intros hρ hρ'. intros x A e.
  simpl. rasimpl.
  eapply hρ in e as [B [e h]].
  eapply hρ' in e as [C [e h']].
  exists C. split. 1: assumption.
  apply (f_equal (λ t, ρ' ⋅ t)) in h. rasimpl in h.
  rasimpl in h'. rewrite h' in h.
  etransitivity. 1: exact h.
  reflexivity.
Qed.

Lemma rtyping_add Γ Δ :
  rtyping (Γ ,,, Δ) (plus (length Δ)) Γ.
Proof.
  intros x A e.
  exists A. split.
  - rewrite nth_error_app2. 2: lia.
    rewrite <- e. f_equal. lia.
  - apply extRen_term. intro. core.unfold_funcomp. lia.
Qed.

Fixpoint uprens k (ρ : nat → nat) :=
  match k with
  | 0 => ρ
  | S k => upRen_term_term (uprens k ρ)
  end.

Lemma scoped_ren :
  ∀ ρ k t,
    scoped k t = true →
    (uprens k ρ) ⋅ t = t.
Proof.
  intros ρ k t h.
  induction t using term_rect in k, h |- *.
  all: try solve [ cbn ; eauto ].
  all: try solve [
    cbn ;
    apply andb_prop in h as [] ;
    change (upRen_term_term (uprens ?k ?ρ)) with (uprens (S k) ρ) ;
    f_equal ;
    eauto
  ].
  cbn - ["<?"] in *. f_equal.
  apply Nat.ltb_lt in h.
  induction n as [| n ih] in k, h |- *.
  - destruct k. 1: lia.
    reflexivity.
  - destruct k. 1: lia.
    cbn. core.unfold_funcomp. f_equal.
    apply ih. lia.
Qed.

Corollary closed_ren :
  ∀ ρ t,
    closed t = true →
    ρ ⋅ t = t.
Proof.
  intros ρ t h.
  eapply scoped_ren in h. eauto.
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

Fixpoint ren_ctx ρ Γ {struct Γ} :=
  match Γ with
  | [] => ∙
  | A :: Γ => (ren_ctx ρ Γ) ,, (uprens (length Γ) ρ ⋅ A)
  end.

Lemma rtyping_uprens Γ Δ Θ ρ :
  rtyping Δ ρ Γ →
  rtyping (Δ ,,, ren_ctx ρ Θ) (uprens (length Θ) ρ) (Γ ,,, Θ).
Proof.
  intros h.
  induction Θ as [| A Θ ih].
  - cbn. assumption.
  - cbn. rewrite app_comm_cons. cbn. eapply rtyping_up. assumption.
Qed.

Corollary rtyping_uprens_eq Γ Δ Θ ρ k :
  rtyping Δ ρ Γ →
  k = length Θ →
  rtyping (Δ ,,, ren_ctx ρ Θ) (uprens k ρ) (Γ ,,, Θ).
Proof.
  intros h ->.
  eapply rtyping_uprens. assumption.
Qed.

Lemma ups_below k σ n :
  n < k →
  ups k σ n = var n.
Proof.
  intro h.
  induction k as [| k ih] in n, σ, h |- *. 1: lia.
  cbn. destruct n as [| ].
  - reflexivity.
  - cbn. core.unfold_funcomp. rewrite ih. 2: lia.
    reflexivity.
Qed.

Lemma ups_above k σ n :
  ups k σ (k + n) = (plus k) ⋅ σ n.
Proof.
  induction k as [| k ih] in n |- *.
  - cbn. rasimpl. reflexivity.
  - cbn. core.unfold_funcomp. rewrite ih.
    rasimpl. reflexivity.
Qed.

Lemma styping_ren :
  ∀ Γ Δ ρ t A,
    rtyping Δ ρ Γ →
    Γ ⊢ t : A →
    Δ ⊢ ρ ⋅ t : ρ ⋅ A.
Proof.
  intros Γ Δ ρ t A hρ ht.
  induction ht using styping_ind in Δ, ρ, hρ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto using rtyping_up ].
  all: rasimpl.
  - eapply hρ in H as [B [? eB]].
    rewrite eB. now econstructor.
  - rasimpl in IHht1; rasimpl in IHht4.
    assert (((0 .: ρ >> S) ⋅ B) <[ (ρ ⋅ u)..] = B <[ ρ ⋅ u .: ρ >> var])
      as <- by now rasimpl.
    econstructor. all: eauto.
    eauto using rtyping_up.
  - rasimpl in IHht2.
    econstructor. all: eauto.
    now apply conv_ren.
Qed.

(** Reproving [ext_term] but with scoping assumption *)

Definition eq_subst_on k (σ θ : nat → term) :=
  ∀ x, x < k → σ x = θ x.

Lemma eq_subst_on_up k σ θ :
  eq_subst_on k σ θ →
  eq_subst_on (S k) (up_term σ) (up_term θ).
Proof.
  intros h [] he.
  - reflexivity.
  - cbn. repeat core.unfold_funcomp. f_equal.
    apply h. lia.
Qed.

Lemma ext_term_scoped k t σ θ :
  scoped k t = true →
  eq_subst_on k σ θ →
  t <[ σ ] = t <[ θ ].
Proof.
  intros h e.
  induction t using term_rect in k, h, σ, θ, e |- *.
  all: try solve [ cbn ; eauto ].
  all: try solve [
    cbn in * ; apply andb_prop in h ;
    f_equal ; intuition eauto using eq_subst_on_up
  ].
  cbn. apply e. cbn - ["<?"] in h.
  now rewrite Nat.ltb_lt in h.
Qed.

(** Corollary: every substitution acts like a list of terms

  We present two versions: one with actual lists, and one where we truncate
  a substitution directly, behaving as a shift outside.
  The latter has the advantage that it verifies the condition for
  [subst_inst] later.

*)

Fixpoint listify k (σ : nat → term) :=
  match k with
  | 0 => []
  | S k => σ 0 :: listify k (S >> σ)
  end.

Fixpoint trunc k d (σ : nat → term) :=
  match k with
  | 0 => plus d >> ids
  | S k => σ 0 .: trunc k d (S >> σ)
  end.

Lemma eq_subst_trunc k d σ :
  eq_subst_on k σ (trunc k d σ).
Proof.
  intros x h.
  induction k as [| k ih] in x, h, σ |- *. 1: lia.
  cbn. destruct x as [| x].
  - reflexivity.
  - cbn. apply (ih (S >> σ)). lia.
Qed.

Lemma trunc_bounds k d σ x :
  trunc k d σ (k + x) = var (d + x).
Proof.
  induction k as [| k ih] in σ, x |- *.
  - cbn. reflexivity.
  - cbn. apply ih.
Qed.

(** Substitution preserves typing *)

Inductive σtyping (Γ : ctx) (σ : nat → term) : ctx → Prop :=
| type_nil : σtyping Γ σ ∙
| type_cons Δ A :
    σtyping Γ (S >> σ) Δ →
    Γ ⊢ σ 0 : A <[ S >> σ ] →
    σtyping Γ σ (Δ ,, A).

#[export] Instance σtyping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff)σtyping.
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

Lemma autosubst_simpl_σtyping :
  ∀ Γ Δ r s,
    SubstSimplification r s →
    σtyping Γ r Δ ↔ σtyping Γ s Δ.
Proof.
  intros Γ Δ r s H.
  apply σtyping_morphism.
  1,3: reflexivity.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_σtyping : rasimpl_outermost.

Lemma σtyping_weak Γ Δ σ A :
  σtyping Γ σ Δ →
  σtyping (Γ,, A) (σ >> ren_term S) Δ.
Proof.
  intros h.
  induction h.
  - constructor.
  - constructor.
    + assumption.
    + assert (S ⋅ A0 <[ S >> σ] = A0 <[ S >> (σ >> ren_term S)]) as <- by now rasimpl.
      eapply styping_ren. 2: eassumption.
      apply rtyping_S.
Qed.

Lemma σtyping_up Γ Δ A σ :
  σtyping Γ σ Δ →
  σtyping (Γ ,, A <[ σ ]) (up_term σ) (Δ,, A).
Proof.
  intros h.
  constructor.
  - rasimpl. now apply σtyping_weak.
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

Lemma scoped_subst σ k t :
  scoped k t = true →
  t <[ ups k σ ] = t.
Proof.
  intros h.
  induction t using term_rect in k, σ, h |- *.
  all: try solve [ cbn ; eauto ].
  all: try solve [
    cbn ;
    apply andb_prop in h as [] ;
    change (up_term_term (ups ?k ?σ)) with (ups (S k) σ) ;
    f_equal ;
    eauto
  ].
  cbn - ["<?"] in *.
  apply ups_below.
  apply Nat.ltb_lt. assumption.
Qed.

Corollary closed_subst σ t :
  closed t = true →
  t <[ σ ] = t.
Proof.
  intros h.
  eapply scoped_subst in h. eauto.
Qed.

Lemma scoped_upwards k l t :
  scoped k t = true →
  k ≤ l →
  scoped l t = true.
Proof.
  intros ht hkl.
  induction t using term_rect in k, l, ht, hkl |- *.
  all: try solve [ cbn ; eauto ].
  all: try solve [
    cbn in * ; rewrite Bool.andb_true_iff in * ;
    intuition eauto with arith
  ].
  cbn - ["<?"] in *. rewrite Nat.ltb_lt in *. lia.
Qed.

Lemma uprens_below k ρ n :
  n < k →
  uprens k ρ n = n.
Proof.
  intro h.
  induction k as [| k ih] in n, ρ, h |- *. 1: lia.
  cbn. destruct n as [| ].
  - reflexivity.
  - cbn. core.unfold_funcomp. rewrite ih. 2: lia.
    reflexivity.
Qed.

Lemma uprens_above k ρ n :
  uprens k ρ (k + n) = k + ρ n.
Proof.
  induction k as [| k ih] in n |- *.
  - cbn. rasimpl. reflexivity.
  - cbn. core.unfold_funcomp. rewrite ih.
    rasimpl. reflexivity.
Qed.

Lemma scoped_lift_gen k l t m :
  scoped (m + l) t = true →
  scoped (m + k + l) (uprens m (plus k) ⋅ t) = true.
Proof.
  intros h.
  induction t using term_rect in m, k, l, h |- *.
  all: try solve [ cbn ; eauto ].
  all: try solve [
    cbn in * ; rewrite Bool.andb_true_iff in * ;
    (* rewrite Nat.ltb_lt in * ; *)
    intuition eauto with arith
  ].
  - cbn - ["<=?"] in *. rewrite Nat.ltb_lt in *.
    destruct (lt_dec n m).
    + rewrite uprens_below. 2: assumption.
      lia.
    + pose (p := n - m). replace n with (m + p) by lia.
      rewrite uprens_above. lia.
  - cbn in *. rewrite Bool.andb_true_iff in *.
    intuition eauto.
    change (upRen_term_term (uprens m ?ρ)) with (uprens (S m) ρ).
    change (S (m + k + l)) with (S m + k + l).
    eauto.
  - cbn in *. rewrite Bool.andb_true_iff in *.
    intuition eauto.
    change (upRen_term_term (uprens m ?ρ)) with (uprens (S m) ρ).
    change (S (m + k + l)) with (S m + k + l).
    eauto.
Qed.

Lemma scoped_lift k l t :
  scoped l t = true →
  scoped (k + l) (plus k ⋅ t) = true.
Proof.
  intros h.
  eapply scoped_lift_gen with (m := 0).
  assumption.
Qed.

Lemma styping_subst Γ Δ σ t A :
  σtyping Δ σ Γ →
  Γ ⊢ t : A →
  Δ ⊢ t <[ σ ] : A <[ σ ].
Proof.
  intros hσ ht.
  induction ht using styping_ind in Δ, σ, hσ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto using σtyping_up ].
  - rasimpl.
    induction hσ in x, H |- *. 1: destruct x ; discriminate.
    destruct x.
    + cbn in H. inversion H. subst. assumption.
    + apply IHhσ. assumption.
  - assert ((B <[ up_term_term σ]) <[ (u <[ σ])..] = (B <[ u..]) <[ σ])
      as <- by now rasimpl.
    cbn in *. econstructor ; eauto using σtyping_up.
  - econstructor. 1,3: eauto.
    eapply conv_subst. eassumption.
Qed.

(** Validity (or presupposition) *)

Lemma σtyping_ids Γ :
  σtyping Γ ids Γ.
Proof.
  induction Γ as [| A Γ ih].
  - constructor.
  - constructor.
    + eapply σtyping_weak with (A := A) in ih.
      assumption.
    + assert (Init.Nat.add 1 ⋅ A = A <[ S >> ids]) as <- by now rasimpl; substify.
      now econstructor.
Qed.

Lemma styping_one Γ A u :
  Γ ⊢ u : A →
  σtyping Γ u.. (Γ ,, A).
Proof.
  intros h.
  constructor. all: rasimpl. 2: auto.
  erewrite autosubst_simpl_σtyping. 2: exact _. (* Somehow rasimpl doesn't work *)
  apply σtyping_ids.
Qed.

(* TODO *)

Lemma valid_wf Γ x A :
  wf Γ →
  nth_error Γ x = Some A →
  ∃ s i, Γ ⊢ (plus (S x)) ⋅ A : Sort s i.
Proof.
  intros hΓ h.
  induction hΓ as [| Γ s i B hΓ ih hB] in x, h |- *.
  1: destruct x ; discriminate.
  destruct x.
  - cbn in *. inversion h. subst.
    exists s, i. rasimpl.
    assert (S ⋅ Sort s i = Sort s i) as <- by easy.
    eapply styping_ren. 1: eapply rtyping_S.
    assumption.
  - cbn in h. eapply ih in h as [s' [j h]]. exists s', j.
    eapply styping_ren in h. 2: eapply rtyping_S.
    rasimpl in h. eassumption.
Qed.

Definition σtyping_alt (Γ : ctx) (σ : nat → term) (Δ : ctx) :=
  ∀ x A,
    nth_error Δ x = Some A →
    Γ ⊢ σ x : ((plus (S x)) ⋅ A) <[ σ ].

Lemma σtyping_alt_equiv Γ σ Δ :
  σtyping Γ σ Δ ↔ σtyping_alt Γ σ Δ.
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

Lemma styping_lift_closed Γ t A :
  ∙ ⊢ t : A →
  closed A = true →
  Γ ⊢ t : A.
Proof.
  intros h hA.
  eapply styping_scoped in h as ht. cbn in ht.
  eapply styping_ren in h. 2: eapply rtyping_add.
  rewrite !closed_ren in h. 2,3: assumption.
  rewrite app_nil_r in h.
  eassumption.
Qed.

Lemma validity Γ t A :
  wf Γ →
  Γ ⊢ t : A →
  ∃ s i, Γ ⊢ A : Sort s i.
Proof.
  intros hΓ h.
  induction h using styping_ind in hΓ |- *.
  all: try solve [ eexists ; econstructor ; intuition eauto using styping ].
  - apply valid_wf. all: assumption.
  - exists s', j.
    assert (Sort s' j <[ u..] = Sort s' j) as <- by easy.
    apply (styping_subst (Γ,,A)).
    + now apply styping_one.
    + assumption.
Qed.

(** * Context conversion *)

Notation ctx_conv Γ Δ := (Forall2 conversion Γ Δ).

Lemma ctx_conv_cons_same Γ Δ A :
  ctx_conv Γ Δ →
  ctx_conv (Γ ,, A) (Δ ,, A).
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

Inductive wf_ctx_conv : ctx → ctx → Prop :=
| wf_conv_nil : wf_ctx_conv ∙ ∙
| wf_conv_cons Γ Δ s i A B :
    wf_ctx_conv Γ Δ →
    Δ ⊢ A : Sort s i →
    A ≡ B →
    wf_ctx_conv (Γ ,, A) (Δ ,, B).

Lemma wf_ctx_conv_nth_error_l Γ Δ x A :
  wf_ctx_conv Γ Δ →
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

Lemma typing_ctx_conv_gen (Γ Δ : ctx) t A :
  wf_ctx_conv Γ Δ →
  Γ ⊢ t : A →
  Δ ⊢ t : A.
Proof.
  intros hctx h.
  induction h in Δ, hctx |- * using styping_ind.
  all: try solve [ econstructor ; eauto using wf_conv_cons, conv_refl ].
  eapply wf_ctx_conv_nth_error_l in hctx as h. 2: eassumption.
  destruct h as (s & i & B & e & hc & h).
  eapply stype_conv.
  - econstructor. eassumption.
  - apply conv_sym. apply conv_ren. assumption.
  - eassumption.
Qed.
  
Lemma typing_ctx_conv (Γ Δ : ctx) t A :
  Γ ⊢ t : A →
  wf Γ →
  ctx_conv Γ Δ →
  Δ ⊢ t : A.
Proof.
  intros ht hΓ hctx.
  eapply typing_ctx_conv_gen. 2: eassumption.
  clear ht. induction hΓ in Δ, hctx |- *.
  - inversion hctx. constructor.
  - inversion hctx. subst.
    econstructor. 1,3: eauto.
    eauto using typing_ctx_conv_gen.
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
