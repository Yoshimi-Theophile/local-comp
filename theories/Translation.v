From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Typing BasicMetaTheory.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Require Import Equations.Prop.DepElim.

Set Default Goal Selector "!".

Section Translation.

  Reserved Notation "[ Γ ]c" (at level 0).
  Reserved Notation "[ Γ | t ]" (at level 0). 
  
  Definition isPTyp (Γ : scope) x : bool :=
    match nth_error Γ x with
    | Some S_PTyp => true
    | _ => false
    end.
  
  Fixpoint tl_tmP (Γ : scope) (t : term) : term :=
    match t with
    | var x =>
        if (isPTyp Γ x) then var x else tt

    | Sort s i =>
        match s with
        | S_Typ => unit
        | S_PTyp => Typ i
        end

    | Pi s s' i j A B =>
        match s' with
        | S_Typ => unit
        | S_PTyp =>
            let A' :=
              match s with
              | S_Typ => unit
              | S_PTyp => [Γ|A]
              end in
            Pi_T i j A' [s :: Γ|B]
        end
          
    | lam s s' A t =>
        match s' with
        | S_Typ => tt
        | S_PTyp =>
            let A' :=
              match s with
              | S_Typ => unit
              | S_PTyp => [Γ|A]
              end in
            lam_T A' [s :: Γ|t]
        end

    | app s s' t u =>
        match s' with
        | S_Typ => tt
        | S_PTyp =>
            let u' :=
              match s with
              | S_Typ => tt
              | S_PTyp => [Γ|u]
              end in
            app_T [Γ|t] u'
        end

    | _ => unit (* inaccessible in styping *)                             
    end

  where "[ Γ | t ]" := (tl_tmP Γ t).
      
  Fixpoint tl_ctxP (Γ : sctx) : tctx :=
    match Γ with
    | nil => ∙t
    | cons (S_Typ, _) Γ => [Γ]c ,,t unit
    | cons (S_PTyp, t) Γ => [Γ]c ,,t [sc Γ|t]
    end
  where "[ Γ ]c" := (tl_ctxP Γ).

  Lemma type_sort_inv Γ s i A :
    Γ ⊢ Sort s i : A →
    A ≡ Sort s (S i).
  Proof.
    intros h.
    dependent induction h.
    all: try solve [discriminate].
    1: injection H; intros -> ->; constructor.
    eapply conv_trans.
    1: apply conv_sym.
    all: eauto.
  Qed.
  
  Lemma conv_sort s s' i j :
    Sort s i ≡ Sort s' j →
    s = s'.
  Admitted.
  
  Lemma styping_stc Γ t B :
    swf Γ →
    Γ ⊢ t : B →
    stc Γ t = stc Γ B.
  Proof.
    intros hΓ h.
    pose (svalidity _ _ _ hΓ h) as h'.
    destruct h' as [h1 [i h2]].
    pose (svalidity _ _ _ hΓ h2) as h''.
    destruct h'' as [h3 [j h4]].
    now apply type_sort_inv, conv_sort in h4.
  Qed.

  Lemma styping_scoping_stc Γ t B :
    swf Γ →
    Γ ⊢ t : B → 
    scoping (sc Γ) t (stc Γ B).
  Proof.
    intros hΓ h.
    pose (svalidity _ _ _ hΓ h) as h'.
    destruct h' as [h1 _].
    now rewrite <-(styping_stc Γ t B hΓ h).
  Qed.

  Lemma styping_scoping_stc_bw Γ t B :
    swf Γ →
    Γ ⊢ t : B → 
    scoping (sc Γ) B (stc Γ t).
  Proof.
    intros hΓ h.
    pose (svalidity _ _ _ hΓ h) as h'.
    destruct h' as [h1 [i h2]].
    pose (svalidity _ _ _ hΓ h2) as h''.
    destruct h'' as [h3 [j h4]].
    apply type_sort_inv, conv_sort in h4.
    now rewrite <-h4.
  Qed.
  
  Lemma rscoping_upren :
  ∀ Γ Δ m ρ,
    rscoping Γ ρ Δ →
    rscoping (m :: Γ) (up_ren ρ) (m :: Δ).
  Proof.
    intros Γ Δ m ρ h. intros x mx e.
    destruct x.
    - cbn in *. assumption.
    - cbn in *. apply h. assumption.
  Qed.
  
  Lemma tl_ren :
  ∀ Γ Δ ρ t,
    rscoping Γ ρ Δ →
    rscoping_comp Γ ρ Δ →
    [ Γ | ρ ⋅ t ] = ρ ⋅ [ Δ | t ].
  Proof.
  intros Γ Δ ρ t hρ hcρ.
  induction t in Γ, Δ, ρ, hρ, hcρ |- *.
  all: try solve [ rasimpl ; cbn ; eauto ].
  all: simpl.
  - unfold isPTyp.
    destruct (nth_error Δ n) eqn:e.
    + eapply hρ in e. rewrite e.
      destruct s. all: reflexivity.
    + eapply hcρ in e. rewrite e. reflexivity.
  - destruct s. all: eauto.
  - erewrite IHt1. 2,3: eassumption.
    erewrite IHt2.
    2:{ eapply rscoping_upren. eassumption. }
    2:{ eapply rscoping_comp_upren. assumption. }
    destruct s0, s. all: auto.
  - erewrite IHt1. 2,3: eassumption.
    erewrite IHt2.
    2:{ eapply rscoping_upren. eassumption. }
    2:{ eapply rscoping_comp_upren. assumption. }
    destruct s0, s. all: auto.
  - erewrite IHt1. 2,3: eassumption.
    erewrite IHt2. 2,3: eassumption.
    destruct s0, s. all: auto.
  Qed.

  Lemma tl_ctx_var Γ x A :
    nth_error Γ x = Some (S_PTyp, A) →
    nth_error [Γ ]c x = Some [skipn (S x) (sc Γ) | A].
  Proof.
    intros h.
    induction Γ in x, A, h |- *.
    1: destruct x; discriminate.
    destruct x.
    - simpl in *. destruct a.
      injection h; intros -> ->.
      reflexivity.
    - simpl. destruct a.
      simpl in h.
      destruct s; rewrite (IHΓ _ A).
      all: easy.
  Qed.
  
  Lemma tl_subst Γ Δ σ t :
    σscoping Γ σ Δ →
    σscoping_comp Γ σ Δ →
    scoping Γ (t <[ σ ]) S_PTyp →
    [ Γ | t <[ σ ] ] = [ Δ | t ] <[ σ >> tl_tmP Γ ].
  Proof.
    intros hσ hcσ hP.
    induction t in Γ, Δ, σ, hσ, hcσ, hP |- *.
    all: try solve [ rasimpl ; cbn ; eauto ].
    - rasimpl. simpl. unfold isPTyp.
      destruct (nth_error Δ n) eqn: e.
      + destruct s.
        2: reflexivity.
        assert (scoping Γ ((var n) <[ σ]) S_Typ) as hP' by
          apply (scoping_subst _ _ _ _ _ hσ (scope_var _ _ _ e)).
        apply scoping_st in hP.
        apply scoping_st in hP'.
        rewrite hP in hP'. discriminate.
      + simpl.
        eapply hcσ in e as e'.
        destruct e' as [m [e1 e2]].
        rewrite e1. cbn.
        unfold isPTyp.
        now rewrite e2.
    - rasimpl. destruct s.
      2: reflexivity.
      apply scoping_st in hP. discriminate.
    - rasimpl. simpl.
      destruct s0.
      1: reflexivity.
      destruct s.
      all: rasimpl.
      + erewrite IHt2.
        2:{ eapply σscoping_shift. eassumption. }
        2:{ rasimpl. eapply σscoping_comp_shift. assumption. }
        * admit.
        * eapply scoping_subst.
          1: eapply σscoping_shift; eassumption.
          inversion hP; subst.
          admit.
      + erewrite IHt1.
        2,3: eauto.
        2: now inversion hP.
        erewrite IHt2.
        2:{ eapply σscoping_shift. eassumption. }
        2:{ rasimpl. eapply σscoping_comp_shift. assumption. }
        * admit.
        * eapply scoping_subst.
          1: eapply σscoping_shift; eassumption.
          inversion hP; subst.
          admit.
    - admit.
    - admit.    
  Admitted.
  
  Lemma tl_conv Γ u v :
    u ≡ v →
    scoping (sc Γ) u S_PTyp →
    [ sc Γ | u ] ≡ [ sc Γ | v ].
  Proof.
    intros h hP.
    induction h in Γ, hP |- *.
    - 
  Admitted.

  Lemma tl_typP Γ t A :
    swf Γ →
    Γ ⊢ t : A →
    scoping (sc Γ) t S_PTyp → 
    [ Γ ]c ⊨ [sc Γ | t ] : [ sc Γ | A ].
  Proof.
    intros hΓ h hP.
    induction h using styping_ind in hΓ, hP |- *.
    - simpl. unfold isPTyp, sc at 1.
      rewrite nth_error_map, H.
      destruct s; simpl.
      + unfold stc in hP.
        assert (nth_error (sc Γ) x = Some S_Typ) as h
            by now unfold sc; rewrite nth_error_map, H.
        apply scoping_st in hP; simpl in hP.
        rewrite (nth_error_nth _ _ _ h) in hP.
        discriminate.
      + rasimpl.
        rewrite (tl_ren _ (skipn (S x) (sc Γ))).
        * constructor.
          now apply tl_ctx_var.
        * intros y my ey.
          now rewrite nth_error_skipn in ey.
        * intros y ey.
          now rewrite nth_error_skipn in ey.
    - apply scoping_st in hP.
      unfold stc in hP; subst.
      constructor.
    - assert (cscoping Γ (Pi s s' i j A B) S_PTyp) as hP' by easy.
      apply scoping_st in hP.
      unfold stc in hP; subst.
      destruct s; simpl in *.
      + constructor.
        1: constructor.
        apply IHh2.
        1: now apply (swf_cons _ _ i).
        inversion hP'; subst.
        assumption.
      + constructor.
        * apply IHh1.
          1: assumption.
          inversion hP'; subst.
          assumption.
        * apply IHh2.
          1: now apply (swf_cons _ _ i).
          inversion hP'; subst.
          assumption.
    - assert (cscoping Γ (lam s s' A t) S_PTyp) as hP' by easy.
      apply scoping_st in hP.
      unfold stc in hP; subst.
      destruct s; simpl in *.
      + constructor.
        1: constructor.
        all: inversion hP'; subst.
        * apply IHh2.
          1: now apply (swf_cons _ _ i).
          change (S_PTyp) with (stc ((Γ,,s (S_Typ, A))) (PTyp j)).
          change (S_Typ :: sc Γ) with (sc (Γ,,s (S_Typ, A))).
          apply styping_scoping_stc.
          1: now apply (swf_cons _ _ i). 
          assumption.
        * apply IHh3.
          1: now apply (swf_cons _ _ i).
          assumption.
      + constructor.
        all: inversion hP'; subst.
        1: now apply IHh1.
        * apply IHh2.
          1: now apply (swf_cons _ _ i).
          change (S_PTyp) with (stc ((Γ,,s (S_PTyp, A))) (PTyp j)) at 2.
          change (S_PTyp :: sc Γ) with (sc (Γ,,s (S_PTyp, A))).
          apply styping_scoping_stc.
          1: now apply (swf_cons _ _ i).
          assumption.
        * apply IHh3.
          1: now apply (swf_cons _ _ i).
          assumption.
    - assert (cscoping Γ (app s s' t u) S_PTyp) as hP' by easy.
      apply scoping_st in hP.
      unfold stc in hP; subst.
      destruct s; simpl in *.
      + rewrite (tl_subst _ (S_Typ :: sc Γ)).
        * assert
            ([S_Typ :: sc Γ | B] <[ u.. >> tl_tmP (sc Γ)] =
             [S_Typ :: sc Γ | B] <[ [ sc Γ | u].. ]) as ->.
          {
            rasimpl.
            admit.
          }
          
          assert (tt = [sc Γ | u]) as -> by admit.
          eapply ttype_app.
          
        * apply σscoping_one. change S_Typ with (stc Γ (Typ i)).
          assert ((stc Γ A) = (stc Γ (Typ i))) as <- by now apply styping_stc.
          now apply styping_scoping_stc.
        * apply σscoping_comp_one.
        * apply (scoping_subst _ (S_Typ :: sc Γ)).
          -- eapply σscoping_one. change S_Typ with (stc Γ (Typ i)).
             assert ((stc Γ A) = (stc Γ (Typ i))) as <- by now apply styping_stc.
             now apply styping_scoping_stc.
          -- change (S_Typ :: sc Γ) with (sc (Γ ,,s (S_Typ, A))).
             change S_PTyp with (stc (Γ ,,s (S_Typ, A)) (PTyp j)).
             apply styping_scoping_stc.
             2: assumption.
             econstructor; eassumption.
      + rewrite (tl_subst _ (S_PTyp :: sc Γ)).
        * admit.
        * apply σscoping_one. change S_PTyp with (stc Γ (PTyp i)).
          assert ((stc Γ A) = (stc Γ (PTyp i))) as <- by now apply styping_stc.
          now apply styping_scoping_stc.
        * apply σscoping_comp_one.
        * apply (scoping_subst _ (S_PTyp :: sc Γ)).
          -- eapply σscoping_one. change S_PTyp with (stc Γ (PTyp i)).
             assert ((stc Γ A) = (stc Γ (PTyp i))) as <- by now apply styping_stc.
             now apply styping_scoping_stc.
          -- change (S_PTyp :: sc Γ) with (sc (Γ ,,s (S_PTyp, A))).
             change S_PTyp with (stc (Γ ,,s (S_PTyp, A)) (PTyp j)).
             apply styping_scoping_stc.
             2: assumption.
             econstructor; eassumption.
    - assert (cscoping Γ t S_PTyp) as hP' by easy.
      apply scoping_st in hP.
      apply (ttype_conv _ i [sc Γ|A]).
      1: now apply IHh1.
      + apply tl_conv.
        1: assumption.
        rewrite <-hP.
        now apply styping_scoping_stc_bw.
      + rewrite (styping_stc _ _ _ hΓ (stype_conv _ _ _ _ _ _ h1 H h2)) in hP.
        rewrite (styping_stc _ _ _ hΓ h2) in hP.
        simpl in hP; subst.
        simpl in IHh2.
        apply IHh2.
        1: assumption.
        change (S_PTyp) with (stc Γ (PTyp i)).
        now apply styping_scoping_stc.
  Admitted.
  
  (*
  Reserved Notation "⟦ Γ | t ⟧" (at level 0).
  Reserved Notation "⟦ Γ ⟧c" (at level 0).
  
  Fixpoint Tl_tm (Γ : scope) (t : term) : term :=
    match t with
    | var x =>
        unit
        (* if (isPTyp Γ x) then sig [Γ|x] else tt *)

    | Sort s i =>
        match s with
        | S_Typ => Typ i
        | S_PTyp => lam_T (Typ i) (Pi_T i (S i) (var 0) (Typ i))
        end

    | _ => unit
    end.

  (*
    | Pi s s' i j A B =>
        match s' with
        | S_Typ => unit
        | S_PTyp =>
            let A' :=
              match s with
              | S_Typ => unit
              | S_PTyp => [Γ|A]
              end in
            Pi_T i j A' [Γ|B]
        end
          
    | lam s s' A t =>
        match s' with
        | S_Typ => tt
        | S_PTyp =>
            let A' :=
              match s with
              | S_Typ => unit
              | S_PTyp => [Γ|A]
              end in
            lam_T A' [Γ|t]
        end

    | app s s' t u =>
        match s' with
        | S_Typ => tt
        | S_PTyp =>
            let u' :=
              match s with
              | S_Typ => tt
              | S_PTyp => [Γ|u]
              end in
            app_T [Γ|t] u'
        end

    | _ => unit (* inaccessible in styping *)                             
    end
*)
  where "[ Γ | t ]" := (tl_tmP Γ t).
      
  Fixpoint tl_ctxP (Γ : sctx) : tctx :=
    match Γ with
    | nil => ∙t
    | cons (S_Typ, _) Γ => [Γ]c ,,t unit
    | cons (S_PTyp, t) Γ => [Γ]c ,,t [sc Γ|t]
    end
  where "[ Γ ]c" := (tl_ctxP Γ).
   *)
  
End Translation.

(* Fixpoint tl_P *)
  
(*
  Fixpoint inline (t : term) :=
    match t with
    | var n => var n
    | Sort i => Sort i
    | Pi A B => Pi ⟦ A ⟧ ⟦ B ⟧
    | lam A t => lam ⟦ A ⟧ ⟦ t ⟧
    | app u v => app ⟦ u ⟧ ⟦ v ⟧
    | const c ξ => inst ⟦ ξ ⟧× (κ c)
    | assm x => assm x
    end

  where "⟦ t ⟧" := (inline t)
  and "⟦ k ⟧×" := (map_instance inline k).

  Notation "⟦ l ⟧*" := (map inline l).

  Definition inline_crule rule := {|
    cr_env := ⟦ rule.(cr_env) ⟧* ;
    cr_pat := ⟦ rule.(cr_pat) ⟧ ;
    cr_sub := rule.(cr_sub) ;
    cr_rep := ⟦ rule.(cr_rep) ⟧ ;
    cr_typ := ⟦ rule.(cr_typ) ⟧
  |}.

  Notation "⟦ r ⟧r" := (inline_crule r).
  Notation "⟦ R ⟧R" := (map inline_crule R).

  Definition inline_idecl (d : idecl) :=
    match d with
    | Assm A => Assm ⟦ A ⟧
    | Comp rl => Comp ⟦ rl ⟧r
    end.

  Notation "⟦ d ⟧d" := (inline_idecl d).
  Notation "⟦ X ⟧e" := (map inline_idecl X).

  Definition gclosed :=
    ∀ c, closed (κ c) = true.

  Context (hclosed : gclosed).

  Lemma inline_ren ρ t :
    ⟦ ρ ⋅ t ⟧ = ρ ⋅ ⟦ t ⟧.
  Proof.
    induction t in ρ |- * using term_rect.
    all: try solve [ cbn ; f_equal ; eauto ].
    cbn. rewrite ren_inst. rewrite closed_ren. 2: auto.
    f_equal.
    rewrite !map_map. apply map_ext_All.
    eapply All_impl. 2: eassumption.
    intros o h.
    rewrite !option_map_option_map. apply option_map_ext_onSomeT.
    eapply onSomeT_impl. 2: eassumption.
    cbn. auto.
  Qed.

  Lemma up_term_inline σ n :
    (up_term_term (σ >> inline)) n = (up_term_term σ >> inline) n.
  Proof.
    rasimpl. destruct n.
    - reflexivity.
    - cbn. unfold core.funcomp. rewrite inline_ren. reflexivity.
  Qed.

  Lemma inline_subst σ t :
    ⟦ t <[ σ ] ⟧ = ⟦ t ⟧ <[ σ >> inline ].
  Proof.
    induction t in σ |- * using term_rect.
    all: try solve [ cbn ; f_equal ; eauto ].
    - cbn. f_equal. 1: eauto.
      rewrite IHt2. eapply ext_term. intro.
      rewrite up_term_inline. reflexivity.
    - cbn. f_equal. 1: eauto.
      rewrite IHt2. eapply ext_term. intro.
      rewrite up_term_inline. reflexivity.
    - cbn. rewrite subst_inst_closed. 2: auto.
      f_equal.
      rewrite !map_map. apply map_ext_All.
      eapply All_impl. 2: eassumption.
      intros ? h.
      rewrite !option_map_option_map. apply option_map_ext_onSomeT.
      eapply onSomeT_impl. 2: eassumption.
      cbn. auto.
  Qed.

  Lemma inline_iget ξ x :
    ⟦ iget ξ x ⟧ = iget ⟦ ξ ⟧× x.
  Proof.
    unfold iget. rewrite nth_error_map.
    destruct nth_error as [[] |]. all: reflexivity.
  Qed.

  Lemma inline_ren_instance ρ ξ :
    ⟦ ren_instance ρ ξ ⟧× = ren_instance ρ ⟦ ξ ⟧×.
  Proof.
    rewrite !map_map. apply map_ext. intro.
    rewrite !option_map_option_map. apply option_map_ext. intro.
    apply inline_ren.
  Qed.

  Lemma inline_inst ξ t :
    ⟦ inst ξ t ⟧ = inst ⟦ ξ ⟧× ⟦ t ⟧.
  Proof.
    induction t in ξ |- * using term_rect.
    all: try solve [ cbn ; f_equal ; eauto ].
    - cbn. f_equal. 1: eauto.
      rewrite IHt2. rewrite inline_ren_instance. reflexivity.
    - cbn. f_equal. 1: eauto.
      rewrite IHt2. rewrite inline_ren_instance. reflexivity.
    - cbn. rewrite inst_inst. f_equal.
      rewrite !map_map. apply map_ext_All.
      eapply All_impl. 2: eassumption.
      intros o ho. rewrite !option_map_option_map. apply option_map_ext_onSomeT.
      eapply onSomeT_impl. 2: eassumption.
      auto.
    - cbn. apply inline_iget.
  Qed.

  Definition g_conv_unfold :=
    ∀ c Ξ' A t,
      Σ c = Some (Def Ξ' A t) →
      [] ;; ⟦ Ξ' ⟧e ⊢ κ c ≡ ⟦ t ⟧.

  Context (h_conv_unfold : g_conv_unfold).

  Lemma conv_ren_inst Ξ ρ ξ ξ' :
    Forall2 (option_rel (conversion Σ Ξ)) ξ ξ' →
    Forall2 (option_rel (conversion Σ Ξ)) (ren_instance ρ ξ) (ren_instance ρ ξ').
  Proof.
    intros h.
    apply Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    intros. apply option_rel_map_l, option_rel_map_r.
    eapply option_rel_impl. 2: eassumption.
    intros. eapply conv_ren. eassumption.
  Qed.

  Lemma ictx_get_assm_inline Ξ x A :
    ictx_get Ξ x = Some (Assm A) →
    ictx_get ⟦ Ξ ⟧e x = Some (Assm ⟦ A ⟧).
  Proof.
    intro h. rewrite ictx_get_map. rewrite h. reflexivity.
  Qed.

  Lemma ictx_get_comp_inline Ξ x rl :
    ictx_get Ξ x = Some (Comp rl) →
    ictx_get ⟦ Ξ ⟧e x = Some (Comp ⟦ rl ⟧r).
  Proof.
    intro h. rewrite ictx_get_map. rewrite h. reflexivity.
  Qed.

  Lemma scoped_instance_inline_ih k ξ :
    All (onSomeT (λ t, ∀ k, scoped k t = true → scoped k ⟦ t ⟧ = true)) ξ →
    scoped_instance k ξ = true →
    scoped_instance k ⟦ ξ ⟧× = true.
  Proof.
    intros ih h.
    apply forallb_All in h. move h at top.
    eapply All_prod in h. 2: eassumption.
    apply All_forallb. apply All_map. eapply All_impl. 2: eassumption.
    cbn. intros o [h1 h2].
    apply onSomeb_onSome, onSomeT_onSome. apply onSomeT_map.
    apply onSomeb_onSome, onSome_onSomeT in h2.
    eapply onSomeT_prod in h1. 2: eassumption.
    eapply onSomeT_impl. 2: eassumption.
    cbn. intros t []. eauto.
  Qed.

  Lemma scoped_inline k t :
    scoped k t = true →
    scoped k ⟦ t ⟧ = true.
  Proof.
    intros h.
    induction t using term_rect in k, h |- *.
    all: try solve [ cbn ; eauto ].
    all: try solve [
      cbn in * ; rewrite Bool.andb_true_iff in * ;
      intuition eauto
    ].
    cbn in h |- *. eapply scoped_inst_closed.
    - eapply scoped_instance_inline_ih. all: assumption.
    - apply hclosed.
  Qed.

  Lemma scoped_instance_inline k ξ :
    scoped_instance k ξ = true →
    scoped_instance k ⟦ ξ ⟧× = true.
  Proof.
    intros h.
    eapply scoped_instance_inline_ih. 2: assumption.
    eapply forall_All. intros o ho.
    destruct o. 2: constructor.
    cbn. intros. eapply scoped_inline. assumption.
  Qed.

  Lemma iscope_instance_inline_ih Ξ ξ :
    Forall (OnSome (λ t : term, iscope ⟦ Ξ ⟧e ⟦ t ⟧)) ξ →
    iscope_instance ⟦ Ξ ⟧e ⟦ ξ ⟧×.
  Proof.
    intros ih.
    apply Forall_map. eapply Forall_impl. 2: eassumption.
    setoid_rewrite OnSome_onSome.
    intros ??.
    apply onSome_map.
    eapply onSome_impl. 2: eassumption.
    auto.
  Qed.

  Lemma iscope_inline Ξ t :
    iscope Ξ t →
    iscope ⟦ Ξ ⟧e ⟦ t ⟧.
  Proof.
    intros h.
    induction h using iscope_ind_alt.
    all: try solve [ cbn ; constructor; eauto ].
    - cbn. eapply iscope_inst.
      eauto using iscope_instance_inline_ih.
    - cbn. econstructor.
      eauto using ictx_get_assm_inline.
  Qed.

  Lemma inline_ctx_inst ξ Γ :
    ⟦ ctx_inst ξ Γ ⟧* = ctx_inst ⟦ ξ ⟧× ⟦ Γ ⟧*.
  Proof.
    induction Γ as [| A Γ ih] in ξ |- *.
    - reflexivity.
    - cbn. rewrite ih. rewrite inline_inst.
      rewrite inline_ren_instance. rewrite length_map. reflexivity.
  Qed.

  Lemma inst_equations_inline_ih Ξ Ξ' ξ :
    inst_equations_ (λ u v, [] ;; ⟦ Ξ ⟧e ⊢ ⟦ u ⟧ ≡ ⟦ v ⟧) ξ Ξ' →
    inst_equations [] ⟦ Ξ ⟧e ⟦ ξ ⟧× ⟦ Ξ' ⟧e.
  Proof.
    intros ih.
    intros x rl hx.
    rewrite ictx_get_map in hx.
    destruct (ictx_get _ _) as [[| rl']|] eqn:hx'. 1,3: discriminate.
    cbn in hx. inversion hx. subst. clear hx.
    specialize (ih _ _ hx') as (hx & hl & hr & ih).
    cbn. rewrite nth_error_map, hx. cbn.
    rewrite !length_map.
    rewrite !inline_inst in ih. rewrite !inline_ren_instance in ih.
    intuition eauto using scoped_inline.
  Qed.

  Lemma cr_pat_inline rl :
    ⟦ rl.(cr_pat) ⟧ = ⟦ rl ⟧r.(cr_pat).
  Proof.
    reflexivity.
  Qed.

  Lemma cr_rep_inline rl :
    ⟦ rl.(cr_rep) ⟧ = ⟦ rl ⟧r.(cr_rep).
  Proof.
    reflexivity.
  Qed.

  Lemma conv_inline Ξ u v :
    Σ ;; Ξ ⊢ u ≡ v →
    [] ;; ⟦ Ξ ⟧e ⊢ ⟦ u ⟧ ≡ ⟦ v ⟧.
  Proof.
    intros h.
    induction h using conversion_ind.
    all: try solve [ cbn ; ttconv ].
    - cbn. rewrite inline_subst. eapply meta_conv_trans_r. 1: econstructor.
      apply ext_term. intros []. all: reflexivity.
    - cbn. rewrite inline_inst. eapply conv_inst_closed.
      + eapply inst_equations_inline_ih. eassumption.
      + eapply h_conv_unfold. eassumption.
    - rewrite !inline_subst. subst lhs rhs.
      rewrite cr_pat_inline, cr_rep_inline.
      eapply conv_red.
      + apply ictx_get_comp_inline. eassumption.
      + cbn. eapply scoped_inline. rewrite length_map. assumption.
      + cbn. eapply scoped_inline. rewrite length_map. assumption.
    - cbn. eapply conv_insts.
      apply Forall2_map_l, Forall2_map_r.
      eapply Forall2_impl. 2: eassumption.
      intros. apply option_rel_map_l, option_rel_map_r.
      eapply option_rel_impl. 2: eassumption.
      cbn. auto.
    - econstructor. assumption.
    - eapply conv_trans. all: eassumption.
  Qed.

  Definition g_type :=
    ∀ c Ξ' A t,
      Σ c = Some (Def Ξ' A t) →
      [] ;; ⟦ Ξ' ⟧e | ∙ ⊢ κ c : ⟦ A ⟧.

  Context (h_type : g_type).

  Lemma inst_typing_inline Ξ Γ ξ Ξ' :
    iwf Σ Ξ' ->
    inst_typing_ (conversion Σ Ξ) (λ t A, [] ;; ⟦ Ξ ⟧e | ⟦ Γ ⟧* ⊢ ⟦ t ⟧ : ⟦ A ⟧) ξ Ξ' →
    inst_typing [] ⟦ Ξ ⟧e ⟦ Γ ⟧* ⟦ ξ ⟧× ⟦ Ξ' ⟧e.
  Proof.
    intro wf.
    induction 1; cbn; depelim wf; try constructor; eauto.
    - rewrite map_app; constructor; auto.
      + apply scoped_inline. cbn.
        now rewrite length_map.
      + eapply iscope_inline. eassumption.
      + apply scoped_inline. cbn.
        now rewrite length_map.
      + eapply iscope_inline. eassumption.
      + cbn. rewrite !length_map.
        rewrite <- !inline_ren_instance.
        rewrite <- !inline_inst.
        now apply conv_inline.
    - rewrite map_app; constructor; auto.
      + eapply iscope_inline. eassumption.
      + apply scoped_inline. assumption.
      + rewrite <- inline_inst. assumption.
  Qed.

  Lemma typing_inline Ξ Γ t A :
    gwf Σ →
    Σ ;; Ξ | Γ ⊢ t : A →
    [] ;; ⟦ Ξ ⟧e | ⟦ Γ ⟧* ⊢ ⟦ t ⟧ : ⟦ A ⟧.
  Proof.
    intros hΣ h.
    induction h using typing_ind.
    all: try solve [ intros ; cbn ; tttype ].
    - cbn. rewrite inline_ren. econstructor.
      rewrite nth_error_map. rewrite H. reflexivity.
    - cbn in *. eapply meta_conv.
      + tttype.
      + rewrite inline_subst. apply ext_term. intros []. all: reflexivity.
    - apply valid_def in H as Hc; auto. destruct Hc as (wf & Hc).
      cbn. rewrite inline_inst. eapply typing_inst_closed.
      + eapply inst_typing_inline; eauto.
      + eapply h_type. all: eassumption.
    - cbn. econstructor.
      + apply ictx_get_assm_inline. assumption.
      + apply scoped_inline. assumption.
    - econstructor. 1,3: eassumption.
      apply conv_inline. assumption.
  Qed.

End Inline.

Notation "⟦ t ⟧⟨ k ⟩" := (inline k t) (at level 0).
Notation "⟦ l ⟧*⟨ k ⟩" := (map (inline k) l).
Notation "⟦ t ⟧×⟨ k ⟩" := (map_instance (inline k) t).
Notation "⟦ X ⟧e⟨ k ⟩" := (map (inline_idecl k) X).
Notation "⟦ r ⟧r⟨ k ⟩" := (inline_crule k r).
Notation "⟦ R ⟧R⟨ k ⟩" := (map (inline_crule k) R).

Reserved Notation "⟦ s ⟧κ" (at level 0).

(* TODO Probably can just use [list (greg * term)] *)

Definition gnil (c : gref) :=
  dummy.

Definition gcons r t κ (c : gref) : term :=
  if (c =? r)%string then t else κ c.

Fixpoint inline_gctx_ufd Σ :=
  match Σ with
  | (c, d) :: Σ =>
    let κ := ⟦ Σ ⟧κ in
    match d with
    | Def Ξ A t => gcons c ⟦ t ⟧⟨ κ ⟩ κ
    end
  | [] => gnil
  end
where "⟦ s ⟧κ" := (inline_gctx_ufd s).

Lemma gcons_eq c c' t κ :
  (c' =? c)%string = true →
  gcons c t κ c' = t.
Proof.
  intro h.
  unfold gcons. rewrite h. reflexivity.
Qed.

Lemma gcons_neq c c' t κ :
  (c' =? c)%string = false →
  gcons c t κ c' = κ c'.
Proof.
  intro h.
  unfold gcons. rewrite h. reflexivity.
Qed.

Definition eq_gscope (Σ : gctx) (κ κ' : ginst) :=
  ∀ c Ξ' A t,
    Σ c = Some (Def Ξ' A t) →
    κ c = κ' c.

Lemma inline_ext Σ t κ κ' :
  gscope Σ t →
  eq_gscope Σ κ κ' →
  ⟦ t ⟧⟨ κ ⟩ = ⟦ t ⟧⟨ κ' ⟩.
Proof.
  intros ht he.
  induction ht in κ, κ', he |- * using gscope_ind.
  all: try solve [ cbn ; eauto ].
  all: try solve [ cbn ; f_equal ; eauto ].
  cbn.
  assert (e : ⟦ ξ ⟧×⟨ κ ⟩ = ⟦ ξ ⟧×⟨ κ' ⟩).
  { apply map_ext_Forall. eapply Forall_impl. 2: eassumption.
    intros o ho.
    rewrite OnSome_onSome in ho. apply onSome_onSomeT in ho.
    apply option_map_ext_onSomeT. eapply onSomeT_impl. 2: eassumption.
    cbn. auto.
  }
  rewrite <- e. f_equal.
  eapply he. eassumption.
Qed.

Lemma inline_instance_ext Σ (ξ : instance) κ κ' :
  gscope_instance Σ ξ →
  eq_gscope Σ κ κ' →
  ⟦ ξ ⟧×⟨ κ ⟩ = ⟦ ξ ⟧×⟨ κ' ⟩.
Proof.
  intros hξ he.
  eapply map_ext_Forall. eapply Forall_impl. 2: eassumption.
  intros o ho. rewrite OnSome_onSome in ho. apply onSome_onSomeT in ho.
  eapply option_map_ext_onSomeT. eapply onSomeT_impl. 2: eassumption.
  intros. eapply inline_ext. all: eassumption.
Qed.

Lemma inline_list_ext Σ l κ κ' :
  Forall (gscope Σ) l →
  eq_gscope Σ κ κ' →
  ⟦ l ⟧*⟨ κ ⟩ = ⟦ l ⟧*⟨ κ' ⟩.
Proof.
  intros hl he.
  eapply map_ext_Forall. eapply Forall_impl. 2: eassumption.
  intros. eapply inline_ext. all: eassumption.
Qed.

Lemma inline_crule_ext Σ rl κ κ' :
  gscope_crule Σ rl →
  eq_gscope Σ κ κ' →
  ⟦ rl ⟧r⟨ κ ⟩ = ⟦ rl ⟧r⟨ κ' ⟩.
Proof.
  intros [? [? []]] he.
  destruct rl as [Θ l r θ A].
  unfold inline_crule. cbn in *. f_equal.
  - eapply inline_list_ext. all: eassumption.
  - eapply inline_ext. all: eassumption.
  - eapply inline_ext. all: eassumption.
  - eapply inline_ext. all: eassumption.
Qed.

Lemma inline_crules_ext Σ R κ κ' :
  Forall (gscope_crule Σ) R →
  eq_gscope Σ κ κ' →
  ⟦ R ⟧R⟨ κ ⟩ = ⟦ R ⟧R⟨ κ' ⟩.
Proof.
  intros hR he.
  eapply map_ext_Forall. eapply Forall_impl. 2: eassumption.
  intros. eapply inline_crule_ext. all: eassumption.
Qed.

Lemma inline_ictx_ext Σ Ξ κ κ' :
  iwf Σ Ξ →
  eq_gscope Σ κ κ' →
  ⟦ Ξ ⟧e⟨ κ ⟩ = ⟦ Ξ ⟧e⟨ κ' ⟩.
Proof.
  intros hΞ he.
  eapply map_ext_Forall.
  induction hΞ as [| B Ξ i hΞ ih hB | rl Ξ hΞ ih hs ht ].
  - constructor.
  - constructor. 2: assumption.
    cbn. f_equal. eapply inline_ext. 2: eassumption.
    eapply typing_gscope. eassumption.
  - constructor. 2: assumption.
    cbn. f_equal. eapply inline_crule_ext. all: eassumption.
Qed.

Lemma inline_ctx_ext Σ Ξ Γ κ κ' :
  wf Σ Ξ Γ →
  eq_gscope Σ κ κ' →
  ⟦ Γ ⟧*⟨ κ ⟩ = ⟦ Γ ⟧*⟨ κ' ⟩.
Proof.
  intros hΓ he.
  eapply inline_list_ext. 2: eassumption.
  eapply wf_gscope. eassumption.
Qed.

Lemma eq_gscope_gcons (Σ : gctx) κ c u :
  Σ c = None →
  eq_gscope Σ κ (gcons c u κ).
Proof.
  intros h c' Ξ A t e.
  destruct (c' =? c)%string eqn:ec.
  1:{ rewrite String.eqb_eq in ec. congruence. }
  rewrite gcons_neq. 2: assumption.
  reflexivity.
Qed.

Lemma gwf_gclosed Σ :
  gwf Σ →
  gclosed ⟦ Σ ⟧κ.
Proof.
  intros h.
  induction h as [ | c' ??????? ih ].
  all: intros c.
  - cbn. reflexivity.
  - cbn. destruct (c =? c')%string eqn:ec.
    + rewrite gcons_eq. 2: assumption.
      eapply scoped_inline. 1: assumption.
      eapply typing_closed. eassumption.
    + rewrite gcons_neq. 2: assumption.
      eauto.
Qed.

Lemma gwf_conv_unfold Σ :
  gwf Σ →
  g_conv_unfold Σ ⟦ Σ ⟧κ.
Proof.
  intros h c Ξ' A t ec.
  apply meta_conv_refl.
  induction h as [ | c' ??????? ih ].
  - discriminate.
  - cbn in *. destruct (c =? c')%string eqn:e.
    + inversion ec. subst. clear ec.
      rewrite gcons_eq. 2: assumption.
      eapply inline_ext.
      all: eauto using eq_gscope_gcons, typing_gscope.
    + rewrite gcons_neq. 2: assumption.
      eapply valid_def in ec as h'. 2: assumption.
      destruct h' as (hΞ' & [j hB] & ht).
      erewrite <- inline_ext.
      2,3: eauto using eq_gscope_gcons, typing_gscope.
      eauto.
Qed.

Lemma gwf_type Σ :
  gwf Σ →
  g_type Σ ⟦ Σ ⟧κ.
Proof.
  intros h.
  induction h as [ | c' ??????? ih ].
  all: intros c Ξ' B u ec.
  - discriminate.
  - cbn in *. destruct (c =? c')%string eqn:e.
    + inversion ec. subst. clear ec.
      rewrite gcons_eq. 2: assumption.
      erewrite <- inline_ictx_ext. 2,3: eauto using eq_gscope_gcons.
      erewrite <- inline_ext with (t := B).
      2,3: eauto using eq_gscope_gcons, typing_gscope.
      eapply typing_inline with (Γ := ∙).
      * eapply gwf_gclosed. assumption.
      * eapply gwf_conv_unfold. assumption.
      * assumption.
      * assumption.
      * assumption.
    + rewrite gcons_neq. 2: assumption.
      eapply valid_def in ec as h'. 2: assumption.
      destruct h' as (hΞ' & [j hB] & ht).
      erewrite <- inline_ictx_ext. 2,3: eauto using eq_gscope_gcons.
      erewrite <- inline_ext with (t := B).
      2,3: eauto using eq_gscope_gcons, typing_gscope.
      eauto.
Qed.

Theorem inlining Ξ Σ Γ t A :
  gwf Σ →
  let κ := ⟦ Σ ⟧κ in
  Σ ;; Ξ | Γ ⊢ t : A →
  [] ;; ⟦ Ξ ⟧e⟨ κ ⟩ | ⟦ Γ ⟧*⟨ κ ⟩ ⊢ ⟦ t ⟧⟨ κ ⟩ : ⟦ A ⟧⟨ κ ⟩.
Proof.
  intros hΣ κ h.
  eapply typing_inline.
  - eapply gwf_gclosed. assumption.
  - eapply gwf_conv_unfold. assumption.
  - eapply gwf_type. assumption.
  - assumption.
  - assumption.
Qed.

(** Conservativity *)

Lemma inline_nil_id t κ :
  gscope [] t →
  ⟦ t ⟧⟨ κ ⟩ = t.
Proof.
  intros h. induction h using gscope_ind.
  all: try solve [ cbn ; f_equal ; eauto ].
  discriminate.
Qed.

Theorem conservativity Σ t A i :
  gwf Σ →
  [] ;; [] | ∙ ⊢ A : Sort i →
  Σ ;; [] | ∙ ⊢ t : A →
  let κ := ⟦ Σ ⟧κ in
  [] ;; [] | ∙ ⊢ ⟦ t ⟧⟨ κ ⟩ : A.
Proof.
  intros hΣ hA ht κ.
  eapply inlining in ht. 2: assumption.
  cbn in ht.
  eapply typing_gscope in hA as gA. eapply inline_nil_id in gA.
  rewrite gA in ht. eassumption.
Qed.


*)
