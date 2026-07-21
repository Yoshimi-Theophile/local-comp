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

    | ⊥ => tt
    | eqT _ _ => tt
    | reflT _ => tt
    | transportT _ _ _ _ _ => tt
                   
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
    - rasimpl. simpl.
      destruct s0.
      1: reflexivity.
      destruct s.
      all: rasimpl.
      + admit.
      + admit.
  Admitted.
    
  Lemma tl_subst_ignore Γ t A i σ τ :
    swf Γ →
    Γ ⊢ t : A →
    Γ ⊢ A : PTyp i →
    (forall x, scoping (sc Γ) (var x) S_PTyp → σ x = τ x) → 
    [sc Γ | t] <[ σ ] = [sc Γ | t] <[ τ ].
  Proof.
    intros hΓ h1 h2 h.
    induction h1 using styping_ind in i, σ, τ, hΓ, h2, h |- *.
    all: try solve [reflexivity].
    - simpl. unfold isPTyp, sc.
      rewrite nth_error_map, H. simpl.
      destruct s.
      1: reflexivity.
      apply h.
      constructor. unfold sc.
      now rewrite nth_error_map, H.
    - destruct s; reflexivity.
    - simpl.
      destruct s'.
      1: reflexivity. (* impossible case *)
      destruct s.
      + simpl in IHh1_2. simpl.
        f_equal.
        apply IHh1_2 with (i := S j).
        1, 2: econstructor; eassumption.
        intros x hx.
        destruct x.
        * reflexivity.
        * apply (ap (ren_term shift)), h.
          inversion hx; subst.
          simpl in H0.
          now constructor.
      + simpl in *. simpl.
        rewrite IHh1_1 with (i := S i0) (τ := τ).
        2, 4: assumption.
        2: constructor.
        f_equal.
        apply IHh1_2 with (i := S j).
        1, 2: econstructor; eassumption.
        intros x hx.
        destruct x.
        * reflexivity.
        * apply (ap (ren_term shift)), h.
          inversion hx; subst.
          simpl in H0.
          now constructor.
    - simpl.
      destruct s'.
      1: reflexivity. (* impossible case *)
      destruct s.
      + simpl.
        f_equal.
        simpl in IHh1_3.
        apply IHh1_3 with (i := j).
        1: econstructor; eassumption.
        1: eauto.
        intros x hx.
        destruct x.
        * reflexivity.
        * apply (ap (ren_term shift)), h.
          inversion hx; subst.
          simpl in H0.
          now constructor.
      + simpl in *. simpl.
        rewrite IHh1_1 with (i := S i0) (τ := τ).
        2, 4: assumption.
        2: constructor.
        f_equal.
        apply IHh1_3 with (i := j).
        1: econstructor; eassumption.
        1: eauto.
        intros x hx.
        destruct x.
        * reflexivity.
        * apply (ap (ren_term shift)), h.
          inversion hx; subst.
          simpl in H0.
          now constructor.
    - simpl.
      destruct s'.
      1: reflexivity. (* impossible case *)
      destruct s.
      + simpl.
        f_equal.
        apply IHh1_1 with (i := max i0 j).
        1, 3: assumption.
        1: constructor; assumption.
      + simpl in *. simpl.
        rewrite IHh1_1 with (i := max i0 j) (τ := τ).
        2, 4: assumption.
        2: constructor; assumption.
        f_equal.
        now apply IHh1_2 with (i := i0).
    - apply IHh1_1 with (i := i).
      1, 3: assumption.
      clear h1_2. clear IHh1_2.
      destruct (svalidity _ _ _ hΓ h1_1) as [h0 [i' h1]].
      destruct (stype_sort_conv _ _ _ _ _ _ _ h1 h2 H) as [<- ->].
      assumption.
  Qed.
    
  Lemma tl_subst_Typ Γ A B u v i j :
    swf Γ →
    Γ ⊢ A : Typ i → 
    Γ,,s (S_Typ, A) ⊢ B : PTyp j →
    [sc (Γ,,s (S_Typ, A)) | B] <[ u.. ] =
    [sc (Γ,,s (S_Typ, A)) | B] <[ v.. ].
  Proof.
    intros hΓ hA hB.
    apply tl_subst_ignore with (A := PTyp j) (i := S j).
    1, 3: econstructor; eassumption.
    1: assumption.
    intros x hx.
    destruct x.
    - apply scoping_st in hx.
      simpl in hx; discriminate.
    - reflexivity.
  Qed.

  Lemma tl_conv Γ u v A :
    swf Γ →
    Γ ⊢ u : A →
    Γ ⊢ v : A →
    u ≡ v →
    scoping (sc Γ) u S_PTyp →
    [ sc Γ | u ] ≡ [ sc Γ | v ].
  Proof.
    intros hΓ hu hv h hP.
    induction h in Γ, A, hu, hv, hΓ, hP |- *.
    all: try solve [constructor].
    - simpl. destruct s'.
      1: apply scoping_st in hP; discriminate.
      destruct s.
      + eapply conv_trans.
        1: eapply conv_beta.
        rewrite tl_subst with (Δ := S_Typ :: sc Γ).
        2: { apply σscoping_one. now inversion hP; subst. }
        2: apply σscoping_comp_one.
        2: { inversion hP; subst.
             inversion H1; subst.
             eapply scoping_subst.
             2: eassumption.
             now apply σscoping_one.
        }
        admit.
      + eapply conv_trans.
        1: eapply conv_beta.
        rewrite tl_subst with (Δ := S_PTyp :: sc Γ).
        2: { apply σscoping_one. now inversion hP; subst. }
        2: apply σscoping_comp_one.
        2: { inversion hP; subst.
             inversion H1; subst.
             eapply scoping_subst.
             2: eassumption.
             now apply σscoping_one.
        }
        admit.
    - simpl. destruct s'.
      1: constructor.
      destruct s.
      + constructor.
        1: constructor.
        change (S_Typ :: sc Γ) with (sc (Γ,,s (S_Typ, A0))).
        apply IHh2 with (A := PTyp j).
        * apply swf_cons with (i := i).
          1: assumption.
          admit.
        * admit.
        * admit.
        * admit.
      + admit.
    - simpl. destruct s'.
      1: constructor.
      destruct s.
      + constructor.
        1: constructor.
        admit.
      + admit.
    - simpl. destruct s'.
      1: constructor.
      destruct s.
      + constructor.
        2: constructor.
        admit.
      + constructor.
        all: admit.
    - apply conv_sym.
      apply IHh with (A := A).
      1-3: assumption.
      admit.
    - admit.
  Admitted.

  (* main lemma for first translation *)
  
  Lemma tl_typP Γ t A :
    swf Γ →
    Γ ⊢ t : A →
    scoping (sc Γ) t S_PTyp → 
    [ Γ ]c ⊨ [sc Γ | t ] : [ sc Γ | A ].
  Proof.
    intros hΓ h hP.
    induction h using styping_ind in hΓ, hP |- *.
    all: try solve [apply scoping_st in hP; discriminate].
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
            change (S_Typ :: sc Γ) with (sc (Γ,,s (S_Typ, A))).
            eapply tl_subst_ignore.
            2: eassumption.
            1, 2: econstructor; eassumption.
            intros x hx.
            destruct x.
            1: reflexivity.
            change ((u .. >> tl_tmP (sc Γ)) (S x)) with [sc Γ | var x ].
            simpl. inversion hx; subst.
            simpl in H0.
            unfold isPTyp. rewrite H0.
            reflexivity.
          }
          assert ([S_Typ :: sc Γ | B] <[ [sc Γ | u]..] = [S_Typ :: sc Γ | B] <[ tt..]).
          {
            change (S_Typ :: sc Γ) with (sc (Γ,,s (S_Typ, A))).
            eapply tl_subst_Typ; eassumption.
          }
          rewrite H.
          eapply ttype_app.
          2, 3: econstructor.
          -- eapply IHh1.
             1: assumption.
             change S_PTyp with (stc Γ (Pi_TP i j A B)).
             now apply styping_scoping_stc.
          -- apply IHh4.
             1: econstructor; eassumption.
             change S_PTyp with (stc (Γ,,s (S_Typ, A)) (PTyp j)).
             change (S_Typ :: sc Γ) with (sc (Γ,,s (S_Typ, A))).
             apply styping_scoping_stc.
             1: econstructor; eassumption.
             assumption.
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
        * assert
            ([S_PTyp :: sc Γ | B] <[ u.. >> tl_tmP (sc Γ)] =
             [S_PTyp :: sc Γ | B] <[ [ sc Γ | u].. ]) as ->.
          {
            change (S_PTyp :: sc Γ) with (sc (Γ,,s (S_PTyp, A))).
            eapply tl_subst_ignore.
            2: eassumption.
            1, 2: econstructor; eassumption.
            intros x hx.
            destruct x.
            1: reflexivity.
            change ((u .. >> tl_tmP (sc Γ)) (S x)) with [sc Γ | var x ].
            simpl. inversion hx; subst.
            simpl in H0.
            unfold isPTyp. rewrite H0.
            reflexivity.
          }
          apply (ttype_app _ i j [sc Γ | A]).
          -- apply IHh1.
             1: assumption.
             change S_PTyp with (stc Γ (Pi_P i j A B)).
             now apply styping_scoping_stc.
          -- apply IHh2.
             1: assumption.
             change S_PTyp with (stc Γ (PTyp i)).
             rewrite <-(styping_stc _ _ _ hΓ h3).
             now apply styping_scoping_stc.
          -- apply IHh3.
             1: assumption.
             change S_PTyp with (stc Γ (PTyp i)).
             now apply styping_scoping_stc.
          -- apply IHh4.
             1: econstructor; eassumption.
             change S_PTyp with (stc (Γ,,s (S_PTyp, A)) (PTyp j)) at 2.
             change (S_PTyp :: sc Γ) with (sc (Γ,,s (S_PTyp, A))).
             apply styping_scoping_stc.
             1: econstructor; eassumption.
             assumption.
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
      + apply tl_conv with (A := Sort s i).
        all: try assumption.
        * destruct (svalidity _ _ _ hΓ h1) as [_ [i' H0]].
          destruct (stype_sort_conv _ _ _ _ _ _ _ H0 h2 H) as [<- ->].
          assumption.
        * rewrite <-hP.
          now apply styping_scoping_stc_bw.
      + rewrite (styping_stc _ _ _ hΓ (stype_conv _ _ _ _ _ _ h1 H h2)) in hP.
        rewrite (styping_stc _ _ _ hΓ h2) in hP.
        simpl in hP; subst.
        simpl in IHh2.
        apply IHh2.
        1: assumption.
        change (S_PTyp) with (stc Γ (PTyp i)).
        now apply styping_scoping_stc.
  Qed.

  (*
  Lemma tl_unit_tt Γ u :
    scoping Γ u S_Typ →
    [Γ | u] = tt ∨ [Γ | u] = unit.
  Proof.
    intros h.
    inversion h; subst.
    all: try solve [firstorder].
    simpl; unfold isPTyp.
    rewrite H.
    firstorder.
  Qed.
   *)
  
  Reserved Notation "⟦ Γ | t ⟧" (at level 0).
  Reserved Notation "⟦ Γ ⟧c" (at level 0).

  Print ttyping.
  
  
  Fixpoint Tl_tm (Γ : scope) (t : term) : term :=
    match t with
    | var x =>
        if (isPTyp Γ x) then (pi2 (var x)) else var x

    | Sort s i =>

        match s with
        | S_Typ => Typ i
        | S_PTyp =>
            lam_T
              [Γ | t] (*(Typ i)*)
              (Pi_T i (S i) (var 0) (Typ i))
        end

    | Pi s s' i j A B =>

        match s, s' with
        | S_Typ, S_Typ =>
            Pi_T i j ⟦Γ | A⟧ ⟦Γ | B⟧
        | S_PTyp, S_Typ =>
            Pi_T i j (Sigma [Γ | A] ⟦Γ | A⟧) ⟦Γ | B⟧
        | S_PTyp, S_PTyp =>
            lam_T
              [Γ | t]
              (Pi_T i j
                 (Sigma [Γ | A] ⟦Γ | A⟧)
                 (app_T ⟦Γ | B⟧ (app_T (var 1) (pi1 (var 0)))))
        | S_Typ, S_PTyp =>
            lam_T
              [Γ | t]
              (Pi_T i j
                 ⟦Γ | A⟧
                 (app_T ⟦Γ | B⟧ (app_T (var 1) (var 0))))
        end

    | lam s s' A t =>
        match s with
        | S_Typ => lam_T ⟦Γ | A⟧ ⟦Γ | t⟧
        | S_PTyp => lam_T (Sigma [Γ | A] ⟦Γ | A⟧) ⟦Γ | t⟧
        end

    | app s s' t u =>
        match s with
        | S_Typ => app_T ⟦Γ | t⟧ ⟦Γ | u⟧
        | S_PTyp => app_T ⟦Γ | t⟧ (sig [Γ | u] ⟦Γ | u⟧)
        end

    | ⊥ => ⊥

    | eqT u v => eqT ⟦Γ | u⟧ ⟦Γ | v⟧

    | reflT u => reflT ⟦Γ | u⟧

    | transportT P u v e pu =>
        transportT ⟦Γ | P⟧ ⟦Γ | u⟧ ⟦Γ | v⟧ ⟦Γ | e⟧ ⟦Γ | pu⟧

    | _ => unit (* inaccessible in styping *)
    end
  where "⟦ Γ | t ⟧" := (Tl_tm Γ t).

  Fixpoint Tl_ctx (Γ : sctx) : tctx :=
    match Γ with
    | nil => ∙t
    | cons (S_Typ, A) Γ => ⟦Γ⟧c ,,t ⟦sc Γ | A⟧
    | cons (S_PTyp, A) Γ => ⟦Γ⟧c ,,t (Sigma [sc Γ | A] ⟦sc Γ | A⟧)
    end
  where "⟦ Γ ⟧c" := (Tl_ctx Γ).

  Definition isPTyp_sc Γ t :=
    match st Γ t with
    | S_PTyp => true
    | S_Typ => false
    end.

  Definition Tl_rhs Γ A t :=
    if isPTyp_sc Γ t
    then app_T ⟦Γ | A⟧ [Γ | t]
    else ⟦Γ | A⟧.

  Lemma isPTyp_sc_isPTyp Γ x :
    isPTyp_sc Γ (var x) = isPTyp Γ x.
  Proof.
    unfold isPTyp_sc.
    unfold isPTyp. simpl.
    rewrite nth_nth_error.
    now destruct (nth_error Γ x).
  Qed.

  (* TODO: Tl_rhs isn't quite right *)
  
  Lemma Tl_typ Γ t A :
    swf Γ →
    Γ ⊢ t : A →
    ⟦ Γ ⟧c ⊨ ⟦sc Γ | t⟧ : Tl_rhs (sc Γ) A t.
  Proof.
    intros hΓ h.
    induction h using styping_ind in hΓ |- *.
    - unfold Tl_rhs. simpl.
      rewrite isPTyp_sc_isPTyp.
      destruct (isPTyp (sc Γ) x) eqn: e.
      + Check ttype_pi2.
  Admitted.

  
    
End Translation.
