From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fuel map_included_utils utils action_model resources.


Section Steps.
  Context {AM1 AM2: ActionModel}.
  Let PM := ProdAM AM1 AM2.
  Context {PROD_LR: AM_strong_lr PM}. 
  Let M := AM2FM PM PROD_LR.

  Context `{Countable (locale Λ)}.
  Context `{LM: LiveModel Λ M}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS AM1 AM2 Σ}.

  Context {LR1: AM_strong_lr AM1} {LR2: AM_strong_lr AM2}.
  Context {INDEP: models_independent AM1 AM2}.
  Existing Instance LR1.
  Existing Instance LR2.

  (* OBS: Maybe use fuel limit instead of generic [f] *)
  Program Definition model_update_set (ζ : locale Λ) (ρ : fmrole M) (f : nat) (δ : LM) : LM :=
    {|
      ls_data :=
        {| ls_under := δ.(ls_under);
           ls_map := alter (alter (λ _, f) ρ) ζ δ.(ls_map); |};
    |}.
  Next Obligation.
    intros ζ ρ f δ ζ1 ζ2 fs1 fs2 Hneq HSome1 HSome2. simpl in *.
    pose proof (δ.(ls_map_disj)) as Hdisj.
    apply lookup_alter_Some in HSome1.
    apply lookup_alter_Some in HSome2.
    destruct HSome1 as [[-> [fs1' [HSome1 ->]]]|[_ HSome1]],
               HSome2 as [[-> [fs2' [HSome2 ->]]]|[_ HSome2]];
               [done| | |].
    - specialize (Hdisj ζ1 ζ2 _ _ Hneq HSome1 HSome2).
      rewrite map_disjoint_dom dom_alter_L.
      rewrite map_disjoint_dom in Hdisj. set_solver.
    - specialize (Hdisj ζ1 ζ2 _ _ Hneq HSome1 HSome2).
      rewrite map_disjoint_dom dom_alter_L.
      rewrite map_disjoint_dom in Hdisj. set_solver.
    - by eapply Hdisj.
  Qed.
  Next Obligation.
    intros ζ ρ f δ ρ' Hρ'. simpl in *.
    pose proof (δ.(ls_map_live)) as Hlive.
    apply Hlive in Hρ' as (ζ'&fs'&HSome&Hρ').
    destruct (decide (ζ = ζ')) as [<-|Hneq].
    - eexists ζ, _. rewrite lookup_alter HSome. split; [done|].
      by rewrite dom_alter_L.
    - eexists ζ', _. by rewrite lookup_alter_ne.
  Qed.

  Definition model_update_state (δ2 : M) (δ1 : LiveStateData Λ M) :
    LiveStateData Λ M :=
    {| ls_under := δ2;
      ls_map := δ1.(ls_map); |}.

  Lemma model_update_state_valid (δ2 : M) (δ1 : LM) :
    M.(live_roles) δ2 ⊆ M.(live_roles) δ1 →
    ∃ δ, (ls_data δ) = model_update_state δ2 δ1.
  Proof.
    intros Hle.
    assert (∀ ζ ζ' fs fs',
              ζ ≠ ζ' → (model_update_state δ2 δ1).(ls_map) !! ζ = Some fs →
              (model_update_state δ2 δ1).(ls_map) !! ζ' = Some fs' → fs ##ₘ fs') as Hdisj'.
    { intros. by eapply (δ1.(ls_map_disj)). }
    assert (∀ ρ, ρ ∈ M.(live_roles) (model_update_state δ2 δ1).(ls_under) →
                 ∃ ζ fs, (model_update_state δ2 δ1).(ls_map) !! ζ = Some fs ∧ ρ ∈ dom fs) as Hlive'.
    { pose proof (δ1.(ls_map_live)) as Hlive.
      intros.
      assert (ρ ∈ live_roles M δ1) as Hin by set_solver.
      apply Hlive in Hin as (?&?&?&?). eexists _, _. done. }
    exists
      {| ls_data := model_update_state δ2 δ1;
         ls_map_disj := Hdisj';
         ls_map_live := Hlive' |}.
    done.
  Qed.

  Definition model_update_model_step
          (ζ : locale Λ) (ρs : gset (fmrole M)) ρ (δ2 : M) (δ : LM) : M :=
    model_update_state δ2 $ model_update_set ζ ρ (LM.(lm_fl) δ2) $ model_update_decr ζ $ model_update_filter ζ ρs δ.

  Lemma model_update_model_step_valid (ζ : locale Λ) (ρs : gset (fmrole M)) ρ (s2 : M) (δ1:LM) :
    M.(live_roles) s2 ⊆ M.(live_roles) (ls_under δ1) →
    ∃ δ, (ls_data δ) = model_update_model_step ζ ρs ρ s2 δ1.
  Proof. intros. by apply model_update_state_valid. Qed.

  Lemma update_model' δ s s' :
    auth_model_is δ -∗ frag_model_is s ==∗
    auth_model_is (s', δ.2) ∗ frag_model_is s'.
  Proof. iApply update_model. Qed. 

  (* OBS: Need to make frag model abstract *)
  Lemma model_state_interp_model_step_update
    (* (ρ : fmrole M) *)
    (ρ : amRole AM1)
        (fs : gmap (fmrole M) nat) tp1 tp2
        (δ δ2 : LM) ζ σ1 σ2 (f1 : nat) (s1 s2: amSt AM1) a:
    inl ρ ∉ dom fs →
    AM_live_roles s2 ⊆ AM_live_roles s1 →
    locale_step (tp1, σ1) (Some ζ) (tp2, σ2) →
    (* fmtrans _ s1 (Some ρ) s2 → *)
    amTrans AM1 s1 (a, Some ρ) s2 ->
    (ls_data δ2) = model_update_model_step ζ ({[inl ρ]} ∪ dom fs) (inl ρ) (s2, (ls_under $ ls_data δ).2) δ →
    model_state_interp tp1 δ -∗
    has_fuels ζ ({[inl ρ := f1]} ∪ (S <$> fs)) -∗
    frag_model_is s1 ==∗
    model_state_interp tp2 δ2 ∗
    has_fuels ζ ({[inl ρ := LM.(lm_flm)]} ∪ fs) ∗
    frag_model_is s2.
  Proof.
    iIntros (Hfs Hlive Hstep Hmstep Hδ2) "Hm Hf Hs".
    iDestruct "Hm" as (fm Hfmle Hfmdead Htp) "(Hm & Hfm)".
    iDestruct (has_fuels_agree with "Hfm Hf") as %Hagree.
    iMod (has_fuels_update _ _ _ ({[inl ρ := lm_flm LM]} ∪ fs) with "Hfm Hf")
      as "[Hfm Hf]".
    iDestruct (model_agree with "Hm Hs") as %<-.
    iMod (update_model' _ _ s2 with "Hm Hs") as "[Hm Hs]".
    iModIntro. iFrame.
    rewrite Hδ2. iFrame.
    iPureIntro.
    split; [|split].
    - split; last first.
      { simpl.
        destruct Hfmle as [Hfmle Hdom].
        pose proof Hfmle as Hfmle'.
        rewrite /fuel_map_le /fuel_map_le_inner map_included_spec in Hfmle.
        pose proof Hagree as Hagree'.
        apply Hfmle in Hagree' as (fs'&HSome&Hfs').
        rewrite -(insert_id (ls_map δ) ζ fs'); [|done].
        rewrite !alter_insert.
        set_solver. }
      simpl.
      destruct Hfmle as [Hfmle Hdom].
      pose proof Hfmle as Hfmle'.
      rewrite /fuel_map_le /fuel_map_le_inner map_included_spec in Hfmle.
      pose proof Hagree as Hagree'.
      apply Hfmle in Hagree' as (fs'&HSome&Hfs').
      rewrite -(insert_id (ls_map δ) ζ fs'); [|done].
      rewrite !alter_insert.
      apply map_included_insert; [|done].
      assert ({[inl ρ := lm_flm LM]} ∪ fs =
              (alter (λ _ : nat, lm_flm LM) (inl ρ)
                     ((λ f : nat, f - 1) <$>
                                         (filter
                                            (λ ρf : fmrole M * nat, ρf.1 ∈ live_roles M δ ∨ ρf.1 ∈ {[inl ρ]} ∪ dom fs)
                                            ({[inl ρ := f1]} ∪ (S <$> fs)))))) as EQ.
      { rewrite -!insert_union_singleton_l.
        rewrite map_filter_insert. simpl.
        case_decide; [|set_solver].
        rewrite fmap_insert. rewrite alter_insert. f_equiv.
        rewrite map_filter_fmap.
        rewrite -map_fmap_compose.
        rewrite decr_succ_compose_id.
        rewrite map_fmap_id.
        rewrite map_filter_id; [done|].
        intros i x Hin. apply elem_of_dom_2 in Hin. set_solver. }
      rewrite EQ. 
      apply map_included_mono_strong; [set_solver..| |].
      { intros k x1 x2 y1 y2 Hx1 Hx2 Hy1 Hy2 HR.
        destruct (decide (k = inl ρ)) as [->|Hneq].
        - erewrite alter_insert_alt in Hy1; [|done].
          erewrite alter_insert_alt in Hy2; [|done].
          rewrite lookup_insert in Hy1.
          rewrite lookup_insert in Hy2. by simplify_eq.
        - rewrite lookup_alter_ne in Hy1; [|done].
          rewrite lookup_alter_ne in Hy2; [|done].
          by simplify_eq. }
      apply map_included_mono_strong; [set_solver..| |].
      { intros k x1 x2 y1 y2 Hx1 Hx2 Hy1 Hy2 HR.
        apply lookup_fmap_Some in Hy1 as (y1'&Hy1'&Hy1).
        apply lookup_fmap_Some in Hy2 as (y2'&Hy2'&Hy2).
        simplify_eq. lia. }
      apply map_included_filter; [set_solver..|].
      done.
    - apply elem_of_subseteq in Hlive.
      intros ρ' Hin.

      (* apply Hlive in Hin. *)
      simpl in Hin.
      assert (ρ' ∈ AM_live_roles (ls_under (ls_data δ))) as LIVE.
      { rewrite prod_indep_live_roles in Hin. 
        apply elem_of_union in Hin. 
        destruct (ls_under (ls_data δ)) as [? ?] eqn:ST. simpl in Hin.  
        rewrite prod_indep_live_roles.  
        rewrite !elem_of_map in Hin. destruct Hin as [(?&->&Hin)|(?&->&Hin)].
        + apply Hlive in Hin. rewrite ST in Hin. set_solver.
        + set_solver. }
      apply Hfmdead in LIVE as (ζ'&ρs&HSome&Hρ).
      destruct (decide (ζ = ζ')) as [<-|Hneq].
      * eexists ζ, _. rewrite lookup_insert. split; [done|]. by set_solver.
      * eexists ζ', _. rewrite lookup_insert_ne; [|done].
        split; [done|]. by set_solver.
        
    - rewrite /fuel_map_preserve_threadpool.
      intros ζ' Hζ'.
      apply locales_of_list_step_incl in Hstep.
      assert (ζ' ∉ locales_of_list tp1) as Hζ'' by set_solver.
      apply Htp in Hζ''.
      rewrite -not_elem_of_dom. rewrite -not_elem_of_dom in Hζ''.
      rewrite dom_insert_L.
      rewrite -(insert_id fm ζ ({[inl ρ := f1]} ∪ (S <$> fs))) in Hζ''; [|done].
      rewrite dom_insert_L in Hζ''.
      set_solver.
  Qed.

  Lemma model_step_suff_data_weak_alt (δ1 δ2 : LiveState Λ M) ρ
        (fs fs': gmap _ nat) ζ :
    fmtrans _ δ1 (Some ρ) δ2 →
    M.(live_roles) δ2 ⊆ M.(live_roles) δ1 →
    δ1.(ls_map) !! ζ = Some fs →
    δ2.(ls_map) = <[ζ := fs']> δ1.(ls_map) →
    ρ ∈ dom fs →
    fs' !! ρ = Some (LM.(lm_fl) (ls_under δ2)) →
    map_included (<) (delete ρ fs') fs →
    (dom fs ∖ dom fs' ∩ M.(live_roles) δ1 = ∅) →
    ls_trans LM.(lm_fl) δ1 (Take_step ρ ζ) δ2.
  Proof.
    intros Hstep Hlive Hfs Hfs' Hρ Hρ' Hlt Hlive'.
    assert (∃ (δ'':LiveState Λ M), δ''.(ls_data) =
          {| ls_under := ls_under δ2;
            ls_map := <[ζ := fs']> δ1.(ls_map) |} ∧
            ls_trans LM.(lm_fl) δ1 (Take_step ρ ζ) δ'') as (δ''&Heq&Htrans).
    { eapply (model_step_suff_data); try done.
      - rewrite map_included_spec in Hlt.
        intros ρ' f f' Hf' Hneq Hf.
        rewrite -(lookup_delete_ne _ ρ ρ') in Hf'; [|done].
        apply Hlt in Hf' as (?&?&?). by simplify_eq.
      - set_solver.
      - apply map_included_subseteq_inv in Hlt. set_solver.
      - apply map_included_subseteq_inv in Hlt. set_solver.
      - set_solver. }
    rewrite Heq -Hfs' in Htrans. by destruct δ2, ls_data.
  Qed.

  Definition model_can_model_step (δ1 : LM) (ζ : locale Λ) (ρ : fmrole M) (δ2 : LM) : Prop :=
    ∃ (fs fs' : gmap (fmrole M) nat),
      fmtrans _ δ1 (Some ρ) δ2 ∧
      M.(live_roles) δ2 ⊆ M.(live_roles) δ1 ∧
      δ1.(ls_map) !! ζ = Some fs ∧
      δ2.(ls_map) = <[ζ := fs']> δ1.(ls_map) ∧
      ρ ∈ dom fs ∧
      fs' !! ρ = Some (LM.(lm_fl) (ls_under δ2)) ∧
      map_included (<) (delete ρ fs') fs ∧
      (dom fs ∖ dom fs' ∩ M.(live_roles) δ1 = ∅).

  Lemma model_can_model_step_trans ζ ρ (δ δ' : LiveState Λ M) :
    model_can_model_step δ ζ ρ δ' → ls_trans (LM.(lm_fl)) δ (Take_step ρ ζ) δ'.
  Proof.
    destruct 1 as (?&?&?&?&?&?&?&?&?&?).
    by eapply model_step_suff_data_weak_alt.
  Qed.

  Lemma fmtrans_left s1 s2 s' a ρ
    (STEP1: amTrans AM1 s1 (a, Some ρ) s2):
    fmtrans M (s1, s') (Some $ inl ρ) (s2, s').
  Proof.
    simpl. econstructor. simpl.
    econstructor; [| done]. 
    intros ?. edestruct INDEP; eauto. eapply action_of_step; eauto.
  Qed.

  Lemma live_roles_preserved_left (s1 s2: amSt AM1) s'
    (LRP1: AM_live_roles s2 ⊆ AM_live_roles s1):
    live_roles M ((s2, s'): fmstate M) ⊆ live_roles M (s1, s').
  Proof.
    simpl. rewrite !prod_indep_live_roles.
    apply union_mono; [| done]. apply set_map_mono; done.
  Qed. 

  Lemma model_state_interp_can_model_step es (δ δ2 : LM) ζ (ρ: amRole AM1) f
        (fs : gmap (fmrole M) nat) (s1 s2 : amSt AM1) a:
    (* fmtrans _ s1 (Some ρ) s2 → *)
    amTrans AM1 s1 (a, Some ρ) s2 →
    (* M.(live_roles) s2 ⊆ M.(live_roles) s1 → *)
    AM_live_roles s2 ⊆ AM_live_roles s1 →
    inl ρ ∉ dom fs →
    (ls_data δ2) = model_update_model_step ζ ({[inl ρ]} ∪ dom fs) (inl ρ) (s2, (ls_under $ ls_data δ).2) δ →
    model_state_interp es δ -∗
    has_fuels ζ ({[inl ρ := f]} ∪ (S <$> fs)) -∗
    frag_model_is s1 -∗
    ⌜model_can_model_step δ ζ (inl ρ) δ2⌝.
  Proof.
    iIntros (Hstep Hle Hρ Hδ2) "Hm Hf Hδ".
    iDestruct "Hm" as (fm Hfmle Hfmdead Htp) "(Hm & Hfm)".
    iDestruct (model_agree with "Hm Hδ") as %<-.
    iDestruct (has_fuels_agree with "Hfm Hf") as %Hagree.
    iPureIntro.
    rewrite /fuel_map_le /fuel_map_le_inner map_included_spec in Hfmle.
    pose proof Hagree as Hagree'.
    apply Hfmle in Hagree as (fs'&Hζ&Hfs').
    assert (inl ρ ∈ dom fs') as Hρ'.
    { apply map_included_subseteq_inv in Hfs'. set_solver. }
    eexists _, _. repeat split; try done.
    - rewrite Hδ2. destruct (ls_under (ls_data δ)) as [? ?] eqn:ST. simpl.
      rewrite ST in Hstep.
      eapply fmtrans_left; eauto. 
    - rewrite Hδ2. destruct (ls_under (ls_data δ)) as [? ?] eqn:ST. simpl.
      rewrite ST in Hle. 
      by apply live_roles_preserved_left. 
    - rewrite Hδ2. simpl. rewrite -!alter_compose.
      rewrite -{1}(insert_id (ls_map δ) ζ fs'); [|done].
      rewrite alter_insert.
      f_equiv.
      done.
    - rewrite Hδ2. simpl. rewrite lookup_alter. rewrite lookup_fmap.
      apply elem_of_dom in Hρ' as [f' Heq].
      apply fmap_Some; eexists; split; last done.
      apply fmap_Some; eexists; split; last done.
      apply map_lookup_filter_Some_2; first done.
      right; set_solver.
    - rewrite map_included_spec.
      intros ρ' f' HSome.
      assert (inl ρ ≠ ρ').
      { intros Heq. rewrite Heq in HSome.
        by rewrite lookup_delete in HSome. }
      rewrite lookup_delete_ne in HSome; [|done].
      exists (f' + 1).
      split; [|lia].
      simpl in *.
      rewrite lookup_alter_ne in HSome; [|done].
      rewrite lookup_fmap in HSome.
      rewrite map_lookup_filter in HSome. simpl in *.
      destruct (fs' !! ρ') eqn:Heqn; [|done].
      simpl in *.
      destruct (decide (ρ' ∈ live_roles M δ ∨ ρ' ∈ {[inl ρ]} ∪ dom fs)) as [Hin|Hnin].
      + rewrite option_guard_True in HSome; [|done].
        simpl in *. simplify_eq. f_equiv.
        assert (ρ' ∈ dom ({[inl ρ := f]} ∪ (S <$> fs))) as Hin'.
        { destruct Hin as [Hin|Hin]; [|set_solver].
          eapply (fuel_map_le_live_roles _ δ.(ls_map)); [| |done..|].
          - intros ???????. by eapply δ.(ls_map_disj).
          - rewrite /fuel_map_le_inner map_included_spec. apply Hfmle.
          - by apply elem_of_dom. }
        rewrite dom_union_L in Hin'.
        apply elem_of_union in Hin' as [Hin'|Hin']; [set_solver|].
        apply elem_of_dom in Hin' as [v2 Hv2].
        rewrite map_included_spec in Hfs'.
        specialize (Hfs' ρ' v2).
        rewrite lookup_union_r in Hfs'; [|by rewrite lookup_insert_ne].
        destruct v2.
        { apply lookup_fmap_Some in Hv2 as (?&?&?). lia. }
        apply Hfs' in Hv2 as (n'&Hn'&Hn'').
        simplify_eq.
        lia.
      + by rewrite option_guard_False in HSome.
    - (* TODO: Make a lemma for this *)
      simpl.
      rewrite dom_alter_L.
      rewrite dom_fmap_L.
      clear.
      induction fs' using map_ind.
      { set_solver. }
      rewrite /filter_fuel_map.
      rewrite map_filter_insert. simpl.
      case_decide.
      + set_solver.
      + rewrite -dom_difference_L.
        rewrite map_filter_delete.
        rewrite -insert_difference.
        set_solver.
  Qed.

  Lemma model_update_locale_spec_model_step extr
        (auxtr : auxiliary_trace LM) ζ c2 ρs ρ δ2 s2 :
    (ls_data δ2) = model_update_model_step ζ ({[ρ]} ∪ ρs) ρ s2
                                           (trace_last auxtr) →
    model_can_model_step (trace_last auxtr) ζ ρ δ2 →
    tids_smaller c2.1 δ2 →
    valid_state_evolution_fairness
      (extr :tr[Some ζ]: c2)
      (auxtr :tr[Take_step ρ ζ]: δ2).
  Proof.
    intros Hstep Htids. destruct c2.
    split; [done|]. split; [by apply model_can_model_step_trans|done].
  Qed.

  Lemma update_model_step
        (extr : execution_trace Λ)
        (auxtr: auxiliary_trace LM) c2 (s1 s2 : amSt AM1) fs 
        (ρ: amRole AM1) (δ1 : LM) ζ f a:
    (* M.(live_roles) s2 ⊆ M.(live_roles) s1 → *)
    AM_live_roles s2 ⊆ AM_live_roles s1 →
    inl ρ ∉ dom fs →
    trace_last auxtr = δ1 →
    locale_step (trace_last extr) (Some ζ) c2 →
    (* fmtrans _ s1 (Some ρ) s2 → *)
    amTrans AM1 s1 (a, Some ρ) s2 →
    has_fuels ζ ({[inl ρ := f]} ∪ (S <$> fs)) -∗ frag_model_is s1 -∗
    model_state_interp (trace_last extr).1 δ1 ==∗
    ∃ (δ2: LM),
      ⌜valid_state_evolution_fairness
        (extr :tr[Some ζ]: c2) (auxtr :tr[ Take_step (inl ρ) ζ]: δ2)⌝ ∗
      has_fuels ζ ({[inl ρ := LM.(lm_flm)]} ∪ fs) ∗
      frag_model_is s2 ∗ model_state_interp c2.1 δ2.
  Proof.
    iIntros (Hlive Hdom Hlast Hstep Htrans) "Hfuel Hfrag Hm".
    iDestruct (model_agree' with "Hm Hfrag") as %<-.
    pose proof (model_update_model_step_valid
                  ζ ({[inl ρ]} ∪ dom fs) (inl ρ) (s2, (ls_under $ ls_data δ1).2) δ1) as [δ2 Hδ2].
    { destruct (ls_under (ls_data δ1)) as [? ?] eqn:ST. simpl.
      rewrite ST in Hlive. 
      by apply live_roles_preserved_left. } 
    iExists δ2.
    iDestruct (model_state_interp_can_model_step with "Hm Hfuel Hfrag")
      as %Hcan_step; [try done..|].
    destruct (trace_last extr), c2.
    iMod (model_state_interp_model_step_update with "Hm Hfuel Hfrag")
      as "(Hm&Hf&Hfrag)"; [done..|].
    iDestruct (model_state_interp_tids_smaller with "Hm") as %Htids.
    iModIntro.
    iFrame "Hm Hf Hfrag".
    iPureIntro. subst.
    by eapply model_update_locale_spec_model_step.
  Qed.

End Steps.
