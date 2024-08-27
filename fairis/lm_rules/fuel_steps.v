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

  Lemma model_state_interp_has_fuels_dealloc tid fs ρ tp (δ: amSt AM1) δ':
    ρ ∉ AM_live_roles δ →
    model_state_interp tp δ' -∗
    frag_model_is δ -∗
    has_fuels tid fs ==∗
    model_state_interp tp δ' ∗ frag_model_is δ ∗ has_fuels tid (delete (inl ρ) fs).
  Proof.
    intros Hρ.
    destruct (decide (inl ρ ∈ dom fs)) as [Hin|Hnin]; last first.
    { assert (delete (inl ρ) fs = fs) as ->.
      { apply delete_notin. by rewrite -not_elem_of_dom. }
      by iIntros "$$$". }
    iDestruct 1 as
      (fm [Hfmle Hdom] Hfmdead Htp) "(Hm & Hfm)".
    iIntros "Hst Hfs". 
    iDestruct (model_agree with "Hm Hst") as %Heq.
    Set Printing Coercions.
    destruct (ls_under (ls_data δ')) as [s1 s'] eqn:ST. simpl in Heq.  subst. 
    (* rewrite !Heq. *)
    assert (is_Some (fs !! inl ρ)) as [f HSome].
    { by rewrite -elem_of_dom. }
    iDestruct (has_fuels_agree with "Hfm Hfs") as %Hagree.
    iMod (has_fuels_delete with "Hfm Hfs") as "[Hfm Hfs]".
    iModIntro.
    iFrame "Hst". iFrame "Hfs".
    iExists _. iFrame. rewrite ST. iFrame.
    iPureIntro.
    repeat split; try done.
    - rewrite /fuel_map_le.
      eapply map_included_transitivity; [|done].
      rewrite -{2}(insert_id fm tid fs); [|done].
      apply map_included_insert; [|apply map_included_refl].
      eapply map_included_subseteq; [|done].
      apply delete_subseteq.
    - rewrite dom_insert_L.
      assert (tid ∈ dom fm).
      { by apply elem_of_dom. }
      set_solver.
    - rewrite /fuel_map_preserve_dead.
      intros ρ' Hρ'.
      assert (inl ρ ≠ ρ').
      { intros <-. 
        simpl in Hρ'. rewrite prod_indep_live_roles in Hρ'; [ | by eauto]. 
        apply elem_of_union in Hρ' as [IN | ?]; [| set_solver].
        apply elem_of_map_inj_gset in IN; [| apply _].
        done. }
      rewrite /fuel_map_preserve_dead in Hfmdead.
      (* rewrite Heq in Hfmdead. *)
      apply Hfmdead in Hρ' as (ζ&ρs&HSome'&Hρs).
      destruct (decide (tid = ζ)) as [->|Hneq].
      + exists ζ, (delete (inl ρ) fs).
        rewrite lookup_insert. set_solver.
      + exists ζ, ρs. rewrite lookup_insert_ne; [|done].
        set_solver.
    - intros ζ Hζ. specialize (Htp ζ Hζ).
      rewrite -not_elem_of_dom.
      rewrite -not_elem_of_dom in Htp.
      assert (ζ ≠ tid).
      { intros ->.
        assert (tid ∈ dom fm).
        { rewrite elem_of_dom. by set_solver. }
        set_solver. }
      set_solver.
  Qed.

  (* TODO: Move this *)
  Lemma silent_step_suff_data_weak fl `(δ: LiveState Λ M)
        (fs fs' : gmap _ nat) ζ :
    δ.(ls_map) !! ζ = Some fs →
    fs ≠ ∅ →
    map_included (<) fs' fs →
    (dom fs ∖ dom fs') ∩ M.(live_roles) δ = ∅ →
    ∃ δ', δ'.(ls_data) =
          {| ls_under := δ;
            ls_map := <[ζ := fs']> δ.(ls_map) |} ∧
            ls_trans fl δ (Silent_step ζ) δ'.
  Proof.
    intros.
    apply (silent_step_suff_data fl δ fs fs' ∅ ζ None); try done.
    - rewrite map_included_spec in H2. done.
    - set_solver.
    - set_solver.
  Qed.

  (* TODO: Change original lemma to not existentially quantify new state *)
  Lemma silent_step_suff_data_weak_alt fl (δ δ' : LiveState Λ M)
        (fs fs' : gmap _ nat) ζ :
    δ.(ls_under) = δ'.(ls_under) →
    δ.(ls_map) !! ζ = Some fs →
    δ'.(ls_map) = <[ζ := fs']>δ.(ls_map) →
    fs ≠ ∅ →
    map_included (<) fs' fs →
    (dom fs ∖ dom fs') ∩ M.(live_roles) δ = ∅ →
    ls_trans fl δ (Silent_step ζ) δ'.
  Proof.
    rewrite map_included_spec. intros Hδ Hfs Hfs' Hne Hle Hlive.
    assert (∃ δ', δ'.(ls_data) =
          {| ls_under := δ;
            ls_map := <[ζ := fs']> δ.(ls_map) |} ∧
            ls_trans fl δ (Silent_step ζ) δ') as (δ''&Heq&Htrans).
    { apply (silent_step_suff_data fl δ fs fs' ∅ ζ None); try set_solver. }
    rewrite Heq Hδ -Hfs' in Htrans. by destruct δ', ls_data.
  Qed.

  Definition model_can_fuel_step (δ1 : LM) (ζ : locale Λ) (δ2 : LM) : Prop :=
    ∃ fs1 fs2,
      δ1.(ls_under) = δ2.(ls_under) ∧
      δ1.(ls_map) !! ζ = Some fs1 ∧
      δ2.(ls_map) = <[ζ := fs2]>δ1.(ls_map) ∧
      fs1 ≠ ∅ ∧
      map_included (<) fs2 fs1 ∧
      (dom fs1 ∖ dom fs2) ∩ M.(live_roles) δ1 = ∅.

  Lemma model_can_fuel_step_trans fl ζ (δ δ' : LiveState Λ M) :
    model_can_fuel_step δ ζ δ' → ls_trans fl δ (Silent_step ζ) δ'.
  Proof.
    destruct 1 as (?&?&?&?&?&?&?&?). by eapply silent_step_suff_data_weak_alt.
  Qed.

  Definition model_update_locale_role_map
          δ (ρs : gset (fmrole M)) : gmap (fmrole M) nat → gmap (fmrole M) nat :=
    decr_fuel_map ∘ filter_fuel_map δ ρs.

  Lemma model_update_locale_role_map_map_included δ ρs fs :
    map_included (≤) (model_update_locale_role_map δ ρs fs) fs.
  Proof.
    rewrite /model_update_locale_role_map.
    eapply map_included_transitivity;
      [eapply decr_fuel_map_included|eapply filter_fuel_map_included].
  Qed.

  Definition model_update_locale_fuel_map
          δ (ζ : locale Λ) (ρs : gset (fmrole M))
          (fm : gmap (locale Λ) (gmap (fmrole M) nat)) :
      gmap (locale Λ) (gmap (fmrole M) nat) :=
    <[ζ:= model_update_locale_role_map δ ρs (fm !!! ζ)]>fm.

  Definition model_update_locale_fuel
             (δ : LM) (ζ : locale Λ) (ρs : gset (fmrole M)) : LM :=
    model_update_decr ζ $ model_update_filter ζ ρs δ.

  Lemma model_update_locale_spec extr (auxtr : auxiliary_trace LM) ζ c2 ρs:
    model_can_fuel_step (trace_last auxtr) ζ ((model_update_locale_fuel (trace_last auxtr) ζ) ρs) →
    tids_smaller c2.1 (model_update_locale_fuel (trace_last auxtr) ζ ρs) →
    valid_state_evolution_fairness
      (extr :tr[Some ζ]: c2)
      (auxtr :tr[Silent_step ζ]:
          (model_update_locale_fuel (trace_last auxtr) ζ) ρs).
  Proof.
    intros Hstep Htids. destruct c2.
    split; [done|]. split; [by apply model_can_fuel_step_trans|done].
  Qed.

  Definition map_disj (m : gmap (locale Λ) (gmap (fmrole M) nat)) :=
    ∀ ζ ζ' fs fs', ζ ≠ ζ' → m !! ζ = Some fs → m !! ζ' = Some fs' → fs ##ₘ fs'.

  Lemma fuel_map_le_disj ζ1 ζ2 fm fs1 fs2 ρ
        (fuel_map : gmap (locale Λ) (gmap (fmrole M) nat)) :
    fuel_map_le_inner fm fuel_map → map_inner_disj fuel_map →
    fm !! ζ1 = Some fs1 → fm !! ζ2 = Some fs2 →
    ρ ∈ dom fs1 → ρ ∈ dom fs2 →
    ζ1 = ζ2 ∧ fs1 = fs2.
  Proof.
    intros Hle Hdisj HSome1 HSome2 [f1 Hf1]%elem_of_dom [f2 Hf2]%elem_of_dom.
    destruct (decide (ζ1 = ζ2)) as [->|Hneq].
    { simplify_eq. set_solver. }
    rewrite /fuel_map_le_inner map_included_spec in Hle.
    apply Hle in HSome1 as (fs1'&Hfs1'&Hle1).
    apply Hle in HSome2 as (fs2'&Hfs2'&Hle2).
    assert (ρ ∈ dom fs1') as [??]%elem_of_dom.
    { apply elem_of_dom. rewrite map_included_spec in Hle1.
      by apply Hle1 in Hf1 as (?&?&?). }
    assert (ρ ∈ dom fs2') as [??]%elem_of_dom.
    { apply elem_of_dom. rewrite map_included_spec in Hle2.
      by apply Hle2 in Hf2 as (?&?&?). }
    exfalso. rewrite /map_inner_disj in Hdisj.
    specialize (Hdisj ζ1 ζ2 fs1' fs2' Hneq Hfs1' Hfs2').
    rewrite map_disjoint_spec in Hdisj. by eapply Hdisj.
  Qed.

  Lemma model_state_interp_can_fuel_step es δ ζ fs :
    fs ≠ ∅ → model_state_interp es δ -∗ has_fuels_S ζ fs -∗
    ⌜model_can_fuel_step δ ζ ((model_update_locale_fuel δ ζ) (dom fs))⌝.
  Proof.
    iIntros (Hfs) "Hm Hfs".
    iDestruct "Hm" as (fm Hfmle Hfmdead Htp) "(Hm & Hfm)".
    rewrite /model_can_fuel_step.
    iDestruct (has_fuels_agree with "Hfm Hfs") as %Hagree.
    rewrite /fuel_map_le /fuel_map_le_inner map_included_spec in Hfmle.
    pose proof Hagree as Hagree'.
    apply Hfmle in Hagree as [v2 [HSome Hle]].
    iPureIntro.
    exists v2. exists (model_update_locale_role_map δ (dom fs) v2).
    repeat split; try done.
    - simpl. rewrite -alter_compose.
      rewrite -alter_insert. f_equiv; [done|by rewrite insert_id].
    - assert (dom fs ⊆ dom v2).
      { erewrite <-dom_fmap_L. by eapply map_included_subseteq_inv. }
      rewrite -dom_empty_iff_L.
      rewrite -dom_empty_iff_L in Hfs.
      set_solver.
    - clear Htp Hfs. pose proof δ.(ls_map_disj) as Hdisj.
      apply map_included_spec.
      rewrite map_included_spec in Hle.
      intros k v1 Hv2.
      rewrite /model_update_locale_role_map lookup_fmap in Hv2.
      apply fmap_Some in Hv2 as [? [Hv2 ->]].
      pose proof Hv2 as Hv2'%map_lookup_filter_Some_1_2.
      apply map_lookup_filter_Some_1_1 in Hv2.
      assert (k ∈ dom fs) as Hv2''.
      { destruct Hv2' as [Hv2'|Hv2']; [|done].
        rewrite -(dom_fmap_L S fs).
        eapply (fuel_map_le_live_roles _ δ.(ls_map)); [| |done..|].
        - intros ???????. eapply Hdisj; try done.
        - rewrite /fuel_map_le_inner map_included_spec. apply Hfmle.
        - by apply elem_of_dom. }
      rewrite -(dom_fmap_L S) in Hv2''.
      apply elem_of_dom in Hv2'' as [f Heq].
      pose proof Heq as Heq'.
      apply lookup_fmap_Some in Heq' as [f' [<- _]].
      apply Hle in Heq as [f'' [Heq Hle']].
      exists f''. split; [done|].
      destruct f''; [lia|].
      simplify_eq.

      (* lia. *)
      simpl in *. rewrite Hv2 in Heq. inversion Heq. lia.  
    - rewrite /model_update_locale_role_map.
      simpl.
      rewrite dom_fmap_L.
      clear.
      induction v2 using map_ind.
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

  Lemma fuel_map_le_fuel_step fm ζ fs (δ:LM) :
    fm !! ζ = Some (S <$> fs) →
    fuel_map_le fm (ls_map δ) →
    fuel_map_le (<[ζ:=fs]> fm) (ls_map (model_update_locale_fuel δ ζ (dom fs))).
  Proof.
    intros Hagree [Hfmle Hfmdom].
    split; [|by apply elem_of_dom_2 in Hagree; set_solver].
    rewrite /model_update_locale_fuel=> /=.
    pose proof Hfmle as Hfmle'. rewrite /fuel_map_le_inner map_included_spec in Hfmle'.
    apply Hfmle' in Hagree as [ρs [HSome Hρs]].
    rewrite -(insert_id (ls_map δ) ζ ρs); [|done].
    rewrite -alter_compose alter_insert=> /=.
    apply map_included_insert; [|done].
    (* OBS: The remaining proof can likely be decomposed into library lemmas *)
    clear Hfmle Hfmle' HSome Hfmdom.
    apply map_included_spec.
    intros ρ f1 Hρ.
    rewrite map_included_spec in Hρs.
    assert ((S <$> fs) !! ρ = Some (S f1)) as Hρ'; [by rewrite lookup_fmap Hρ|].
    specialize (Hρs ρ (S f1) Hρ') as [v2 [Hv2 Hle]].
    destruct v2; [lia|]. exists v2. split; [|lia].
    rewrite !lookup_fmap.
    erewrite map_lookup_filter_Some_2; [|done|]; first by simpl; f_equal; lia.
    simpl.
    destruct (decide (ρ ∈ live_roles M δ ∨ ρ ∈ dom fs))
      as [Hin|Hnin]; first done.
    apply Decidable.not_or in Hnin. destruct Hnin as [Hnin1 Hnin2].
    apply not_elem_of_dom in Hnin2. set_solver.
  Qed.

  Lemma fuel_map_preserve_dead_fuel_step fm ζ fs (δ:LM) :
    fm !! ζ = Some (S <$> fs) →
    fuel_map_preserve_dead fm
      (M.(live_roles) $ model_update_locale_fuel δ ζ (dom fs)) →
    fuel_map_preserve_dead (<[ζ:=fs]> fm)
      (M.(live_roles) $ (model_update_locale_fuel δ ζ (dom fs))).
  Proof.
    intros Hagree Hfmdead ρ Hin. apply Hfmdead in Hin as (ζ'&ρs&HSome&Hρ).
    destruct (decide (ζ = ζ')) as [<-|Hneq].
    + exists ζ, fs. rewrite lookup_insert. by set_solver.
    + exists ζ', ρs. rewrite lookup_insert_ne; [by set_solver|done].
  Qed.

  Lemma fuel_map_preserve_threadpool_fuel_step
        c1 ζ c2 (fm1 fm2 : gmap _ (gmap (fmrole M) nat)) :
    dom fm1 = dom fm2 → locale_step c1 (Some ζ) c2 →
    fuel_map_preserve_threadpool c1.1 fm1 →
    fuel_map_preserve_threadpool c2.1 fm2.
  Proof.
    rewrite /fuel_map_preserve_threadpool.
    intros Hdom Hstep Htp. intros ζ' Hζ'. destruct c1, c2.
    apply locales_of_list_step_incl in Hstep.
    assert (ζ' ∉ locales_of_list l) as Hζ'' by set_solver.
    apply Htp in Hζ''.
    rewrite -not_elem_of_dom. rewrite -not_elem_of_dom in Hζ''.
    set_solver.
  Qed.

  Lemma model_state_interp_fuel_update c1 c2 δ ζ fs :
    locale_step c1 (Some ζ) c2 →
    model_state_interp c1.1 δ -∗
    has_fuels_S ζ fs ==∗
    model_state_interp c2.1 (model_update_locale_fuel δ ζ (dom fs)) ∗
    has_fuels ζ fs.
  Proof.
    iIntros (Hstep) "Hm Hfs".
    iDestruct "Hm" as (fm Hfmle Hfmdead Htp) "(Hm & Hfm)".
    iDestruct (has_fuels_agree with "Hfm Hfs") as %Hagree.
    iMod (has_fuels_decr with "Hfm Hfs") as "[Hfm $]".
    iModIntro. iExists _. iFrame. iPureIntro.
    split; [|split].
    - by apply fuel_map_le_fuel_step.
    - by apply fuel_map_preserve_dead_fuel_step.
    - eapply fuel_map_preserve_threadpool_fuel_step; [|done..].
      apply elem_of_dom_2 in Hagree. by set_solver.
  Qed.

  Lemma update_fuel_step extr (auxtr : auxiliary_trace LM) c2 fs ζ :
    fs ≠ ∅ →
    locale_step (trace_last extr) (Some ζ) c2 →
    has_fuels_S ζ fs -∗
    model_state_interp (trace_last extr).1 (trace_last auxtr) ==∗
    ∃ δ2,
      ⌜ valid_state_evolution_fairness
        (extr :tr[Some ζ]: c2) (auxtr :tr[Silent_step ζ]: δ2) ⌝ ∗
      has_fuels ζ fs ∗ model_state_interp c2.1 δ2.
  Proof.
    iIntros (Hdom Hstep) "Hfuel Hm".
    iExists (model_update_locale_fuel (trace_last auxtr) ζ (dom fs)).
    iDestruct (model_state_interp_can_fuel_step with "Hm Hfuel") as %Hcan_step;
      [done|].
    iMod (model_state_interp_fuel_update with "Hm Hfuel") as "[Hm Hfuel]";
      [done..|].
    iDestruct (model_state_interp_tids_smaller with "Hm") as %Htids.
    iModIntro.
    iFrame "Hm Hfuel".
    iPureIntro. by apply model_update_locale_spec.
  Qed.

End Steps.
