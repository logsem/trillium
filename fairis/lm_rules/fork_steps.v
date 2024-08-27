From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl.
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

  (* Context {LR1: AM_strong_lr AM1} {LR2: AM_strong_lr AM2}. *)
  (* Context {INDEP: models_independent AM1 AM2}. *)
  (* Existing Instance LR1. *)
  (* Existing Instance LR2. *)

  Context `{EqDecision (expr Λ)}. 

  Definition has_forked (tp1 tp2 : list (expr Λ)) e : Prop :=
    ∃ tp1', tp2 = tp1' ++ [e] ∧ locales_equiv tp1 tp1'.

  Definition model_update_split
             (ζ ζf : locale Λ) (ρs : gset (fmrole M))
             (δ : LiveStateData Λ M) : LiveStateData Λ M :=
    {| ls_under := δ.(ls_under);
       ls_map := <[ζf := (filter (λ ρf, ρf.1 ∈ ρs)) (δ.(ls_map) !!! ζ)]>
                   (alter (filter (λ ρf, ρf.1 ∉ ρs)) ζ δ.(ls_map)); |}.

  Definition map_live (ρs : gset (fmrole M))
             (m : gmap (locale Λ) (gmap (fmrole M) nat)) : Prop :=
    ∀ ρ, ρ ∈ ρs → ∃ ζ fs, m !! ζ = Some fs ∧ ρ ∈ dom fs.

  (* Lemma disjoint_subseteq `{Countable A} (xs1 xs2 ys1 ys2 : gset A) : *)
  (*   xs1 ⊆ xs2 → ys1 ⊆ ys2 → xs2 ## ys2 → xs1 ## ys1. *)
  (* Proof. *)
  (*   intros Hle1 Hle2 Hdisj x Hxs Hys. *)
  (*   eapply Hdisj; [by apply Hle1|by apply Hle2]. *)
  (* Qed. *)

  Lemma model_update_split_valid ζ ζf ρs (δ1 : LM) :
    ζ ∈ dom δ1.(ls_map) → ζf ∉ dom δ1.(ls_map) →
    ∃ δ2, (ls_data δ2) = model_update_split ζ ζf ρs δ1.
  Proof.
    intros [ρs' HSome]%elem_of_dom Hnin.
    set δ2 := model_update_split ζ ζf ρs δ1.
    assert (ζ ≠ ζf) as Hneq.
    { intros ->. apply not_elem_of_dom in Hnin. set_solver. }
    assert (map_inner_disj δ2.(ls_map)) as Hdisj.
    { simpl.
      pose proof δ1.(ls_map_disj) as Hdisj.
      intros ζ1 ζ2 ρs1 ρs2 Hneq' HSome1 HSome2.
      destruct (decide (ζf = ζ1)) as [<-|Hneqf1].
      { rewrite lookup_insert in HSome1.
        rewrite lookup_insert_ne in HSome2; [|done].
        rewrite lookup_total_alt in HSome1.
        rewrite HSome in HSome1.
        simpl in *.
        destruct (decide (ζ = ζ2)) as [<-|Hneq2].
        { rewrite lookup_alter in HSome2.
          rewrite HSome in HSome2. simpl in *. simplify_eq.
          apply map_disjoint_dom.
          pose proof (disjoint_filter_complement
                        (λ ρ : fmrole M, ρ ∈ ρs) (dom ρs')) as Hcomp.
          by rewrite !filter_dom_L in Hcomp. }
        rewrite lookup_alter_ne in HSome2; [|done].
        simplify_eq.
        apply map_disjoint_dom.
        pose proof (Hdisj ζ ζ2 _ _ Hneq2 HSome HSome2) as Hdisj.
        apply map_disjoint_dom in Hdisj.
        eapply disjoint_subseteq_l; [|done].
        apply dom_filter_subseteq. }
      rewrite lookup_insert_ne in HSome1; [|done].
      destruct (decide (ζf = ζ2)) as [<-|Hneqf2].
      { rewrite lookup_insert in HSome2.
        destruct (decide (ζ = ζ1)) as [<-|Hneq2].
        { rewrite lookup_alter in HSome1.
          rewrite lookup_total_alt in HSome2.
          rewrite HSome in HSome1.
          rewrite HSome in HSome2.
          simpl in *. simplify_eq.
          apply map_disjoint_dom.
          pose proof (disjoint_filter_complement
                        (λ ρ : fmrole M, ρ ∈ ρs) (dom ρs')) as Hcomp.
          by rewrite !filter_dom_L in Hcomp. }
        rewrite lookup_alter_ne in HSome1; [|done].
        rewrite lookup_total_alt in HSome2.
        rewrite HSome in HSome2.
        simpl in *. simplify_eq.
        pose proof (Hdisj ζ ζ1 _ _ Hneq2 HSome HSome1) as Hdisj.
        apply map_disjoint_dom.
        apply map_disjoint_dom in Hdisj.
        eapply disjoint_subseteq_r; [|done].
        apply dom_filter_subseteq. }
      destruct (decide (ζ = ζ1)) as [<-|Hneq1].
      { rewrite lookup_alter in HSome1.
        rewrite lookup_insert_ne in HSome2; [|done].
        rewrite lookup_alter_ne in HSome2; [|done].
        rewrite HSome in HSome1.
        simpl in *. simplify_eq.
        pose proof (Hdisj ζ ζ2 _ _ Hneq' HSome HSome2) as Hdisj.
        apply map_disjoint_dom.
        apply map_disjoint_dom in Hdisj.
        eapply disjoint_subseteq_l; [|done].
        apply dom_filter_subseteq. }
      destruct (decide (ζ = ζ2)) as [<-|Hneq2].
      { rewrite lookup_alter_ne in HSome1; [|done].
        rewrite lookup_insert_ne in HSome2; [|done].
        rewrite lookup_alter in HSome2.
        rewrite HSome in HSome2.
        simpl in *. simplify_eq.
        pose proof (Hdisj ζ ζ1 _ _ Hneq1 HSome HSome1) as Hdisj.
        apply map_disjoint_dom.
        apply map_disjoint_dom in Hdisj.
        eapply disjoint_subseteq_r; [|done].
        apply dom_filter_subseteq. }
      rewrite lookup_alter_ne in HSome1; [|done].
      rewrite lookup_insert_ne in HSome2; [|done].
      rewrite lookup_alter_ne in HSome2; [|done].
      pose proof (Hdisj ζ1 ζ2 _ _ Hneq' HSome1 HSome2).
      done. }
    assert (map_live (M.(live_roles) δ2) δ2.(ls_map)) as Hlive.
    { intros ρ Hin.
      pose proof (δ1.(ls_map_live)) as Hlive.
      apply Hlive in Hin as (ζ'&fs&HSome'&Hin').
      destruct (decide (ζ' = ζf)) as [->|Hneqf].
      { apply not_elem_of_dom in Hnin. set_solver. }
      destruct (decide (ζ' = ζ)) as [->|Hneq'].
      { rewrite HSome in HSome'. simplify_eq.
        simpl.
        destruct (decide (ρ ∈ ρs)) as [Hin|Hnin'].
        - exists ζf, (filter (λ ρf : fmrole M * nat, ρf.1 ∈ ρs) fs).
          rewrite lookup_insert. rewrite lookup_total_alt. rewrite HSome. simpl.
          split; [done|].
          apply elem_of_dom. rewrite /is_Some.
          apply elem_of_dom in Hin' as [??].
          eexists _. by apply map_lookup_filter_Some_2.
        - exists ζ, (filter (λ ρf : fmrole M * nat, ρf.1 ∉ ρs) fs).
          rewrite lookup_insert_ne; [|done].
          rewrite lookup_alter. rewrite HSome. simpl.
          split; [done|].
          apply elem_of_dom. rewrite /is_Some.
          apply elem_of_dom in Hin' as [??].
          eexists _. by apply map_lookup_filter_Some_2. }
      exists ζ', fs. split; [|done].
      simpl. rewrite !lookup_insert_ne; [|done].
      rewrite lookup_alter_ne; [|done].
      done. }
    by exists
      {| ls_data := δ2;
         ls_map_disj := Hdisj;
         ls_map_live := Hlive |}.
  Qed.

  Definition model_update_fork
          (ζ : locale Λ) (ζf : locale Λ)
          (ρs1 ρs2 : gset (fmrole M)) (δ : LM) :
      LiveStateData Λ M :=
    model_update_split ζ ζf ρs2 $
    model_update_decr ζ $
    model_update_filter ζ ρs1 δ.

  Lemma model_update_fork_valid
        ζ ζf (ρs1 ρs2 : gset (fmrole M)) (δ1 : LM) :
    ζ ∈ dom δ1.(ls_map) → ζf ∉ dom δ1.(ls_map) →
    ∃ δ2, (ls_data δ2) = model_update_fork ζ ζf ρs1 ρs2 δ1.
  Proof. intros ??. by apply model_update_split_valid; set_solver. Qed.

  Lemma has_fuels_alloc fm ζ fs :
    ζ ∉ dom fm →
    auth_fuel_mapping_is fm ==∗
    auth_fuel_mapping_is (<[ζ := fs]>fm) ∗ has_fuels ζ fs.
  Proof.
    iIntros (Hnin) "Hfm".
    rewrite /has_fuels_S.
    iMod (own_update with "Hfm") as "[$ $]"; [|done].
    apply auth_update_alloc.
    rewrite !fmap_insert.
    rewrite !fmap_empty.
    eapply alloc_local_update; [|done].
    apply not_elem_of_dom in Hnin. by rewrite lookup_fmap Hnin.
  Qed.

  Lemma has_fuels_split fm ζ ζf fs1 fs2 :
    ζf ∉ dom fm → fs1 ##ₘ fs2 →
    auth_fuel_mapping_is fm -∗ has_fuels ζ (fs1 ∪ fs2) ==∗
    auth_fuel_mapping_is (<[ζf := fs2]>(<[ζ := fs1]>fm)) ∗
    has_fuels ζ fs1 ∗ has_fuels ζf fs2.
  Proof.
    iIntros (Hnin Hdisj) "Hfm Hfs".
    iDestruct (has_fuels_agree with "Hfm Hfs") as %HSome.
    assert (ζ ≠ ζf) as Hneq.
    { rewrite not_elem_of_dom in Hnin. set_solver. }
    iMod (has_fuels_update with "Hfm Hfs") as "[Hfm $]".
    iMod (has_fuels_alloc with "Hfm") as "[$$]"; set_solver.
  Qed.

  Lemma not_elem_of_locale_of_from_list (tp : list $ expr Λ) e :
    locale_of tp e ∉ locales_of_list tp.
  Proof.
    unfold locales_of_list_from.
    intros Habs.
    apply elem_of_list_fmap in Habs as ((tp1&e1) & Hlo & Hpf).
    apply prefixes_from_spec in Hpf as (tp2&tp3&He1&He2).
    simplify_eq.
    list_simplifier.
    have Hdone: (tp2 ++ e1 :: tp3, e) ∈ prefixes_from (tp2++[e1]) (tp3 ++ [e]).
    { apply prefixes_from_spec. eexists _, _. list_simplifier. naive_solver. }
    by apply locale_injective in Hdone.
  Qed.

  Lemma elem_of_locale_of_from_list (tp1 tp2 : list $ expr Λ) e :
    locales_equiv tp1 tp2 →
    locale_of tp1 e ∈ locales_of_list (tp2++[e]).
  Proof.
    intros Heq. rewrite (locale_equiv _ _ _ Heq) /locales_of_list_from.
    apply elem_of_list_fmap. exists (tp2, e). split=>//.
    apply prefixes_from_spec. eexists _, _. list_simplifier. naive_solver.
  Qed.

  Lemma model_state_interp_fork_update fs1 fs2 tp1 tp2
        (δ1 δ2 : LM) ζ efork σ1 σ2 :
    (ls_data δ2) = model_update_fork ζ (locale_of tp1 efork) (dom fs1 ∪ dom fs2) (dom fs2) δ1 →
    fs1 ∪ fs2 ≠ ∅ → fs1 ##ₘ fs2 →
    has_forked tp1 tp2 efork →
    locale_step (tp1, σ1) (Some ζ) (tp2, σ2) →
    model_state_interp tp1 δ1 -∗
    has_fuels_S ζ (fs1 ∪ fs2) ==∗
    model_state_interp tp2 δ2 ∗
    has_fuels ζ fs1 ∗
    has_fuels (locale_of tp1 efork) fs2.
  Proof.
    iIntros (Hδ2 Hfs Hdisj Hforked Hstep) "Hm Hf".
    iDestruct "Hm" as (fm Hfmle Hfmdead Htp) "(Hm & Hfm)".
    iDestruct (has_fuels_agree with "Hfm Hf") as %Hagree.
    assert (locale_of tp1 efork ∉ dom fm) as Hnin.
    { pose proof (not_elem_of_locale_of_from_list tp1 efork) as Hes%Htp.
      apply not_elem_of_dom in Hes. set_solver. }
    assert (ζ ≠ locale_of tp1 efork) as Hneq.
    { rewrite not_elem_of_dom in Hnin. set_solver. }
    iMod (has_fuels_decr with "Hfm Hf") as "[Hfm Hf]".
    iMod (has_fuels_split _ _ (locale_of tp1 efork) with "Hfm Hf")
      as "[Hfm [Hf1 Hf2]]"; [|done|].
    { set_solver. }
    iModIntro. iFrame. rewrite Hδ2. iFrame.
    iPureIntro.
    split; [|split].
    - split; last first.
      { simpl.
        destruct Hfmle as [Hfmle Hdom].
        pose proof Hfmle as Hfmle'.
        rewrite /fuel_map_le /fuel_map_le_inner map_included_spec in Hfmle.
        pose proof Hagree as Hagree'.
        apply Hfmle in Hagree' as (fs'&HSome&Hfs').
        rewrite -(insert_id (ls_map δ1) ζ fs'); [|done].
        rewrite !alter_insert.
        set_solver. }
      simpl.
      destruct Hfmle as [Hfmle Hdom].
      pose proof Hfmle as Hfmle'.
      rewrite /fuel_map_le /fuel_map_le_inner map_included_spec in Hfmle.
      pose proof Hagree as Hagree'.
      apply Hfmle in Hagree' as (fs'&HSome&Hfs').
      rewrite -(insert_id (ls_map δ1) ζ fs'); [|done].
      rewrite !alter_insert.
      rewrite insert_insert.

      apply map_included_map_agree_R in Hfs'
          as (fs12'&fsf'&->&Hdisj'&Hfs').
      pose proof Hfs' as Hfs''.
      apply map_agree_R_fmap_inv in Hfs'' as [fs1'' ->]; last first.
      { intros ?[]?; [lia|by eauto]. }
      apply map_agree_R_fmap in Hfs'; last first.
      { intros. lia. }
      apply map_agree_R_union_inv in Hfs'
          as (fs1'&fs2'&->&Hfs1'&Hfs2'); [|done].

      apply map_included_insert.
      { rewrite lookup_total_alt.
        rewrite lookup_insert.
        rewrite map_filter_fmap.
        rewrite map_filter_filter.
        rewrite map_fmap_union.
        rewrite map_filter_union; last first.
        { apply map_disjoint_dom. apply map_disjoint_dom in Hdisj'.
          set_solver. }
        rewrite map_filter_union; last first.
        { apply map_disjoint_dom. apply map_disjoint_dom in Hdisj.
          apply map_agree_R_dom in Hfs1'.
          apply map_agree_R_dom in Hfs2'.
          set_solver. }
        rewrite !map_fmap_union.
        eapply map_included_subseteq_r.
        { apply map_union_subseteq_l. }
        eapply map_included_subseteq_r.
        { apply map_union_subseteq_r.
          apply map_disjoint_dom.
          rewrite !map_filter_fmap. rewrite !dom_fmap_L.
          apply map_disjoint_dom in Hdisj.
          apply map_agree_R_dom in Hfs1'.
          apply map_agree_R_dom in Hfs2'.
          eapply disjoint_subseteq_l; [apply dom_filter_subseteq|].
          eapply disjoint_subseteq_r; [apply dom_filter_subseteq|].
          set_solver. }
        rewrite map_filter_id; last first.
        { simpl.
          intros. apply elem_of_dom_2 in H0.
          apply map_agree_R_dom in Hfs1'.
          apply map_agree_R_dom in Hfs2'.
          split; [set_solver|].
          set_solver. }
        rewrite -map_fmap_compose.
        rewrite decr_succ_compose_id. rewrite map_fmap_id.
        by apply map_agree_R_map_included. }

      apply map_included_insert; [|done].
      rewrite map_filter_fmap.
      rewrite map_filter_filter.

      rewrite !map_fmap_union.
      rewrite map_filter_union; last first.
      { apply map_disjoint_dom. apply map_disjoint_dom in Hdisj'.
        set_solver. }
      rewrite map_filter_union; last first.
      { apply map_disjoint_dom. apply map_disjoint_dom in Hdisj.
        apply map_agree_R_dom in Hfs1'.
        apply map_agree_R_dom in Hfs2'.
        set_solver. }
      rewrite !map_fmap_union.
      eapply map_included_subseteq_r.
      { apply map_union_subseteq_l. }
      eapply map_included_subseteq_r.
      { apply map_union_subseteq_l. }

      rewrite map_filter_id; last first.
      { simpl.
        intros. apply elem_of_dom_2 in H0.
        apply map_agree_R_dom in Hfs1'.
        apply map_agree_R_dom in Hfs2'.
        rewrite dom_fmap in H0.
        apply map_disjoint_dom in Hdisj.
        split; [set_solver|].
        set_solver. }
      rewrite -map_fmap_compose.
      rewrite decr_succ_compose_id. rewrite map_fmap_id.
      by apply map_agree_R_map_included.
  - intros ρ' Hin.
      apply Hfmdead in Hin as (ζ'&ρs&HSome&Hρ).
      destruct (decide (ζ = ζ')) as [<-|Hneq'].
      + rewrite Hagree in HSome.
        simplify_eq.
        rewrite dom_fmap_L in Hρ.
        rewrite dom_union_L in Hρ.
        apply elem_of_union in Hρ.
        destruct Hρ as [Hρ|Hρ].
        * eexists ζ, _. rewrite insert_insert.
          rewrite insert_commute; [|done].
          rewrite lookup_insert. done.
        * eexists (locale_of tp1 efork), _. rewrite insert_insert.
          rewrite lookup_insert. done.
      + assert (ζ' ≠ locale_of tp1 efork) as Hneq''.
        { intros ->. apply not_elem_of_dom in Hnin. set_solver. }
        eexists ζ', _.
        rewrite lookup_insert_ne; [|done].
        rewrite insert_insert.
        rewrite lookup_insert_ne; [|done].
        split; [done|]. by set_solver.
    - rewrite /fuel_map_preserve_threadpool.
      intros ζ' Hζ'.
      apply locales_of_list_step_incl in Hstep.
      assert (ζ' ∉ locales_of_list tp1) as Hζ'' by set_solver.
      apply Htp in Hζ''.
      rewrite insert_insert.
      assert (ζ ≠ ζ') as Hneq'.
      { set_solver. }
      assert (locale_of tp1 efork ≠ ζ') as Hneq''.
      { assert (locale_of tp1 efork ∈ locales_of_list tp2).
        { destruct Hforked as [tp2' [-> Hequiv]].
          by apply elem_of_locale_of_from_list. }
        set_solver. }
      rewrite lookup_insert_ne; [|done].
      rewrite lookup_insert_ne; [|done].
      done.
  Qed.

  Definition model_can_fork_step (δ1 : LM) (ζ ζf : locale Λ) (δ2 : LM) : Prop :=
    ∃ fs fs1 fs2,
      δ1.(ls_under) = δ2.(ls_under) ∧
      δ1.(ls_map) !! ζ = Some fs ∧ fs ≠ ∅ ∧
      δ2.(ls_map) = <[ζ := fs1]>(<[ζf := fs2]> δ1.(ls_map)) ∧
      map_included (<) fs1 fs ∧
      map_included (<) fs2 fs ∧
      (dom fs ∖ (dom fs1 ∪ dom fs2) ∩ M.(live_roles) δ1 = ∅) ∧
      (dom fs1 ∩ dom fs2 = ∅) ∧
      ζf ∉ dom δ1.(ls_map).

  Lemma silent_step_suff_data_fork_weak fl `(δ: LiveState Λ M)
        (fs fs1 fs2 : gmap _ nat) ζ ζf :
    δ.(ls_map) !! ζ = Some fs →
    fs ≠ ∅ →
    map_included (<) fs1 fs →
    map_included (<) fs2 fs →
    (dom fs ∖ (dom fs1 ∪ dom fs2)) ∩ M.(live_roles) δ = ∅ →
    (dom fs1 ∩ dom fs2 = ∅) →
    ζf ∉ dom δ.(ls_map) →
    ∃ δ', δ'.(ls_data) =
          {| ls_under := δ;
            ls_map := <[ζ := fs1]>(<[ζf := fs2]> δ.(ls_map)) |} ∧
            ls_trans fl δ (Silent_step ζ) δ'.
  Proof.
    intros.
    apply (silent_step_suff_data fl δ fs fs1 fs2 ζ (Some ζf)); try done.
    - rewrite map_included_spec in H2. done.
    - rewrite map_included_spec in H3. done.
    - set_solver.
  Qed.

  (* TODO: Change original lemma to not existentially quantify new state *)
  Lemma silent_step_suff_data_fork_weak_alt fl (δ δ': LiveState Λ M)
        (fs fs1 fs2 : gmap _ nat) ζ ζf :
    δ.(ls_under) = δ'.(ls_under) →
    δ.(ls_map) !! ζ = Some fs →
    δ'.(ls_map) = <[ζ := fs1]>(<[ζf := fs2]> δ.(ls_map)) →
    fs ≠ ∅ →
    map_included (<) fs1 fs →
    map_included (<) fs2 fs →
    (dom fs ∖ (dom fs1 ∪ dom fs2)) ∩ M.(live_roles) δ = ∅ →
    (dom fs1 ∩ dom fs2 = ∅) →
    ζf ∉ dom δ.(ls_map) →
    ls_trans fl δ (Silent_step ζ) δ'.
  Proof.
    rewrite !map_included_spec.
    intros Hδ Hfs Hfs12 Hne Hle1 Hle2 Hlive Hdisj Hnin.
    assert (∃ δ', δ'.(ls_data) =
          {| ls_under := δ;
            ls_map := <[ζ := fs1]> (<[ζf := fs2]>δ.(ls_map)) |} ∧
            ls_trans fl δ (Silent_step ζ) δ') as (δ''&Heq&Htrans).
    { apply (silent_step_suff_data fl δ fs fs1 fs2 ζ (Some ζf));
        try set_solver. }
    rewrite Heq Hδ -Hfs12 in Htrans. by destruct δ', ls_data.
  Qed.

  Lemma model_can_fork_step_trans fl ζ ζf (δ δ' : LiveState Λ M) :
    model_can_fork_step δ ζ ζf δ' → ls_trans fl δ (Silent_step ζ) δ'.
  Proof.
    destruct 1 as (?&?&?&?&?&?&?&?&?&?&?&?).
    by eapply silent_step_suff_data_fork_weak_alt.
  Qed.

  Lemma model_state_interp_can_fork_step es (δ1 δ2 : LM) ζ
        (fs1 fs2 : gmap (fmrole M) nat) e :
    (ls_data δ2) = model_update_fork ζ (locale_of es e) (dom fs1 ∪ dom fs2) (dom fs2) δ1 →
    (fs1 ∪ fs2) ≠ ∅ → fs1 ##ₘ fs2 →
    model_state_interp es δ1 -∗ has_fuels_S ζ (fs1 ∪ fs2) -∗
    ⌜model_can_fork_step δ1 ζ (locale_of es e) δ2⌝.
  Proof.
    iIntros (Hδ2 Hne Hdisj) "Hm Hf".
    iDestruct "Hm" as (fm [Hfmle Hdom] Hfmdead Htp) "(Hm & Hfm)".
    iDestruct (has_fuels_agree with "Hfm Hf") as %Hagree.
    pose proof Hagree as Hagree'.
    rewrite /fuel_map_le_inner map_included_spec in Hfmle.
    apply Hfmle in Hagree as (fs'&HSome&Hle).
    iPureIntro.
    apply map_included_map_agree_R in Hle as (fs12'&fsf'&->&Hdisj'&Hle).
    pose proof Hle as Hle'.
    apply map_agree_R_fmap_inv in Hle' as (fs12''&->); last first.
    { intros. destruct v2; [lia|by eauto]. }
    apply map_agree_R_fmap in Hle; last first.
    { intros. lia. }
    apply map_agree_R_union_inv in Hle as (fs1'&fs2'&->&Hle1&Hle2);
      [|done].
    eexists _, fs1', fs2'.
    repeat split.
    - rewrite Hδ2. done.
    - done.
    - apply map_agree_R_dom in Hle1.
      apply map_agree_R_dom in Hle2.
      intros Heq. apply Hne.
      apply dom_empty_iff_L in Heq.
      apply dom_empty_iff_L.
      set_solver.
    - rewrite Hδ2. simpl.
      rewrite insert_commute; last first.
      { assert (locale_of es e ∉ locales_of_list es) as Hes%Htp.
        apply not_elem_of_locale_of_from_list.
        set_solver. }
      f_equiv.
      { rewrite lookup_total_alt. simpl.
        rewrite !lookup_alter. rewrite HSome.
        simpl.
        rewrite map_filter_fmap. simpl.
        rewrite map_filter_filter. simpl.
        rewrite !map_fmap_union.
        apply map_agree_R_dom in Hle1.
        apply map_agree_R_dom in Hle2.
        apply map_disjoint_dom in Hdisj.
        apply map_disjoint_dom in Hdisj'.
        rewrite map_filter_union; [|apply map_disjoint_dom; set_solver].
        rewrite map_filter_union; [|apply map_disjoint_dom; set_solver].
        assert (filter
                  (λ '(i, _),
                     i ∈ dom fs2 ∧ (i ∈ live_roles M δ1 ∨ i ∈ dom fs1 ∪ dom fs2))
                  (S <$> fs1') = ∅) as Hfs1'.
        { apply map_filter_empty_iff.
          intros ρ f Hρ [HP1 HP2].
          apply elem_of_dom_2 in Hρ.
          rewrite dom_fmap_L in Hρ. set_solver. }
        assert (filter
                  (λ '(i, _),
                     i ∈ dom fs2 ∧ (i ∈ live_roles M δ1 ∨ i ∈ dom fs1 ∪ dom fs2))
                  fsf' = ∅) as Hfsf'.
        { apply map_filter_empty_iff.
          intros ρ f Hρ [HP1 HP2].
          apply elem_of_dom_2 in Hρ. set_solver. }
        rewrite Hfs1' Hfsf'.
        rewrite left_id right_id.
        rewrite map_filter_id; last first.
        { intros. split.
          - apply elem_of_dom_2 in H0. set_solver.
          - right.
            apply elem_of_dom_2 in H0. set_solver. }
        rewrite -map_fmap_compose.
        rewrite decr_succ_compose_id.
        rewrite map_fmap_id.
        done. }
      rewrite -!alter_compose.
      erewrite alter_insert_alt; [|done].
      f_equiv; [| done].
      simpl.
      rewrite map_filter_fmap. simpl.
      rewrite map_filter_filter. simpl.
      apply map_agree_R_dom in Hle1.
      apply map_agree_R_dom in Hle2.
      apply map_disjoint_dom in Hdisj.
      apply map_disjoint_dom in Hdisj'.
      rewrite !map_fmap_union.
      rewrite map_filter_union; [|apply map_disjoint_dom; set_solver].
      rewrite map_filter_union; [|apply map_disjoint_dom; set_solver].
      assert (filter
             (λ '(i, _),
                (i ∉ dom fs2) ∧ (i ∈ live_roles M δ1 ∨ i ∈ dom fs1 ∪ dom fs2))
             (S <$> fs2') = ∅) as Hfs2'.
      { apply map_filter_empty_iff.
        intros ρ f Hρ [HP1 HP2].
        apply elem_of_dom_2 in Hρ.
        rewrite dom_fmap_L in Hρ. set_solver. }
      assert (filter
                (λ '(i, _),
                   (i ∉ dom fs2) ∧ (i ∈ live_roles M δ1 ∨ i ∈ dom fs1 ∪ dom fs2))
                fsf' = ∅) as Hfsf'.
      { apply map_filter_empty_iff.
        intros ρ f Hρ [HP1 HP2].
        apply elem_of_dom_2 in Hρ.
        rewrite Hle2 in HP1.
        clear HP1.
        assert (ρ ∈ (dom fs1 ∪ dom fs2)).
        { destruct HP2 as [HP2|?]; [|done].
          rewrite -dom_union_L.
          rewrite -(dom_fmap_L S).
          eapply fuel_map_le_live_roles; [| | |apply Hagree'|..].
          - intros ????. by apply δ1.(ls_map_disj).
            (* TODO: Fix this by unifying defs *)
          - rewrite /fuel_map_le_inner map_included_spec.
            eapply Hfmle.
          - done.
          - done.
          - done.
          - set_solver. }
        set_solver. }
      rewrite Hfs2' Hfsf'.
      rewrite right_id right_id.
      rewrite map_filter_id; last first.
      { intros. split.
        - apply elem_of_dom_2 in H0. set_solver.
        - right.
          apply elem_of_dom_2 in H0. set_solver. }
      rewrite -map_fmap_compose.
      rewrite decr_succ_compose_id.
      rewrite map_fmap_id.
      done.
    - eapply (map_included_subseteq_r _ _ (S <$> fs1')).
      { rewrite map_fmap_union.
        etransitivity; apply map_union_subseteq_l. }
      apply map_included_spec.
      intros k v1 Hv1. exists (S v1).  split; [|lia].
      by rewrite lookup_fmap Hv1.
    - eapply (map_included_subseteq_r _ _ (S <$> fs2')).
      { rewrite map_fmap_union.
        rewrite (map_union_comm (S <$> fs1') (S <$> fs2')).
        - etransitivity; apply map_union_subseteq_l.
        - apply map_disjoint_dom. rewrite !dom_fmap_L.
          apply map_disjoint_dom in Hdisj.
          apply map_agree_R_dom in Hle1.
          apply map_agree_R_dom in Hle2.
          set_solver. }
      apply map_included_spec.
      intros k v1 Hv1. exists (S v1). split; [|lia].
      by rewrite lookup_fmap Hv1.
    - rewrite -dom_empty_iff_L in Hne.
      apply map_agree_R_dom in Hle1.
      apply map_agree_R_dom in Hle2.
      apply disjoint_intersection_L.
      apply map_disjoint_dom in Hdisj.
      apply map_disjoint_dom in Hdisj'.
      rewrite dom_union_L.
      rewrite dom_fmap_L.
      rewrite -dom_union_L.
      replace (dom (fs1' ∪ fs2' ∪ fsf') ∖ (dom fs1' ∪ dom fs2'))
        with (dom fsf') by set_solver.
      intros ρ Hin1 Hin2.
      assert (ρ ∈ (dom fs1 ∪ dom fs2)).
      { rewrite -dom_union_L.
        rewrite -(dom_fmap_L S).
        eapply fuel_map_le_live_roles; [| | |apply Hagree'|..].
        - intros ????. by apply δ1.(ls_map_disj).
        - rewrite /fuel_map_le_inner map_included_spec.
          eapply Hfmle.
        - done.
        - done.
        - done.
        - set_solver. }
      set_solver.
    - apply map_agree_R_dom in Hle1.
      apply map_agree_R_dom in Hle2.
      apply disjoint_intersection_L.
      apply map_disjoint_dom in Hdisj.
      set_solver.
    - pose proof (not_elem_of_locale_of_from_list es e)
        as Hes%Htp.
      apply not_elem_of_dom in Hes. set_solver.
  Qed.

  Lemma model_update_locale_spec_fork extr
        (auxtr : auxiliary_trace LM) ζ ζf c2 ρs1 ρs2 δ2 :
    δ2.(ls_data) = model_update_fork ζ ζf ρs1 ρs2 (trace_last auxtr) →
    model_can_fork_step (trace_last auxtr) ζ ζf δ2 →
    tids_smaller c2.1 δ2 →
    valid_state_evolution_fairness
      (extr :tr[Some ζ]: c2)
      (auxtr :tr[Silent_step ζ]: δ2).
  Proof.
    intros Hstep Htids. destruct c2.
    split; [done|]. split; [by eapply model_can_fork_step_trans|done].
  Qed.

  Lemma model_state_interp_has_fuels_agree es δ ζ (fs : gmap (fmrole M) nat) :
    model_state_interp es δ -∗ has_fuels ζ fs -∗
    ⌜∃ fs', δ.(ls_map) !! ζ = Some fs' ∧ map_included (≤) fs fs'⌝.
  Proof.
    iIntros "Hm Hf".
    iDestruct "Hm" as (fm [Hfmle _] Hfmdead Htp) "(Hm & Hfm)".
    iDestruct (has_fuels_agree with "Hfm Hf") as %Hagree.
    rewrite /fuel_map_le_inner map_included_spec in Hfmle.
    apply Hfmle in Hagree as (fs'&HSome&Hfs').
    iPureIntro. by eexists _.
  Qed.

  Lemma update_fork_step fs1 fs2 tp1 tp2 (extr : execution_trace Λ)
        (auxtr: auxiliary_trace LM) ζ efork σ1 σ2 :
    fs1 ∪ fs2 ≠ ∅ → fs1 ##ₘ fs2 →
    trace_last extr = (tp1, σ1) →
    locale_step (tp1, σ1) (Some ζ) (tp2, σ2) →
    has_forked tp1 tp2 efork →
    has_fuels_S ζ (fs1 ∪ fs2) -∗
    model_state_interp tp1 (trace_last auxtr) ==∗
    ∃ δ2,
      ⌜valid_state_evolution_fairness
        (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[Silent_step ζ]: δ2)⌝ ∗
      has_fuels ζ fs1 ∗ has_fuels (locale_of tp1 efork) fs2 ∗
      model_state_interp tp2 δ2.
  Proof.
    iIntros (Hdom Hdisj Hlast Hstep Hforked) "Hfuel Hm".
    iDestruct (model_state_interp_has_fuels_agree with "Hm Hfuel")
      as %(fs'&HSome&Hfs').
    iAssert (⌜(locale_of tp1 efork) ∉ dom (ls_map (trace_last auxtr))⌝)%I as %Hnin.
    { destruct Hforked as (?&?&?).
      iDestruct "Hm" as (fm [_ Hdom'] _ Htp) "[Hm Hfm]".
      rewrite -Hdom'.
      iPureIntro. apply not_elem_of_dom. apply Htp.
      apply locale_step_equiv in Hstep. simpl in *.
      apply not_elem_of_locale_of_from_list. }
    epose proof (model_update_fork_valid _ _ _ _ _) as [δ2 Hδ];
      [by apply elem_of_dom|done|].
    iDestruct (model_state_interp_can_fork_step with "Hm Hfuel") as %Hcan_step;
      [done..|].
    iMod (model_state_interp_fork_update with "Hm Hfuel") as "(Hm&Hf1&Hf2)";
      [done..|].
    iDestruct (model_state_interp_tids_smaller with "Hm") as %Htids.
    iModIntro.
    iExists δ2.
    iFrame "Hm Hf1 Hf2".
    iPureIntro.
    by eapply model_update_locale_spec_fork.
  Qed.

End Steps.
