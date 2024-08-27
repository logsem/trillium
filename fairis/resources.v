From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fuel map_included_utils utils action_model.

(* Canonical Structure ModelO (Mdl : FairModel) := leibnizO Mdl. *)
Canonical Structure AMO (AM : ActionModel) := leibnizO (amSt AM). 
(* Canonical Structure RoleO (Mdl : FairModel) := leibnizO (Mdl.(fmrole)). *)
Canonical Structure RoleO (AM : ActionModel) := leibnizO (amRole AM).
Canonical Structure localeO (Λ : language) := leibnizO (locale Λ).

Definition AM_repr (AM: ActionModel) :=
  optionUR $ exclR $ AMO AM. 

Class fairnessGpreS `{Countable (locale Λ)} (AM1 AM2: ActionModel) Σ := {
  fairnessGpreS_model :> inG Σ (authUR (prodUR (AM_repr AM1) (AM_repr AM2)));
  fairnessGpreS_model_fuel_mapping :>
    inG Σ (authUR (gmapUR (localeO Λ)
                          (exclR $ gmapUR (RoleO (ProdAM AM1 AM2)) natO)));
  fairnessGpreS_model_free_roles :> inG Σ (authUR (gset_disjUR (RoleO (ProdAM AM1 AM2))));
}.

Class fairnessGS `{Countable (locale Λ)} (AM1 AM2: ActionModel) Σ := FairnessGS {
  fairness_inG :> fairnessGpreS AM1 AM2 Σ;
  (** Underlying models *)
  fairness_model_name : gname;
  fairness_aux_model_name : gname;
  (** Mapping of threads to roles with fuel *)
  fairness_model_fuel_mapping_name : gname;
  (** Set of free/availble roles *)
  fairness_model_free_roles_name : gname;
}.

Global Arguments fairnessGS {_ _ _} AM1 AM2 Σ.
Global Arguments fairness_model_name {_ _ _ AM1 AM2 Σ} _.
Global Arguments fairness_model_fuel_mapping_name {Λ _ _ AM1 AM2 Σ} _ : assert.
Global Arguments fairness_model_free_roles_name {Λ _ _ AM1 AM2 Σ} _ : assert.

Definition fairnessΣ Λ AM1 AM2 `{Countable (locale Λ)} : gFunctors := #[
   GFunctor (authUR (prodUR (AM_repr AM1) (AM_repr AM2)));
   GFunctor (authUR (gmapUR (localeO Λ)
                            (exclR $ gmapUR (RoleO (ProdAM AM1 AM2)) natO)));
   GFunctor (authUR (gset_disjUR (RoleO (ProdAM AM1 AM2))))
].

Global Instance subG_fairnessGpreS {Σ} `{Countable (locale Λ)} {AM1 AM2}
       :
  subG (fairnessΣ Λ AM1 AM2) Σ -> fairnessGpreS AM1 AM2 Σ.
Proof.
  (* solve_inG.  *)
  intros. split.
  all:
    rewrite /fairnessΣ in H0;
    repeat (apply subG_inv in H0; destruct H0 as [?X H0]);
    solve_inG.
Qed.


Section model_state_interp.
  Context `{Countable (locale Λ)}.

  Context {AM1 AM2: ActionModel}.
  (* Context `(AM_strong_lr AM1) `(AM_strong_lr AM2). *)
  Let PM := ProdAM AM1 AM2.
  Context {PROD_LR: AM_strong_lr PM}. 
  Let M := AM2FM PM PROD_LR.
  
  Context `{LM: LiveModel Λ M}.
  Context {Σ : gFunctors}.

  Context {fG: fairnessGS AM1 AM2 Σ}.

  Notation Role := (M.(fmrole)).

  Definition auth_fuel_mapping_is
             (m: gmap (locale Λ) (gmap Role nat)) : iProp Σ :=
    own (fairness_model_fuel_mapping_name fG)
        (● (fmap Excl m :
              ucmra_car (gmapUR _ (exclR $ gmapUR (RoleO PM) natO)
        ))).

  Definition frag_fuel_mapping_is
             (m: gmap (locale Λ) (gmap Role nat)) : iProp Σ :=
    own (fairness_model_fuel_mapping_name fG)
        (◯ (fmap Excl m:
              ucmra_car (gmapUR _ (exclR $ gmapUR (RoleO PM) natO)
        ))).

  Definition auth_model_is (fm: fmstate M): iProp Σ :=
    own (fairness_model_name fG) (● (Excl' fm.1, Excl' fm.2)).

  (* TODO: rename *)
  Definition frag_model_is (m: amSt AM1): iProp Σ :=
    own (fairness_model_name fG) (◯ (Excl' m, None)).

  Definition auth_free_roles_are (FR: gset Role): iProp Σ :=
    own (fairness_model_free_roles_name fG) (● (GSet FR)).

  Definition frag_free_roles_are (FR: gset Role): iProp Σ :=
    own (fairness_model_free_roles_name fG) (◯ (GSet FR)).

  Definition fuel_map_le_inner (m1 m2 : gmap (locale Λ) (gmap Role nat)) :=
    map_included (λ (fs1 fs2 : gmap Role nat),
                    map_included (≤) fs1 fs2) m1 m2.

  Definition fuel_map_le (m1 m2 : gmap (locale Λ) (gmap Role nat)) :=
    fuel_map_le_inner m1 m2 ∧
    (* OBS: This is a bit hacky, should instead change definition. *)
    dom m1 = dom m2.

  Definition fuel_map_preserve_dead
             (m : gmap (locale Λ) (gmap Role nat))
             (ρs : gset Role) :=
    ∀ ρ, ρ ∈ ρs → ∃ ζ fs, m !! ζ = Some fs ∧ ρ ∈ dom fs.

  Definition fuel_map_preserve_threadpool (tp: list $ expr Λ)
             (fuel_map : gmap (locale Λ) (gmap Role nat)) :=
     ∀ ζ, ζ ∉ locales_of_list tp → fuel_map !! ζ = None.

  Definition model_state_interp (tp: list $ expr Λ) (δ: LiveState Λ M): iProp Σ :=
    ∃ fuel_map,
      ⌜ fuel_map_le fuel_map δ.(ls_map) ⌝ ∗
      ⌜ fuel_map_preserve_dead fuel_map (M.(live_roles) δ) ⌝ ∗
      ⌜ fuel_map_preserve_threadpool tp fuel_map ⌝ ∗
      auth_model_is δ ∗ auth_fuel_mapping_is fuel_map.

  Lemma model_state_interp_tids_smaller δ tp :
    model_state_interp tp δ -∗ ⌜ tids_smaller tp δ ⌝.
  Proof.
    iIntros "(%m&[_ %Heq]&%&%Hbig&_)".
    iPureIntro.
    intros ζ Hin.
    assert (¬ (ζ ∉ locales_of_list tp)).
    - intros contra.
      specialize (Hbig _ contra).
      rewrite -Heq elem_of_dom Hbig in Hin.
      inversion Hin. naive_solver.
    - destruct (decide (ζ ∈ locales_of_list tp)) as [Hin'|] =>//.
      apply elem_of_list_fmap in Hin' as [[tp' e'] [-> Hin']].
      unfold from_locale. exists e'. by apply from_locale_from_Some.
  Qed.

End model_state_interp.

Lemma own_proper `{inG Σ X} γ (x y: X):
  x ≡ y ->
  own γ x -∗ own γ y.
Proof. intros ->; auto. Qed.

Section model_state_lemmas.
  Context `{Countable (locale Λ)}.

  Context {AM1 AM2: ActionModel}.
  Let PM := ProdAM AM1 AM2.
  Context {PROD_LR: AM_strong_lr PM}. 
  Let M := AM2FM PM PROD_LR.

  Context `{LM: LiveModel Λ M}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS AM1 AM2 Σ}.

  Notation Role := (M.(fmrole)).

  Definition has_fuels (ζ: locale Λ) (fs: gmap Role nat) : iProp Σ :=
    frag_fuel_mapping_is {[ ζ := fs ]}.

  #[global] Instance has_fuels_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (has_fuels).
  Proof. solve_proper. Qed.

  #[global] Instance has_fuels_timeless (ζ: locale Λ) (fs: gmap Role nat):
    Timeless (has_fuels ζ fs).
  Proof. rewrite /has_fuels. apply _. Qed.

  Definition has_fuels_S (ζ: locale Λ) (fs: gmap Role nat): iProp Σ :=
    has_fuels ζ (S <$> fs).

  Definition has_fuels_plus (n: nat) (ζ: locale Λ) (fs: gmap Role nat): iProp Σ :=
    has_fuels ζ (fmap (fun m => n+m) fs).

  Lemma has_fuel_fuels_plus_1 (ζ: locale Λ) fs:
    has_fuels_plus 1 ζ fs ⊣⊢ has_fuels_S ζ fs.
  Proof.
    rewrite /has_fuels_plus /has_fuels_S. do 2 f_equiv.
    intros m m' ->. apply leibniz_equiv_iff. lia.
  Qed.

  Lemma has_fuel_fuels_plus_0 (ζ: locale Λ) fs:
    has_fuels_plus 0 ζ fs ⊣⊢ has_fuels ζ fs.
  Proof.
    rewrite /has_fuels_plus /=.  f_equiv. intros ?.
    rewrite lookup_fmap. apply leibniz_equiv_iff.
    destruct (fs !! i) eqn:Heq; rewrite Heq //.
  Qed.

  Lemma has_fuels_plus_split_S n (ζ: locale Λ) fs:
    has_fuels_plus (S n) ζ fs ⊣⊢ has_fuels_S ζ ((λ m, n + m) <$> fs).
  Proof.
    rewrite /has_fuels_plus /has_fuels_S. f_equiv.
    rewrite -map_fmap_compose /= => ρ.
    rewrite !lookup_fmap //.
  Qed.

  (* TODO: move *)
  Lemma frag_free_roles_are_sep: forall fr1 fr2 (DISJ: fr1 ## fr2), 
        frag_free_roles_are (fr1 ∪ fr2) ⊣⊢ frag_free_roles_are fr1 ∗ frag_free_roles_are fr2.
  Proof.
    intros. rewrite /frag_free_roles_are /frag_free_roles_are.    
    rewrite -gset.gset_op.
    rewrite -gset.gset_disj_union; auto. 
    rewrite -own_op. by rewrite -auth_frag_op.
  Qed. 

  Lemma update_model (δ δ1 δ2: amSt AM1) (δ': amSt AM2):
    auth_model_is (δ1, δ') -∗ frag_model_is δ2 ==∗ auth_model_is (δ, δ') ∗ frag_model_is δ.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    iMod (own_update with "H") as "[??]"; eauto.
    - apply auth_update.
      apply prod_local_update'; simpl.
      2: reflexivity. 
      by apply option_local_update, (exclusive_local_update _ (Excl δ)).
    - iModIntro. iFrame.
  Qed.

  Lemma model_agree s1 s2:
    auth_model_is s1 -∗ frag_model_is s2 -∗ ⌜ s1.1 = s2 ⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %[SUB ?]%auth_both_valid_discrete.
    apply pair_included in SUB as [SUB _]. 
    by apply Excl_included, leibniz_equiv in SUB. 
  Qed.

  Lemma model_agree' δ1 s2 n:
    model_state_interp n δ1 -∗ frag_model_is s2 -∗ ⌜ (ls_under δ1).1 = s2 ⌝.
  Proof.
    iIntros "Hsi Hs2". iDestruct "Hsi" as (??) "(_&_&Hs1&_)".
    iApply (model_agree with "Hs1 Hs2").
  Qed.

  Lemma has_fuels_agree (ζ : locale Λ) (fs : gmap (fmrole M) nat)
        (m : gmap (locale Λ) (gmap (fmrole M) nat)) :
    auth_fuel_mapping_is m -∗ has_fuels ζ fs -∗ ⌜m !! ζ = Some fs⌝.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
    iPureIntro.
    apply auth_both_valid_discrete in Hvalid as [Hincl Hvalid].
    rewrite map_fmap_singleton in Hincl.
    apply singleton_included_exclusive_l in Hincl;
      [|apply _|done].
    rewrite lookup_fmap in Hincl.
    apply leibniz_equiv in Hincl.
    destruct (m !! ζ) eqn:L.
    all: rewrite L in Hincl; simplify_eq /=; done.
  Qed.

  Lemma has_fuels_update fm ζ fs fs' :
    auth_fuel_mapping_is fm -∗ has_fuels ζ fs ==∗
    auth_fuel_mapping_is (<[ζ := fs']>fm) ∗ has_fuels ζ fs'.
  Proof.
    iIntros "Hfm Hfs".
    rewrite /has_fuels_S.
    iDestruct (has_fuels_agree with "Hfm Hfs") as %Hagree.
    iMod (own_update_2 with "Hfm Hfs") as "[$ $]"; [|done].
    apply auth_update.
    rewrite !fmap_insert.

    rewrite !fmap_empty !insert_empty.
    eapply singleton_local_update.
    { rewrite lookup_fmap. rewrite Hagree. simpl. reflexivity. }
    apply exclusive_local_update. done. 
  Qed.

  Lemma has_fuels_decr (ζ : locale Λ) (fs : gmap (fmrole M) nat)
        (m : gmap (locale Λ) (gmap (fmrole M) nat)) :
    auth_fuel_mapping_is m -∗ has_fuels_S ζ fs ==∗
    auth_fuel_mapping_is (<[ζ := fs]>m) ∗ has_fuels ζ fs.
  Proof.
    iIntros "Hfm Hfs".
    iMod (has_fuels_update with "Hfm Hfs") as "[Hfm Hfs]".
    by iFrame.
  Qed.

  Lemma has_fuels_delete fs ζ ρs ρ :
    auth_fuel_mapping_is fs -∗ has_fuels ζ ρs ==∗
    auth_fuel_mapping_is (<[ζ := delete ρ ρs]>fs) ∗
    has_fuels ζ (delete ρ ρs).
  Proof.
    iIntros "Hfm Hfs".
    iMod (has_fuels_update with "Hfm Hfs") as "[Hfm Hfs]".
    by iFrame.
  Qed.

  Lemma model_state_interp_has_fuels_decr tp δ tid fs :
    model_state_interp tp δ -∗ has_fuels_S tid fs ==∗
    model_state_interp tp δ ∗ has_fuels tid fs.
  Proof using.
    iDestruct 1 as
      (fm [Hfmle Hdom] Hfmdead Htp) "(Hδ & Hfm)".
    iIntros "Hfs".
    iDestruct (has_fuels_agree with "Hfm Hfs") as %Hagree.
    iMod (has_fuels_decr with "Hfm Hfs") as "[Hfm Hfs]".
    iModIntro. iFrame "Hfs".
    iExists _. iFrame.
    iPureIntro. repeat split.
    - eapply map_included_transitivity; [|done].
      rewrite -{2}(insert_id fm tid (S <$> fs)); [|done].
      apply map_included_insert; [|apply map_included_refl].
      apply map_included_fmap. lia.
    - rewrite -Hdom. rewrite -{2}(insert_id fm tid (S <$> fs)); [set_solver|].
      done.
    - intros ρ Hin. apply Hfmdead in Hin as (ζ'&ρs&HSome&Hρ).
      destruct (decide (tid = ζ')) as [->|Hneq].
      + exists ζ', fs. rewrite lookup_insert.
        split; [done|]. set_solver.
      + exists ζ', ρs. rewrite lookup_insert_ne; [|done]. done.
    - intros ζ Hζ.
      specialize (Htp ζ Hζ).
      rewrite -(insert_id fm tid (S <$> fs)) in Htp; [|done].
      rewrite -not_elem_of_dom.
      rewrite -not_elem_of_dom in Htp.
      set_solver.
  Qed.

  Lemma free_roles_inclusion FR fr:
    auth_free_roles_are FR -∗
    frag_free_roles_are fr -∗
    ⌜fr ⊆ FR⌝.
  Proof.
    iIntros "HFR Hfr".
    iDestruct (own_valid_2 with "HFR Hfr") as %Hval. iPureIntro.
    apply auth_both_valid_discrete in Hval as [??].
    by apply gset_disj_included.
  Qed.

  Lemma update_free_roles rem FR fr1:
    rem ⊆ fr1 ->
    auth_free_roles_are FR -∗
    frag_free_roles_are fr1 ==∗
    auth_free_roles_are (FR ∖ rem) ∗
    frag_free_roles_are (fr1 ∖ rem).
  Proof.
    iIntros (?) "HFR Hfr1".
    iDestruct (free_roles_inclusion with "HFR Hfr1") as %Hincl.
    replace FR with ((FR ∖ rem) ∪ rem); last first.
    { rewrite difference_union_L. set_solver. }
    replace fr1 with ((fr1 ∖ rem) ∪ rem); last first.
    { rewrite difference_union_L. set_solver. }
    iAssert (frag_free_roles_are (fr1 ∖ rem) ∗ frag_free_roles_are rem)%I with "[Hfr1]" as "[Hfr2 Hrem]".
    { rewrite /frag_free_roles_are -own_op -auth_frag_op gset_disj_union //. set_solver. }
    iCombine "HFR Hrem" as "H".
    iMod (own_update with "H") as "[??]" ; eauto.
    - apply auth_update, gset_disj_dealloc_local_update.
    - iModIntro. iFrame. iApply (own_proper with "Hfr2").
      do 2 f_equiv. set_solver.
  Qed.

  Definition filter_fuel_map
             δ (ρs : gset (fmrole M)) (fs : gmap (fmrole M) nat) :
      gmap (fmrole M) nat :=
    (filter (λ ρf, ρf.1 ∈ M.(live_roles) δ.(ls_under) ∨ ρf.1 ∈ ρs)) fs.

  Lemma filter_fuel_map_included δ ρs fs :
    map_included (≤) (filter_fuel_map δ ρs fs) fs.
  Proof.
    apply map_included_spec.
    intros k v1 Hm.
    exists v1. split; [|lia].
    pose proof (map_filter_subseteq
                  (λ ρf : fmrole M * nat, ρf.1 ∈ live_roles M δ ∨ ρf.1 ∈ ρs) fs)
      as Hle.
    rewrite map_subseteq_spec in Hle.
    by apply Hle.
  Qed.

  Program Definition model_update_filter
          (ζ : locale Λ) (ρs : gset (fmrole M)) (δ : LM) : LM :=
    {|
      ls_data :=
        {| ls_under := δ.(ls_under);
           ls_map :=
             alter (filter
                       (λ ρf, ρf.1 ∈ M.(live_roles) δ.(ls_under) ∨ ρf.1 ∈ ρs))
                       ζ δ.(ls_map); |};
    |}.
  Next Obligation.
    intros ζ ρs δ ζ1 ζ2 fs1 fs2 Hneq HSome1 HSome2.
    simpl in *.
    pose proof δ.(ls_map_disj) as Hdisj.
    assert (∃ fs1', map_included (≤) fs1 fs1' ∧ ls_map δ !!! ζ1 = fs1')
      as (fs1' & Hle1 & Hfs1').
    { destruct (decide (ζ = ζ1)) as [<-|Hneq'].
      + rewrite lookup_alter in HSome1.
        rewrite -lookup_fmap in HSome1.
        apply lookup_fmap_Some in HSome1 as (fs1'&Hfs1'&HSome1').
        simplify_eq.
        exists fs1'. rewrite lookup_total_alt. simpl. rewrite HSome1'.
        split; [apply filter_fuel_map_included|done].
      + rewrite lookup_alter_ne in HSome1; [|done].
        rewrite lookup_total_alt. eexists _.
        split; [done|by rewrite HSome1]. }
    assert (∃ fs2', map_included (≤) fs2 fs2' ∧ ls_map δ !!! ζ2 = fs2')
      as (fs2' & Hle2 & Hfs2').
    { destruct (decide (ζ = ζ2)) as [<-|Hneq'].
      + rewrite lookup_alter in HSome2.
        rewrite -lookup_fmap in HSome2.
        apply lookup_fmap_Some in HSome2 as (fs2'&Hfs2'&HSome2').
        simplify_eq.
        exists fs2'. rewrite lookup_total_alt. simpl. rewrite HSome2'.
        split; [apply filter_fuel_map_included|done].
      + rewrite lookup_alter_ne in HSome2; [|done].
        rewrite lookup_total_alt. eexists _.
        split; [done|by rewrite HSome2]. }
    rewrite lookup_total_alt in Hfs1'.
    rewrite lookup_total_alt in Hfs2'.
    destruct (ls_map δ !! ζ1) as [fs1''|] eqn:Hfs1''; last first.
    { apply map_included_subseteq_inv in Hle1.
      rewrite Hfs1'' in Hfs1'. simpl in Hfs1'. subst.
      apply map_disjoint_dom. set_solver. }
    destruct (ls_map δ !! ζ2) as [fs2''|] eqn:Hfs2''; last first.
    { apply map_included_subseteq_inv in Hle2.
      rewrite Hfs2'' in Hfs2'. simpl in Hfs2'. subst.
      apply map_disjoint_dom. set_solver. }
    simplify_eq; simpl in *.
    specialize (Hdisj ζ1 ζ2 fs1'' fs2'' Hneq Hfs1'' Hfs2'').
    apply map_disjoint_spec.
    rewrite map_disjoint_spec in Hdisj.
    intros i x y HSome1' HSome2'.
    rewrite map_included_spec in Hle1.
    apply Hle1 in HSome1' as (?&?&?).
    rewrite map_included_spec in Hle2.
    apply Hle2 in HSome2' as (?&?&?).
    rewrite Hfs1'' in H0. rewrite Hfs2'' in H2. simpl in H0, H2.  
    by eapply Hdisj.
  Qed.
  Next Obligation.
    intros ζ ρs δ ρ Hlive.
    simpl in *.
    pose proof Hlive as Hlive'.
    apply (ls_map_live δ) in Hlive as (ζ' & fs & HSome & Hdom).
    destruct (decide (ζ = ζ')) as [<-|Hneq].
    - eexists ζ, _.
      rewrite lookup_alter. rewrite HSome. simpl.
      split; [done|].
      rewrite map_filter_or.
      rewrite dom_union_L.
      apply elem_of_union. left.
      apply elem_of_dom.
      apply elem_of_dom in Hdom as [f Heq]. exists f.
      by apply map_lookup_filter_Some_2.
    - eexists ζ', fs. by rewrite lookup_alter_ne.
  Qed.

  Definition decr_fuel_map (fs : gmap (fmrole M) nat) : gmap (fmrole M) nat :=
    (λ f, f - 1) <$> fs.

  Lemma decr_fuel_map_included fs : map_included (≤) (decr_fuel_map fs) fs.
  Proof.
    apply map_included_spec. intros k v1 Hm.
    apply lookup_fmap_Some in Hm as [v2 [Hv2 Hm]].
    exists v2. split; [done|lia].
  Qed.

  Program Definition model_update_decr (ζ : locale Λ) (δ : LM) : LM :=
    {|
      ls_data :=
        {| ls_under := δ.(ls_under);
           ls_map := alter (fmap (λ f, f - 1)) ζ δ.(ls_map); |};
    |}.
  Next Obligation.
    intros ζ δ ζ1 ζ2 fs1 fs2 Hneq HSome1 HSome2.
    simpl in *.
    pose proof δ.(ls_map_disj) as Hdisj.
    assert (∃ fs1', map_included (≤) fs1 fs1' ∧ ls_map δ !!! ζ1 = fs1')
      as (fs1' & Hle1 & Hfs1').
    { destruct (decide (ζ = ζ1)) as [<-|Hneq'].
      + rewrite lookup_alter in HSome1.
        rewrite -lookup_fmap in HSome1.
        apply lookup_fmap_Some in HSome1 as (fs1'&Hfs1'&HSome1').
        simplify_eq.
        exists fs1'. rewrite lookup_total_alt. simpl. rewrite HSome1'.
        split; [apply decr_fuel_map_included|done].
      + rewrite lookup_alter_ne in HSome1; [|done].
        rewrite lookup_total_alt. eexists _.
        split; [done|by rewrite HSome1]. }
    assert (∃ fs2', map_included (≤) fs2 fs2' ∧ ls_map δ !!! ζ2 = fs2')
      as (fs2' & Hle2 & Hfs2').
    { destruct (decide (ζ = ζ2)) as [<-|Hneq'].
      + rewrite lookup_alter in HSome2.
        rewrite -lookup_fmap in HSome2.
        apply lookup_fmap_Some in HSome2 as (fs2'&Hfs2'&HSome2').
        simplify_eq.
        exists fs2'. rewrite lookup_total_alt. simpl. rewrite HSome2'.
        split; [apply decr_fuel_map_included|done].
      + rewrite lookup_alter_ne in HSome2; [|done].
        rewrite lookup_total_alt. eexists _.
        split; [done|by rewrite HSome2]. }
    rewrite lookup_total_alt in Hfs1'.
    rewrite lookup_total_alt in Hfs2'.
    destruct (ls_map δ !! ζ1) as [fs1''|] eqn:Hfs1''; last first.
    { apply map_included_subseteq_inv in Hle1.
      apply map_disjoint_dom.
      rewrite Hfs1'' in Hfs1'. simpl in Hfs1'.
      subst. set_solver. }
    destruct (ls_map δ !! ζ2) as [fs2''|] eqn:Hfs2''; last first.
    { apply map_included_subseteq_inv in Hle2.
      apply map_disjoint_dom. 
      rewrite Hfs2'' in Hfs2'. simpl in Hfs2'.
      subst. set_solver. }
    simplify_eq; simpl in *.
    specialize (Hdisj ζ1 ζ2 fs1'' fs2'' Hneq Hfs1'' Hfs2'').
    apply map_disjoint_spec.
    rewrite map_disjoint_spec in Hdisj.
    intros i x y HSome1' HSome2'.
    rewrite map_included_spec in Hle1.
    apply Hle1 in HSome1' as (?&?&?).
    rewrite map_included_spec in Hle2.
    apply Hle2 in HSome2' as (?&?&?).
    rewrite Hfs1'' in H0. rewrite Hfs2'' in H2. simpl in H0, H2.  
    eapply Hdisj; eauto. 
  Qed.
  Next Obligation.
    intros ζ δ ρ Hlive.
    simpl in *.
    pose proof Hlive as Hlive'.
    apply (ls_map_live δ) in Hlive as (ζ' & fs & HSome & Hdom).
    destruct (decide (ζ = ζ')) as [<-|Hneq].
    - eexists ζ, _.
      rewrite lookup_alter. rewrite HSome. simpl.
      split; [done|].
      rewrite dom_fmap. done.
    - eexists ζ', fs. by rewrite lookup_alter_ne.
  Qed.

  Definition map_inner_disj `{Countable K1} `{Countable K2} {V}
             (m : gmap K1 (gmap K2 V)) :=
    ∀ (k1 k2 : K1) (vs1 vs2 : gmap K2 V),
      k1 ≠ k2 → m !! k1 = Some vs1 → m !! k2 = Some vs2 → vs1 ##ₘ vs2.

  Lemma decr_succ_compose_id : (λ f : nat, f - 1) ∘ S = id.
  Proof. apply FunExt. intros x. simpl. lia. Qed.

  Lemma fuel_map_le_disj' ζ1 ζ2 fm fs1 fs2 fs1' fs2' ρ
        (fuel_map : gmap (locale Λ) (gmap (fmrole M) nat)) :
    fuel_map_le_inner fm fuel_map → map_inner_disj fuel_map →
    fm !! ζ1 = Some fs1 → fm !! ζ2 = Some fs2 →
    fuel_map !! ζ1 = Some fs1' → fuel_map !! ζ2 = Some fs2' →
    ρ ∈ dom fs1' → ρ ∈ dom fs2' →
    ζ1 = ζ2 ∧ fs1 = fs2.
  Proof.
    intros Hle Hdisj HSome1 HSome2 HSome1' HSome2'
           [f1 Hf1]%elem_of_dom [f2 Hf2]%elem_of_dom.
    destruct (decide (ζ1 = ζ2)) as [->|Hneq].
    { simplify_eq. set_solver. }
    rewrite /fuel_map_le_inner map_included_spec in Hle.
    exfalso. rewrite /map_inner_disj in Hdisj.
    specialize (Hdisj ζ1 ζ2 fs1' fs2' Hneq HSome1' HSome2').
    rewrite map_disjoint_spec in Hdisj. by eapply Hdisj.
  Qed.

  (* TODO: Clean up *)
  Lemma fuel_map_le_live_roles fm fm' (lρs : gset (fmrole M)) ζ ρs ρs' ρ :
    map_inner_disj fm' → fuel_map_le_inner fm fm' →
    fuel_map_preserve_dead fm lρs →
    fm !! ζ = Some ρs → fm' !! ζ = Some ρs' →
    ρ ∈ lρs → ρ ∈ dom ρs' →
    ρ ∈ dom ρs.
  Proof.
    intros Hdisj Hfmle Hfmdead Hρ Hρs' Hlive [f Hf]%elem_of_dom.
    rewrite /fuel_map_le_inner map_included_spec in Hfmle.
    apply Hfmdead in Hlive as (ζ'&fs'&Hfs'&Hv2').
    assert (dom ρs = dom fs') as Heq.
    { f_equiv. pose proof Hfs' as Hfs''. apply Hfmle in Hfs'' as (fs''&?&Hfs'').
      eapply (fuel_map_le_disj' ζ ζ' fm ρs fs' ρs' fs'' ρ
                                fm'); try done.
      - rewrite /fuel_map_le_inner map_included_spec. apply Hfmle.
      - by apply elem_of_dom.
      - rewrite map_included_spec in Hfs''.
        apply elem_of_dom in Hv2' as [??].
        apply Hfs'' in H1. destruct H1 as (?&?&?).
        by apply elem_of_dom. }
    set_solver.
  Qed.

  Lemma alter_insert_alt `{Countable K} {A} (m : gmap K A) i f x :
    m !! i = Some x → alter f i m = <[i := f x]> m.
  Proof.
    intros. rewrite -{1}(insert_id m i x); [|done]. apply alter_insert.
  Qed.


End model_state_lemmas.

Notation "tid ↦M R" := (has_fuels tid R) (at level 20, format "tid  ↦M  R") : bi_scope.
Notation "tid ↦M++ R" := (has_fuels_S tid R) (at level 20, format "tid  ↦M++  R") : bi_scope.

Section adequacy.
  Context `{Countable (locale Λ)}.

  Context {AM1 AM2: ActionModel}.
  Let PM := ProdAM AM1 AM2.
  Context {PROD_LR: AM_strong_lr PM}. 
  Let M := AM2FM PM PROD_LR.

  Context `{LM: LiveModel Λ M}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGpreS AM1 AM2 Σ}.

  Lemma model_state_init (s0: M) :
    ⊢ |==> ∃ γ,
        own
          (* (A := authUR (optionUR (exclR (AMO AM)))) *)
          γ
            (● (Excl' s0.1, Excl' s0.2) ⋅ ◯ (Excl' s0.1, None) ⋅ ◯ (None, Excl' s0.2)).
  Proof.
    iMod (own_alloc (● (Excl' s0.1, Excl' s0.2) ⋅ ◯ _)) as (γ) "[Hfl Hfr]".
    { by apply auth_both_valid_2. }
    iModIntro. 
    iExists _. rewrite -cmra_assoc. rewrite -auth_frag_op.
    rewrite own_op. iFrame. 
  Qed.

  Definition init_fuel_map (s0: M) (ζ0: locale Λ) :
    gmap (locale Λ) (exclR $ gmap (fmrole M) nat) :=
    {[ ζ0 := Excl (gset_to_gmap (LM.(lm_fl) s0) (M.(live_roles) s0)) ]}.

  Lemma model_fuel_mapping_init (s0: M) (ζ0: locale Λ) :
    ⊢ |==> ∃ γ,
      own γ (● (init_fuel_map s0 ζ0)) ∗
      own γ (◯ (init_fuel_map s0 ζ0)).
  Proof.
    iMod (own_alloc (● (init_fuel_map s0 ζ0) ⋅
                     ◯ (init_fuel_map s0 ζ0))) as (γ) "[Hfl Hfr]".
    { apply auth_both_valid_2; eauto. by apply singleton_valid. }
    iExists _. by iSplitL "Hfl".
  Qed.

  Lemma model_free_roles_init (s0: M) (FR: gset _):
    ⊢ |==> ∃ γ,
        own (A := authUR (gset_disjUR (RoleO PM))) γ (● GSet FR  ⋅ ◯ GSet FR).
  Proof.
    iMod (own_alloc (● GSet FR  ⋅ ◯ GSet FR)) as (γ) "[H1 H2]".
    { apply auth_both_valid_2 =>//. }
    iExists _. by iSplitL "H1".
  Qed.
End adequacy.
