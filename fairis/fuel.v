From stdpp Require Import option.
From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Export inftraces fairness.

Section fairness.
  Context {Λ : language}.
  Context {M: FairModel}.
  Context `{Countable (locale Λ)}.

  Record LiveStateData := MkLiveStateData {
    ls_under:> M.(fmstate);
    ls_map: gmap (locale Λ) (gmap M.(fmrole) nat);
  }.
  Record LiveState := MkLiveState {
    ls_data :> LiveStateData;

    ls_map_disj: ∀ ζ ζ' fs fs', ζ ≠ ζ' → ls_data.(ls_map) !! ζ = Some fs → ls_data.(ls_map) !! ζ' = Some fs' → fs ##ₘ fs';
    ls_map_live: ∀ ρ, ρ ∈ M.(live_roles) ls_data.(ls_under) → ∃ ζ fs, ls_data.(ls_map) !! ζ = Some fs ∧ ρ ∈ dom fs;
  }.

  Implicit Type δ : LiveState.

  Definition ls_fuel (δ: LiveStateData) : gmap M.(fmrole) nat :=
    map_fold (λ _ m fs, m ∪ fs) ∅ δ.(ls_map).
  Definition add_stuff ζ (m: gmap M.(fmrole) (locale Λ)) (rs: gset M.(fmrole)) :=
    gset_to_gmap ζ rs ∪ m.
  Definition ls_mapping (δ: LiveStateData) : gmap M.(fmrole) (locale Λ) :=
    map_fold (λ ζ fs m, add_stuff ζ m (dom fs)) (∅: gmap M.(fmrole) (locale Λ)) δ.(ls_map).

  (* Lemma ls_fuel_dom δ ρ: ρ ∈ dom $ ls_mapping δ = dom $ ls_fuel δ. *)
  Lemma dom_add_stuff ζ m rs : dom $ add_stuff ζ m rs = rs ∪ dom m.
  Proof.
    rewrite /add_stuff.
    revert m. induction rs using set_ind_L; first set_solver; intros m.
    rewrite  gset_to_gmap_union_singleton !dom_union_L dom_insert_L. set_solver.
  Qed.

  Lemma add_stuff_commute ζ1 ζ2 m s1 s2 :
    s1 ## s2 →
    add_stuff ζ2 (add_stuff ζ1 m s1) s2 = add_stuff ζ1 (add_stuff ζ2 m s2) s1.
  Proof.
    rewrite /add_stuff. intros Hdisj. rewrite !assoc. f_equal.
    rewrite map_union_comm //.
    apply map_disjoint_dom_2. rewrite !dom_gset_to_gmap //.
  Qed.
  (*TODO: why commute above and comm below? *)

  Lemma ls_same_doms δ: dom $ ls_mapping δ = dom $ ls_fuel δ.
  Proof.
    rewrite /ls_mapping /ls_fuel.
    generalize (ls_map_disj δ).
    induction δ.(ls_map) as [|ζ fs m Hnotin IH] using map_ind ; first set_solver.
    intros Hdisj.
    rewrite map_fold_insert_L //; last first.
    { intros. apply add_stuff_commute. eapply map_disjoint_dom. rewrite comm in H0. eapply Hdisj; eauto. }
    rewrite map_fold_insert_L //; last first.
    { intros. rewrite !assoc. rewrite (map_union_comm z1 z2) //. eapply Hdisj; eauto. }
    rewrite dom_add_stuff !dom_union_L.
    rewrite IH //. intros. eapply Hdisj; eauto; rewrite lookup_insert_ne //; naive_solver.
  Qed.

  Lemma ls_fuel_data ρ δ ζ fs f: δ.(ls_map) !! ζ = Some fs → fs !! ρ = Some f → ls_fuel δ !! ρ = Some f.
  Proof.
    rewrite /ls_fuel. revert ρ ζ fs f.
    generalize (ls_map_disj δ).
    induction δ.(ls_map) as [|ζ' fs' m Hnotin IH] using map_ind ; first set_solver.
    intros Hdisj ρ ζ fs f Hsome Hin.
    rewrite map_fold_insert_L //; last first.
    { intros. rewrite !assoc. rewrite (map_union_comm z1 z2) //. eapply Hdisj; eauto. }
    rewrite lookup_union_Some_raw. destruct (decide (ζ = ζ')) as [->|Hneq].
    - left. rewrite lookup_insert in Hsome. naive_solver.
    - right. rewrite lookup_insert_ne // in Hsome. split.
      + assert (fs ##ₘ fs').
        { eapply Hdisj; eauto; [rewrite lookup_insert_ne // | rewrite lookup_insert //]. }
        by eapply map_disjoint_Some_l.
      + eapply IH; eauto. intros.
        eapply Hdisj; eauto; rewrite lookup_insert_ne //; set_solver.
  Qed.

  Lemma ls_mapping_data ρ δ ζ fs: δ.(ls_map) !! ζ = Some fs → ρ ∈ dom fs → ls_mapping δ !! ρ = Some ζ.
  Proof.
    rewrite /ls_mapping. revert ρ ζ fs.
    generalize (ls_map_disj δ).
    induction δ.(ls_map) as [|ζ' fs' m Hnotin IH] using map_ind ; first set_solver.
    intros Hdisj ρ ζ fs Hsome Hin.
    rewrite map_fold_insert_L //; last first.
    { intros. apply add_stuff_commute. eapply map_disjoint_dom. rewrite comm in H0. eapply Hdisj; eauto. }
    rewrite /add_stuff.
    rewrite lookup_union_Some_raw. destruct (decide (ζ = ζ')) as [->|Hneq].
    - left. rewrite lookup_insert in Hsome. rewrite lookup_gset_to_gmap_Some. naive_solver.
    - right. rewrite lookup_insert_ne // in Hsome. split.
      + assert (fs ##ₘ fs').
        { eapply Hdisj; eauto; [rewrite lookup_insert_ne // | rewrite lookup_insert //]. }
        rewrite lookup_gset_to_gmap_None not_elem_of_dom. apply elem_of_dom in Hin as [??].
        by eapply map_disjoint_Some_l.
      + eapply IH; eauto. intros.
        eapply Hdisj; eauto; rewrite lookup_insert_ne //; set_solver.
  Qed.
  Lemma ls_mapping_data_inv ρ δ ζ: ls_mapping δ !! ρ = Some ζ → ∃ fs, δ.(ls_map) !! ζ = Some fs ∧ ρ ∈ dom fs.
  Proof.
    rewrite /ls_mapping. revert ρ ζ.
    generalize (ls_map_disj δ).
    induction δ.(ls_map) as [|ζ' fs' m Hnotin IH] using map_ind ; first set_solver.
    intros Hdisj ρ ζ Hsome.
    rewrite map_fold_insert_L // in Hsome; last first.
    { intros. apply add_stuff_commute. eapply map_disjoint_dom. rewrite comm in H0. eapply Hdisj; eauto. }
    rewrite /add_stuff in Hsome.
    rewrite lookup_union_Some_raw in Hsome. destruct Hsome as [Hsome|[Hnone Hsome]].
    - rewrite lookup_gset_to_gmap_Some in Hsome. destruct Hsome as [? ->].
      rewrite lookup_insert. naive_solver.
    - assert (∃ fs : gmap (fmrole M) nat, m !! ζ = Some fs ∧ ρ ∈ dom fs) as (fs&?&?).
      { eapply IH; eauto. intros. eapply Hdisj; eauto; rewrite lookup_insert_ne //; set_solver. }
      exists fs; split; eauto.
      rewrite lookup_insert_ne //. naive_solver.
  Qed.

  Lemma ls_fuel_dom_data ρ δ ζ fs: δ.(ls_map) !! ζ = Some fs → ρ ∈ dom fs → ρ ∈ dom $ ls_fuel δ.
  Proof.
    rewrite /ls_fuel. revert ρ ζ fs.
    generalize (ls_map_disj δ).
    induction δ.(ls_map) as [|ζ' fs' m Hnotin IH] using map_ind ; first set_solver.
    intros Hdisj ρ ζ fs Hsome Hin.
    rewrite map_fold_insert_L //; last first.
    { intros. rewrite !assoc. rewrite (map_union_comm z1 z2) //. eapply Hdisj; eauto. }
    rewrite dom_union. apply elem_of_union. destruct (decide (ζ = ζ')) as [->|Hneq].
    - left. rewrite lookup_insert in Hsome. naive_solver.
    - right. rewrite lookup_insert_ne // in Hsome. eapply IH; eauto. intros.
      eapply Hdisj; eauto; rewrite lookup_insert_ne //; set_solver.
  Qed.

  Lemma ls_fuel_data_inv ρ δ f: ls_fuel δ !! ρ = Some f → ∃ ζ fs, δ.(ls_map) !! ζ = Some fs ∧ fs !! ρ = Some f.
  Proof.
    rewrite /ls_fuel. revert ρ f.
    generalize (ls_map_disj δ).
    induction δ.(ls_map) as [|ζ' fs' m Hnotin IH] using map_ind.
    { intros ??. rewrite map_fold_empty. set_solver. }
    intros Hdisj ρ f Hin.
    rewrite map_fold_insert_L // in Hin; last first.
    { intros. rewrite !assoc. rewrite (map_union_comm z1 z2) //. eapply Hdisj; eauto. }
    rewrite lookup_union_Some_raw in Hin. destruct Hin as [Hin|[? Hin]].
    - exists ζ', fs'. rewrite lookup_insert. naive_solver.
    - assert (∃ ζ fs, m !! ζ = Some fs ∧ fs !! ρ = Some f) as [ζ [fs Hζ]].
      { apply IH; eauto.
        intros ???????. eapply Hdisj; eauto; rewrite lookup_insert_ne //; set_solver. }
      exists ζ, fs. rewrite lookup_insert_ne //. naive_solver.
  Qed.

  Lemma ls_fuel_dom_data_inv ρ δ: ρ ∈ dom $ ls_fuel δ → ∃ ζ fs, δ.(ls_map) !! ζ = Some fs ∧ ρ ∈ dom fs.
  Proof.
    rewrite /ls_fuel. revert ρ.
    generalize (ls_map_disj δ).
    induction δ.(ls_map) as [|ζ' fs' m Hnotin IH] using map_ind.
    { intros ??. rewrite map_fold_empty. set_solver. }
    intros Hdisj ρ Hin.
    rewrite map_fold_insert_L // in Hin; last first.
    { intros. rewrite !assoc. rewrite (map_union_comm z1 z2) //. eapply Hdisj; eauto. }
    rewrite dom_union in Hin. apply elem_of_union in Hin as [Hin|Hin].
    - exists ζ', fs'. rewrite lookup_insert. naive_solver.
    - assert (∃ ζ fs, m !! ζ = Some fs ∧ ρ ∈ dom fs) as [ζ [fs Hζ]].
      { apply IH; eauto.
        intros ???????. eapply Hdisj; eauto; rewrite lookup_insert_ne //; set_solver. }
      exists ζ, fs. rewrite lookup_insert_ne //. naive_solver.
  Qed.

  Lemma ls_fuel_suff δ ρ: ρ ∈ dom $ ls_fuel δ → ∃ ζ fs, δ.(ls_map) !! ζ = Some fs ∧ ρ ∈ dom fs.
  Proof.
    rewrite /ls_fuel. revert ρ.
    generalize (ls_map_disj δ).
    induction δ.(ls_map) as [|ζ' fs' m Hnotin IH] using map_ind.
    { intros ??. rewrite map_fold_empty. set_solver. }
    intros Hdisj ρ Hin.
    rewrite map_fold_insert_L // in Hin; last first.
    { intros. rewrite !assoc. rewrite (map_union_comm z1 z2) //. eapply Hdisj; eauto. }
    rewrite dom_union in Hin. apply elem_of_union in Hin as [Hin|Hin].
    - exists ζ', fs'. rewrite lookup_insert. naive_solver.
    - assert (∃ ζ fs, m !! ζ = Some fs ∧ ρ ∈ dom fs) as [ζ [fs Hζ]].
      { apply IH; eauto.
        intros ???????. eapply Hdisj; eauto; rewrite lookup_insert_ne //; set_solver. }
      exists ζ, fs. rewrite lookup_insert_ne //. naive_solver.
  Qed.


  Lemma ls_fuel_dom δ: M.(live_roles) δ.(ls_under) ⊆ dom $ ls_fuel δ.
  Proof.
    generalize (ls_map_live δ).
    induction (live_roles M δ) as [|ρ ρs Hnotin IH] using set_ind_L ; first set_solver.
    intros Hlive. apply union_subseteq; split; last first.
    { apply IH. intros. apply Hlive. set_solver. }
    apply singleton_subseteq_l. destruct (Hlive ρ ltac:(set_solver)) as (ζ&fs&Hlk&Hin).
    by eapply ls_fuel_dom_data.
  Qed.


  Lemma ls_mapping_dom (m: LiveState):
    M.(live_roles) m.(ls_under) ⊆ dom $ ls_mapping m.
  Proof. rewrite ls_same_doms. apply ls_fuel_dom. Qed.

  Inductive FairLabel {Roles} :=
  | Take_step: Roles -> locale Λ -> FairLabel
  | Silent_step: locale Λ -> FairLabel
  | Config_step: FairLabel
  .
  Arguments FairLabel : clear implicits.

  Definition less (x y: option nat) :=
    match x, y with
    | Some x, Some y => x < y
    | _, _ => False
    end.

  Inductive must_decrease (ρ': M.(fmrole)) (oρ: option M.(fmrole)) (a b: LiveStateData):
    olocale Λ -> Prop :=
  | Same_tid tid (Hneqρ: Some ρ' ≠ oρ) (Hsametid: Some tid = ls_mapping a !! ρ'):
      must_decrease ρ' oρ a b (Some tid)
  | Change_tid otid (Hneqtid: ls_mapping a !! ρ' ≠ ls_mapping b !! ρ')
               (Hissome: is_Some (ls_mapping b !! ρ')):
    must_decrease ρ' oρ a b otid
  (* | Zombie otid (Hismainrole: oρ = Some ρ') (Hnotalive: ρ' ∉ live_roles _ b) (Hnotdead: ρ' ∈ dom $ ls_fuel b): *)
  (*   must_decrease ρ' oρ a b otid *)
  .

  Definition fuel_decr (tid: olocale Λ) (oρ: option M.(fmrole))
    (a b: LiveStateData) :=
    ∀ ρ', ρ' ∈ dom $ ls_fuel a -> ρ' ∈ dom $ ls_fuel b →
          must_decrease ρ' oρ a b tid ->
          oless (ls_fuel b !! ρ') (ls_fuel a !! ρ').

  Definition fuel_must_not_incr oρ (a b: LiveStateData) :=
    ∀ ρ', ρ' ∈ dom $ ls_fuel a -> Some ρ' ≠ oρ ->
          (oleq (ls_fuel b !! ρ') (ls_fuel a !! ρ')
                ∨ (ρ' ∉ dom $ ls_fuel b ∧ ρ' ∉ M.(live_roles) a.(ls_under))).

  Lemma ls_map_agree {δ ρ ζ1 ζ2 fs1 fs2} :
    δ.(ls_map) !! ζ1 = Some fs1 →
    δ.(ls_map) !! ζ2 = Some fs2 →
    ρ ∈ dom fs1 →
    ρ ∈ dom fs2 →
    ζ1 = ζ2 ∧ fs1 = fs2.
  Proof.
    intros Hlk1 Hlk2 [??]%elem_of_dom [??]%elem_of_dom.
    destruct (decide (ζ1 = ζ2)) as [|Hneq]; first naive_solver.
    have ?:= ls_map_disj _ _ _ _ _ Hneq Hlk1 Hlk2. exfalso.
    by eapply map_disjoint_spec.
  Qed.

  Definition ls_trans (fuel_limit :  M → nat) (a: LiveStateData) ℓ (b: LiveStateData): Prop :=
    match ℓ with
    | Take_step ρ tid =>
      M.(fmtrans) a (Some ρ) b
      ∧ ls_mapping a !! ρ = Some tid
      ∧ fuel_decr (Some tid) (Some ρ) a b
      ∧ fuel_must_not_incr (Some ρ) a b
      ∧ (oleq (ls_fuel b !! ρ) (Some (fuel_limit b)))
      ∧ (∀ ρ, ρ ∈ (dom $ ls_fuel b) ∖ (dom $ ls_fuel a) -> oleq (ls_fuel b !! ρ) (Some (fuel_limit b)))
      ∧ (dom $ ls_fuel b) ∖ (dom $ ls_fuel a) ⊆ live_roles _ b ∖ live_roles _ a
    | Silent_step tid =>
      (∃ ρ, ls_mapping a !! ρ = Some tid)
      ∧ fuel_decr (Some tid) None a b
      ∧ fuel_must_not_incr None a b
      ∧ dom $ ls_fuel b ⊆ dom $ ls_fuel a
      ∧ a.(ls_under) = b.(ls_under)
    | Config_step =>
      M.(fmtrans) a None b
      ∧ fuel_decr None None a b
      ∧ fuel_must_not_incr None a b
      ∧ (∀ ρ, ρ ∈ M.(live_roles) b ∖ M.(live_roles) a -> oleq (ls_fuel b !! ρ) (Some (fuel_limit b)))
      ∧ False (* TODO: add support for config steps later! *)
    end.

  Lemma silent_step_suff_data fl (δ: LiveState) (fs fs' fs'': gmap _ nat) ζ (oζ' : option $ locale Λ) :
    δ.(ls_map) !! ζ = Some fs →
    fs ≠ ∅ →
    (∀ ρ f', fs' !! ρ = Some f' → ∃ f, fs !! ρ = Some f ∧ f' < f) →
    (∀ ρ f', fs'' !! ρ = Some f' → ∃ f, fs !! ρ = Some f ∧ f' < f) →
    (dom fs ∖ (dom fs' ∪ dom fs'') ∩ M.(live_roles) δ = ∅) →
    (dom fs' ∩ dom fs'' = ∅) →
    (∀ ζ', oζ' = Some ζ' → ζ' ∉ dom δ.(ls_map)) →
    (oζ' = None → fs'' = ∅) →
    let data' :=
          match oζ' with
          | None => δ.(ls_map)
          | Some ζ' => <[ζ' := fs'']> δ.(ls_map)
          end
    in
    let data'' := <[ζ := fs']> data' in
    ∃ δ', δ'.(ls_data) = {| ls_under := δ; ls_map := data'' |} ∧
            ls_trans fl δ (Silent_step ζ) δ'.
  Proof.
    intros Hζ Hnemp Hfs' Hfs'' Hlives Hdisj Hnlocale Hifnone data' data''.
    have Hincl' : dom fs' ⊆ dom fs.
    { intros ?[? Hin]%elem_of_dom. by apply Hfs' in Hin as [?[?%elem_of_dom_2 ?]]. }
    have Hincl'' : dom fs'' ⊆ dom fs.
    { intros ?[? Hin]%elem_of_dom. by apply Hfs'' in Hin as [?[?%elem_of_dom_2 ?]]. }
    assert (∃ δ', δ'.(ls_data) = {| ls_under := δ; ls_map := data'' |}) as [δ' Hd].
    { unshelve refine (ex_intro _ {| ls_data := {| ls_under := δ; ls_map := data'' |} |} _); last done.
      { rewrite /data'' /=. intros z1 z2 fs1 fs2 Hneq Hlk1 Hlk2. apply map_disjoint_dom_2.
        intros ρ Hin1 Hin2. destruct (decide (z1 = ζ)) as [->|Hneq1].
        - rewrite lookup_insert in Hlk1. simplify_eq. rewrite lookup_insert_ne // /data' in Hlk2.
          destruct oζ' as [ζ'|].
          + destruct (decide (z2 = ζ')) as [->|Hneq2].
            * rewrite lookup_insert in Hlk2. simplify_eq. set_solver.
            * rewrite lookup_insert_ne // in Hlk2. have ?: ρ ∈ dom fs by set_solver.
              apply Hneq. eapply ls_map_agree; eauto.
          + apply Hneq. eapply ls_map_agree; eauto.
        - rewrite lookup_insert_ne // /data' in Hlk1.
          destruct oζ' as [ζ'|].
          + destruct (decide (z1 = ζ')) as [->|Hneq2].
            * rewrite lookup_insert in Hlk1. simplify_eq.
              destruct (decide (z2 = ζ)) as [->|Hneq3].
              ** rewrite lookup_insert in Hlk2. simplify_eq. set_solver.
              ** rewrite !lookup_insert_ne // in Hlk2. specialize (Hnlocale _ ltac:(done)).
                 have ?: ρ ∈ dom fs by set_solver.
                 have ?: z2 = ζ by eapply ls_map_agree. simplify_eq.
            * rewrite lookup_insert_ne // in Hlk1.
              destruct (decide (z2 = ζ)) as [->|Hneq3].
              ** rewrite lookup_insert in Hlk2. simplify_eq.
                 have ?: ρ ∈ dom fs by set_solver.
                 apply Hneq. by eapply ls_map_agree.
              ** rewrite lookup_insert_ne // /data' in Hlk2.
                 destruct (decide (z2 = ζ')) as [->|Hneq4].
                 *** rewrite lookup_insert in Hlk2. simplify_eq.
                     apply Hneq1. eapply ls_map_agree; eauto.
                 *** rewrite lookup_insert_ne // in Hlk2.
                     have Hdone: fs1 ##ₘ fs2 by eapply (ls_map_disj δ z1 z2).
                     apply map_disjoint_dom in Hdone.
                     set_solver.
          + destruct (decide (z2 = ζ)) as [->|Hneq3].
            ** rewrite lookup_insert in Hlk2. simplify_eq.
               have ?: ρ ∈ dom fs by set_solver.
               apply Hneq. by eapply ls_map_agree.
            ** rewrite lookup_insert_ne // /data' in Hlk2.
               have Hdone: fs1 ##ₘ fs2 by eapply (ls_map_disj δ z1 z2).
               apply map_disjoint_dom in Hdone.
               set_solver. }
      { intros ρ Hlive. destruct (ls_map_live δ ρ Hlive) as (ζ0&fs0&?&?).
        destruct (decide (ζ = ζ0)) as [->|].
        - have Hin: ρ ∈ dom fs' ∪ dom fs''.
          { simpl in Hlive. simplify_eq. clear Hincl' Hincl''.
            destruct (decide (ρ ∈ dom fs' ∪ dom fs'')); [done|set_solver]. }
          apply elem_of_union in Hin as [Hin|Hin].
          + exists ζ0, fs'. rewrite lookup_insert //.
          + destruct oζ' as [ζn|]; last naive_solver.
            exists ζn, fs''. split=>//=. rewrite /data'' /data' lookup_insert_ne // ?lookup_insert //.
            intros ->. eapply Hnlocale; eauto. by eapply elem_of_dom_2.
        - exists ζ0, fs0. split; last done. rewrite /data'' /data' lookup_insert_ne // ?lookup_insert //.
          destruct oζ' as [ζn|]; last naive_solver. rewrite lookup_insert_ne //.
          intros ->. eapply Hnlocale; eauto. by eapply elem_of_dom_2. } }
    exists δ'. split; first done.
    constructor.
    { destruct (map_choose _ Hnemp) as (ρ&?&?). exists ρ. eapply ls_mapping_data; eauto.
      apply elem_of_dom. naive_solver. }
    split; [|split; [| split; [|by rewrite Hd//]]].
    - rewrite /fuel_decr /=. intros ρ' Hin Hin' Hmd.
      apply elem_of_dom in Hin as [f Hf].
      apply elem_of_dom in Hin' as [f' Hf'].
      rewrite Hf Hf' /=.
      inversion Hmd; simplify_eq.
      + symmetry in Hsametid.
        apply ls_mapping_data_inv in Hsametid as (fs0&Hmap0&Hin0).
        simplify_eq.
        apply ls_fuel_data_inv in Hf as (ζ'&fs0&?&?).
        have [??] : ζ' = ζ ∧ fs0 = fs.
        { eapply ls_map_agree; eauto. apply elem_of_dom; naive_solver. }
        simplify_eq.
        apply ls_fuel_data_inv in Hf' as (ζ2&fs2&Hmap'&Hfs2).
        rewrite Hd /= /data'' in Hmap'. destruct (decide (ζ = ζ2)) as [->|Hneq].
        { rewrite lookup_insert in Hmap'. simplify_eq.
          destruct (Hfs' _ _ Hfs2). naive_solver. }
        rewrite lookup_insert_ne // /data' in Hmap'. destruct (oζ') as [ζn|].
        * destruct (decide (ζn = ζ2)) as [->|Hneqζ].
            ** rewrite lookup_insert in Hmap'. simplify_eq.
               destruct (Hfs'' _ _ Hfs2). naive_solver.
            ** rewrite lookup_insert_ne // in Hmap'.
              have [??] : ζ2 = ζ ∧ fs2 = fs; last by simplify_eq.
              eapply ls_map_agree; eauto. apply elem_of_dom; naive_solver.
        * have [??] : ζ2 = ζ ∧ fs2 = fs; last by simplify_eq.
          eapply ls_map_agree; eauto. apply elem_of_dom; naive_solver.
      + destruct Hissome as [ζ0 Hlk0].
        rewrite Hlk0 in Hneqtid.
        apply ls_fuel_data_inv in Hf as (ζ'&fs0&?&?).
        apply ls_fuel_data_inv in Hf' as (ζ2&fs2&Hmap'&Hfs2).
        apply ls_mapping_data_inv in Hlk0 as (fs3&Hmap3&Hdom3).
        have [??] : ζ0 = ζ2 ∧ fs3 = fs2.
        { eapply ls_map_agree; eauto. apply elem_of_dom; naive_solver. }
        simplify_eq.
        rewrite Hd /data'' /= in Hmap'. destruct (decide (ζ2 = ζ)); first simplify_eq.
        * rewrite lookup_insert in Hmap'. symmetry in Hmap'. simplify_eq.
          destruct (Hfs' _ _ Hfs2) as (?&?&?). exfalso; apply Hneqtid.
          rewrite (ls_mapping_data ρ' δ ζ fs) in Hneqtid; [done|done|apply elem_of_dom; naive_solver].
        * rewrite lookup_insert_ne // /data' in Hmap'. destruct oζ' as [ζn|]. destruct (decide (ζ2 = ζn)).
          ** simplify_eq. rewrite lookup_insert in Hmap'. simplify_eq.
             destruct (Hfs'' _ _ Hfs2) as (ff&?&?).
             have [??] : ζ' = ζ ∧ fs0 = fs; last by simplify_eq.
             eapply ls_map_agree; eauto; apply elem_of_dom; naive_solver.
          ** rewrite lookup_insert_ne // in Hmap'. exfalso; apply Hneqtid.
             rewrite (ls_mapping_data ρ' δ ζ2 fs2) in Hneqtid; done.
          ** have [??] : ζ' = ζ2 ∧ fs0 = fs2; last simplify_eq.
             { eapply ls_map_agree; eauto; apply elem_of_dom; naive_solver. }
             exfalso; apply Hneqtid.
             eapply ls_mapping_data; eauto.
    - rewrite /fuel_must_not_incr. intros ρ' Hin' _.
      apply elem_of_dom in Hin' as [f Hf]. rewrite Hf.
      apply ls_fuel_data_inv in Hf as (ζ'&fs0&Hmap&Hlk).
      destruct (decide (ζ' = ζ)) as [->|].
      + have ? : fs0 = fs by naive_solver. simplify_eq.
        destruct (decide (ρ' ∈ dom fs' ∪ dom fs'')) as [[Hin|Hin]%elem_of_union|Hnin].
        * left. apply elem_of_dom in Hin as [f' Hlk'].
          destruct (Hfs' _ _ Hlk') as (?&?&?).
          have -> /= : ls_fuel δ' !! ρ' = Some f'.
          { eapply (ls_fuel_data _ _ ζ); eauto. rewrite Hd /data'' /= lookup_insert //. }
          naive_solver lia.
        * left. apply elem_of_dom in Hin as [f' Hlk'].
          destruct (Hfs'' _ _ Hlk') as (?&?&?).
          have -> /= : ls_fuel δ' !! ρ' = Some f'.
          destruct oζ' as [ζn|]; last set_solver.
          { eapply (ls_fuel_data _ _ ζn); eauto.
            rewrite Hd /data'' /= lookup_insert_ne // /data' ?lookup_insert //.
            intros ->. eapply Hnlocale; eauto. by eapply elem_of_dom_2. }
          naive_solver lia.
        * have Hdead: ρ' ∉ live_roles _ δ.
          { eapply elem_of_dom_2 in Hlk. set_solver. }
          right. split; last done. intros Habs. apply ls_fuel_dom_data_inv in Habs as (ζa&fsa&Hlka&Hina).
          rewrite Hd /data'' /= in Hlka.
          destruct (decide (ζa = ζ)).
          { simplify_eq. rewrite lookup_insert in Hlka. simplify_eq. set_solver. }
          rewrite lookup_insert_ne // /data' in Hlka.
          destruct oζ' as [ζn|].
          ** destruct (decide (ζa = ζn)).
             { simplify_eq. rewrite lookup_insert in Hlka. simplify_eq. set_solver. }
             rewrite lookup_insert_ne // in Hlka.
             have [??] : ζ = ζa ∧ fs = fsa; last done.
             eapply ls_map_agree; eauto; apply elem_of_dom; naive_solver.
          ** have [??] : ζ = ζa ∧ fs = fsa; last done.
             eapply ls_map_agree; eauto; apply elem_of_dom; naive_solver.
      + left. have ->: ls_fuel δ' !! ρ' = Some f; last naive_solver.
        eapply (ls_fuel_data _ _ ζ'); eauto.
        rewrite Hd /data'' /= lookup_insert_ne // /data'. destruct oζ' as [ζn|]; last done.
        rewrite lookup_insert_ne //. intros ->. apply (Hnlocale ζ'); eauto.
        by eapply elem_of_dom_2.
    - intros ρ Hin. apply ls_fuel_dom_data_inv in Hin as (ζ0&fs0&Hlk0&Hin0).
      rewrite Hd /data'' /= in Hlk0. destruct (decide (ζ0 = ζ)) as [->|].
      + rewrite lookup_insert in Hlk0. simplify_eq. eapply ls_fuel_dom_data; eauto.
      + rewrite lookup_insert_ne // /data' in Hlk0.
        destruct oζ' as [ζn|].
        * destruct (decide (ζ0 = ζn)) as [->|].
          ** rewrite lookup_insert in Hlk0. simplify_eq. eapply ls_fuel_dom_data; eauto.
          ** rewrite lookup_insert_ne // /data' in Hlk0. eapply ls_fuel_dom_data; eauto.
        * eapply ls_fuel_dom_data; eauto.
  Qed.

  Lemma model_step_suff_data fl (δ: LiveState) ρ0 m' (fs fs': gmap _ nat) ζ :
    fmtrans _ δ (Some ρ0) m' →
    δ.(ls_map) !! ζ = Some fs →
    ρ0 ∈ dom fs →
    (∀ ρ f f', fs' !! ρ = Some f' → ρ ≠ ρ0 → fs !! ρ = Some f → f' < f) →
    (∀ f'0, fs' !! ρ0 = Some f'0 → f'0 ≤ fl m') →
    (∀ ρ, ρ ∈ dom fs' ∖ dom fs → ∀ f', fs' !! ρ = Some f' → f' ≤ fl m') →
    (M.(live_roles) m' ∖ M.(live_roles) δ = dom fs' ∖ dom fs) →
    (∀ ρ, ρ ∈ M.(live_roles) m' ∖ M.(live_roles) δ → ∀ ζ' fs', δ.(ls_map) !! ζ' = Some fs' → ρ ∉ dom fs') →
    (dom fs ∖ dom fs' ∩ M.(live_roles) δ = ∅) →
    let data' := <[ζ := fs']> δ.(ls_map) in
    ∃ δ', δ'.(ls_data) = {| ls_under := m'; ls_map := data' |} ∧
            ls_trans fl δ (Take_step ρ0 ζ) δ'.
  Proof.
    intros Htrans Hζ Hρ0in Hfs' Hfl0 Hfln Hborn Hnew Hdead data'.
    assert (∃ δ', δ'.(ls_data) = {| ls_under := m'; ls_map := data' |}) as [δ' Hd].
    { unshelve refine (ex_intro _ {| ls_data := {| ls_under := m'; ls_map := data' |} |} _); last done.
      { rewrite /data' /=. intros z1 z2 fs1 fs2 Hneq Hlk1 Hlk2. apply map_disjoint_dom_2.
        intros ρ Hin1 Hin2.
        destruct (decide (z1 = ζ)) as [->|Hneq1]; destruct (decide (z2 = ζ)) as [->|Hneq2] =>//.
        - rewrite lookup_insert in Hlk1. rewrite lookup_insert_ne // in Hlk2. simplify_eq.
          destruct (decide (ρ ∈ dom fs)).
          + have Hdone: fs ##ₘ fs2 by eapply (ls_map_disj δ ζ z2).
            apply map_disjoint_dom in Hdone. set_solver.
          + have Hdone: ρ ∉ dom fs2; last done. eapply Hnew. set_solver. done.
        - rewrite lookup_insert in Hlk2. rewrite lookup_insert_ne // in Hlk1. simplify_eq.
          destruct (decide (ρ ∈ dom fs)).
          + have Hdone: fs ##ₘ fs1 by eapply (ls_map_disj δ ζ z1).
            apply map_disjoint_dom in Hdone. set_solver.
          + have Hdone: ρ ∉ dom fs1; last done. eapply Hnew. set_solver. done.
        - rewrite lookup_insert_ne // in Hlk1. rewrite lookup_insert_ne // in Hlk2.
          have Hdone: fs1 ##ₘ fs2 by eapply (ls_map_disj δ z1 z2).
          apply map_disjoint_dom in Hdone. set_solver. }
      { simpl. intros ρ Hlive. destruct (decide (ρ ∈ live_roles _ δ)) as [Hwaslive|Hnewborn].
        - destruct (ls_map_live δ ρ Hwaslive) as (ζ'&fs''&Hlk&Hdom). destruct (decide (ζ = ζ')).
          + simplify_eq. exists ζ', fs'. rewrite lookup_insert. split; first done. set_solver.
          + exists ζ', fs''. rewrite lookup_insert_ne //.
        - exists ζ, fs'. rewrite lookup_insert. split; first done. set_solver. } }
    have H0live: ρ0 ∈ live_roles _ δ by eapply fm_live_spec.
    have Hζ' : ls_map δ' !! ζ = Some fs' by rewrite Hd lookup_insert //.
    exists δ'. split; first done. constructor; first by rewrite Hd //.

    have Hdom: dom (ls_fuel δ') ∖ dom (ls_fuel δ) ⊆ live_roles M δ' ∖ live_roles M δ.
    { intros ρ [Hin Hnin]%elem_of_difference. rewrite Hd Hborn.
      apply elem_of_dom in Hin as [f' Hin].
      apply ls_fuel_data_inv in Hin as (ζ1&fs1&Hlk1&Hlk'1).
      destruct (decide (ζ1 = ζ)); first simplify_eq; last first.
      { rewrite Hd lookup_insert_ne // in Hlk1. exfalso. apply Hnin.
        eapply ls_fuel_dom_data=>//. by apply elem_of_dom_2 in Hlk'1. }
      apply elem_of_difference. split; first by apply elem_of_dom_2 in Hlk'1.
      intros Hina. apply Hnin. eapply ls_fuel_dom_data=>//. }

    split; [| split; [| split; [| split; [| split; [| done]]]]].
    - eapply ls_mapping_data =>//.
    - intros ρ Hin Hin' Hmd.
      apply elem_of_dom in Hin as [f Hf].
      apply elem_of_dom in Hin' as [f' Hf'].
      rewrite Hf Hf' /=. inversion Hmd; simplify_eq.
      + symmetry in Hsametid. apply ls_mapping_data_inv in Hsametid as (fs1&Hlk1&Hin1).
        rewrite Hζ in Hlk1. symmetry in Hlk1. simplify_eq.
        apply ls_fuel_data_inv in Hf as (ζ1&fs1&Hlk1&Hlk'1).
        have [??] : ζ1 = ζ ∧ fs1 = fs; last simplify_eq.
        { eapply (ls_map_agree (ρ := ρ) Hlk1); eauto. by apply elem_of_dom_2 in Hlk'1. }

        apply ls_fuel_data_inv in Hf' as (ζ2&fs2&Hlk2&Hlk'2).
        destruct (decide (ζ2 = ζ)); last first.
        { rewrite Hd lookup_insert_ne // in Hlk2.
        have [??] : ζ2 = ζ ∧ fs2 = fs; last simplify_eq.
        eapply (ls_map_agree (ρ := ρ) Hlk2); eauto. by apply elem_of_dom_2 in Hlk'2. }
        simplify_eq. eapply Hfs'=>//. naive_solver.
      + exfalso. destruct Hissome as [ζ1 Hmap]. have Hmap' := Hmap.
        apply ls_mapping_data_inv in Hmap as (fs1&Hlk&YHin).
        destruct (decide (ζ1 = ζ)) as [->|].
        * simplify_eq. have ?: ρ ∈ dom fs.
          { apply ls_fuel_data_inv in Hf as (ζ1&fs1&Hlk1&Hlk'1).
            destruct (decide (ρ ∈ dom fs)); first done. exfalso.
            eapply Hnew; eauto; last by apply elem_of_dom_2 in Hlk'1.
            rewrite Hborn. set_solver. }
          apply Hneqtid. rewrite Hmap'. by eapply ls_mapping_data.
        * apply Hneqtid. rewrite Hmap'.
          eapply ls_mapping_data=>//.
          rewrite Hd lookup_insert_ne // in Hlk.
    - intros ρ Hin Hneq. apply ls_fuel_dom_data_inv in Hin as (ζ1&fs1&Hlk1&Hdom1).
      destruct (decide (ζ1 = ζ)).
      + simplify_eq. destruct (decide (ρ ∈ dom fs')) as [Hin|]; [left| right; split; [|set_solver]].
        * apply elem_of_dom in Hin as [f' Hf'].
          have ->: ls_fuel δ' !! ρ = Some f' by eapply ls_fuel_data.
          apply elem_of_dom in Hdom1 as [f Hf].
          have -> /=: ls_fuel δ !! ρ = Some f by eapply ls_fuel_data.
          naive_solver lia.
        * intros Ha. apply ls_fuel_dom_data_inv in Ha as (ζ1&fs1&Hlk1&Hin1).
          destruct (decide (ζ1 = ζ)) as [|Hneq1]; first naive_solver.
          rewrite Hd lookup_insert_ne // in Hlk1. apply Hneq1.
          by eapply ls_map_agree.
      + left. apply elem_of_dom in Hdom1 as (f'&Hf').
        have ->: ls_fuel δ' !! ρ = Some f'.
        { eapply (ls_fuel_data _ _ ζ1); eauto. rewrite Hd lookup_insert_ne //. }
        have ->: ls_fuel δ !! ρ = Some f'.
        { eapply (ls_fuel_data _ _ ζ1); eauto. }
        naive_solver.
    - intros. have H0dom: ρ0 ∈ dom fs' by set_solver. apply elem_of_dom in H0dom as [f' Hf'].
      rewrite (ls_fuel_data _ _ _ _ _ Hζ' Hf') Hd /=. by eapply Hfl0.
    - intros ρ [Hρin Hρnin]%elem_of_difference.
      have Hn: ρ ∈ dom fs' ∖ dom fs.
      { rewrite -Hborn. rewrite elem_of_subseteq {2}Hd /= in Hdom. apply Hdom. set_solver. }
      apply elem_of_dom in Hρin as [f' Hρin]. rewrite Hρin.
      apply ls_fuel_data_inv in Hρin as (ζ1&fs1&Hlk1&Hlk'1). simpl. rewrite Hd /=.
      apply elem_of_difference in Hn as [Hn1 Hn2].
      have [??] : ζ1 = ζ ∧ fs1 = fs'.
      { eapply ls_map_agree=>//. by apply elem_of_dom_2 in Hlk'1. }
      simplify_eq. eapply Hfln; last done. by apply elem_of_difference.
  Qed.

  Record LiveModel := {
      lm_flm: nat;
      lm_fl := fun _ => lm_flm;
      lm_ls := LiveState;
      lm_lbl := FairLabel M.(fmrole);
      lm_ls_trans (δ: LiveState) (ℓ: FairLabel (fmrole M)) := ls_trans lm_fl δ ℓ;
    }.

  Definition fair_model_model `(LM : LiveModel) : Model := {|
    mstate := lm_ls LM;
    mlabel := lm_lbl LM;
    mtrans := lm_ls_trans LM;
  |}.

  Definition tids_smaller (c : list (expr Λ)) (δ: LiveState) :=
    ∀ ζ, ζ ∈ dom $ ls_map δ -> is_Some (from_locale c ζ).

  Program Definition initial_ls `{LM: LiveModel} (s0: M) (ζ0: locale Λ)
    : LM.(lm_ls) :=
    {| ls_data := {| ls_under := s0;
      ls_map := {[ζ0 := gset_to_gmap (LM.(lm_fl) s0) (M.(live_roles) s0)]};
    |} |}.
  Next Obligation.
    intros ???????? Hlk1 Hlk2. simpl in *. exfalso.
    apply lookup_singleton_Some in Hlk1.
    apply lookup_singleton_Some in Hlk2.
    naive_solver.
  Qed.
  Next Obligation.
    intros ?? ζ ??. eexists ζ, _. rewrite lookup_singleton. split; eauto.
    rewrite dom_gset_to_gmap //.
  Qed.

  Definition labels_match `{LM:LiveModel} (oζ : olocale Λ) (ℓ : LM.(lm_lbl)) : Prop :=
    match oζ, ℓ with
    | None, Config_step => True
    | Some ζ, Silent_step ζ' => ζ = ζ'
    | Some ζ, Take_step ρ ζ' => ζ = ζ'
    | _, _ => False
    end.

End fairness.

Arguments LiveState _ _ {_ _}.
Arguments LiveStateData _ _ {_ _}.
Arguments LiveModel _ _ {_ _}.
Arguments fair_model_model _ {_ _ _} _.

Definition live_model_to_model Λ M `{Countable (locale Λ)} : LiveModel Λ M -> Model :=
  λ lm, fair_model_model Λ lm.
Coercion live_model_to_model : LiveModel >-> Model.
Arguments live_model_to_model {_ _ _ _}.

(* TODO: Why do we need explicit [LM] here? *)
Definition valid_state_evolution_fairness `{Countable (locale Λ)} `{LM: LiveModel Λ M}
  (extr : execution_trace Λ) (auxtr : auxiliary_trace LM) :=
  match extr, auxtr with
  | (extr :tr[oζ]: (es, σ)), auxtr :tr[ℓ]: δ =>
      labels_match (LM:=LM) oζ ℓ ∧ LM.(lm_ls_trans) (trace_last auxtr) ℓ δ ∧
      tids_smaller es δ
  | _, _ => True
  end.

Definition valid_lift_fairness `{Countable (locale Λ)} `{LM: LiveModel Λ M}
  (φ: execution_trace Λ -> auxiliary_trace LM -> Prop)
  (extr : execution_trace Λ) (auxtr : auxiliary_trace LM) :=
  valid_state_evolution_fairness extr auxtr ∧ φ extr auxtr.

