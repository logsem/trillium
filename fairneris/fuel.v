From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.program_logic Require Export adequacy.
From fairneris Require Export inftraces fairness.

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

  Inductive FairLabel {FM: FairModel} :=
  | Take_step: FM.(fmrole) -> FM.(fmaction) → locale Λ -> action Λ → FairLabel
  | Silent_step: locale Λ -> action Λ → FairLabel
  | Config_step: FM.(fmconfig) → config_label Λ → FairLabel
  .
  Arguments FairLabel : clear implicits.

  Definition less (x y: option nat) :=
    match x, y with
    | Some x, Some y => x < y
    | _, _ => False
    end.

  Inductive must_decrease (ρ': M.(fmrole)) (oρ: option M.(fmrole)) (a b: LiveStateData):
    (option $ locale Λ) -> Prop :=
  | Same_tid tid (Hneqρ: Some ρ' ≠ oρ) (Hsametid: Some tid = ls_mapping a !! ρ'):
      must_decrease ρ' oρ a b (Some tid)
  | Change_tid otid (Hneqtid: ls_mapping a !! ρ' ≠ ls_mapping b !! ρ')
               (Hissome: is_Some (ls_mapping b !! ρ')):
    must_decrease ρ' oρ a b otid
  (* | Zombie otid (Hismainrole: oρ = Some ρ') (Hnotalive: ρ' ∉ live_roles _ b) (Hnotdead: ρ' ∈ dom $ ls_fuel b): *)
  (*   must_decrease ρ' oρ a b otid *)
  .

  Definition fuel_decr (tid: option $ locale Λ) (oρ: option M.(fmrole))
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
    | Take_step ρ fmact tid act =>
      M.(fmtrans) a (inl (ρ, fmact)) b
      ∧ ls_mapping a !! ρ = Some tid
      ∧ fuel_decr (Some tid) (Some ρ) a b
      ∧ fuel_must_not_incr (Some ρ) a b
      ∧ (oleq (ls_fuel b !! ρ) (Some (fuel_limit b)))
      ∧ (∀ ρ, ρ ∈ (dom $ ls_fuel b) ∖ (dom $ ls_fuel a) -> oleq (ls_fuel b !! ρ) (Some (fuel_limit b)))
      ∧ (dom $ ls_fuel b) ∖ (dom $ ls_fuel a) ⊆ live_roles _ b ∖ live_roles _ a
    | Silent_step tid act =>
      (∃ ρ, ls_mapping a !! ρ = Some tid)
      ∧ fuel_decr (Some tid) None a b
      ∧ fuel_must_not_incr None a b
      ∧ dom $ ls_fuel b ⊆ dom $ ls_fuel a
      ∧ a.(ls_under) = b.(ls_under)
    | Config_step fmact act =>
      M.(fmtrans) a (inr fmact) b
      ∧ a.(ls_map) = b.(ls_map)
      ∧ live_roles _ a = live_roles _ b
   end.

  Lemma silent_step_suff_data fl (δ: LiveState) (fs fs' fs'': gmap _ nat) ζ (oζ' : option $ locale Λ) act :
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
            ls_trans fl δ (Silent_step ζ act) δ'.
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

  Lemma model_step_suff_data fl (δ: LiveState) ρ0 fmact0 m' (fs fs': gmap _ nat) ζ act :
    fmtrans _ δ (inl (ρ0, fmact0)) m' →
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
            ls_trans fl δ (Take_step ρ0 fmact0 ζ act) δ'.
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
      lm_fl : M → nat;
      lm_ls := LiveState;
      lm_lbl := FairLabel M;
      lm_ls_trans (δ: LiveState) (ℓ: FairLabel M) := ls_trans lm_fl δ ℓ;
    }.

  Definition live_model_model `(LM : LiveModel) : Model := {|
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

  Definition labels_match `{LM:LiveModel} (pl : locale_label Λ + config_label Λ) (ℓ : LM.(lm_lbl)) : Prop :=
    match pl, ℓ with
    | inr cfg, Config_step fmcfg cfg' => cfg = cfg'
    | inl (ζ, act), Silent_step ζ' act' => ζ = ζ' ∧ act = act'
    | inl (ζ, act), Take_step ρ fmact ζ' act' => ζ = ζ' ∧ act = act'
    | _, _ => False
    end.

End fairness.

Arguments LiveState _ _ {_ _}.
Arguments LiveStateData _ _ {_ _}.
Arguments LiveModel _ _ {_ _}.
Arguments live_model_model _ {_ _ _} _.

Definition live_model_to_model Λ M `{Countable (locale Λ)} : LiveModel Λ M -> Model :=
  λ lm, live_model_model Λ lm.
Coercion live_model_to_model : LiveModel >-> Model.
Arguments live_model_to_model {_ _ _ _}.

Definition auxtrace {Λ M} `{Countable (locale Λ)} (LM: LiveModel Λ M) := trace LM.(lm_ls) LM.(lm_lbl).

Section aux_trace.
  Context `{Countable (locale Λ)} `{LM: LiveModel Λ M}.

  Definition role_enabled ρ (δ: LiveState Λ M) := ρ ∈ M.(live_roles) δ.

  Definition fair_aux ρ (auxtr: auxtrace LM): Prop  :=
    forall n, pred_at auxtr n (λ δ _, role_enabled ρ δ) ->
         ∃ m, pred_at auxtr (n+m) (λ δ ℓ, ¬role_enabled ρ δ ∨
                                            ∃ tid fmact act, ℓ = Some (Take_step ρ fmact tid act)).

  Lemma fair_aux_after ρ auxtr n auxtr':
    fair_aux ρ auxtr ->
    after n auxtr = Some auxtr' ->
    fair_aux ρ auxtr'.
  Proof.
    rewrite /fair_aux => Hfair Hafter m Hpa.
    specialize (Hfair (n+m)).
    rewrite -> (pred_at_sum _ n) in Hfair. rewrite Hafter in Hfair.
    destruct (Hfair Hpa) as (p&Hp).
    exists (p). by rewrite <-Nat.add_assoc, ->!(pred_at_sum _ n), Hafter in Hp.
  Qed.

  CoInductive auxtrace_valid: auxtrace LM -> Prop :=
  | auxtrace_valid_singleton δ: auxtrace_valid ⟨δ⟩
  | auxtrace_valid_cons (δ: LiveState Λ M) ℓ (tr: auxtrace LM):
      LM.(lm_ls_trans) δ ℓ (trfirst tr) ->
      auxtrace_valid tr →
      auxtrace_valid (δ -[ℓ]-> tr).

  Lemma auxtrace_valid_forall (tr: auxtrace LM) :
    auxtrace_valid tr ->
    ∀ n, match after n tr with
         | Some ⟨ _ ⟩ | None => True
         | Some (δ -[ℓ]-> tr') => LM.(lm_ls_trans) δ ℓ (trfirst tr')
         end.
  Proof.
    intros Hval n. revert tr Hval. induction n as [|n]; intros tr Hval;
      destruct (after _ tr) as [trn|] eqn: Heq =>//; simpl in Heq;
      simplify_eq; destruct trn =>//; inversion Hval; simplify_eq; try done.
    specialize (IHn _ H1) (* TODO *). rewrite Heq in IHn. done.
  Qed.

End aux_trace.

Ltac SS :=
  epose proof ls_fuel_dom;
  (* epose proof ls_mapping_dom; *)
  set_solver.

Definition live_tids `{Countable (locale Λ)} `{LM:LiveModel Λ M}
           (c : cfg Λ) (δ : LM.(lm_ls)) : Prop :=
  (∀ ρ ζ, ls_mapping δ !! ρ = Some ζ -> is_Some (from_locale c.1 ζ)) ∧
  ∀ ζ e, from_locale c.1 ζ = Some e -> (to_val e ≠ None) ->
         ∀ ρ, ls_mapping δ !! ρ = Some ζ → ρ ∉ M.(live_roles) δ.

Definition exaux_traces_match  `{Countable (locale Λ)} `{LM:LiveModel Λ M} :
  extrace Λ → auxtrace LM → Prop :=
  traces_match labels_match
               live_tids
               locale_step
               LM.(lm_ls_trans).

Section fairness_preserved.
  Context `{Countable (locale Λ)}.
  Context `{LM: LiveModel Λ M}.
  Implicit Type δ : LiveState Λ M.

  Lemma exaux_preserves_validity extr (auxtr : auxtrace LM):
    exaux_traces_match extr auxtr ->
    auxtrace_valid auxtr.
  Proof.
    revert extr auxtr. cofix CH. intros extr auxtr Hmatch.
    inversion Hmatch; first by constructor.
    constructor =>//. by eapply CH.
  Qed.

  Lemma exaux_preserves_termination extr (auxtr : auxtrace LM) :
    exaux_traces_match extr auxtr ->
    terminating_trace auxtr ->
    terminating_trace extr.
  Proof.
    intros Hmatch [n HNone].
    revert extr auxtr Hmatch HNone. induction n as [|n IHn]; first done.
    intros extr auxtr Hmatch HNone.
    replace (S n) with (1 + n) in HNone =>//.
    rewrite (after_sum' _ 1) in HNone.
    destruct auxtr as [s| s ℓ auxtr'];
      first by inversion Hmatch; simplify_eq; exists 1.
    simpl in HNone.
    inversion Hmatch; simplify_eq.
    apply terminating_trace_cons.
    eapply IHn =>//.
  Qed.

  Lemma traces_match_labels tid act ℓ c δ rex (raux : auxtrace LM) :
    exaux_traces_match (c -[inl (tid, act)]-> rex) (δ -[ℓ]-> raux) ->
    ((∃ ρ fmact, ℓ = Take_step ρ fmact tid act) ∨ (ℓ = Silent_step tid act)).
  Proof.
    intros Hm. inversion Hm as [|?????? Hlab]; simplify_eq.
    destruct ℓ; eauto; inversion Hlab; simplify_eq; eauto.
  Qed.

  Lemma mapping_live_role (δ: LiveState Λ M) ρ:
    ρ ∈ M.(live_roles) δ ->
    is_Some (ls_mapping (Λ := Λ) δ !! ρ).
  Proof. rewrite -elem_of_dom ls_same_doms. SS. Qed.
  Lemma fuel_live_role (δ: LiveState Λ M) ρ:
    ρ ∈ M.(live_roles) δ ->
    is_Some (ls_fuel (Λ := Λ) δ !! ρ).
  Proof. rewrite -elem_of_dom. SS. Qed.

  Local Hint Resolve mapping_live_role: core.
  Local Hint Resolve fuel_live_role: core.

  Lemma match_locale_enabled (extr : extrace Λ) (auxtr : auxtrace LM) ζ ρ:
    ρ ∈ M.(live_roles) (trfirst auxtr) →
    exaux_traces_match extr auxtr ->
    ls_mapping (trfirst auxtr) !! ρ = Some ζ ->
    locale_enabled ζ (trfirst extr).
  Proof.
    intros Hlive Hm Hloc.
    rewrite /locale_enabled. have [HiS Hneqloc] := traces_match_first _ _ _ _ _ _ Hm.
    have [e Hein] := (HiS _ _ Hloc). exists e. split; first done.
    destruct (to_val e) eqn:Heqe =>//.
    exfalso. specialize (Hneqloc ζ e Hein). rewrite Heqe in Hneqloc.
    have Hv: Some v ≠ None by []. by specialize (Hneqloc Hv ρ Hloc).
  Qed.

  Local Hint Resolve match_locale_enabled: core.
  Local Hint Resolve pred_first_trace: core.

  Definition fairness_induction_stmt ρ fm f m ζ extr (auxtr : auxtrace LM) δ c :=
      infinite_trace extr ->
       (forall ζ, fair_scheduling_ex ζ extr) ->
       fm = (f, m) ->
       exaux_traces_match extr auxtr ->
       c = trfirst extr -> δ = trfirst auxtr ->
       ls_fuel δ !! ρ = Some f ->
       ls_mapping δ !! ρ = Some ζ ->
       (pred_at extr m (λ c oζ, ¬locale_enabled ζ c ∨ ∃ act, oζ = Some (inl (ζ, act)))) ->
      ∃ M, pred_at auxtr M (λ δ ℓ, ¬role_enabled ρ δ ∨ ∃ ζ0 fmact act, ℓ = Some (Take_step ρ fmact ζ0 act)).

  Local Lemma case1 ρ f m (extr' : extrace Λ) (auxtr' : auxtrace LM) δ ℓ :
    (∀ m0 : nat * nat,
         strict lt_lex m0 (f, m)
         → ∀ (f m: nat) (ζ: locale Λ) (extr : extrace Λ) (auxtr : auxtrace LM)
             (δ : LiveState Λ M) (c : cfg Λ), fairness_induction_stmt ρ m0 f m ζ extr auxtr δ c) ->
    (ρ ∈ dom (ls_fuel (trfirst auxtr')) → oless (ls_fuel (trfirst auxtr') !! ρ) (ls_fuel δ !! ρ)) ->
    exaux_traces_match extr' auxtr' ->
    infinite_trace extr' ->
    ls_fuel δ !! ρ = Some f ->
    (∀ ζ, fair_scheduling_ex ζ extr') ->
    ∃ M0 : nat,
      pred_at (δ -[ ℓ ]-> auxtr') M0
              (λ δ0 ℓ, ¬ role_enabled ρ δ0 ∨ ∃ ζ0 fmact act, ℓ = Some (Take_step ρ fmact ζ0 act)).
    Proof.
      intros IH Hdec Hmatch Hinf Hsome Hfair.
      unfold oless in Hdec.
      simpl in *.
      rewrite -> Hsome in *.
      destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq.
      - destruct (decide (ρ ∈ live_roles M (trfirst auxtr'))) as [Hρlive'|]; last first.
        { exists 1. unfold pred_at. simpl. destruct auxtr'; eauto. }
        have [ζ' Hζ'] : is_Some (ls_mapping (trfirst auxtr') !! ρ) by eauto.

        have Hloc'en: pred_at extr' 0 (λ (c : cfg Λ) (_ : option $ ex_label Λ),
                          locale_enabled ζ' c).
        { rewrite /pred_at /= pred_first_trace. eauto. }

        have [p Hp] := (Hfair ζ' 0 Hloc'en).
        have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ (δ0 : LiveState Λ M) ℓ, ¬ role_enabled ρ δ0 ∨
                                          ∃ ζ0 fmact act, ℓ = Some (Take_step ρ fmact ζ0 act)).
        { eapply (IH (f', p) _ f' p ζ' extr' auxtr'); eauto.
          Unshelve. unfold strict, lt_lex. specialize (Hdec ltac:(by eapply elem_of_dom_2)). lia. }
        exists (1+P). rewrite !pred_at_sum. simpl. done.
      - exists 1. rewrite /pred_at /=. rewrite /role_enabled.
        destruct auxtr' =>/=; left.
        + apply not_elem_of_dom in Heq; eapply not_elem_of_weaken; last (by apply ls_fuel_dom); set_solver.
        + apply not_elem_of_dom in Heq; eapply not_elem_of_weaken; last (by apply ls_fuel_dom); set_solver.
    Qed.

    Lemma fairness_preserved_ind ρ:
      ∀ fm f m ζ (extr: extrace Λ) (auxtr: auxtrace LM) δ c,
        fairness_induction_stmt ρ fm f m ζ extr auxtr δ c.
    Proof.
      induction fm as [fm IH] using lex_ind.
      intros f m ζ extr auxtr δ c Hexinfin Hfair -> Htm -> -> Hfuel Hmapping Hexen.
      destruct extr as [|c ζ' extr'] eqn:Heq.
      { have [??] := Hexinfin 1. done. }
      have Hfair': (forall ζ, fair_scheduling_ex ζ extr').
      { intros. by eapply fair_scheduling_ex_cons. }
      destruct auxtr as [|δ ℓ auxtr']; first by inversion Htm.
      destruct (decide (ρ ∈ live_roles M δ)) as [Hρlive|]; last first.
      { exists 0. left. unfold pred_at. simpl. intros contra. eauto. }
      destruct ζ' as [[ζ' act]|cfg]; last first.
      { simplify_eq. simpl in Htm.
        inversion Htm as [|??????? Hlive ? Htrans]; simplify_eq. destruct ℓ as [| |]=>//.
        simpl in *. simplify_eq. destruct Htrans as [?[Hmap ?]].
        destruct m as [|m].
        { exfalso. rewrite /pred_at /= in Hexen. destruct Hexen as [Hlocale|]; [|naive_solver].
          destruct Hlive as [Hen Hlive].
          assert (ρ ∉ live_roles M δ); last set_solver.
          destruct (Hen _ _ Hmapping). rewrite /locale_enabled in Hlocale. naive_solver. }
        apply pred_at_S in Hexen.
        ospecialize (IH (f, m) _).
        { rewrite /strict /lt_lex. lia. }
        rewrite /fairness_induction_stmt in IH.
        odestruct (IH f m ζ extr' _ _ _ _ _ _ _ _ _ _ _ Hexen) as [M' HM']; try done.
        { by eapply infinite_cons. }
        { rewrite /ls_fuel -Hmap //. }
        { rewrite /ls_mapping -Hmap //. }
        exists (S M'). by apply pred_at_S. }
      destruct (decide (ζ = ζ')) as [Hζ|Hζ].
      - rewrite <- Hζ in *. simplify_eq.
        destruct (traces_match_labels _ _ _ _ _ _ _ Htm) as [[ρ' [? ->]]| ->]; last first.
        + inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
          unfold ls_trans in Hls.
          destruct Hls as (? & Hlsdec & Hlsincr).
          unfold fuel_decr in Hlsdec.
          have Hmustdec: must_decrease ρ None δ (trfirst auxtr') (Some ζ').
          { constructor; eauto. }
          eapply case1 =>//.
          * move=> Hinfuel; apply Hlsdec => //; first set_solver.
          * eapply infinite_cons =>//.
        + (* Three cases: *)
(*              (1) ρ' = ρ and we are done *)
(*              (2) ρ' ≠ ρ but they share the same ρ -> ρ decreases *)
(*              (3) ρ' ≠ ρ and they don't have the same tid -> *)
(*              impossible because tid and the label must match! *)
          inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
          destruct (decide (ρ = ρ')) as [->|Hρneq].
          { exists 0. right. rewrite /pred_at /=. eauto. }
          destruct Hls as (?&Hsame&Hdec&Hnotinc&_).
          rewrite -Hsame /= in Hmapping.
          have Hmustdec: must_decrease ρ (Some ρ') δ (trfirst auxtr') (Some ζ').
          { constructor; eauto; congruence. }
          (* Copy and paste begins here *)
          eapply case1 =>//; last by eauto using infinite_cons.
          intros Hinfuels. apply Hdec =>//. SS.
      - (* Another thread is taking a step. *)
        destruct (decide (ρ ∈ live_roles M (trfirst auxtr'))) as [Hρlive'|]; last first.
        { exists 1. unfold pred_at. simpl. destruct auxtr'; eauto. }
        have [ζ'' Hζ''] : is_Some (ls_mapping (trfirst auxtr') !! ρ) by eauto.
        destruct (decide (ζ = ζ'')) as [<-|Hchange].
        + have [f' [Hfuel' Hff']] : exists f', ls_fuel (trfirst auxtr') !! ρ = Some f' ∧ f' ≤ f.
          { inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
            simpl in *. destruct ℓ as [ρ0 ζ0| ζ0|]; try done.
            + destruct Hls as (?&?&?&Hnoninc&?).
              destruct Hl; simplify_eq.
              unfold fuel_must_not_incr in Hnoninc.
              have Hneq: Some ρ ≠ Some ρ0 by congruence.
              specialize (Hnoninc ρ ltac:(SS) Hneq).
              unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
              destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [|set_solver].
              eexists; split =>//. destruct Hnoninc as [Hnoninc|Hnoninc]=>//.
              apply elem_of_dom_2 in Heq. set_solver.
            + destruct Hls as (?&?&Hnoninc&?).
              destruct Hl; simplify_eq.
              unfold fuel_must_not_incr in Hnoninc.
              have Hneq: Some ρ ≠ None by congruence.
              specialize (Hnoninc ρ ltac:(SS) Hneq).
              unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
              destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [|set_solver].
              eexists; split =>//. destruct Hnoninc as [Hnoninc|Hnoninc]=>//.
              apply elem_of_dom_2 in Heq. set_solver. }

          unfold fair_scheduling_ex in *.
          have Hζ'en: pred_at extr' 0 (λ (c : cfg Λ) _, locale_enabled ζ c).
          { rewrite /pred_at /= pred_first_trace. inversion Htm; eauto. }
          destruct m as [| m'].
          { rewrite -> !pred_at_0 in Hexen. destruct Hexen as [Hexen|Hexen].
            - exfalso. apply Hexen. unfold locale_enabled. by eapply (match_locale_enabled _ _ _ _ _ Htm).
            - simplify_eq. naive_solver. }

          have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ δ0 ℓ, ¬ role_enabled ρ δ0 ∨
                            ∃ ζ0 fmact act, ℓ = Some $ Take_step ρ fmact ζ0 act).
          { eapply (IH _ _ _ m' _ extr'); eauto. by eapply infinite_cons. by inversion Htm.
            Unshelve.
            - done.
            - unfold strict, lt_lex. lia. }
          exists (1+P). rewrite !pred_at_sum. simpl. done.
        + have [f' [Hfuel' Hff']] : exists f', ls_fuel (trfirst auxtr') !! ρ = Some f' ∧ f' < f.
          { inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
              simpl in *. destruct ℓ as [ρ0 ? ζ0 ?| ζ0|]; try done.
              + destruct Hls as (?&?&Hdec&?&?).
                unfold fuel_decr in Hdec. destruct Hl; simplify_eq.
                have Hmd: must_decrease ρ (Some ρ0) δ (trfirst auxtr') (Some ζ0).
                { econstructor 2. congruence. rewrite Hζ''; eauto. }
                specialize (Hdec ρ ltac:(SS) ltac:(SS) Hmd).
                unfold oleq in Hdec. rewrite Hfuel in Hdec.
                destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [by eexists|done].
              + destruct Hls as (?&Hdec&_).
                unfold fuel_decr in Hdec. simplify_eq.
                have Hmd: must_decrease ρ None δ (trfirst auxtr') (Some ζ0).
                { econstructor 2. congruence. rewrite Hζ''; eauto. }
                specialize (Hdec ρ ltac:(SS) ltac:(SS) Hmd).
                unfold oleq in Hdec. rewrite Hfuel in Hdec.
                destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [by eexists|done]. }

          unfold fair_scheduling_ex in *.
          have: pred_at extr' 0 (λ c _, locale_enabled ζ'' c).
          { rewrite /pred_at /= pred_first_trace. inversion Htm; eauto. }
          have Hζ'en: pred_at extr' 0 (λ c _, locale_enabled ζ'' c).
          { rewrite /pred_at /= pred_first_trace. inversion Htm; eauto. }
          have [p Hp] := (Hfair' ζ'' 0 Hζ'en).
          have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ δ0 ℓ, ¬ role_enabled ρ δ0 ∨
                                          ∃ ζ0 fmact act, ℓ = Some (Take_step ρ fmact ζ0 act)).
          { eapply (IH _ _ _ p _ extr'); eauto. by eapply infinite_cons. by inversion Htm.
            Unshelve. unfold strict, lt_lex. lia. }
          exists (1+P). rewrite !pred_at_sum. simpl. done.
  Qed.

  Theorem fairness_preserved (extr: extrace Λ) (auxtr: auxtrace LM):
    infinite_trace extr ->
    exaux_traces_match extr auxtr ->
    (forall ζ, fair_scheduling_ex ζ extr) -> (forall ρ, fair_aux ρ auxtr).
  Proof.
    intros Hinfin Hmatch Hex ρ n Hn.
    unfold pred_at in Hn.
    destruct (after n auxtr) as [tr|] eqn:Heq =>//.
    setoid_rewrite pred_at_sum. rewrite Heq.
    have Hen: role_enabled ρ (trfirst tr) by destruct tr.
    have [ζ Hζ] : is_Some(ls_mapping (trfirst tr) !! ρ) by eauto.
    have [f Hfuel] : is_Some(ls_fuel (trfirst tr) !! ρ) by eauto.
    have Hex' := Hex ζ n.
    have [tr1' [Heq' Htr]] : exists tr1', after n extr = Some tr1' ∧ exaux_traces_match tr1' tr
     by eapply traces_match_after.
    have Hte: locale_enabled ζ (trfirst tr1').
    { rewrite /locale_enabled. have [HiS Hneqζ] := traces_match_first _ _ _ _ _ _ Htr.
      have [e Hein] := (HiS _ _ Hζ). exists e. split; first done.
      destruct (to_val e) eqn:Heqe =>//.
      exfalso. specialize (Hneqζ ζ e Hein). rewrite Heqe in Hneqζ.
      have HnotNull: Some v ≠ None by []. specialize (Hneqζ HnotNull ρ Hζ). done. }
    setoid_rewrite pred_at_sum in Hex'. rewrite Heq' in Hex'.
    have Hpa: pred_at extr n (λ c _, locale_enabled ζ c).
    { unfold pred_at. rewrite Heq'. destruct tr1'; eauto. }
    destruct (Hex' Hpa) as [m Hm].
    have ?: infinite_trace tr1'.
    { have Hinf := infinite_trace_after n extr Hinfin. by rewrite Heq' in Hinf. }
    eapply (fairness_preserved_ind ρ _ f m ζ _ tr); eauto.
    intros ?. by eapply fair_scheduling_ex_after.
  Qed.

  Tactic Notation "inv" open_constr(P) := match goal with
                | [H: P |- _] => inversion H; clear H; simplify_eq
                                          end.

  (* TODO: Why do we need explicit [LM] here? *)
  Definition valid_state_evolution_fairness
             (extr : execution_trace Λ) (auxtr : auxiliary_trace LM) :=
    match extr, auxtr with
    | (extr :tr[oζ]: (es, σ)), auxtr :tr[ℓ]: δ =>
        labels_match (LM:=LM) oζ ℓ ∧ LM.(lm_ls_trans) (trace_last auxtr) ℓ δ ∧
        tids_smaller es δ
    | _, _ => True
    end.

  Definition valid_lift_fairness
             (φ: execution_trace Λ -> auxiliary_trace LM -> Prop)
             (extr : execution_trace Λ) (auxtr : auxiliary_trace LM) :=
    valid_state_evolution_fairness extr auxtr ∧ φ extr auxtr.

  (* TODO: Why do we need explicit [LM] here? *)
  Lemma valid_inf_system_trace_implies_traces_match_strong
        (φ : execution_trace Λ -> auxiliary_trace LM -> Prop)
        (ψ : _ → _ → Prop)
        ex atr iex iatr progtr (auxtr : auxtrace LM):
    (forall (ex: execution_trace Λ) (atr: auxiliary_trace LM),
        φ ex atr -> live_tids (LM:=LM) (trace_last ex) (trace_last atr)) ->
    (forall (ex: execution_trace Λ) (atr: auxiliary_trace LM),
        φ ex atr -> valid_state_evolution_fairness ex atr) ->
    (∀ extr auxtr, φ extr auxtr → ψ (trace_last extr) (trace_last auxtr)) →
    exec_trace_match ex iex progtr ->
    exec_trace_match atr iatr auxtr ->
    valid_inf_system_trace φ ex atr iex iatr ->
    traces_match labels_match
                 (λ σ δ, live_tids (LM := LM) σ δ ∧ ψ σ δ)
                 locale_step
                 LM.(lm_ls_trans) progtr auxtr.
  Proof.
    intros Hφ1 Hφ2 Hφψ.
    revert ex atr iex iatr auxtr progtr. cofix IH.
    intros ex atr iex iatr auxtr progtr Hem Ham Hval.
    inversion Hval as [?? Hphi |ex' atr' c [? σ'] δ' iex' iatr' oζ ℓ Hphi [=] ? Hinf]; simplify_eq.
    - inversion Hem; inversion Ham. econstructor; eauto.
      pose proof (Hφ1 ex atr Hphi).
      split; [by simplify_eq|]. simplify_eq. by apply Hφψ.
    - inversion Hem; inversion Ham. subst.
      pose proof (valid_inf_system_trace_inv _ _ _ _ _ Hinf) as Hphi'.
      destruct (Hφ2 (ex :tr[ oζ ]: (l, σ')) (atr :tr[ ℓ ]: δ') Hphi') as (?&?&?).
      econstructor.
      + eauto.
      + eauto.
      + match goal with
        | [H: exec_trace_match _ iex' _ |- _] => inversion H; clear H; simplify_eq
        end; done.
      + match goal with
        | [H: exec_trace_match _ iatr' _ |- _] => inversion H; clear H; simplify_eq
        end; done.
      + eapply IH; eauto.
  Qed.

  (* TODO: Why do we need explicit [LM] here? *)
  Lemma valid_inf_system_trace_implies_traces_match
        (φ: execution_trace Λ -> auxiliary_trace LM -> Prop)
        ex atr iex iatr progtr (auxtr : auxtrace LM):
    (forall (ex: execution_trace Λ) (atr: auxiliary_trace LM),
        φ ex atr -> live_tids (LM:=LM) (trace_last ex) (trace_last atr)) ->
    (forall (ex: execution_trace Λ) (atr: auxiliary_trace LM),
        φ ex atr -> valid_state_evolution_fairness ex atr) ->
    exec_trace_match ex iex progtr ->
    exec_trace_match atr iatr auxtr ->
    valid_inf_system_trace φ ex atr iex iatr ->
    exaux_traces_match progtr auxtr.
  Proof.
    intros Hφ1 Hφ2.
    revert ex atr iex iatr auxtr progtr. cofix IH.
    intros ex atr iex iatr auxtr progtr Hem Ham Hval.
    inversion Hval as [?? Hphi |ex' atr' c [? σ'] δ' iex' iatr' oζ ℓ Hphi [=] ? Hinf]; simplify_eq.
    - inversion Hem; inversion Ham. econstructor; eauto.
      pose proof (Hφ1 ex atr Hphi).
      by simplify_eq.
    - inversion Hem; inversion Ham. subst.
      pose proof (valid_inf_system_trace_inv _ _ _ _ _ Hinf) as Hphi'.
      destruct (Hφ2 (ex :tr[ oζ ]: (l, σ')) (atr :tr[ ℓ ]: δ') Hphi') as (?&?&?).
      econstructor.
      + eauto.
      + eauto.
      + match goal with
        | [H: exec_trace_match _ iex' _ |- _] => inversion H; clear H; simplify_eq
        end; done.
      + match goal with
        | [H: exec_trace_match _ iatr' _ |- _] => inversion H; clear H; simplify_eq
        end; done.
      + eapply IH; eauto.
  Qed.

End fairness_preserved.

Section fuel_dec_unless.
  Context `{Countable (locale Λ)}.
  Context `{LM: LiveModel Λ Mdl}.
  Implicit Type δ : LiveState Λ Mdl.

  Definition Ul (ℓ: LM.(mlabel)) : option (fmlabel Mdl) :=
    match ℓ with
    | Take_step ρ fmact _ _ => Some (inl (ρ, fmact))
    | Config_step fmcfg _ => Some (inr fmcfg)
    | _ => None
    end.

  Definition Ψ (δ: LiveState Λ Mdl) :=
    (size $ ls_fuel δ) + [^ Nat.add map] ρ ↦ f ∈ ls_fuel δ, f.

  Lemma fuel_dec_unless (auxtr: auxtrace LM) :
    auxtrace_valid auxtr ->
    dec_unless (λ x, ls_under (ls_data x)) Ul Ψ auxtr.
  Proof.
    intros Hval n. revert auxtr Hval. induction n; intros auxtr Hval; last first.
    { edestruct (after (S n) auxtr) as [auxtrn|] eqn:Heq; rewrite Heq =>//.
      simpl in Heq;
      simplify_eq. destruct auxtrn as [|δ ℓ auxtr']=>//; last first.
      inversion Hval as [|???? Hmatch]; simplify_eq =>//.
      specialize (IHn _ Hmatch). rewrite Heq // in IHn. }
    edestruct (after 0 auxtr) as [auxtrn|] eqn:Heq; rewrite Heq =>//.
    simpl in Heq; simplify_eq. destruct auxtrn as [|δ ℓ auxtr']=>//; last first.

    inversion Hval as [|??? Htrans Hmatch]; simplify_eq =>//.
    destruct ℓ as [| tid' |];
      [left; eexists; done| right | inversion Htrans; naive_solver ].
    destruct Htrans as (Hne&Hdec&Hni&Hincl&Heq). rewrite -> Heq in *. split; last done.

    destruct (decide (dom $ ls_fuel δ = dom $ ls_fuel (trfirst auxtr'))) as [Hdomeq|Hdomneq].
    - destruct Hne as [ρ Hρtid].

      assert (ρ ∈ dom $ ls_fuel δ) as Hin by rewrite -ls_same_doms elem_of_dom //.
      pose proof Hin as Hin'. pose proof Hin as Hin''.
      apply elem_of_dom in Hin as [f Hf].
      rewrite Hdomeq in Hin'. apply elem_of_dom in Hin' as [f' Hf'].
      rewrite /Ψ -!size_dom Hdomeq.
      apply Nat.add_lt_mono_l.

      rewrite /Ψ (big_opM_delete (λ _ f, f) (ls_fuel $ ls_data (trfirst _)) ρ) //.
      rewrite (big_opM_delete (λ _ f, f) (ls_fuel  δ) ρ) //.
      apply Nat.add_lt_le_mono.
      { rewrite /fuel_decr in Hdec. specialize (Hdec ρ). rewrite Hf Hf' /= in Hdec.
        apply Hdec; [set_solver | set_solver | by econstructor]. }

      apply big_addM_leq_forall => ρ' Hρ'.
      rewrite dom_delete_L in Hρ'.
      have Hρneqρ' : ρ ≠ ρ' by set_solver.
      rewrite !lookup_delete_ne //.
      destruct (decide (ρ' ∈ dom $ ls_fuel δ)) as [Hin|Hnotin]; last set_solver.
      rewrite /fuel_must_not_incr in Hni.
      destruct (Hni ρ' ltac:(done) ltac:(done)); [done|set_solver].
    - assert (size $ ls_fuel (trfirst auxtr') < size $ ls_fuel δ).
      { rewrite -!size_dom. apply subset_size. set_solver. }
      apply Nat.add_lt_le_mono =>//.
      apply big_addM_leq_forall => ρ' Hρ'.
      destruct (Hni ρ' ltac:(set_solver) ltac:(done)); [done|set_solver].
  Qed.
End fuel_dec_unless.

Section destuttering_auxtr.
  Context `{Countable (locale Λ)}.
  Context `{LM: LiveModel Λ M}.

  (* Why is [LM] needed here? *)
  Definition upto_stutter_auxtr :=
    upto_stutter (λ x, ls_under (Λ:=Λ) (M:=M) (ls_data x)) (Ul (LM := LM)).

  Lemma can_destutter_auxtr auxtr:
    auxtrace_valid auxtr →
    ∃ mtr, upto_stutter_auxtr auxtr mtr.
  Proof.
    intros ?. eapply can_destutter.
    eapply fuel_dec_unless =>//.
  Qed.

End destuttering_auxtr.

Section upto_preserves.
  Context `{Countable (locale Λ)}.
  Context `{LM: LiveModel Λ M}.

  Lemma upto_stutter_mono' :
    monotone2 (upto_stutter_ind (λ x, ls_under (Λ:=Λ) (M:=M) (ls_data x)) (Ul (LM:=LM))).
  Proof.
    unfold monotone2. intros x0 x1 r r' IN LE.
    induction IN; try (econstructor; eauto; done).
  Qed.
  Hint Resolve upto_stutter_mono' : paco.

  Lemma upto_preserves_validity (auxtr : auxtrace LM) mtr:
    upto_stutter_auxtr auxtr mtr ->
    auxtrace_valid auxtr ->
    mtrace_valid mtr.
  Proof.
    revert auxtr mtr. pcofix CH. intros auxtr mtr Hupto Hval.
    punfold Hupto.
    induction Hupto as [| |btr str δ ????? IH].
    - pfold. constructor.
    - apply IHHupto. inversion Hval. assumption.
    - pfold; constructor=>//.
      + subst. inversion Hval as [| A B C Htrans E F ] =>//. subst. unfold ls_trans in *.
        destruct ℓ; [|done|].
        * simpl in *. simplify_eq.
          destruct Htrans as [??].
          have <- //: ls_under $ trfirst btr = trfirst str.
          destruct IH as [IH|]; last done. punfold IH. inversion IH =>//.
        * destruct Htrans as [Htrans [Hmap Hlive]].
          destruct ℓ'=>//. rewrite /= in H1. simplify_eq.
          suff -> : trfirst str = trfirst btr; first by naive_solver.
          destruct IH as [IH|]=>//.
          punfold IH. inversion IH; simplify_eq=>//.
      + right. eapply CH.
        { destruct IH =>//. }
        subst. by inversion Hval.
  Qed.

End upto_preserves.

Section upto_stutter_preserves_fairness_and_termination.
  Context `{Countable (locale Λ)}.
  Context `{LM: LiveModel Λ M}.

  Notation upto_stutter_aux := (upto_stutter (λ x, ls_under (Λ := Λ) (ls_data x)) (Ul (Λ := Λ) (LM := LM))).

  Lemma upto_stutter_mono'' : (* TODO fix this proliferation *)
    monotone2 (upto_stutter_ind (λ x, ls_under (Λ:=Λ) (M:=M) (ls_data x)) (Ul (LM:=LM))).
  Proof.
    unfold monotone2. intros x0 x1 r r' IN LE.
    induction IN; try (econstructor; eauto; done).
  Qed.
  Hint Resolve upto_stutter_mono' : paco.

  Lemma upto_stutter_fairness_0 ρ auxtr (mtr: mtrace M):
    upto_stutter_aux auxtr mtr ->
    (* role_enabled_model ρ (trfirst mtr) -> *)
    (∃ n, pred_at auxtr n (λ δ ℓ, ¬role_enabled (Λ := Λ) ρ δ ∨
                                ∃ ζ fmact act, ℓ = Some (Take_step ρ fmact ζ act))) ->
    ∃ m, pred_at mtr m (λ δ ℓ, ¬role_enabled_model ρ δ ∨ ∃ act, ℓ = Some $ inl (ρ, act)).
    Proof.
      intros Hupto (* Hre *) [n Hstep].
      revert auxtr mtr Hupto (* Hre *) Hstep.
      induction n as [|n]; intros auxtr mtr Hupto (* Hre *) Hstep.
      - punfold Hupto. inversion Hupto; simplify_eq.
        + destruct Hstep as [Hpa|[??]].
          * exists 0. left. rewrite /pred_at /=. rewrite /pred_at //= in Hpa.
          * naive_solver.
        + rewrite -> !pred_at_0 in Hstep. exists 0.
          destruct Hstep as [Hstep| [tid Hstep]].
          * rewrite /pred_at /=. destruct mtr; simpl in *; left; congruence.
          * exfalso. destruct Hstep as [? [? Hstep]].
            injection Hstep => Heq. rewrite -> Heq in *.
            unfold Ul in *. congruence.
        + rewrite -> !pred_at_0 in Hstep. exists 0.
          destruct Hstep as [Hstep| [tid Hstep]]; [left|right].
          * rewrite /pred_at //=.
          * rewrite /pred_at //=. destruct Hstep as [? [? Hstep]]. injection Hstep.
            intros Heq. simplify_eq. unfold Ul in *. naive_solver.
      - punfold Hupto. inversion Hupto as [| |?????? ?? IH ]; simplify_eq.
        + rewrite /pred_at //= in Hstep.
        + rewrite -> !pred_at_S in Hstep.
          eapply IHn; eauto.
          by pfold.
        + rewrite pred_at_S in Hstep.
          destruct ℓ' as [[ρ' act']|fmcfg].
          * destruct (decide (ρ' = ρ)).
            ** simplify_eq. exists 0. right. naive_solver.
            ** have Hw: ∀ (P: nat -> Prop), (∃ n, P (S n)) -> (∃ n, P n).
               { intros P [x ?]. by exists (S x). }
               apply Hw. setoid_rewrite pred_at_S.
               eapply IHn; eauto.
               { destruct IH as [|]; done. }
          * odestruct (IHn _ str _ Hstep) as [m Hm].
            ** inversion Hupto; simplify_eq.
               match goal with [H: upaco2 _ _ _ _ |- _] => destruct H end; [ naive_solver | done].
            ** exists (S m). by apply pred_at_S.
    Qed.

  Lemma upto_stutter_fairness (auxtr:auxtrace LM) (mtr: mtrace M):
    upto_stutter_aux auxtr mtr ->
    (∀ ρ, fair_aux ρ auxtr) ->
    (∀ ρ, fair_scheduling_mtr ρ mtr).
  Proof.
    intros Hupto Hfa ρ n Hpmod.
    unfold pred_at in Hpmod.
    destruct (after n mtr) as [mtr'|] eqn:Heq; rewrite Heq // in Hpmod.
    destruct (upto_stutter_after _ _ n Hupto Heq) as (n'&auxtr'&Heq'&Hupto').
    have Hre: role_enabled_model ρ (trfirst mtr') by destruct mtr'.
    specialize (Hfa ρ).
    have Henaux : role_enabled ρ (trfirst auxtr').
    { have HUs: ls_under (trfirst auxtr') = trfirst mtr'.
      - punfold Hupto'. by inversion Hupto'.
      - unfold role_enabled, role_enabled_model in *.
        rewrite HUs //. }
    have Hfa' := (fair_aux_after ρ auxtr n' auxtr' Hfa Heq' 0).
    have Hpredat: pred_at auxtr' 0 (λ δ _, role_enabled ρ δ).
    { rewrite /pred_at /=. destruct auxtr'; done. }
    destruct (upto_stutter_fairness_0 ρ auxtr' mtr' Hupto' (Hfa' Hpredat)) as (m&Hres).
    exists m. rewrite !(pred_at_sum _ n) Heq //.
  Qed.

  Lemma upto_stutter_finiteness auxtr (mtr: mtrace M):
    upto_stutter_aux auxtr mtr ->
    terminating_trace mtr ->
    terminating_trace auxtr.
  Proof.
    intros Hupto [n Hfin].
    have [n' ?] := upto_stutter_after_None _ _ n Hupto Hfin.
    eexists; done.
  Qed.

End upto_stutter_preserves_fairness_and_termination.
