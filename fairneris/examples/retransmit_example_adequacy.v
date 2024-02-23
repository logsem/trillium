From stdpp Require Import list fin_maps.
From iris.proofmode Require Import proofmode.
From trillium.program_logic Require Import ectx_lifting.
From fairneris Require Import fairness.
From fairneris.examples Require Import retransmit_model.
From fairneris.aneris_lang Require Import aneris_lang.
From fairneris.aneris_lang.state_interp Require Import state_interp state_interp_events.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From fairneris.aneris_lang Require Import aneris_lang adequacy.
From fairneris Require Import retransmit_example.

From fairneris.lib Require Import singletons.

Definition initial_state shA shB :=
  ([mkExpr ipA (Aprog shA); mkExpr ipB (Bprog shB)],
     {| state_heaps := {[ipA:=∅; ipB:=∅]};
        state_sockets := {[ipA := {[shA := (sA, [])]};
                           ipB := {[shB := (sB, [])]}]};
        state_ms := ∅; |}).

Definition initial_model_state : retransmit_state :=
  (retransmit_model.Start, ∅, ∅).

Lemma retransmit_continued_simulation shA shB :
  fairly_terminating localeB (initial_state shA shB).
Proof.
  assert (anerisPreG retransmit_fair_model (anerisΣ retransmit_fair_model)) as HPreG.
  { apply _. }
  eapply (simulation_adequacy_fair_termination_multiple {[saA;saB]} NotStuck _ _ initial_model_state);
    [| |simpl; lia|set_solver|..|done|]=> /=.
  { intros ℓ ζ Hmatch Henabled. rewrite /role_enabled_model in Henabled. simpl.
    assert (ℓ = Arole ∨ ℓ = Brole) as [Heq|Heq] by set_solver; simplify_eq.
    - assert (ζ = ("0.0.0.0", 0%nat)) as ->.
      { rewrite /roles_match /locale_retransmit_role in Hmatch.
        by repeat case_match; simplify_eq. }
      eexists _. simpl. done.
    - assert (ζ = ("0.0.0.1", 0%nat)) as ->.
      { rewrite /roles_match /locale_retransmit_role in Hmatch.
        by repeat case_match; simplify_eq. }
      eexists _. simpl. done. }
  { rewrite /config_state_valid. simpl. split; [done|].
    rewrite /model_state_socket_coh.
    intros.
    (* OBS: Might be able to make this simpler with a total lookup *)
    rewrite insert_union_singleton_l in H.
    apply lookup_union_Some in H; [|apply map_disjoint_dom; set_solver].
    destruct H as [H|H].
    - destruct (decide (ip = ipA)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in H. }
      rewrite lookup_insert in H.
      simplify_eq.
      destruct (decide (sh = shA)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in H0. }
      rewrite lookup_insert in H0.
      simplify_eq.
      assert (sa = saA) as -> by set_solver.
      set_solver.
    - destruct (decide (ip = ipB)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in H. }
      rewrite lookup_insert in H.
      simplify_eq.
      destruct (decide (sh = shB)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in H0. }
      rewrite lookup_insert in H0.
      simplify_eq.
      assert (sa = saB) as -> by set_solver.
      set_solver. }
  { intros ip ps HPs Sn Hip p Hps.
    intros sh skt a r Hsh Hskt.
    intros <-.
    assert (ports_in_use {[ipA := {[shA := (sA, [])]}; ipB := {[shB := (sB, [])]}]} = {[saA; saB]}) as Heq.
    { rewrite /ports_in_use.
      rewrite map_fold_insert_L; [by rewrite !map_fold_singleton| |set_solver].
      intros j1 j2 z1 z2 y Hneq Hz1 Hz2.
      rewrite insert_union_singleton_l in Hz1.
      apply lookup_union_Some in Hz1; last first.
      { apply map_disjoint_dom. clear. set_solver. }
      rewrite insert_union_singleton_l in Hz2.
      apply lookup_union_Some in Hz2; last first.
      { apply map_disjoint_dom. clear. set_solver. }
      destruct Hz1 as [Hz1|Hz1], Hz2 as [Hz2|Hz2].
      - apply lookup_singleton_Some in Hz1 as [<- <-].
        apply lookup_singleton_Some in Hz2 as [<- <-].
        done.
      - apply lookup_singleton_Some in Hz1 as [<- <-].
        apply lookup_singleton_Some in Hz2 as [<- <-].
        rewrite !map_fold_singleton=> /=.
        clear. rewrite !union_empty_r_L !union_assoc_L. set_solver.
      - apply lookup_singleton_Some in Hz1 as [<- <-].
        apply lookup_singleton_Some in Hz2 as [<- <-].
        rewrite !map_fold_singleton=> /=.
        clear. rewrite !union_empty_r_L !union_assoc_L. set_solver.
      - apply lookup_singleton_Some in Hz1 as [<- <-].
        apply lookup_singleton_Some in Hz2 as [<- <-].
        rewrite !map_fold_singleton=> /=.
        clear. rewrite !union_empty_r_L !union_assoc_L. set_solver. }
    rewrite Heq in HPs. clear Heq.
    rewrite difference_diag_L in HPs. done. }
  { intros ip Sn Hip.
    intros sh [skt bs] Hsh.
    rewrite insert_union_singleton_l in Hip.
    apply lookup_union_Some in Hip; [|apply map_disjoint_dom; set_solver].
    destruct Hip as [Hip|Hip].
    - destruct (decide (ip = ipA)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in Hip. }
      rewrite lookup_insert in Hip.
      simplify_eq.
      destruct (decide (sh = shA)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in Hsh. }
      rewrite lookup_insert in Hsh.
      simplify_eq. done.
    - destruct (decide (ip = ipB)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in Hip. }
      rewrite lookup_insert in Hip.
      simplify_eq.
      destruct (decide (sh = shB)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in Hsh. }
      rewrite lookup_insert in Hsh.
      simplify_eq. done. }
  { intros ip Sn Hip sh sh' skt skt' bs bs' Hsh Hsh' Hskt Heq.
    rewrite insert_union_singleton_l in Hip.
    apply lookup_union_Some in Hip; [|apply map_disjoint_dom; set_solver].
    destruct Hip as [Hip|Hip].
    - destruct (decide (ip = ipA)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in Hip. }
      rewrite lookup_insert in Hip.
      simplify_eq.
      destruct (decide (sh = shA)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in Hsh. }
      rewrite lookup_insert in Hsh.
      destruct (decide (sh' = shA)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in Hsh'. }
      rewrite lookup_insert in Hsh'.
      done.
    - destruct (decide (ip = ipB)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in Hip. }
      rewrite lookup_insert in Hip.
      simplify_eq.
      destruct (decide (sh = shB)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in Hsh. }
      rewrite lookup_insert in Hsh.
      destruct (decide (sh' = shB)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in Hsh'. }
      rewrite lookup_insert in Hsh'.
      simplify_eq. done. }
  { intros ip Sn Hip sh skt bs sa Hsh Hskt.
    rewrite insert_union_singleton_l in Hip.
    apply lookup_union_Some in Hip; [|apply map_disjoint_dom; set_solver].
    destruct Hip as [Hip|Hip].
    - destruct (decide (ip = ipA)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in Hip. }
      rewrite lookup_insert in Hip.
      simplify_eq.
      destruct (decide (sh = shA)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in Hsh. }
      rewrite lookup_insert in Hsh. simplify_eq. set_solver.
    - destruct (decide (ip = ipB)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in Hip. }
      rewrite lookup_insert in Hip.
      simplify_eq.
      destruct (decide (sh = shB)) as [->|Hneq]; last first.
      { by rewrite lookup_insert_ne in Hsh. }
      rewrite lookup_insert in Hsh. simplify_eq. set_solver. }
  iIntros (Hinv) "!> Hunallocated Hrt Hlive Hdead Hσ _ Hfrag Hnode Hst".
  iDestruct (unallocated_split with "Hunallocated") as "[HA HB]"; [set_solver|].
  iMod (aneris_state_interp_socket_interp_allocate_singleton with "Hst [HB]")
    as "[$ #HB]".
  { rewrite /unallocated to_singletons_singleton. iApply "HB". }
  iIntros "!>".
  rewrite big_sepS_union; [|set_solver].
  iDestruct "Hrt" as "[HrtA HrtB]".
  rewrite !big_sepS_singleton.
  rewrite /retransmit_live_roles=> /=.
  iDestruct (live_roles_own_split with "Hlive") as "[HliveA HliveB]";
    [set_solver|].
  replace (dom {[ipA := ∅; ipB := ∅]}) with ({[ipA]} ∪ {[ipB]} : gset _)
                                            by set_solver.
  rewrite !big_sepS_union; [|set_solver..].
  rewrite !big_sepS_singleton.
  rewrite !lookup_total_insert.
  rewrite !big_sepM_singleton.
  simpl.
  iDestruct "Hnode" as "[HnodeA HnodeB]".
  iDestruct "Hσ" as "[[_ HshA] [_ HshB]]".
  iSplitL "HrtA HnodeA HshA HliveA".
  { iApply (wp_A with "[$HrtA $HshA $HliveA //]").
    iIntros "!>" (v) "H".
    iExists _. by iFrame. }
  iSplitL "HrtB HnodeB HshB HliveB".
  { iApply (wp_B with "[$HrtB $HshB $HliveB //]").
    iIntros "!>" (v) "H".
    iExists _. by iFrame. }
  done.
Qed.
