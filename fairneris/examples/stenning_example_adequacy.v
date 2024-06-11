From stdpp Require Import list fin_maps.
From iris.proofmode Require Import proofmode.
From fairneris.aneris_lang Require Import network_model.
From iris.algebra Require Import excl_auth.
From iris.base_logic.lib Require Import invariants.
From trillium.program_logic Require Import ectx_lifting.
From fairneris Require Import fairness.
From fairneris.examples Require Import stenning_model.
From fairneris.aneris_lang Require Import aneris_lang.
From fairneris.aneris_lang.state_interp Require Import state_interp state_interp_events.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From fairneris.aneris_lang Require Import aneris_lang adequacy.
From fairneris Require Import stenning_code.

From fairneris.lib Require Import singletons.

Definition initial_state :=
  ([mkExpr ipA (client saA saB #()); mkExpr ipB (server saA saB #())],
     {| state_heaps := {[ipA:=∅; ipB:=∅]};
        state_sockets := {[ipA:=∅; ipB:=∅]} ;
        state_ms := ∅; |}).

Definition initial_model_state : stenning_state := (ASending 0, BReceiving 0).

Lemma stenning_continued_simulation extr :
  trfirst extr = initial_state →
  extrace_valid extr →
  ex_fair extr →
  True.
  (* (extr ⊩ ◊ ℓ↓ (λ ℓ, ∃ ℓ' ζ, ℓ = inl (ζ, Some ℓ') ∧ ℓ' = Send mDone)). *)
Proof.
  intros Hfirst Hval Hfair.

  assert (anerisPreG (live_model_of_user stenning_model net_model) stenningΣ) as HPreG.
  { apply _. }

  assert (good_fuel_alloc initial_state.1 initial_model_state [ {[ Arole ]}; {[ Brole]} ]) as Hfss.
  { split; first done. split.
    - intros n1 n2 fs1 fs2 Hneq. destruct n1 as [|n1]=>//.
      + rewrite -head_lookup /=. destruct n2 as [|n2]=>//.
        rewrite -lookup_tail /=. destruct n2.
        * rewrite -head_lookup /=. naive_solver set_solver.
        * rewrite -lookup_tail /=. naive_solver set_solver.
      + rewrite -lookup_tail /=. destruct n1; last by rewrite -lookup_tail //=.
        rewrite -head_lookup /=. destruct n2 as [|n2]=>//.
        * rewrite -head_lookup /=. naive_solver set_solver.
        * rewrite -lookup_tail /=. destruct n2; last by rewrite -lookup_tail //=.
          rewrite -head_lookup /=. naive_solver set_solver.
    - intros [|] Hin; [exists 0%nat|exists 1%nat]; rewrite ?tail_lookup ?head_lookup //=; naive_solver set_solver. }

  assert (continued_simulation_init
            (valid_state_evolution_fairness (live_model_of_user stenning_model net_model) (λ _, False))
            initial_state (lm_init _ _ _ (∅, ∅) Hfss)
    ) as Hcs.
  { eapply (simulation_adequacy_multiple_strong _ {[saA;saB]} NotStuck _ _ _ _ ∅).
    { rewrite /initial_state /=. lia. }
    { rewrite //=. }
    { rewrite /config_net_match /model_state_socket_incl /model_state_socket_coh /=. split=>//. split.
      - naive_solver.
      - intros ip Sn sh skt sa ms. destruct (decide (ip = ipA)) as [->|].
        + rewrite lookup_insert. naive_solver.
        + destruct (decide (ip = ipB)) as [->|].
          rewrite lookup_insert_ne // lookup_insert; naive_solver.
          rewrite lookup_insert_ne // lookup_insert_ne //; naive_solver. }
    { simpl. intros ip ps ? Sn Hlk p Hin.
      destruct (decide (ip = ipA)) as [->|]; [|destruct (decide (ip = ipB)) as [->|]].
      - rewrite lookup_insert in Hlk. simplify_eq Hlk. intros <-.
        intros ?????. naive_solver.
      - rewrite lookup_insert_ne in Hlk; last done. rewrite lookup_insert in Hlk.
        simplify_eq Hlk. intros <-. intros ?????. naive_solver.
      - rewrite ?lookup_insert_ne in Hlk=>//. }
    { simpl. apply map_Forall_insert. naive_solver. split. apply map_Forall_empty.
      apply map_Forall_insert. naive_solver. split; apply map_Forall_empty. }
    { have ?: socket_handlers_coh ∅.
      { rewrite /socket_handlers_coh. naive_solver. }
      simpl. apply map_Forall_insert. naive_solver. split=>//.
      apply map_Forall_insert. naive_solver. split; [done | apply map_Forall_empty]. }
    { simpl. apply map_Forall_insert. naive_solver. split=>//.
      apply map_Forall_insert. naive_solver. split; [done | apply map_Forall_empty]. }
    { done. }

    iIntros (Hinv) "!> Hunallocated Hrt Hlive Hfp Hσ HFR Hfuel Hnode Hst".
    iDestruct (unallocated_split with "Hunallocated") as "[HA HB]"; [set_solver|].

    iMod (own_alloc (●E (ASending 0) ⋅ ◯E (ASending 0))) as (γA) "[HresAA HresFA]".
    { apply auth_both_valid_2; eauto. by compute. }
    iMod (own_alloc (●E (BReceiving 0) ⋅ ◯E (BReceiving 0))) as (γB) "[HresAB HresFB]".
    { apply auth_both_valid_2; eauto. by compute. }

    pose (X := {| stenning_A_name := γA; stenning_B_name := γB |} : stenningG stenningΣ).

    rewrite (subseteq_empty_difference_L ∅); last set_solver.
    iMod (inv_alloc (nroot .@ "stenning") _ retinv with "[Hσ HresAA HresAB HFR]") as "#Hinv".
    { iNext. rewrite /retinv. iFrame. iExists _, _. iFrame. }

    iMod (aneris_state_interp_socket_interp_allocate_singleton with "Hst [HA]")
      as "[Hst #HA]".
    { rewrite /unallocated to_singletons_singleton. iApply "HA". }
    iMod (aneris_state_interp_socket_interp_allocate_singleton with "Hst [HB]")
      as "[$ #HB]".
    { rewrite /unallocated to_singletons_singleton. iApply "HB". }

    iIntros "!>".
    rewrite big_sepS_union; [|set_solver].
    iDestruct "Hrt" as "[HrtA HrtB]".
    rewrite !big_sepS_singleton.

    iClear "Hlive".

    rewrite /stenning_live_roles=> /=.
    replace (dom {[ipA := ∅; ipB := ∅]}) with ({[ipA]} ∪ {[ipB]} : gset _)
                                              by set_solver.
    rewrite !big_sepS_union; [|set_solver..].
    rewrite !big_sepS_singleton.

    iDestruct "Hnode" as "[HnodeA HnodeB]".

    rewrite /initial_fuel_map /initial_fuel_map_from /=.
    rewrite (big_sepM_insert _ _ (locale_of _ _)) ; [|set_solver..].
    rewrite (big_sepM_insert _ _ (locale_of _ _)) ; [|set_solver..].
    iDestruct "Hfuel" as "(HfuelA & HfuelB & _)".

    rewrite ports_in_use_empty ?difference_empty_L; last first.
    { intros ip m. destruct (decide (ip = ipA)) as [->|]; [|destruct (decide (ip = ipB)) as [->|]].
      - rewrite lookup_insert. naive_solver.
      - rewrite lookup_insert_ne // lookup_insert. naive_solver.
      - rewrite ?lookup_insert_ne //. }

    rewrite /addrs_to_ip_ports_map set_fold_disj_union_strong; last first.
    { set_solver. }
    { intros sa sa' m ???. apply insert_commute.
      destruct (decide (sa = saA)) as [->|]; [|destruct (decide (sa = saB)) as [->|]]=>//.
      - destruct (decide (sa' = saA)) as [->|]; [|destruct (decide (sa' = saB)) as [->|]]=>//. set_solver.
      - destruct (decide (sa' = saA)) as [->|]; [|destruct (decide (sa' = saB)) as [->|]]=>//. set_solver.
      - set_solver. }

    rewrite !set_fold_singleton.
    rewrite big_sepM_insert //.
    rewrite big_sepM_insert //.
    iDestruct "Hfp" as "(HfpB & HfpA & _)".

    iSplit.
    { iModIntro. iIntros (st) "Hst". iApply fupd_mask_intro. set_solver. iIntros "_". iFrame. admit. }
    iSplitL "HrtA HnodeA HfuelA HfpA HresFA".
    { iApply (wp_client _ (usr_fl (initial_model_state : stenning_model)) with
               "[HrtA HnodeA HfuelA HfpA HresFA]").
      { rewrite //=. }
      { rewrite /locale_of /=. rewrite gset_to_gmap_singleton. iFrame "#∗". }
      iIntros "!>" (v) "H".
      rewrite /locale_of. iFrame. }
    iSplitL "HrtB HnodeB HfuelB HresFB HfpB".
    { iApply (wp_server _ (usr_fl (initial_model_state : stenning_model)) with "[-]").
      { rewrite /=. lia. }
      { rewrite /locale_of /=. rewrite gset_to_gmap_singleton. iFrame "#∗". }
      iIntros "!>" (v) "H".
      rewrite /locale_of. iFrame. }
    done. }

  eapply program_model_refinement_preserves_upward in Hcs =>//.
(*   rewrite /= in Hcs. destruct Hcs as (utr & Href & Hafair & Haval & Heq). *)
(*   eapply program_model_refinement_downward_eventually=>//. *)

(*   eapply trace_eventually_mono; last apply stenning_fair_node_B_sends; last first=>//. *)
(*   { rewrite ltl_sat_def /trace_now /pred_at /=. destruct utr=>//. } *)
(*   intros tr. rewrite !ltl_sat_def /trace_label /pred_at /usr_send_filter /=. destruct tr=>//. *)
(*   intros [ρ ->]. naive_solver. *)
(* Qed. *)
Admitted.
