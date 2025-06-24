From stdpp Require Import list fin_maps.
From iris.proofmode Require Import proofmode.
From fairneris.aneris_lang Require Import network_model.
From iris.algebra Require Import excl_auth.
From iris.base_logic.lib Require Import invariants.
From trillium.program_logic Require Import ectx_lifting.
From fairneris Require Import fairness ltl_lite.
From fairneris.examples Require Import stenning_ho_model.
From fairneris.aneris_lang Require Import aneris_lang.
From fairneris.aneris_lang.state_interp Require Import state_interp state_interp_events.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From fairneris.aneris_lang Require Import aneris_lang adequacy.
From fairneris.aneris_lang.lib Require Import list_code.
From fairneris.lib Require Import gen_heap_light.
From fairneris.examples Require Import stenning_ho_code.
From fairneris.lib Require Import singletons.

Definition initial_state :=
  ([mkExpr ipA (client_example saA saB #()); mkExpr ipB (server_example saA saB)],
     {| state_heaps := {[ipA:=∅; ipB:=∅]};
        state_sockets := {[ipA:=∅; ipB:=∅]} ;
        state_ms := ∅; |}).

Definition initial_model_state : stenning_state := (ASending 0, BReceiving 0).

Definition safety_inv := λ st, let (n, m) := stenning_get_n st in (n = m ∨ m = n + 1)%Z.

Lemma stenning_continued_simulation extr :
  trfirst extr = initial_state →
  extrace_valid extr →
  ex_fair extr →
  ∃ utr : lts_trace stenning_model,
    program_model_refinement (LM := live_model_of_user stenning_model net_model) extr utr ∧ usr_fair utr ∧
      usr_trace_valid utr ∧ trfirst utr = initial_model_state ∧ (utr ⊩ □ ↓ λ s _, safety_inv s).
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
            (valid_state_evolution_fairness (live_model_of_user stenning_model net_model) safety_inv)
            initial_state (lm_init _ _ _ (∅, ∅) Hfss)
    ) as Hcs.
  { eapply (simulation_adequacy_multiple_strong _ {[saA;saB]} NotStuck _ _ _ _ ∅).
    { rewrite /initial_state /=. lia. }
    { intros s1 act. eapply (in_list_finite (stenning_enum_next s1)).
      intros [s2 ρ]. apply stenning_enum_next_spec. }
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
    iMod (gen_heap_light_init (∅ : gmap socket_address Z)) as (γC) "Hw".

    pose (X := {| stenning_A_name := γA; stenning_B_name := γB; stenning_cnt_name := γC |} : stenningG stenningΣ).

    iMod (gen_heap_light_alloc _ saA γC 0%Z with "Hw") as "[Hw [Hcc [Hcci Hccm]]]"; [set_solver|].
    iMod (gen_heap_light_alloc _ saB γC (-1)%Z with "Hw") as "[Hw [Hcs [Hcsi Hcsm]]]"; [set_solver|].

    rewrite (subseteq_empty_difference_L ∅); last set_solver.
    iMod (inv_alloc (nroot .@ "stenning") _ retinv with "[Hσ HresAA HresAB HFR Hcci Hcsi]") as "#Hinv".
    { iNext. rewrite /retinv. iFrame. iExists _, _. iFrame. simpl.
      replace (0-1)%Z with (-1)%Z by lia.
      replace (1/2/2)%Qp with (1/4)%Qp by compute_done.
      iFrame. naive_solver. }
    iMod (inv_alloc (nroot .@ "counter") _
            (∃ w, gen_heap_light_ctx (L:=socket_address) (V:=Z) stenning_cnt_name w)%I
           with "[Hw]") as "#Hcinv".
    { naive_solver. }

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
    { iModIntro. iIntros (st) "Hst".
      iInv "Hinv" as ">Hi" "Hclose". rewrite /retinv.
      iDestruct "Hi" as "(_&%stA&%stB&Hst'&?&?&H)".
      iApply fupd_mask_intro. set_solver. iIntros "_".
      iDestruct (model_agree with "Hst Hst'") as %->. cbn.
      iDestruct "H" as "(%Hstinv&?)". iFrame. iPureIntro. naive_solver. }
    iSplitL "HrtA HnodeA HfuelA HfpA HresFA Hcc Hccm Hcsm".
    { simpl.
      iApply (wp_client_example _ (usr_fl (initial_model_state : stenning_model)) with
               "[HrtA HnodeA HfuelA HfpA HresFA Hcc Hccm Hcsm]").
      { rewrite //=. lia. }
      { rewrite /locale_of /=. rewrite gset_to_gmap_singleton. iFrame "#∗".
        iDestruct "Hcc" as "[??]".
        replace (1/2/2)%Qp with (1/4)%Qp by compute_done. iFrame.       
      }
      iIntros "!>" (v) "H".
      rewrite /locale_of. iFrame.
    }
    iSplitL "HrtB HnodeB HfuelB HresFB HfpB Hcs".
    { iApply (wp_server_example _ (usr_fl (initial_model_state : stenning_model)) with "[-]").
      { rewrite /=. lia. }
      { rewrite /locale_of /=. rewrite gset_to_gmap_singleton. iFrame "#∗". }
      iIntros "!>" (v) "H".
      rewrite /locale_of. iFrame.
    }
    done. }

  eapply program_model_refinement_preserves_upward in Hcs =>//.
Qed.

Lemma stenning_fair_live_extr extr i :
  trfirst extr = initial_state →
  extrace_valid extr →
  ex_fair extr →
  (extr ⊩ ◊ ℓ↓ (λ ℓ, ∃ ℓ' ζ, ℓ = inl (ζ, Some ℓ') ∧ ∃ j, ℓ' = Send $ mAB i j)).
Proof.
  intros.
  apply stenning_continued_simulation in H1 as (?&?&?&?&?&?); [|done..].
  eapply program_model_refinement_downward_eventually; [done|].
  by apply stenning_fair_live.
Qed.
