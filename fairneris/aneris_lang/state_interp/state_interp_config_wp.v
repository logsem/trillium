From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export adequacy.
From fairneris.aneris_lang Require Import
     aneris_lang network resources.
From fairneris.prelude Require Import gmultiset.
From fairneris.aneris_lang.state_interp Require Import
     state_interp_def
     state_interp_local_coh
     state_interp_gnames_coh
     state_interp_free_ips_coh
     state_interp_network_sockets_coh
     state_interp_socket_interp_coh
     state_interp_messages_resource_coh
     state_interp_messages_history_coh
     state_interp_events
     state_interp_messages_history.
From fairneris Require Import fairness.
From fairneris Require Import retransmit_model_progress_ltl.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG retransmit_fair_model Σ}.

  (* TODO: Move this elsehwere and use it where we now use ad hoc induction *)
  Lemma fupd_elim_laterN E1 E2 n (P:iProp Σ) :
    E2 ⊆ E1 → (|={E1}=> P)%I -∗ |={E1,E2}=> |={E2}▷=>^n |={E2,E1}=> P.
  Proof.
    iIntros (Hle) "HP".
    iApply fupd_mask_intro; [done|].
    iIntros "Hclose".
    iInduction n as [|n] "IHn"; [by iMod "Hclose"|]=> /=.
    iIntros "!>!>!>".
    iApply ("IHn" with "HP Hclose").
  Qed.

  Lemma state_buffers_lookup ip (skts : gmap ip_address sockets)
        Sn sh skt bs sa :
    network_sockets_coh skts →
    skts !! ip = Some Sn → Sn !! sh = Some (skt,bs) →
    saddress skt = Some sa →
    state_buffers skts !! sa = Some bs.
  Proof. Admitted.

  Lemma state_buffers_insert ip (skts : gmap ip_address sockets)
        skts' sh skt bs bs' sa :
    network_sockets_coh skts →
    skts !! ip = Some skts' → skts' !! sh = Some (skt,bs) →
    saddress skt = Some sa →
    <[sa := bs']>(state_buffers skts) =
    (state_buffers (<[ip:=<[sh := (skt,bs')]>skts']>skts)).
  Proof. Admitted.

  Lemma config_wp_correct : ⊢ config_wp.
  Proof.
    rewrite /config_wp. iModIntro.
    iIntros (ex atr c lbl σ2 Hexvalid Hex Hstep) "(% & Hevs & Hsi & Hlive & Hauth)".
    rewrite (last_eq_trace_ends_in ex c); [|done].
    iDestruct "Hsi" as (γm mh)
                         "(%Hhist & %Hgcoh & %Hnscoh & %Hmhcoh &
                           Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    iApply fupd_elim_laterN; [solve_ndisj|].
    destruct c as [tp1 σ1]=> /=.
    rewrite /simple_valid_state_evolution in H.
    rewrite /trace_ends_in in Hex.
    rewrite Hex in H. simpl in *.
    destruct σ1; simpl in *; simplify_eq.
    destruct (trace_last atr) as [[δ ms] bs] eqn:Hs.
    inversion Hstep as
      [ip σ Sn Sn' sh a skt R m Hm HSn Hsh HSn' Hsaddr|
        σ|
        σ];
      simplify_eq/=.
    (* Deliver *)
    - destruct H as (Hsteps & Hmatch & Hlive & Hσ).
      iExists (δ, ms ∖ {[+ m +]}, <[m_destination m := m::R]>bs),
                (inr ((), Some m)).
      rewrite (aneris_events_state_interp_same_tp _ (tp1, _));
        [| |done|done]; last first.
      { econstructor; [done| |done]. econstructor 2; eauto. }
      iSplitR.
      { iPureIntro.
        rewrite /simple_valid_state_evolution.
        rewrite /messages_to_receive_at_multi_soup in Hm.
        split.
        { econstructor; [done|econstructor|done].
          - destruct Hσ as [Hσ1 Hσ2].
            simpl in *. rewrite Hσ1 in Hm.
            apply elem_of_filter in Hm as [? Hm].
            apply elem_of_gset_of_gmultiset in Hm.
            set_solver.
          - destruct Hσ as [Hσ1 Hσ2].
            simpl in *.
            rewrite -Hσ2.
            rewrite lookup_total_alt.
            assert (a = m_destination m) as ->.
            { by apply elem_of_filter in Hm as [-> _]. }
            by erewrite state_buffers_lookup. }
        split; [done|].
        split; [done|].
        split.
        { simpl. destruct Hσ as [Hσ1 Hσ2].
          simpl in *. by rewrite Hσ1. }
        simpl.
        destruct Hσ as [Hσ1 Hσ2].
        assert (a = m_destination m) as ->.
        { by apply elem_of_filter in Hm as [-> _]. }
        by erewrite <-state_buffers_insert; [by f_equiv|..].
      }
      iFrame "Hauth Hevs Hlive".
      iModIntro.
      iExists γm, mh. iFrame.
      iSplit.
      { apply (last_eq_trace_ends_in) in Hex as ->.
        erewrite <- message_history_evolution_deliver_message;
          eauto with set_solver. }
      iSplitR; [eauto using gnames_coh_update_sockets|].
      iSplitR; [eauto using network_sockets_coh_deliver_message|].
      iSplitR; [iPureIntro; apply messages_history_coh_drop_message;
                eauto using messages_history_coh_deliver_message|].
      iSplitL "Hlcoh";
        [by iApply (local_state_coh_deliver_message with "Hlcoh")|].
      by iApply (free_ips_coh_deliver_message with "Hfreeips").
    - destruct H as (Hsteps & Hmatch & Hlive & Hσ).
      iExists (δ, ms ⊎ {[+ m +]}, bs), (inr ((), None)).
      rewrite (aneris_events_state_interp_same_tp _ (tp1, _));
        [| |done|done]; last first.
      { econstructor; [done| |done]. econstructor 2; eauto. }
      iSplitR.
      { iPureIntro.
        rewrite /simple_valid_state_evolution.
        split.
        { econstructor; [done|econstructor|done].
          destruct Hσ as [Hσ1 Hσ2].
          simpl in *. by rewrite Hσ1 in H0. }
        split; [done|].
        split; [done|].
        split.
        { simpl. destruct Hσ as [Hσ1 Hσ2].
          simpl in *. by rewrite Hσ1. }
        simpl. by destruct Hσ as [Hσ1 Hσ2].
      }
      iFrame "Hauth Hevs Hlive".
      iModIntro.
      iExists γm, mh. iFrame.
      iSplit.
      { apply (last_eq_trace_ends_in) in Hex as ->.
        erewrite <- message_history_evolution_duplicate_message;
          eauto with set_solver. multiset_solver. }
      iSplitR; [eauto using gnames_coh_update_sockets|].
      iSplitR; [eauto using network_sockets_coh_deliver_message|].
      eauto using messages_history_coh_duplicate_message.
    - destruct H as (Hsteps & Hmatch & Hlive & Hσ).
      iExists (δ, ms ∖ {[+ m +]}, bs), (inr ((), None)).
      rewrite (aneris_events_state_interp_same_tp _ (tp1, _));
        [| |done|done]; last first.
      { econstructor; [done| |done]. econstructor 2; eauto. }
      iSplitR.
      { iPureIntro.
        rewrite /simple_valid_state_evolution.
        split.
        { econstructor; [done|econstructor|done].
          destruct Hσ as [Hσ1 Hσ2].
          simpl in *. by rewrite Hσ1 in H0. }
        split; [done|].
        split; [done|].
        split.
        { simpl. destruct Hσ as [Hσ1 Hσ2].
          simpl in *. by rewrite Hσ1. }
        simpl. by destruct Hσ as [Hσ1 Hσ2].
      }
      iFrame "Hauth Hevs Hlive".
      iModIntro.
      iExists γm, mh. iFrame.
      iSplit.
      { apply (last_eq_trace_ends_in) in Hex as ->.
        erewrite <- message_history_evolution_drop_message;
          eauto with set_solver. multiset_solver. }
      iSplitR; [eauto using gnames_coh_update_sockets|].
      iSplitR; [eauto using network_sockets_coh_deliver_message|].
      eauto using messages_history_coh_drop_message.
  Qed.

End state_interpretation.
