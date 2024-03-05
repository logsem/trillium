From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export adequacy.
From fairneris Require Import fuel.
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

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{LM: LiveModel aneris_lang Mod}.
  Context `{aG : !anerisG LM Σ}.

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

  (* OBS: A general update lemma could be nicer, but needs changes to
   [network_sockets_coh] API *)
  Lemma state_buffers_insert ip (skts : gmap ip_address sockets)
        sh skt bs m R Sn sa :
    network_sockets_coh skts →
    m_destination m = sa →
    ip = ip_of_address sa →
    skts !! ip = Some Sn →
    Sn !! sh = Some (skt, R) →
    saddress skt = Some sa →
    model_state_socket_coh skts bs →
    model_state_socket_coh (<[ip:=<[sh:=(skt, m :: R)]> Sn]> skts)
                           (<[sa:=m :: R]> bs).
  Proof.
    intros Hscoh Hm -> Hip Hsh Hsa Hcoh ip' Sn' sh' skt' sa' R' Hip' Hsh' Hskt'.
    assert (network_sockets_coh (<[ip_of_address sa:=<[sh:=(skt, m :: R)]> Sn]> skts)) as Hscoh'.
    { by eapply network_sockets_coh_deliver_message. }
    assert (ip_of_address sa' = ip') as <-.
    { by eapply Hscoh'. }
    destruct (decide (sa = sa')) as [<-|Hsaneq].
    { destruct sa.
      rewrite lookup_total_insert.
      rewrite lookup_insert in Hip'.
      simplify_eq.
      assert(sh = sh') as <-.
      { eapply Hscoh'; [| |done|..].
        - apply lookup_insert.
        - rewrite lookup_insert. done.
        - done.
        - rewrite Hsa. rewrite Hskt'. done. }
      rewrite lookup_insert in Hsh'.
      simplify_eq. done. }
    rewrite lookup_total_insert_ne; [|done].
    destruct (decide (ip_of_address sa = ip_of_address sa')) as [Heq|Hneq].
    { rewrite Heq in Hip'. rewrite lookup_insert in Hip'.
      simplify_eq.
      assert(sh ≠ sh') as Hshneq.
      { intros <-. rewrite lookup_insert in Hsh'. simplify_eq. }
      rewrite lookup_insert_ne in Hsh'; [|done].
      by eapply Hcoh. }
    rewrite lookup_insert_ne in Hip'; [|done].
    by eapply Hcoh.
  Qed.

  Lemma state_buffers_delete ip (skts : gmap ip_address sockets)
        sh skt bs m R Sn sa :
    network_sockets_coh skts →
    m_destination m = sa →
    ip = ip_of_address sa →
    skts !! ip = Some Sn →
    Sn !! sh = Some (skt, R ++ [m]) →
    saddress skt = Some sa →
    model_state_socket_coh skts bs →
    model_state_socket_coh (<[ip:=<[sh:=(skt, R)]> Sn]> skts)
                           (<[sa:=R]> bs).
  Proof.
    intros Hscoh Hm -> Hip Hsh Hsa Hcoh ip' Sn' sh' skt' sa' R' Hip' Hsh' Hskt'.
    assert (network_sockets_coh (<[ip_of_address sa:=<[sh:=(skt, R)]> Sn]> skts)) as Hscoh'.
    { by eapply network_sockets_coh_receive. }
    assert (ip_of_address sa' = ip') as <-.
    { by eapply Hscoh'. }
    destruct (decide (sa = sa')) as [<-|Hsaneq].
    { destruct sa.
      rewrite lookup_total_insert.
      rewrite lookup_insert in Hip'.
      simplify_eq.
      assert(sh = sh') as <-.
      { eapply Hscoh'; [| |done|..].
        - apply lookup_insert.
        - rewrite lookup_insert. done.
        - done.
        - rewrite Hsa. rewrite Hskt'. done. }
      rewrite lookup_insert in Hsh'.
      simplify_eq. done. }
    rewrite lookup_total_insert_ne; [|done].
    destruct (decide (ip_of_address sa = ip_of_address sa')) as [Heq|Hneq].
    { rewrite Heq in Hip'. rewrite lookup_insert in Hip'.
      simplify_eq.
      assert(sh ≠ sh') as Hshneq.
      { intros <-. rewrite lookup_insert in Hsh'. simplify_eq. }
      rewrite lookup_insert_ne in Hsh'; [|done].
      by eapply Hcoh. }
    rewrite lookup_insert_ne in Hip'; [|done].
    by eapply Hcoh.
  Qed.

  Lemma config_wp_correct : ⊢ config_wp.
  Proof.
    rewrite /config_wp. iModIntro.
    iIntros (ex atr c lbl σ2 Hexvalid Hex Hstep) "(% & Hsi & Hlive & Hauth)".
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
            assert (a = m_destination m) as ->.
            { by apply elem_of_filter in Hm as [-> _]. }
            by erewrite Hσ2. }
        split; [done|].
        split; [done|].
        split.
        { simpl. destruct Hσ as [Hσ1 Hσ2].
          simpl in *. by rewrite Hσ1. }
        simpl.
        destruct Hσ as [Hσ1 Hσ2].
        assert (a = m_destination m) as ->.
        { by apply elem_of_filter in Hm as [-> _]. }
        simpl in *.
        apply state_buffers_insert; try done.
        symmetry.
        by eapply Hnscoh. }
      iFrame "Hauth Hlive".
      iModIntro.
      iExists γm, mh. iFrame.
      iSplit.
      { apply (last_eq_trace_ends_in) in Hex as ->.
        erewrite <- message_history_evolution_deliver_message;
          eauto with set_solver. }
      iSplitR; [eauto using gnames_coh_update_sockets|].
      assert (m_destination m = a) by set_solver. (* TODO: Remove filter thing *)
      iSplitR; [eauto using network_sockets_coh_deliver_message|].
      iSplitR; [iPureIntro; apply messages_history_coh_drop_message;
                eauto using messages_history_coh_deliver_message|].
      iSplitL "Hlcoh";
        [by iApply (local_state_coh_deliver_message with "Hlcoh")|].
      by iApply (free_ips_coh_deliver_message with "Hfreeips").
    - destruct H as (Hsteps & Hmatch & Hlive & Hσ).
      iExists (δ, ms ⊎ {[+ m +]}, bs), (inr ((), None)).
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
      iFrame "Hauth Hlive".
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
      iFrame "Hauth Hlive".
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
