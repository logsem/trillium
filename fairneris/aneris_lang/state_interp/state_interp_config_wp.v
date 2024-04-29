From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export adequacy.
From fairneris Require Import fuel env_model.
From fairneris.aneris_lang Require Import
     aneris_lang network resources network_model.
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
From fairneris Require Import fairness fair_resources.
From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{LM: LiveModel aneris_lang (joint_model Mod net_model)}.
  Context `{LMeq: !LiveModelEq LM}.
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
  (* Lemma state_buffers_insert ip (skts : gmap ip_address sockets) *)
  (*       sh skt bs m R Sn sa : *)
  (*   network_sockets_coh skts → *)
  (*   m_destination m = sa → *)
  (*   ip = ip_of_address sa → *)
  (*   skts !! ip = Some Sn → *)
  (*   Sn !! sh = Some (skt, R) → *)
  (*   saddress skt = Some sa → *)
  (*   model_state_socket_coh skts bs → *)
  (*   model_state_socket_coh (<[ip:=<[sh:=(skt, m :: R)]> Sn]> skts) *)
  (*                          (<[sa:=m :: R]> bs). *)
  (* Proof. *)
  (*   intros Hscoh Hm -> Hip Hsh Hsa Hcoh ip' Sn' sh' skt' sa' R' Hip' Hsh' Hskt'. *)
  (*   assert (network_sockets_coh (<[ip_of_address sa:=<[sh:=(skt, m :: R)]> Sn]> skts)) as Hscoh'. *)
  (*   { by eapply network_sockets_coh_deliver_message. } *)
  (*   assert (ip_of_address sa' = ip') as <-. *)
  (*   { by eapply Hscoh'. } *)
  (*   destruct (decide (sa = sa')) as [<-|Hsaneq]. *)
  (*   { destruct sa. *)
  (*     rewrite lookup_total_insert. *)
  (*     rewrite lookup_insert in Hip'. *)
  (*     simplify_eq. *)
  (*     assert(sh = sh') as <-. *)
  (*     { eapply Hscoh'; [| |done|..]. *)
  (*       - apply lookup_insert. *)
  (*       - rewrite lookup_insert. done. *)
  (*       - done. *)
  (*       - rewrite Hsa. rewrite Hskt'. done. } *)
  (*     rewrite lookup_insert in Hsh'. *)
  (*     simplify_eq. done. } *)
  (*   rewrite lookup_total_insert_ne; [|done]. *)
  (*   destruct (decide (ip_of_address sa = ip_of_address sa')) as [Heq|Hneq]. *)
  (*   { rewrite Heq in Hip'. rewrite lookup_insert in Hip'. *)
  (*     simplify_eq. *)
  (*     assert(sh ≠ sh') as Hshneq. *)
  (*     { intros <-. rewrite lookup_insert in Hsh'. simplify_eq. } *)
  (*     rewrite lookup_insert_ne in Hsh'; [|done]. *)
  (*     by eapply Hcoh. } *)
  (*   rewrite lookup_insert_ne in Hip'; [|done]. *)
  (*   by eapply Hcoh. *)
  (* Qed. *)

  (* Lemma state_buffers_delete ip (skts : gmap ip_address sockets) *)
  (*       sh skt bs m R Sn sa : *)
  (*   network_sockets_coh skts → *)
  (*   m_destination m = sa → *)
  (*   ip = ip_of_address sa → *)
  (*   skts !! ip = Some Sn → *)
  (*   Sn !! sh = Some (skt, R ++ [m]) → *)
  (*   saddress skt = Some sa → *)
  (*   model_state_socket_coh skts bs → *)
  (*   model_state_socket_coh (<[ip:=<[sh:=(skt, R)]> Sn]> skts) *)
  (*                          (<[sa:=R]> bs). *)
  (* Proof. *)
  (*   intros Hscoh Hm -> Hip Hsh Hsa Hcoh ip' Sn' sh' skt' sa' R' Hip' Hsh' Hskt'. *)
  (*   assert (network_sockets_coh (<[ip_of_address sa:=<[sh:=(skt, R)]> Sn]> skts)) as Hscoh'. *)
  (*   { by eapply network_sockets_coh_receive. } *)
  (*   assert (ip_of_address sa' = ip') as <-. *)
  (*   { by eapply Hscoh'. } *)
  (*   destruct (decide (sa = sa')) as [<-|Hsaneq]. *)
  (*   { destruct sa. *)
  (*     rewrite lookup_total_insert. *)
  (*     rewrite lookup_insert in Hip'. *)
  (*     simplify_eq. *)
  (*     assert(sh = sh') as <-. *)
  (*     { eapply Hscoh'; [| |done|..]. *)
  (*       - apply lookup_insert. *)
  (*       - rewrite lookup_insert. done. *)
  (*       - done. *)
  (*       - rewrite Hsa. rewrite Hskt'. done. } *)
  (*     rewrite lookup_insert in Hsh'. *)
  (*     simplify_eq. done. } *)
  (*   rewrite lookup_total_insert_ne; [|done]. *)
  (*   destruct (decide (ip_of_address sa = ip_of_address sa')) as [Heq|Hneq]. *)
  (*   { rewrite Heq in Hip'. rewrite lookup_insert in Hip'. *)
  (*     simplify_eq. *)
  (*     assert(sh ≠ sh') as Hshneq. *)
  (*     { intros <-. rewrite lookup_insert in Hsh'. simplify_eq. } *)
  (*     rewrite lookup_insert_ne in Hsh'; [|done]. *)
  (*     by eapply Hcoh. } *)
  (*   rewrite lookup_insert_ne in Hip'; [|done]. *)
  (*   by eapply Hcoh. *)
  (* Qed. *)

  (*TODO: lots of copy pasta! *)
  Lemma config_wp_correct : ⊢ config_wp.
  Proof using LM LMeq Mod aG Σ.
    rewrite /config_wp. iModIntro.
    iIntros (ex atr c lbl σ2 Hexvalid Hex Hstep) "[[Hsi Hauth] [% Hlive]]".
    rewrite (last_eq_trace_ends_in ex c); [|done].
    rewrite /aneris_state_interp.
    iDestruct "Hsi" as (γm mh)
                         "(%Hhist & %Hgcoh & %Hnscoh & %Hmhcoh &
                           Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    iApply fupd_elim_laterN; [solve_ndisj|].
    destruct c as [tp1 σ1]=> /=.
    rewrite /valid_state_evolution_fairness in H.
    rewrite /trace_ends_in in Hex.
    have Hlstep: locale_step (tp1, σ1) (inr lbl) (tp1, σ2) by econstructor.
    destruct σ1; simpl in *; simplify_eq.
    pose (trace_last atr) as δ.
    pose net' := (env_apply_trans aneris_lang net_model (env_state δ) (inr lbl)).
    unshelve iExists ({| ls_data :=
        {| ls_under := (usr_state δ, net'): fmstate (joint_model Mod net_model); ls_map := δ.(ls_data).(ls_map) |} |}).
    { intros **. eapply ls_map_disj=>//. }
    { intros **. eapply ls_map_live=>//. }
    simpl.
    iExists (Config_step (lbl : fmconfig (joint_model Mod net_model)) lbl).
    inversion Hstep as
      [ip σ Sn Sn' sh a skt R m Hm HSn Hsh HSn' Hsaddr|
        σ|
        σ];
      simplify_eq/=.
    (* Deliver *)
    - destruct H as (Hsteps & Hmatch & Htids).
      iSplitR "Hlive".
      + iFrame "Hauth".
        iExists γm, mh. iFrame. simpl. iModIntro.        
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
      + iModIntro.
        iSplit.
        * simpl. iPureIntro.
          rewrite /valid_state_evolution_fairness.
          rewrite /messages_to_receive_at_multi_soup in Hm.
          split.
          { econstructor; [done|econstructor|done]; simpl.
            - destruct (trace_last atr) as [[[??]]] eqn:Heq. simpl.
              rewrite /usr_state. simpl.
              apply NetTrans.
              by eapply env_apply_trans_spec_trans.
            - split=>//.  }
          split; [|].
          simpl. split=>//. by apply cfg_labels_match_is_eq.
          by rewrite /tids_smaller ?Hex //= in Htids *.
        * iDestruct "Hlive" as "(%fm&?&?&?&Hst&?&%Hem)".
          iExists _. iFrame. iPureIntro.
          unshelve by eapply env_apply_trans_spec_both.
          exact inhabitant.
    - destruct H as (Hsteps & Hmatch & Htids).
      iSplitR "Hlive".
      + iFrame "Hauth". iModIntro. simpl.
        iExists γm, mh. iFrame.
        iSplit.
        { apply (last_eq_trace_ends_in) in Hex as ->.
          erewrite <- message_history_evolution_duplicate_message;
            eauto with set_solver. multiset_solver. }
        iSplitR; [eauto using gnames_coh_update_sockets|].
        iSplitR; [eauto using network_sockets_coh_deliver_message|].
        eauto using messages_history_coh_duplicate_message.
      + iModIntro.
        iSplit.
        * simpl. iPureIntro.
          rewrite /valid_state_evolution_fairness.
          split.
          { econstructor; [done|econstructor|done]; simpl.
            - destruct (trace_last atr) as [[[??]]] eqn:Heq. simpl.
              rewrite /usr_state. simpl.
              apply NetTrans.
              by eapply env_apply_trans_spec_trans.
            - split=>//.  }
          split; [|].
          simpl. split=>//. by apply cfg_labels_match_is_eq.
          by rewrite /tids_smaller ?Hex //= in Htids *.
        * iDestruct "Hlive" as "(%fm&?&?&?&Hst&?&%Hem)".
          iExists _. iFrame. iFrame. iPureIntro.
          unshelve by eapply env_apply_trans_spec_both.
          exact inhabitant.
    - destruct H as (Hsteps & Hmatch & Htids).
      iSplitR "Hlive".
      + iFrame "Hauth". simpl. iModIntro.
        iExists γm, mh. iFrame.
        iSplit.
        { apply (last_eq_trace_ends_in) in Hex as ->.
          erewrite <- message_history_evolution_drop_message;
            eauto with set_solver. multiset_solver. }
        iSplitR; [eauto using gnames_coh_update_sockets|].
        iSplitR; [eauto using network_sockets_coh_deliver_message|].
        eauto using messages_history_coh_drop_message.
      + iSplitR.
        * simpl. iPureIntro.
          rewrite /valid_state_evolution_fairness.
          split.
          { econstructor; [done|econstructor|done]; simpl.
            - destruct (trace_last atr) as [[[??]]] eqn:Heq. simpl.
              rewrite /usr_state. simpl.
              apply NetTrans.
              by eapply env_apply_trans_spec_trans.
            - split=>//.  }
          split; [|].
          simpl. split=>//. by apply cfg_labels_match_is_eq.
          by rewrite /tids_smaller ?Hex //= in Htids *.
        * iDestruct "Hlive" as "(%fm&?&?&?&Hst&?&%Hem)".
          iExists _. iFrame. iFrame. iPureIntro.
          unshelve by eapply env_apply_trans_spec_both.
          exact inhabitant.
  Qed.

End state_interpretation.
