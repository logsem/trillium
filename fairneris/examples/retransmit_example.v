From stdpp Require Import list fin_maps.
From iris.proofmode Require Import proofmode.
From trillium.program_logic Require Import ectx_lifting.
From fairneris Require Import fairness.
From fairneris.examples Require Import retransmit_model_progress_ltl.
From fairneris.aneris_lang Require Import aneris_lang.
From fairneris.aneris_lang.state_interp Require Import state_interp state_interp_events.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.
(* From fairneris Require Import adequacy. *)

Definition Aprog shA : expr := SendToRepeat #(LitSocket shA) #"Hello" #saB.
Definition Bprog shB : expr := ReceiveFrom #(LitSocket shB).

Section with_Σ.
  Context `{anerisG retransmit_fair_model Σ}.

  Lemma wp_A s E shA :
    {{{ shA ↪[ip_of_address saA] sA ∗ saA ⤳ (∅,∅) ∗ saB ⤇ (λ _, True) ∗
        live_role_frag_own Arole }}}
      (mkExpr (ip_of_address saA) (Aprog shA)) @ s; (ip_of_address saA,tidA); E
    {{{ v, RET v; dead_role_frag_own Arole }}}.
  Proof.
    iIntros (Φ) "(Hsh & Hrt & #Hmsg & HA) HΦ".
    iAssert (∃ R T, saA ⤳ (R, T) ∗
            [∗ set] m ∈ R, socket_address_group_own {[m_sender m]})%I
      with "[Hrt]" as (R T) "[HRT HR]"; [by eauto|].
    iLöb as "IH" forall (R T).
    iApply wp_lift_head_step_fupd; [done|].
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale)
            "(%Hvalid & Hσ & [Hlive_auth Hlive_owns] & Hauth) /=".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplitR.
    { iPureIntro; do 4 eexists. eapply SocketStepS; eauto. by econstructor. }
    iIntros (α ? ? ? Hstep). simpl in *. iModIntro. inv_head_step; iNext.
    rewrite (insert_id (state_sockets σ)); last done.
    iAssert (socket_address_group_own {[saA]})%I as "#HsaA".
    { iDestruct "HRT" as "[(%send & %recv & _ & _ & _ & $ & _) _]". }
    iAssert (socket_address_group_own {[saB]})%I as "#HsaB".
    { by iDestruct "Hmsg" as (γ) "[H _]". }
    iMod (aneris_state_interp_send shA saA {[saA]} saB {[saB]} _ _ sA _ _ _ _ _
                                   "Hello"
           with "[$HsaA] [$HsaB] [$Hsh] [HRT] [$Hmsg] [] [$Hσ]")
        as "(%Hmhe & Hσ & Hsh & HRT)";
      [try set_solver..|].
    { apply message_group_equiv_refl; set_solver. }
    { iDestruct "HRT" as "[$ _]". }
    { by rewrite /from_singleton; eauto. }
    iDestruct (live_role_auth_elem_of with "Hlive_auth HA") as %Hrole.
    destruct (trace_last atr) as [[st ms] bs] eqn:Heqn.
    iExists (st,ms ⊎ {[ (mkMessage saA saB "Hello") ]},bs),
              (inl (Arole,Some (mkMessage saA saB "Hello"))).
    iMod "Hclose". rewrite -Hmhe. iFrame=> /=.
    iSplitR; last first.
    { iDestruct "HR" as "#HR".
      iApply ("IH" with "Hsh HA HΦ [HRT]"); [by iSplitL|done]. }
    iPureIntro.
    rewrite /simple_valid_state_evolution in Hvalid.
    rewrite /simple_valid_state_evolution=> /=.
    destruct Hvalid as (Hsteps & Hmatch & Hlive & Hms & Hskt).
    rewrite /trace_ends_in in Hex.
    rewrite Hex in Hms. simpl in Hms. rewrite Hms.
    split; [econstructor; [done|econstructor|done]|].
    split; [done|].
    split.
    { intros ℓ ζ Hlabels Henabled=> /=. rewrite right_id_L.
      rewrite Hex in Hlive. eapply Hlive; [done|by rewrite Heqn]. }
    split; last first.
    { simpl. rewrite Hex in Hskt. simpl in *. by rewrite Heqn in Hskt. }
    simpl. rewrite Heqn in Hms. simpl in *.
    rewrite Heqn. simpl. multiset_solver.
  Qed.

  Lemma wp_B s E shB :
    {{{ shB ↪[ip_of_address saB] sB ∗ saB ⤳ (∅,∅) ∗ saB ⤇ (λ _, True) ∗
        live_role_frag_own Brole }}}
      (mkExpr (ip_of_address saB) (Bprog shB)) @ s; (ip_of_address saB, tidB); E
    {{{ v, RET v; dead_role_frag_own Brole }}}.
  Proof.
    iIntros (Φ) "(Hsh & Hrt & #HΨ & HB) HΦ".
    iLöb as "IH".
    iApply wp_lift_head_step; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex) "(%Hvalid & Hσ & [Hlive_auth Hdead_auth] & Hauth) /=".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_network_sockets_coh_valid with "Hσ") as %Hcoh.
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    iDestruct (live_role_auth_elem_of with "Hlive_auth HB") as %Hrole.
    destruct (trace_last atr) as [[[] ms] bs] eqn:Heqn; last first.
    { rewrite Heqn in Hrole. set_solver. }
    simpl in *.
    destruct Hvalid as (Hsteps & Hmatch & Hlive & [Hms Hskts]).
    rewrite Hex in Hskts. rewrite Heqn in Hskts.
    simpl in *.
    subst.
    assert (bs !! saB = Some r) as Hbs.
    { by eapply Hskts. }
    destruct (decide (r = [])) as [-> | Hneq].
    - iMod (fupd_mask_intro_subseteq _ ∅ True%I with "[]") as "Hmk";
        first set_solver; auto.
      iModIntro. iSplitR.
      { by iPureIntro; do 4 eexists; eapply SocketStepS; eauto; econstructor. }
      iIntros (v2' ? ? ? Hstep).
      inv_head_step.
      { assert (length (r ++ [m]) = length ([] : list message))
          as Hdone; [by f_equal|].
        rewrite app_length /= in Hdone. lia. }
      rewrite (insert_id (state_sockets σ)); last done.
      iNext.
      iMod "Hmk" as "_".
      iModIntro.
      iExists (retransmit_model_base.Start, ms, bs), (inl (Brole, None)).
      rewrite -message_history_evolution_id.
      rewrite Heqn.
      iFrame.
      iSplitR; last first.
      { iSplitL; [|done]. by iApply ("IH" with "Hsh Hrt HB HΦ"). }
      iPureIntro.
      rewrite /trace_ends_in in Hex.
      rewrite /trace_ends_in in Hex.
      split; [econstructor;[done|econstructor|done]|].
      { rewrite lookup_total_alt. by rewrite Hbs. }
      rewrite Hex in Hms. rewrite Heqn in Hms.
      split; [done|].
      split; [|done].
      intros ℓ ζ Hlabels Henabled.
      rewrite right_id_L.
      rewrite Hex in Hlive. eapply Hlive; [done|by rewrite Heqn].
    - iMod (fupd_mask_intro_subseteq _ ∅ True%I with "[]") as "Hmk";
        first set_solver; auto.
      iModIntro. iSplitR.
      { iPureIntro. apply last_is_Some in Hneq as [m Hneq].
        apply last_Some in Hneq as [? ->].
        do 4 eexists; eapply SocketStepS; eauto; econstructor; eauto 2. }
      iIntros (v2' ? ? ? Hstep).
      inv_head_step.
      iNext.
      iMod "Hmk" as "_".
      iAssert (socket_address_group_own {[saB]})%I as "#HsaB".
      { iDestruct "Hrt" as "[(%send & %recv & _ & _ & _ & $ & _) _]". }

      iPoseProof (aneris_state_interp_receive_some saB {[saB]} _ _ _ _ (Some _)
                   with "[] [$HΨ] [$Hσ] [$Hsh] [Hrt]")
        as (R' sagT) "(%HinT & #HownT & %Hhist & %HR & Hrt & Hrest)";
        [by set_solver..| | |].
      { iFrame "#". iPureIntro. set_solver. }
      { iDestruct "Hrt" as "[$ Hrt]". }
      iMod "Hrest" as "(Hσ & Hsh & Ha)".
      iMod (live_roles_auth_delete with "Hlive_auth HB") as "Hlive_auth".
      iMod (dead_role_auth_extend _ (Brole : fmrole retransmit_fair_model) with "Hdead_auth")
        as "[Hdead_auth Hdead_own]"; [by set_solver|].
      iModIntro.
      iExists (retransmit_model_base.Received, ms, <[saB:=r0]>bs),
                (inl (Brole, None)).
      rewrite Heqn Hhist=> /=.
      rewrite /thread_live_roles_interp /retransmit_live_roles. simpl in *.
      replace ({[Arole; Brole]} ∖ {[Brole]}) with ({[Arole]} : gset _)
                                                  by set_solver.
      replace({[Brole]} ∪ all_roles ∖ {[Arole; Brole]}) with
        (all_roles ∖ {[Arole]} : gset _) by set_solver.
      rewrite !right_id_L.
      iFrame "Hauth Hlive_auth Hdead_auth Hσ".
      iSplitR "HΦ Hdead_own"; last first.
      { iSplit; [|done]. iApply wp_value. by iApply "HΦ". }
      iPureIntro.
      split; [econstructor;[done|econstructor|done]|].
      { rewrite lookup_total_alt. by rewrite Hbs. }
      rewrite Hex in Hms. rewrite Heqn in Hms.
      split; [done|].
      split; last first.
      { split; [done|]. by eapply state_buffers_delete. }
      intros [ℓ α] ζ Hlabels Henabled.
      rewrite Hex in Hlive. rewrite Heqn in Hlive. simpl.
      assert (ℓ = Arole).
      { rewrite /role_enabled_model in Henabled. simpl in *.
        rewrite /retransmit_live_roles in Henabled. simpl in *.
        set_solver. }
      simplify_eq.
      eapply from_locale_step; last first.
      { eapply Hlive; [done|].
        rewrite /role_enabled_model.
        set_solver. }
      eapply locale_step_atomic; eauto.
      { f_equiv; [|done].
        f_equiv. f_equiv. apply app_nil_end. }
      repeat econstructor; set_solver.
  Qed.

End with_Σ.

(* Definition initial_state shA shB := *)
(*   ([mkExpr ipA (Aprog shA); mkExpr ipB (Bprog shB)], *)
(*      {| state_heaps := {[ipA:=∅; ipB:=∅]}; *)
(*        state_sockets := {[ipA := {[shA := (sA, [])]}; *)
(*                           ipB := {[shB := (sB, [])]}]}; *)
(*        state_ms := ∅; |}). *)

(* Lemma no_drop_dup_continued_simulation shA shB : *)
(*   fairly_terminating (initial_state shA shB). *)
(* Proof. *)
(*   assert (anerisPreG simple_fair_model (anerisΣ simple_fair_model)) as HPreG. *)
(*   { apply _. } *)
(*   eapply (simulation_adequacy_fair_termination_multiple _ _ _ _ _ {[saA;saB]}); *)
(*     [simpl; lia| |set_solver|set_solver| |set_solver|set_solver|..| |]=> /=. *)
(*   { intros ℓ ζ Hmatch Henabled. rewrite /role_enabled_model in Henabled. simpl. *)
(*     assert (ℓ = A_role ∨ ℓ = B_role) as [Heq|Heq] by set_solver; simplify_eq. *)
(*     - assert (ζ = ("0.0.0.0", 0%nat)) as ->. *)
(*       { rewrite /labels_match /locale_simple_label in Hmatch. *)
(*         by repeat case_match; simplify_eq. } *)
(*       eexists _. simpl. done. *)
(*     - assert (ζ = ("0.0.0.1", 0%nat)) as ->. *)
(*       { rewrite /labels_match /locale_simple_label in Hmatch. *)
(*         by repeat case_match; simplify_eq. } *)
(*       eexists _. simpl. done. } *)
(*   { iIntros (Hinv) "!> Hunallocated Hrt Hlive Hdead Hfree Hnode Hlbl Hsendevs Hrecvevs". *)
(*     iIntros "Hsend_obs Hrecv_obs". *)
(*     iIntros "!>". *)
(*     iDestruct (unallocated_split with "Hunallocated") as "[HA HB]"; [set_solver|]. *)
(*     rewrite big_sepS_union; [|set_solver]. *)
(*     iDestruct "Hrt" as "[HrtA HrtB]". *)
(*     rewrite !big_sepS_singleton. *)
(*     rewrite /simple_live_roles=> /=. *)
(*     replace ({[A_role; B_role]} ∖ config_roles) with (({[A_role; B_role]}):gset _) *)
(*                                                      by set_solver. *)
(*     iDestruct (live_roles_own_split with "Hlive") as "[HliveA HliveB]"; *)
(*       [set_solver|]. *)
(*     iSplitL "HrtA". *)
(*     { iApply (wp_A with "[HrtA]"); [admit|]. *)
(*       iIntros "!>" (v) "H". *)
(*       iExists _. by iFrame. } *)
(*     iSplitL "HrtB". *)
(*     { iApply (wp_B with "[HrtB]"); [admit|]. *)
(*       iIntros "!>" (v) "H". *)
(*       iExists _. by iFrame. } *)
(*     done. } *)
(*   (* Needs to simplify requirements on initial node in Aneris adequacy *) *)
(* Admitted. *)
