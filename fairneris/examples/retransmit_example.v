From stdpp Require Import list fin_maps.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From trillium.program_logic Require Import ectx_lifting.
From fairneris Require Import fairness fair_resources fuel.
From fairneris.examples Require Import retransmit_model.
From fairneris.aneris_lang Require Import proofmode.
From fairneris.aneris_lang.state_interp Require Import state_interp state_interp_events.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.

(*Temporary*)
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.

Definition Aprog (saA saB : socket_address) : expr :=
  let: "shA" := NewSocket #() in
  SocketBind "shA" #saA;;
  let: "f" := (rec: "go" <> := SendTo "shA" #"Hello" #saB;; "go" #()) in
  "f" #().

Definition Bprog shB : expr := ReceiveFrom #(LitSocket shB).

Tactic Notation "mu_fuel" :=
  let solve_fuel _ :=
    let fs := match goal with |- _ = Some (_, has_fuels _ ?fs) => fs end in
    iAssumptionCore || fail "wp_pure: cannot find" fs in
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (MU ?E ?locale None ?P) =>
      eapply (tac_mu_fuel _ locale E);
      [let fs := match goal with |- _ = Some (_, has_fuels _ ?fs) => fs end in
       iAssumptionCore || fail "mu_fuel: cannot find" fs
      | try apply map_non_empty_singleton; try apply insert_non_empty; try done
      | try solve_fuel_positive
      | pm_reduce; simpl_has_fuels; wp_finish
      ]
  | _ => fail "wp_pure: not a 'wp'"
  end.

Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?locale ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      idtac K;
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ _ _ (@fill base_ectxi_lang K e') _ _ 1); idtac "Hi";
      [ let fs := match goal with |- _ = Some (_, has_fuels _ ?fs) => fs end in
       iAssumptionCore || fail "wp_pure: cannot find" fs
      | tc_solve
      | try solve_fuel_positive
      | try apply map_non_empty_singleton; try apply insert_non_empty; try done
      | try naive_solver
      | tc_solve
      | pm_reduce; simpl_has_fuels; wp_finish
      ])
      (* [try tc_solve                       (* PureExec *) *)
      (* |try solve_vals_compare_safe    (* The pure condition for PureExec *) *)
      (* |try tc_solve                       (* IntoLaters *) *)
      (* |try wp_finish                      (* new goal *) *)
      (* ]) *)
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  end.

Section with_Σ.
  Context `{anerisG _ _ (live_model_of_user retransmit_model) Σ}.
  Let Ns := nroot .@ "retransmit".

  Notation loA := (ip_of_address saA, tidA).

  Definition retinv : iProp Σ := ∃ st, frag_model_is st ∗ True.

  Lemma wp_A f (Hf: f > 9) :
    {{{ inv Ns retinv ∗ frag_free_roles_are ∅ ∗ is_node loA.1 ∗ saB ⤇ (λ _, True) ∗
          loA ↦M {[ Arole := f ]} ∗ saA ⤳ (∅, ∅) ∗
          free_ports (ip_of_address saA) {[port_of_address saA]} }}}
      (mkExpr (ip_of_address saA) (Aprog saA saB)) @ loA; ⊤
    {{{ v, RET v; loA ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hfr & #Hisn & #Hmsg & HA & Hrt & Hfp) HΦ".

    rewrite /Aprog.
    wp_bind (NewSocket _).

    iApply sswp_MU_wp. iApply wp_new_socket=>//.
    iIntros (sh) "Hsh'".

    mu_fuel.
    iApply wp_value'.

    idtac "ASDLKFJ".
    do 2 wp_pure _.

    wp_bind (SocketBind _ _).
    change "0.0.0.0" with (ip_of_address saA).
    iApply sswp_MU_wp.
    iApply (wp_socketbind with "[Hfp] [Hsh']")=>//=; first done.
    iIntros "Hsh".
    mu_fuel.
    iApply wp_value'.
    do 5 wp_pure _.

    iAssert (∃ R T, saA ⤳ (R, T) ∗
            [∗ set] m ∈ R, socket_address_group_own {[m_sender m]})%I
      with "[Hrt]" as (R T) "[HRT HR]"; [by eauto|].
    iAssert (∃ f, ⌜ f > 0 ⌝ ∗ ("0.0.0.0", tidA) ↦M <[Arole:=f]> ∅)%I
      with "[HA]" as (f') "[Hf HA]".
    { iExists _. iSplit; last iFrame. iPureIntro. lia. }

    clear Hf.
    iLöb as "IH" forall (f' R T) "Hf".
    iDestruct "Hf" as %Hf.
    wp_pure _.

    wp_bind (SendTo _ _ _).
    iApply sswp_MU_wp_fupd.

    iInv Ns as (st) "(Hst & Hrest)" "Hclose".
    iModIntro.

    iApply (wp_send _ _ false with "[Hsh] [HRT] [Hmsg]")=>//=>//=>//.
    iIntros "Hsh HRT".

    iApply (mu_step_model _ _ _ _ ∅ ∅ _ st with "Hst [HA] [Hfr //]").
    { constructor. }
    { set_solver. }
    { set_solver. }
    { rewrite fmap_empty map_union_empty //. }
    iIntros "Hst HA Hfr".

    iMod ("Hclose" with "[Hst]").
    { iNext. iExists st. naive_solver. }
    iModIntro.
    simpl.
    rewrite /= ?map_union_empty //.

    iApply wp_value'.
    do 2 wp_pure _.
    iApply ("IH" $! 8 with "[$] [$] [$] [$] [$] [$] []").
    iPureIntro; lia.
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
    assert (bs !!! saB = r) as Hbs.
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
      iExists (retransmit_model.Start, ms, bs), (inl (Brole, None)).
      rewrite -message_history_evolution_id.
      rewrite Heqn.
      iFrame.
      iSplitR; last first.
      { iSplitL; [|done]. by iApply ("IH" with "Hsh Hrt HB HΦ"). }
      iPureIntro.
      rewrite /trace_ends_in in Hex.
      rewrite /trace_ends_in in Hex.
      split; [econstructor;[done|by econstructor|done]|].
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
      rewrite -H1 in Hr.
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
      iExists (retransmit_model.Received, ms, <[saB:=r]>bs),
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
      split; [econstructor;[done|by econstructor|done]|].
      rewrite Hex in Hms. rewrite Heqn in Hms.
      split; [done|].
      split; last first.
      { split; [done|]. by eapply state_buffers_delete. }
      intros ℓ ζ Hlabels Henabled.
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
        f_equiv. f_equiv. symmetry. apply app_nil_r. }
      repeat econstructor; set_solver.
  Qed.

End with_Σ.
