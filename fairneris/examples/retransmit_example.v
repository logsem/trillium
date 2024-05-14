From stdpp Require Import list fin_maps.
From iris.proofmode Require Import proofmode.
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
  (rec: "go" <> := SendTo "shA" #"Hello" #saB;; "go" #()) #().

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

  Notation loA := (ip_of_address saA, tidA).

  Lemma wp_A E :
    {{{ is_node loA.1 ∗ saB ⤇ (λ _, True) ∗ loA ↦M {[ Arole := 10%nat ]} ∗
          saA ⤳ (∅, ∅) ∗ free_ports (ip_of_address saA) {[port_of_address saA]} }}}
      (mkExpr (ip_of_address saA) (Aprog saA saB)) @ loA; E
    {{{ v, RET v; loA ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hisn & #Hmsg & HA & Hrt & Hfp) HΦ".

    rewrite /Aprog.
    wp_bind (NewSocket _).

    iApply sswp_MU_wp. iApply wp_new_socket=>//.
    iIntros (sh) "Hsh'".

    mu_fuel.
    iApply wp_value'.

    idtac "ASDLKFJ".
    wp_pure _.
    wp_pure _.

    wp_bind (SocketBind _ _).
    change "0.0.0.0" with (ip_of_address saA).
    iApply sswp_MU_wp.
    iApply (wp_socketbind with "[Hfp] [Hsh']")=>//=; first done.
    iIntros "Hsh".
    mu_fuel.
    iApply wp_value'.
    wp_pure _.

    iAssert (∃ R T, saA ⤳ (R, T) ∗
            [∗ set] m ∈ R, socket_address_group_own {[m_sender m]})%I
      with "[Hrt]" as (R T) "[HRT HR]"; [by eauto|].
    wp_pure _.

    iLöb as "IH" forall (R T).

    wp_pure _.
    wp_pure _.

    wp_bind (SendTo _ _ _).
    iApply sswp_MU_wp.
    iApply (wp_send _ _ false with "[Hsh] [HRT] [Hmsg]")=>//=>//=>//.
    iIntros "Hsh HRT".

    (* TODO: put the model state in an invariant, and add ghost state on the second note to control it? *)

    iApply (mu_step_model _ _ _ _ ∅ ∅ with "Hmod [HA] []").

  Lemma mu_step_model `{!LiveModelEq LM} ζ ρ α (f1 : nat) fs fr s1 s2 E P :
    lts_trans Mod s1 (ρ, α) s2 →
    Mod.(usr_live_roles) s2 ⊆ Mod.(usr_live_roles) s1 →
    ρ ∉ dom fs →
    ▷ frag_model_is s1 -∗
    ▷ ζ ↦M ({[ρ:=f1]} ∪ fmap S fs) -∗
    ▷ frag_free_roles_are fr -∗
    (frag_model_is s2 -∗
     ζ ↦M ({[ρ:=(Mod.(usr_fl) s2)]} ∪ fs) -∗
     frag_free_roles_are fr -∗ P) -∗
    MU E ζ α P.
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
