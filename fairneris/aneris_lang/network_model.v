From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From fairneris Require Export trace_utils fairness env_model fuel ltl_lite env_model_project fair_resources.
From fairneris.aneris_lang Require Import ast network lang aneris_lang.

Definition net_state : Set :=
  message_multi_soup * gmap socket_address (list message).

Inductive net_trans : net_state → (action aneris_lang + config_label aneris_lang) → net_state → Prop :=
| NetSend ms bs msg :
  net_trans (ms, bs) (inl $ Send msg) (ms ⊎ {[+ msg +]}, bs)
| NetDuplicate ms bs msg :
  msg ∈ ms → net_trans (ms, bs) (inr $ Duplicate msg) (ms ⊎ {[+ msg +]}, bs)
| NetDrop ms bs msg :
  msg ∈ ms →
  net_trans (ms, bs) (inr (Drop msg)) (ms ∖ {[+ msg +]}, bs)
| NetDeliver ms ms' bs msg :
  msg ∈ ms →
  bs !!! m_destination msg = ms' →
  net_trans (ms, bs) (inr (Deliver msg)) (ms ∖ {[+ msg +]}, <[m_destination msg := msg::ms']>bs)
| NetRecvFail ms bs sa :
  bs !!! sa = [] →
  net_trans (ms, bs) (inl $ (Recv sa None)) (ms, bs)
| NetRecvSucc ms bs msg ms' sa :
  bs !!! sa = ms'++[msg] →
  net_trans (ms, bs) (inl $ Recv sa (Some msg)) (ms, <[sa := ms']>bs).

Program Definition net_lts : Lts (action aneris_lang + config_label aneris_lang) :=
  {|
    lts_state := net_state;
    lts_trans := net_trans;
  |}.

Definition model_state_socket_coh
           (skts : gmap ip_address sockets)
           (bs : gmap socket_address (list message)) :=
  ∀ ip Sn sh skt sa ms,
  skts !! ip = Some Sn → Sn !! sh = Some (skt,ms) →
  saddress skt = Some sa →
  bs !!! sa = ms.

Definition config_net_match (c : cfg aneris_lang) (δ : net_state) :=
  state_ms c.2 = δ.1 ∧ model_state_socket_coh (state_sockets c.2) δ.2.

Definition net_apply_trans (s: net_state) (l: action aneris_lang + config_label aneris_lang) : net_state :=
  let '(ms, bs) := s in
  match l with
  | inl (Send msg) => (ms ⊎ {[+ msg +]}, bs)
  | inr (Duplicate msg) => (ms ⊎ {[+ msg +]}, bs)
  | inr (Drop msg) => (ms ∖ {[+ msg +]}, bs)
  | inr (Deliver msg) =>
      let ms' := bs !!! m_destination msg in
      (ms ∖ {[+ msg +]}, <[m_destination msg := msg::ms']>bs)
  | inl (Recv _ None) => (ms, bs)
  | inl (Recv _ (Some msg)) =>
      let ms' := bs !!! m_destination msg in
      (ms, <[m_destination msg := take (length ms' - 1) ms']>bs)
  end.

Program Definition net_model : EnvModel aneris_lang :=
  {|
    env_lts := net_lts;
    env_states_match := config_net_match;
    env_apply_trans := net_apply_trans;
    env_fairness _ := True;
  |}.
Next Obligation.
  (* Correctness of [net_apply_trans] *)
Admitted.
Next Obligation.
  (* Correctness of [net_apply_trans] *)
Admitted.
Next Obligation.
  (* Unlabeled steps don't change the network state *)
Admitted.

Section fairness.
  Context {M: UserModel aneris_lang}.

  Notation jmlabel := ((usr_role M * option (action aneris_lang)) + config_label aneris_lang)%type.
  Notation jmtrace := (trace (joint_model M net_model) jmlabel).

  Definition send_filter msg : jmlabel → Prop :=
    λ l, ∃ ρ, l = inl $ (ρ, Some $ Send msg).
  Instance send_filter_decision msg l : Decision (send_filter msg l).
  Proof. apply make_decision. Qed.

  Definition deliver_filter msg : jmlabel → Prop :=
    λ l, l = inr $ Deliver msg.
  Instance deliver_filter_decision msg l : Decision (deliver_filter msg l).
  Proof. apply make_decision. Qed.

  Definition recv_filter msg : jmlabel → Prop :=
    λ l, ∃ ρ, l = inl $ (ρ, Some $ Recv (m_destination msg) (Some msg)).
  Instance recv_filter_decision msg l : Decision (recv_filter msg l).
  Proof. apply make_decision. Qed.

  Definition any_recv_filter sa : jmlabel → Prop :=
    λ l, ∃ ρ omsg, l = inl $ (ρ, Some $ Recv sa omsg).
  Instance any_recv_filter_decision msg l : Decision (any_recv_filter msg l).
  Proof. apply make_decision. Qed.

  Definition jm_network_fair_delivery_of msg : jmtrace → Prop :=
    □ (□◊ ℓ↓send_filter msg → ◊ ℓ↓ deliver_filter msg).

  Definition jm_network_fair_delivery (mtr : jmtrace) : Prop :=
    ∀ msg, jm_network_fair_delivery_of msg mtr.

  Definition jm_network_fair_send_receive_of msg : jmtrace → Prop :=
    □ (□◊ℓ↓send_filter msg → □◊ℓ↓ any_recv_filter (m_destination msg) → ◊ℓ↓ recv_filter msg).

  Definition jm_network_fair_send_receive (mtr : jmtrace) : Prop :=
    ∀ msg, jm_network_fair_send_receive_of msg mtr.


  Definition usr_send_filter msg : lts_label M → Prop :=
    λ l, ∃ ρ, l = (ρ, Some $ Send msg).
  Instance usr_send_filter_decision msg l : Decision (usr_send_filter msg l).
  Proof. apply make_decision. Qed.

  Definition usr_recv_filter msg : lts_label M → Prop :=
    λ l, ∃ ρ, l = (ρ, Some $ Recv (m_destination msg) (Some msg)).
  Instance usr_recv_filter_decision msg l : Decision (usr_recv_filter msg l).
  Proof. apply make_decision. Qed.

  Definition usr_any_recv_filter sa : lts_label M → Prop :=
    λ l, ∃ ρ omsg, l = (ρ, Some $ Recv sa omsg).
  Instance usr_any_recv_filter_decision msg l : Decision (usr_any_recv_filter msg l).
  Proof. apply make_decision. Qed.

  Definition usr_network_fair_send_receive_of msg : lts_trace M → Prop :=
    □ (□◊ℓ↓ usr_send_filter msg → □◊ℓ↓ usr_any_recv_filter (m_destination msg) → ◊ℓ↓ usr_recv_filter msg).

  Definition usr_network_fair_send_receive (utr : lts_trace M) : Prop :=
    ∀ msg, usr_network_fair_send_receive_of msg utr.
End fairness.

Instance aneris_good_lang : GoodLang aneris_lang.
Proof. Qed.

Section fuel_fairness.
  Context `{LM: LiveModel aneris_lang (joint_model M net_model)}.
  Context `{!LiveModelEq LM}.

  Notation jmlabel := ((usr_role M * option (action aneris_lang)) + config_label aneris_lang)%type.
  Notation jmtrace := (trace (joint_model M net_model) jmlabel).

  Notation fuel_trace := (trace LM LM.(lm_lbl)).

  Definition fuel_send_filter msg : LM.(lm_lbl) → Prop :=
    λ l, ∃ ρ ζ x, l = Take_step ρ (Some $ Send msg : fmaction (joint_model M _)) ζ x.
  Instance fuel_send_filter_decision msg l : Decision (fuel_send_filter msg l).
  Proof. apply make_decision. Qed.

  Definition fuel_deliver_filter msg : LM.(lm_lbl) → Prop :=
    λ l, ∃ x, l = Config_step (Deliver msg : fmconfig (joint_model M _)) x.
  Instance fuel_deliver_filter_decision msg l : Decision (fuel_deliver_filter msg l).
  Proof. apply make_decision. Qed.

  Definition fuel_network_fair_delivery_of msg : fuel_trace → Prop :=
    □ (□◊ ℓ↓fuel_send_filter msg → ◊ ℓ↓ fuel_deliver_filter msg).

  Definition fuel_network_fair_delivery (mtr : fuel_trace) : Prop :=
    ∀ msg, fuel_network_fair_delivery_of msg mtr.

  Lemma fuel_network_fairness_destutter :
    fuel_se fuel_network_fair_delivery jm_network_fair_delivery.
  Proof.
    apply ltl_se_forall=> msg.
    apply ltl_se_always, ltl_se_impl.
    - apply ltl_se_always, ltl_se_eventually_now.
      intros l. rewrite /fuel_send_filter /send_filter. split.
      + intros (?&?&?). simplify_eq. naive_solver.
      + intros (?&?&?&?). simplify_eq. destruct l=>//. simpl in *. simplify_eq.
        eexists _, _, _. reflexivity.
    - apply ltl_se_eventually_now.
      intros l. rewrite /fuel_deliver_filter /deliver_filter. split; first naive_solver.
      + intros (?&?&?). simplify_eq. destruct l=>//. simpl in *; simplify_eq. naive_solver.
  Qed.
End fuel_fairness.

Definition ex_send_filter msg : ex_label aneris_lang → Prop :=
  λ l, sum_map snd id l = inl $ Some $ Send msg.
Instance ex_send_filter_decision msg l : Decision (ex_send_filter msg l).
Proof. apply make_decision. Qed.

Definition ex_deliver_filter msg : ex_label aneris_lang → Prop :=
  λ l, sum_map snd id l = inr $ Deliver msg.
Instance ex_deliver_filter_decision msg l : Decision (ex_deliver_filter msg l).
Proof. apply make_decision. Qed.
Definition ex_fair_network_of msg : extrace aneris_lang → Prop :=
  □ (□◊ ℓ↓ex_send_filter msg → ◊ ℓ↓ex_deliver_filter msg).

Definition ex_fair_network (extr : extrace aneris_lang) : Prop :=
  ∀ msg, ex_fair_network_of msg extr.

Section exec_fairness.
  Context `{LM: LiveModel aneris_lang (joint_model M net_model)}.
  Context `{!LiveModelEq LM}.

  Lemma exec_fuel_fairness:
    exaux_tme (LM := LM) ex_fair_network fuel_network_fair_delivery.
  Proof.
    apply ltl_tme_forall=> msg.
    apply ltl_tme_always, ltl_tme_impl.
    - apply ltl_tme_always, ltl_tme_eventually, ltl_tme_now.
      intros l1 l2 Hlm. split.
      + destruct l1 as [[? [|]]|], l2 =>//=; try naive_solver.
        rewrite /ex_send_filter /=. intros ?. simplify_eq.
        destruct Hlm as (?&?&Hlm). apply actions_match_is_eq in Hlm. simplify_eq.
        rewrite /fuel_send_filter. naive_solver.
      + rewrite /fuel_send_filter /ex_send_filter.
        destruct l1 as [[? ?]|], l2 =>//=; try naive_solver.
        intros ?. simplify_eq.
        destruct Hlm as (?&?&Hlm). apply actions_match_is_eq in Hlm. simplify_eq.
        rewrite /fuel_send_filter. naive_solver.
    - apply ltl_tme_eventually, ltl_tme_now.
      intros l1 l2 Hlm. split.
      + destruct l1 as [|[| |]], l2 =>//=; try naive_solver.
        rewrite /ex_deliver_filter /=. intros ?. simplify_eq.
        destruct Hlm as (?&Hcm). apply cfg_labels_match_is_eq in Hcm. simplify_eq.
        rewrite /fuel_deliver_filter. naive_solver.
      + rewrite /ex_deliver_filter /fuel_deliver_filter. intros (?&?). simplify_eq.
        destruct l1 as [[?[|]]|] =>//=; try naive_solver.
        destruct Hlm as [? Hlm].
        apply cfg_labels_match_is_eq in Hlm. simplify_eq. done.
  Qed.
End exec_fairness.

Section fairness.
  Context {M: UserModel aneris_lang}.

  Notation jmlabel := ((usr_role M * option (action aneris_lang)) + config_label aneris_lang)%type.
  Notation jmtrace := (trace (joint_model M net_model) jmlabel).

  Notation ltl_equiv P := (ltl_tme (S1 := joint_model M net_model) (L1 := jmlabel)
                             eq eq (λ _ _ _, True) (λ _ _ _, True) P P).

  Lemma trim_preserves_network_fairness (tr: jmtrace):
    jm_network_fair_delivery tr →
    jm_network_fair_delivery (trim_trace tr).
  Proof.
    rewrite /jm_network_fair_delivery /jm_network_fair_delivery_of.
    intros Hf msg. specialize (Hf msg).
    apply trace_alwaysI. intros tr' Hsuff. rewrite trace_impliesI. intros Hae.
    have Hinf: infinite_trace tr'.
    { by eapply trace_always_eventually_label_infinite. }
    have Hinf': infinite_trace (trim_trace tr).
    { eapply trace_suffix_of_infinite=>//. }
    apply trim_trace_infinite in Hinf'.
    rewrite trace_alwaysI in Hf.
    eapply traces_match_suffix_of in Hsuff as (tr''&Hsuff'&?)=>//.
    specialize (Hf _ Hsuff').
    rewrite trace_impliesI in Hf.

    have Hleq: ltl_equiv (□ ◊ ℓ↓ send_filter msg).
    { apply ltl_tme_always, ltl_tme_eventually, ltl_tme_now. naive_solver. }

    ospecialize (Hf _); first by eapply Hleq=>//.

    have {}Hleq: ltl_equiv (◊ ℓ↓ deliver_filter msg).
    { apply ltl_tme_eventually, ltl_tme_now. naive_solver. }

    eapply Hleq=>//.
  Qed.
End fairness.


Section user_fairness.
  Context {M: UserModel aneris_lang}.

  Notation jmlabel := ((usr_role M * option (action aneris_lang)) + config_label aneris_lang)%type.
  Notation jmtrace := (trace (joint_model M net_model) jmlabel).

  Notation buffer_of sa ns := (ns.2.2 !!! sa).

  Local Lemma not_receive_buffer {msg rest s ℓ} {tr : jmtrace} :
    let sa := m_destination msg in
   (∃ pre : list message, buffer_of sa (trfirst (s -[ ℓ ]-> tr)) = pre ++ msg :: rest) →
   jmtrace_valid (s -[ ℓ ]-> tr) →
   trace_not (ℓ↓ any_recv_filter (m_destination msg)) (s -[ ℓ ]-> tr) →
   ∃ pre : list message, buffer_of sa (trfirst tr) = pre ++ msg :: rest.
  Proof.
    intros sa Hbuf1 Hv Hnot.
    apply trace_always_elim in Hv. simpl in Hv.
    destruct (trfirst tr) eqn:Heq. rewrite Heq in Hv.
    destruct Hbuf1 as (pre&Hbuf1). simpl in Hbuf1.
    inversion Hv as [| AA BB CC DD Hnet FF|??????? Hnet]; simplify_eq.
    - by exists pre.
    - inversion Hnet; simplify_eq; try (by exists pre).
      match goal with
      | [_: ?msg0 ∈ _ |- _] => pose msg' := msg0
      end.
      destruct (decide (m_destination msg' = sa)) as [Heq'|].
      + exists (msg'::pre). rewrite /= /msg' Heq' lookup_total_insert Hbuf1 //.
      + exists pre. rewrite lookup_total_insert_ne //.
    - inversion Hnet; simplify_eq; try (by exists pre).
      match goal with
      | [_: _ !!! ?sa0 = _ |- _] => pose sa' := sa0
      end.
      destruct (decide (sa' = sa)) as [Heq'|].
      + exfalso. apply Hnot. rewrite /sa' in Heq'. rewrite /trace_label /pred_at /any_recv_filter Heq' /=.
        naive_solver.
      + exists pre. rewrite lookup_total_insert_ne //.
  Qed.

  Proposition network_fairness_user (jmtr: jmtrace) :
    jmtrace_valid jmtr →
    jm_network_fair_delivery jmtr →
    jm_network_fair_send_receive jmtr.
  Proof.
    intros Hv Hf msg. apply trace_alwaysI. intros tr' Hsuff.
    apply trace_impliesI. intros Hae.
    specialize (Hf msg).
    rewrite /jm_network_fair_delivery_of trace_alwaysI in Hf. specialize (Hf _ Hsuff).
    rewrite trace_impliesI in Hf. specialize (Hf Hae). clear Hae.
    rewrite trace_impliesI. intros Hae.
    apply trace_always_eventually_always_until in Hae.

    rewrite trace_eventuallyI in Hf. destruct Hf as (tr1&Hsuff1&Hdel).
    destruct tr1 as [|s1 ℓ1 tr1].
    { rewrite /trace_label /pred_at //= in Hdel. }
    pose sa := m_destination msg.
    assert (∃ rest, (buffer_of sa (trfirst tr1) = msg::rest)) as [rest Hbuf1].
    { do 2 eapply trace_always_suffix_of in Hv=>//.
      apply trace_always_elim in Hv. simpl in Hv.
      destruct (trfirst tr1) eqn:Heq. rewrite Heq in Hv.
      rewrite /trace_label /pred_at /deliver_filter /= in Hdel.
      inversion Hv as [|???? Hnet|]; simplify_eq.
      inversion Hnet; simplify_eq.
      eexists. simpl. rewrite lookup_total_insert. done. }

    (* Execute unil the next message in the buffer is msg *)
    assert (∃ tr2, trace_suffix_of tr2 tr1 ∧ ∃ pre, buffer_of sa (trfirst tr2) = pre ++ [msg])
      as [tr2 [Hsuff2 Hbuf2]].
    { have {Hv}: jmtrace_valid tr1.
      { eapply trace_always_suffix_of =>//. eapply trace_suffix_of_trans;
          [eapply trace_suffix_of_cons_l=>// | done]. }
      have {Hbuf1}: ∃ pre, buffer_of sa (trfirst tr1) = pre ++ msg :: rest by exists nil.
      have {Hae}: (□ trace_until (trace_not (ℓ↓ any_recv_filter (m_destination msg))) (ℓ↓ any_recv_filter (m_destination msg))) tr1.
      { eapply trace_always_suffix_of =>//. eapply trace_suffix_of_cons_l=>//. }
      clear Hdel Hsuff1.
      revert tr1. induction rest as [|msg' rest IH] using rev_ind.
      { intros tr1 Hae [pre Hbuf1] Hv. exists tr1; split; first apply trace_suffix_of_refl. exists pre=>//. }
      intros tr1 Hae Hbuf Hv.
      have Hrecvs := Hae.
      apply trace_always_elim in Hrecvs.
      induction Hrecvs as [tr Hnow|s ℓ tr Hnot Huntil IHuntil].
      - destruct tr as [s|s2 ℓ2 tr2] eqn:Htr.
        { rewrite /trace_label /pred_at //= in Hnow. }
        rewrite /trace_label /pred_at /= in Hnow.
        destruct ℓ2 as [ℓ2|ℓ2]; last first.
        { rewrite /any_recv_filter in Hnow. naive_solver. }
        have Hv' := Hv.
        rewrite /any_recv_filter in Hnow. destruct Hnow as (ρ&omsg&Heq). simplify_eq.
        apply trace_always_elim in Hv. simpl in Hv.
        destruct (trfirst tr2) eqn:Heq. rewrite Heq in Hv.
        destruct Hbuf as (pre&Hbuf1). simpl in Hbuf1.
        inversion Hv as [| | ??????? Hnet]; simplify_eq.
        simpl in Hbuf1.
        inversion Hnet; simplify_eq;
        match goal with
        | [H: _ !!! _ = _ |- _] => rewrite Hbuf1 in H
        end.
        + exfalso. destruct pre=>//.
        + list_simplifier.
          odestruct (IH tr2 _ _ _) as (tr3&Hsuff3&pre3&Heq3).
          { eapply trace_always_suffix_of in Hae =>//.
            apply trace_suffix_of_cons_r'. }
          { exists pre. rewrite Heq /= lookup_total_insert //. }
          { eapply trace_always_suffix_of=>//. apply trace_suffix_of_cons_r'. }
          exists tr3. split=>//; last by exists pre3.
          apply (trace_suffix_of_trans _ tr2)=>//. apply trace_suffix_of_cons_r, trace_suffix_of_refl.
      - have Hbuf':  ∃ pre : list message, buffer_of sa (trfirst tr) = pre ++ msg :: rest ++ [msg'].
        { eapply not_receive_buffer=>//. }
        odestruct (IHuntil _ Hbuf' _) as (tr2&Hsuff2&pre2&Hbuf2).
        { eapply trace_always_suffix_of=>//. apply trace_suffix_of_cons_r'. }
        { eapply trace_always_suffix_of=>//. apply trace_suffix_of_cons_r'. }
        exists tr2. split=>//; last by exists pre2. apply (trace_suffix_of_trans _ tr)=>//.
        apply trace_suffix_of_cons_r'. }
    (* Now we need to execute until the next receive!. *)
    rewrite trace_alwaysI in Hae. ospecialize (Hae tr2 _).
    { apply (trace_suffix_of_trans _ tr1)=>//. by apply trace_suffix_of_cons_l in Hsuff1. }
    have {Hv}: jmtrace_valid tr'.
    { eapply trace_always_suffix_of; done. }
    induction Hae as [tr2 Hnow |s ℓ tr2 Hnot Huntil IH]; intros Hv.
    - have Hsuff3: trace_suffix_of tr2 tr'.
      { eapply (trace_suffix_of_trans _ tr1)=>//. by eapply trace_suffix_of_cons_l. }
      have {}Hv: jmtrace_valid tr2.
      { eapply trace_always_suffix_of; done. }
      apply trace_eventuallyI. exists tr2. split=>//.
      destruct tr2 as [|s2 ℓ2 tr3] eqn:Heq; first done.
      destruct Hnow as (ρ&omsg&Heq'). simplify_eq.
      apply trace_always_elim in Hv. simpl in Hv.
      destruct (trfirst tr3) eqn:Heq. rewrite Heq in Hv.
      destruct Hbuf2 as (pre2&Hbuf2). simpl in Hbuf2.
      inversion Hv as [| | ??????? Hnet]; simplify_eq.
      inversion Hnet; simplify_eq.
      + rewrite /sa /= in Hbuf2. rewrite -> Hbuf2 in *. destruct pre2=>//.
      + rewrite /sa /= in Hbuf2. rewrite -> Hbuf2 in *. list_simplifier.
      rewrite /trace_label /pred_at /recv_filter /=. naive_solver.
    - opose proof (not_receive_buffer Hbuf2 _ Hnot).
      { eapply trace_always_suffix_of; last done.
        eapply (trace_suffix_of_trans _ tr1) =>//.
        by eapply trace_suffix_of_cons_l. }
      apply IH=>//. by eapply trace_suffix_of_cons_l.
  Qed.

  Proposition network_fairness_project_usr (jmtr: jmtrace) (utr: lts_trace M) :
    jmtrace_valid jmtr →
    upto_stutter_env jmtr utr →
    jm_network_fair_delivery jmtr →
    usr_network_fair_send_receive utr.
  Proof.
    move=> Hval ? /network_fairness_user Hf // msg. specialize (Hf Hval msg).
    have Hse //: ltl_se_env (M := M) (jm_network_fair_send_receive_of msg) (usr_network_fair_send_receive_of msg);
      last by eapply Hse.
    apply ltl_se_always, ltl_se_impl; last apply ltl_se_impl.
    - apply ltl_se_always, ltl_se_eventually_now. rewrite /send_filter /usr_send_filter.
      intros [?|?]; naive_solver.
    - apply ltl_se_always, ltl_se_eventually_now. rewrite /any_recv_filter /usr_any_recv_filter.
      intros [?|?]; naive_solver.
    - apply ltl_se_eventually_now. rewrite /recv_filter /usr_recv_filter. intros [?|?]; naive_solver.
  Qed.
End user_fairness.
