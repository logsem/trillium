From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From fairneris Require Export trace_utils fairness env_model fuel ltl_lite.
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

Class LiveModelEq `(LM: LiveModel aneris_lang (joint_model Mod net_model)) := {
    cfg_labels_match_is_eq: ∀ x y, lm_cfg_labels_match LM x y ↔ x = y;
    actions_match_is_eq: ∀ x y, lm_actions_match LM x y ↔ Some x = y;
}.
Arguments LiveModelEq {_}.

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

  Definition network_fair_delivery_of msg : jmtrace → Prop :=
    □ (□◊ ℓ↓send_filter msg → ◊ ℓ↓ deliver_filter msg).

  Definition network_fair_delivery (mtr : jmtrace) : Prop :=
    ∀ msg, network_fair_delivery_of msg mtr.
End fairness.

Section fuel_fairness.
  Context `{@LiveModelEq M LM}.

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
    fuel_se fuel_network_fair_delivery network_fair_delivery.
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

Eval cbv in (ex_label aneris_lang).

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
  Context `{@LiveModelEq M LM}.

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
        destruct l1 as [[? [|]]|], l2 =>//=; try naive_solver.
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
