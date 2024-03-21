From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From fairneris Require Export trace_utils fairness env_model fuel.
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

Record Lts lab `{Countable lab, Inhabited lab}: Type := {
  lts_state :> Type;
  lts_state_eqdec :: EqDecision lts_state;
  lts_state_inhabited :: Inhabited lts_state;

  lts_trans: lts_state → lab → lts_state → Prop;
}.

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

Class LiveModelEq `(LM: LiveModel aneris_lang (joint_model Mod network_model)) := {
    cfg_labels_match_is_eq: ∀ x y, lm_cfg_labels_match LM x y ↔ x = y;
    actions_match_is_eq: ∀ x y, lm_actions_match LM x y ↔ Some x = y;
}.
Arguments LiveModelEq {_ _}.
