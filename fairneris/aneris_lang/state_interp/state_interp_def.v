From RecordUpdate Require Import RecordSet.
From stdpp Require Import fin_maps gmap option finite.
From trillium.prelude Require Import
     quantifiers finitary classical_instances sigma.
From iris.bi.lib Require Import fractional.
From iris.algebra Require Import auth.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap mono_nat.
From trillium.program_logic Require Import weakestpre adequacy.
From trillium.events Require Import event.
From fairneris Require Import fairness.
From fairneris.examples Require Import retransmit_model_progress_ltl.
From fairneris.prelude Require Import collect gset_map gmultiset.
From fairneris.aneris_lang Require Import resources events.
From fairneris.lib Require Import gen_heap_light.
From fairneris.aneris_lang Require Export aneris_lang network resources.
From fairneris.aneris_lang.state_interp Require Export messages_history.
From fairneris.algebra Require Import disj_gsets.
(* From fairneris Require Import model_draft. *)

Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section definitions.
  Context `{anerisG FM Σ}.
  Implicit Types σ : state.
  Implicit Types h : heap.
  Implicit Types H : gmap ip_address heap.
  Implicit Types S : gmap ip_address sockets.
  Implicit Types Sn : sockets.
  Implicit Types ps : gset port.
  Implicit Types ips : gset ip_address.
  Implicit Types M : message_multi_soup.
  Implicit Types R T : message_soup.
  Implicit Types m : message.
  Implicit Types a : socket_address.
  Implicit Types ip : ip_address.
  Implicit Types sh : socket_handle.
  Implicit Types skt : socket.
  Implicit Types A B : gset socket_address_group.
  Implicit Types mhm : messages_history_map.
  Implicit Types rt : message_soup * message_soup.
  Implicit Types γm : gmap ip_address node_gnames.
  Implicit Types sis : gmap socket_address_group gname.

  (** Local state coherence *)

  (* The local state of the node at [ip] is coherent
     with physical state [σ] and ghost names [γs]. *)
  Definition local_state_coh σ ip γs :=
    (∃ h Sn,
        ⌜state_heaps σ !! ip = Some h⌝ ∗
        ⌜state_sockets σ !! ip = Some Sn⌝ ∗
        mapsto_node ip γs ∗
        heap_ctx γs h ∗
        sockets_ctx γs ((λ x, x.1) <$> Sn))%I.

  (** The domains of heaps and sockets coincide with the gname map [γm] *)
  Definition gnames_coh γm H S :=
    dom γm = dom H ∧
    dom γm = dom S.

  Definition sis_own (sags : gset socket_address_group) : iProp Σ :=
    ∃ (sis : gmap socket_address_group gname),
      saved_si_auth sis ∗
      ⌜dom sis = sags⌝ ∗
      [∗ set] sag ∈ sags, ∃ φ, sag ⤇* φ.

  (** Socket interpretation coherence *)
  (* Addresses with socket interpretations are bound *)
  Definition socket_interp_coh :=
    (∃ (sags : gset socket_address_group)
       (A : gset socket_address_group),
        ⌜A ⊆ sags⌝ ∗
        (* socket_address_group_ctx A ∗ *)
        socket_address_group_ctx sags ∗
        (* [A] is the set of socket addresses without an interpretation *)
        unallocated_groups_auth A ∗
        (* [sags ∖ A] is the set of addresses with a saved socket interpretation *)
        sis_own (sags ∖ A))%I.

  (** Free ips coherence *)
  (* Free ips have no bound ports, no heap, and no sockets  *)
  Definition free_ips_coh σ :=
    (∃ free_ips free_ports,
      (* the domains of [free_ips] and [free_ports] are disjoint *)
      (⌜dom free_ports ## free_ips ∧
      (* if the ip [ip] is free, neither a heap nor a socket map has been
          allocated *)
      (∀ ip, ip ∈ free_ips →
              state_heaps σ !! ip = None ∧ state_sockets σ !! ip = None) ∧
      (* free ports and bound ports are disjoint *)
      (∀ ip ps, free_ports !! ip = Some (GSet ps) →
                ∀ Sn, (state_sockets σ) !! ip = Some Sn →
                      ∀ p, p ∈ ps → port_not_in_use p Sn)⌝) ∗
      (* we have the auth parts of the resources for free ips and ports *)
      free_ips_auth free_ips ∗
      free_ports_auth free_ports)%I.

  (** Network sockets coherence for bound ports, socket handlers,
      receive buffers, and socket addresses *)
  (* All sockets in [Sn] with the same address have the same handler *)
  Definition socket_handlers_coh Sn :=
    ∀ sh sh' skt skt' r r',
    Sn !! sh = Some (skt, r) →
    Sn !! sh' = Some (skt', r') →
    is_Some (saddress skt) →
    saddress skt = saddress skt' →
    sh = sh'.

  (* Sent and received messages at all socket in [Sn] are in [M] *)
  Definition socket_messages_coh Sn :=
    ∀ sh skt r a,
    Sn !! sh = Some (skt, r) →
    saddress skt = Some a →
    ∀ m, m ∈ r → m_destination m = a.

  (* All sockets in [Sn] are bound to ip address [ip] *)
  Definition socket_addresses_coh Sn ip :=
    ∀ sh skt r a,
    Sn !! sh = Some (skt, r) →
    saddress skt = Some a →
    ip_of_address a = ip.

  (* Receive buffers of unbound sockets are empty. *)
  Definition socket_unbound_empty_buf_coh Sn ip :=
    ∀ sh skt r,
    Sn !! sh = Some (skt, r) →
    saddress skt = None →
    r = [].

  Definition network_sockets_coh S :=
    ∀ ip Sn,
    S !! ip = Some Sn →
    socket_handlers_coh Sn ∧
    socket_messages_coh Sn ∧
    socket_addresses_coh Sn ip ∧
    socket_unbound_empty_buf_coh Sn ip.

  (* Every message present in the message soup [M] has been recorded in the
     message history [mhm] as sent from the node of its origin. *)
  Definition message_soup_coh M mhm :=
    ∀ m, m ∈ M → ∃ R T sag, (m_sender m) ∈ sag ∧ mhm !! sag = Some (R, T) ∧ m ∈ T.

  (* Every message in the receive buffers of [S] has been recorded in the
     message history [mhm] as sent from the node of its origin. *)
  Definition receive_buffers_coh S mhm :=
    ∀ ip Sn sh skt r m,
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    m ∈ r →
    ∃ R T sag, (m_sender m) ∈ sag ∧ mhm !! sag = Some (R, T) ∧ m ∈ T.

  Definition messages_history_coh M S mhm :=
    message_soup_coh M mhm ∧
    receive_buffers_coh S mhm ∧
    messages_addresses_coh mhm ∧
    messages_received_from_sent_coh mhm.

  (* For all messages [m] in [M], either the network owns the resources [Φ m]
     described by some socket protocol [Φ] or it has been delivered. *)
  Definition messages_resource_coh mhm : iProp Σ :=
    (* All sets in the domain of [mhm] are disjoint *)
    own (A:=authUR socket_address_groupUR) aneris_socket_address_group_name
        (◯ (DGSets (dom mhm))) ∗
    (* Take the set [ms] of sent messages closed under group equivalence *)
    ∃ ms,
      (* [ms] is a subset of [mhm], ... *)
      ⌜ms ⊆ (messages_sent mhm)⌝ ∗
      (* and carries one message, for each message sent by a group in `mhm` *)
      ([∗ set] m ∈ messages_sent mhm, ∃ sagT sagR m',
          ⌜m ≡g{sagT,sagR} m' ∧ m' ∈ ms⌝ ∗
          socket_address_group_own sagT ∗
          socket_address_group_own sagR) ∗
      (* For any message [m] in [ms] *)
      ([∗ set] m ∈ ms,
         ∃ sagT sagR Φ,
           (* The group of the message is disjoint, and *)
           ⌜m_destination m ∈ sagR⌝ ∗ sagR ⤇* Φ ∗
           socket_address_group_own sagT ∗
           (* either [m] is governed by a protocol [Φ] and the network owns the
              resources  specified by the protocol *)
           ((∃ m', ⌜m ≡g{sagT,sagR} m'⌝ ∗ ▷ Φ m') ∨
            (* or [m] has been delivered somewhere *)
            (∃ m', ⌜m ≡g{sagT,sagR} m'⌝ ∗ ⌜message_received m' mhm⌝))).

  (** State interpretation *)
  Definition aneris_state_interp σ (rt : messages_history) :=
    (∃ γm mhm,
        ⌜messages_received_sent mhm = rt⌝ ∗
        ⌜gnames_coh γm (state_heaps σ) (state_sockets σ)⌝ ∗
        ⌜network_sockets_coh (state_sockets σ)⌝ ∗
        ⌜messages_history_coh (state_ms σ) (state_sockets σ) mhm⌝ ∗
        node_gnames_auth γm ∗
        socket_interp_coh ∗
        ([∗ map] ip ↦ γs ∈ γm, local_state_coh σ ip γs) ∗
        free_ips_coh σ ∗
        messages_ctx mhm ∗
        messages_resource_coh mhm)%I.

  Program Definition aneris_events_state_interp (ex : execution_trace aneris_lang) : iProp Σ :=
    ∃ (As Ar : gset socket_address_group) (lbls : gset string),
      own (A:=authUR socket_address_groupUR) aneris_socket_address_group_name
          (◯ (DGSets (As ∪ Ar))) ∗
      observed_send_groups As ∗ observed_receive_groups Ar ∗
      sendon_evs_ctx (fn_to_gmap As (λ sag, events_of_trace (sendonEV_groups sag) ex)) ∗
      receiveon_evs_ctx (fn_to_gmap Ar (λ sag, events_of_trace (receiveonEV_groups sag) ex)) ∗
      alloc_evs_ctx (fn_to_gmap lbls (λ lbl, events_of_trace (allocEV lbl) ex)).

  Definition buffers (S : gmap ip_address sockets) : message_multi_soup :=
    (multi_collect (λ ip Sn, multi_collect (λ sh sr, list_to_set_disj sr.2) Sn) S).

  Definition message_history_evolution
             (M1 M2 : message_multi_soup)
             (S1 S2 : gmap ip_address sockets)
             (mhm : messages_history) : messages_history :=
    (dom (buffers S1 ∖ buffers S2) ∪ mhm.1, (gset_of_gmultiset M2 ∖ gset_of_gmultiset M1) ∪ mhm.2).

  Fixpoint trace_messages_history (ex : execution_trace aneris_lang) : messages_history :=
    match ex with
    | {tr[c]} => (∅, gset_of_gmultiset (state_ms c.2))
    | ex' :tr[_]: c =>
      message_history_evolution
        (state_ms (trace_last ex').2)
        (state_ms c.2)
        (state_sockets (trace_last ex').2)
        (state_sockets c.2)
        (trace_messages_history ex')
    end.

End definitions.

Section Aneris_AS.
  Context `{aG : !anerisG retransmit_fair_model Σ}.

  Definition ipA := "0.0.0.0".
  Definition saA := SocketAddressInet ipA 80.
  Definition sA := mkSocket (Some saA) true.
  Definition tidA := 0.
  Definition localeA := (ipA, tidA).

  Definition ipB := "0.0.0.1".
  Definition saB := SocketAddressInet ipB 80.
  Definition sB := mkSocket (Some saB) true.
  Definition tidB := 0.
  Definition localeB := (ipB, tidB).

  Definition mAB := mkMessage saA saB "Hello".

  (* TODO: Should align model and semantic actions / labels *)
  Definition locale_retransmit_role (ζ : locale aneris_lang) : option retransmit_node_role :=
    match ζ with
    | ("0.0.0.0",0) => Some Arole
    | ("0.0.0.1",0) => Some Brole
    | _ => None
   end.

  Definition locale_retransmit_label (ζ : ex_label aneris_lang) : option retransmit_label :=
    match ζ with
    | inl (tid,α) => option_map (λ ρ, inl (ρ,α)) (locale_retransmit_role tid)
    | inr α => Some $ inr $ ((),α)
   end.

  Definition retransmit_label_locale (ℓ : retransmit_label) : ex_label aneris_lang :=
    match ℓ with
    | inl (Arole,α) => inl (("0.0.0.0",0),α)
    | inl (Brole,α) => inl (("0.0.0.1",0),α)
    | inr ((),α) => inr α
    end.

  Definition labels_match (ζ : ex_label aneris_lang) (ℓ : retransmit_label) : Prop :=
    Some ℓ = locale_retransmit_label ζ.

  Definition roles_match (ζ : locale aneris_lang) (ℓ : retransmit_node_role) : Prop :=
    Some ℓ = locale_retransmit_role ζ.

  Lemma labels_match_roles_match ζ ℓ α :
    labels_match (inl (ζ,α)) (inl (ℓ,α)) → roles_match ζ ℓ.
  Proof.
    inversion 1. rewrite /roles_match.
    by destruct (locale_retransmit_role ζ); inversion H1.
  Qed.

  Lemma labels_match_roles_match_alt ζ ℓ :
    labels_match (inl ζ) (inl ℓ) →
    ∃ ζ' ℓ' α, ζ = (ζ',α) ∧ ℓ = (ℓ',α) ∧ roles_match ζ' ℓ'.
  Proof.
    destruct ζ as [], ℓ as []; inversion 1.
    destruct (locale_retransmit_role l); inversion H1.
    simplify_eq.
    eexists _, _, _. split; [done|]. split; [done|].
    by eapply labels_match_roles_match.
  Qed.

  Definition labels_match_trace (ex : execution_trace aneris_lang)
             (atr : auxiliary_trace (fair_model_to_model retransmit_fair_model))
    : Prop :=
    match ex, atr with
    | _ :tr[ζ]: _, _ :tr[ℓ]: _ => labels_match ζ ℓ
    | {tr[_]}, {tr[_]} => True
    | _, _ => False
    end.

  Definition role_enabled_locale_exists
             (c : cfg aneris_lang) (δ : retransmit_state) :=
    ∀ (ℓ:retransmit_node_role) ζ,
    roles_match ζ ℓ →
    role_enabled_model (ℓ : fmrole retransmit_fair_model) δ →
    is_Some (from_locale c.1 ζ).

  Definition model_state_socket_coh
             (skts : gmap ip_address sockets)
             (bs : gmap socket_address (list message)) :=
    ∀ ip Sn sh skt sa ms,
    skts !! ip = Some Sn → Sn !! sh = Some (skt,ms) →
    saddress skt = Some sa →
    bs !!! sa = ms.

  Definition config_state_valid (c : cfg aneris_lang) (δ : retransmit_state) :=
    state_ms c.2 = δ.1.2 ∧ model_state_socket_coh (state_sockets c.2) δ.2.

  Definition auxtr_valid auxtr :=
    trace_steps retransmit_trans auxtr.

  Definition simple_valid_state_evolution (ex : execution_trace aneris_lang)
             (atr : auxiliary_trace (fair_model_to_model retransmit_fair_model))
      : Prop :=
    auxtr_valid atr ∧
    labels_match_trace ex atr ∧
    role_enabled_locale_exists (trace_last ex) (trace_last atr) ∧
    config_state_valid (trace_last ex) (trace_last atr).

  Definition all_roles : gset retransmit_node_role :=
    {[ Arole; Brole ]}.

  Definition thread_live_roles_interp (δ : retransmit_state) : iProp Σ :=
    live_roles_auth_own (retransmit_live_roles δ) ∗
    dead_roles_auth_own (all_roles ∖ retransmit_live_roles δ).

  Global Instance anerisG_irisG :
    irisG aneris_lang (fair_model_to_model retransmit_fair_model) Σ := {
    iris_invGS := _;
    state_interp ex atr :=
      (⌜simple_valid_state_evolution ex atr⌝ ∗
       aneris_state_interp
         (trace_last ex).2
         (trace_messages_history ex) ∗
       thread_live_roles_interp (trace_last atr) ∗
       steps_auth (trace_length ex))%I;
    fork_post ζ _ := (∃ ℓ, ⌜roles_match ζ ℓ⌝ ∗ dead_role_frag_own ℓ)%I }.

End Aneris_AS.

Global Opaque iris_invGS.

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl : core.
Local Hint Constructors head_step : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

Ltac ddeq k1 k2 :=
  destruct (decide (k1 = k2)); subst;
  repeat
    match goal with
    | Hyp : context[ (<[_:=_]>_) !! _ ] |- _ =>
      rewrite lookup_insert in
          Hyp || (rewrite lookup_insert_ne in Hyp; last done);
      simplify_eq /=
    | Hyp : is_Some _ |- _ => destruct Hyp
    | |- context[ (<[_:=_]>_) !! _ ] =>
      rewrite lookup_insert || (rewrite lookup_insert_ne; last done);
      simplify_eq /=
    |  H1 : ?x = ?z, Heq : ?x = ?y |- _ =>
       rewrite Heq in H1; simplify_eq /=; try eauto
    | Hdel : context[ delete ?n ?m !! ?n = _] |- _ =>
      rewrite lookup_delete in Hdel; simplify_eq /=
    end.
