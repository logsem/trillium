From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From fairneris Require Import fuel env_model.
From fairneris.lib Require Import gen_heap_light.
From fairneris.aneris_lang Require Import
     aneris_lang network resources.
From fairneris.aneris_lang.state_interp Require Import
     state_interp_def.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{LM: LiveModel aneris_lang (joint_model Mod Net)}.
  Context `{aG : !anerisG LM Σ}.

  (* TODO: Find alternative *)
  Lemma aneris_state_interp_network_sockets_coh_valid σ rt :
    aneris_state_interp σ rt -∗ ⌜network_sockets_coh (state_sockets σ)⌝.
  Proof. by iDestruct 1 as (??) "(?&?&?&?)". Qed.

  (** socket_handlers_coh *)
  Lemma socket_handlers_coh_alloc_socket Sn sh s :
    saddress s = None →
    socket_handlers_coh Sn →
    socket_handlers_coh (<[sh:=(s, [])]> Sn).
  Proof.
    intros ?? sh1 sh2 * ??? H. symmetry in H.
    ddeq sh1 sh2; ddeq sh1 sh; ddeq sh2 sh; eauto.
  Qed.

  Lemma socket_handlers_coh_socketbind Sn sh skt a :
    (∀ sh' skt' r' a',
       Sn !! sh' = Some (skt', r') →
       saddress skt' = Some a' →
       port_of_address a' ≠ port_of_address a) →
    socket_handlers_coh Sn →
    socket_handlers_coh (<[sh:=(skt <| saddress := Some a |>, [])]> Sn).
  Proof.
    intros ? Hscoh sh1 sh2 skt1 skt2 ????? Heq.
    ddeq sh1 sh; ddeq sh2 sh; simplify_eq=>//.
    - destruct skt, skt2; simplify_map_eq. set_solver.
    - destruct skt, skt1. simplify_map_eq. set_solver.
    - destruct skt1, skt2. simplify_map_eq. eapply Hscoh; eauto.
  Qed.

  Lemma socket_handlers_coh_update_buffer Sn sh skt R R' :
    Sn !! sh = Some (skt, R) →
    socket_handlers_coh Sn →
    socket_handlers_coh (<[sh:=(skt, R')]> Sn).
  Proof.
    intros Hsh HSn sh1 sh2 skt1 skt2 r1 r2 Hsh1 Hsh2 Hskt1 Hskt12.
    destruct (decide (sh1 = sh)) as [->|];
      destruct (decide (sh2 = sh)) as [->|]; simplify_eq; eauto.
    - rewrite lookup_insert in Hsh1; rewrite lookup_insert_ne in Hsh2;
        last done.
      eapply HSn; eauto; naive_solver.
    - rewrite lookup_insert_ne in Hsh1; last done;
        rewrite lookup_insert in Hsh2.
      eapply HSn; eauto; naive_solver.
    - rewrite lookup_insert_ne in Hsh1; last done;
        rewrite lookup_insert_ne in Hsh2; last done.
      eapply HSn; eauto; naive_solver.
  Qed.

  Lemma socket_handlers_coh_update_sblock σ Sn ip sh skt r b :
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    socket_handlers_coh Sn  →
    socket_handlers_coh
      (<[sh:=({| saddress := saddress skt;
                 sblock := b |}, r)]> Sn).
  Proof.
    intros ?? Hscoh sh1 sh2 skt1 skt2 ????? Heq.
    ddeq sh1 sh; ddeq sh2 sh; simplify_eq=>//.
    - eapply Hscoh; eauto. by rewrite Heq in H1.
    - eapply Hscoh; eauto. rewrite Heq. eauto.
    - eapply Hscoh; eauto. rewrite Heq. naive_solver.
  Qed.

  (** socket_messages_coh *)
  Lemma socket_messages_coh_update_socket Sn sh skt :
    socket_messages_coh Sn →
    socket_messages_coh (<[sh:=(skt, [])]> Sn).
  Proof. intros ? sh' **. ddeq sh sh'; [set_solver|]. eauto. Qed.

  Lemma socket_messages_coh_update_buffer a sh skt Sn R R' :
    Sn !! sh = Some (skt, R) →
    Forall (λ m, m_destination m = a) R' →
    saddress skt = Some a →
    socket_messages_coh Sn →
    socket_messages_coh (<[sh:=(skt, R')]> Sn).
  Proof.
    intros ? Hall ? Hmcoh sh' skt' r' a' Hsh' ?.
    destruct (decide (sh = sh')); simplify_eq; last first.
    { rewrite lookup_insert_ne // in Hsh'. by eapply Hmcoh. }
    rewrite lookup_insert in Hsh'; simplify_eq.
    by rewrite Forall_forall in Hall.
  Qed.

  Lemma socket_messages_coh_deliver_message Sn sh skt a R m :
    m_destination m = a →
    Sn !! sh = Some (skt, R) →
    saddress skt = Some a →
    socket_messages_coh Sn →
    socket_messages_coh (<[sh:=(skt, m :: R)]> Sn).
  Proof.
    intros ??? Hmcoh.
    eapply socket_messages_coh_update_buffer; [done| |done..].
    apply Forall_forall.
    intros m' [HR | ?] %elem_of_cons; subst; [done|].
    by eapply Hmcoh.
  Qed.

  Lemma socket_messages_coh_shrink_buffer Sn sh skt R1 R2 :
    Sn !! sh = Some (skt, R1 ++ R2) →
    socket_messages_coh Sn →
    socket_messages_coh (<[sh:=(skt, R1)]> Sn).
  Proof.
    intros HSn Hcoh sh' kt' r' a' Hsh' Hskt' m' Hm'.
    ddeq sh sh'; eapply Hcoh; eauto. set_solver.
  Qed.

  Lemma socket_messages_coh_receive Sn sh skt r m :
    Sn !! sh = Some (skt, r ++ [m]) →
    socket_messages_coh Sn →
    socket_messages_coh (<[sh:=(skt, r)]> Sn).
  Proof. by apply socket_messages_coh_shrink_buffer. Qed.

  Lemma socket_messages_coh_update_sblock Sn sh skt r b:
    Sn !! sh = Some (skt, r) →
    socket_messages_coh Sn →
    socket_messages_coh   (<[sh:=({| saddress := saddress skt;
                                     sblock := b |}, r)]> Sn).
  Proof.
    intros HSn Hcoh sh' kt' r' a' Hsh' Hskt' m' Hm'.
    ddeq sh sh'; eapply Hcoh; eauto.
  Qed.

  (** socket_addresses_coh *)
  Lemma socket_addresses_coh_alloc_socket Sn sh skt n :
    saddress skt = None →
    socket_addresses_coh Sn n →
    socket_addresses_coh (<[sh:=(skt, [])]> Sn) n.
  Proof. intros ? ? sh' **. ddeq sh' sh; eauto. Qed.

  Lemma socket_addresses_coh_socketbind Sn sh skt a :
    saddress skt = None →
    socket_addresses_coh Sn (ip_of_address a) →
    socket_addresses_coh
      (<[sh:=(skt <| saddress := Some a |>, [])]> Sn) (ip_of_address a).
  Proof. intros ? ? sh' **; ddeq sh sh'; eauto. Qed.

  Lemma socket_addresses_coh_insert_received sh a skt m R Sn :
    saddress skt = Some a →
    socket_addresses_coh Sn (ip_of_address a) →
    socket_addresses_coh (<[sh:=(skt, m :: R)]> Sn) (ip_of_address a).
  Proof. intros ?? sh' **; ddeq sh sh'; eauto. Qed.

  Lemma socket_addresses_coh_update_buffer Sn sh ip skt R1 R2 :
    Sn !! sh = Some (skt, R1) →
    socket_addresses_coh Sn ip →
    socket_addresses_coh (<[sh:=(skt, R2)]> Sn) ip.
  Proof.
    intros Hsh HSn sh' skt' R' sa Hsh' Hskt'.
    destruct (decide (sh = sh')) as [->|].
    - rewrite lookup_insert in Hsh'; simplify_eq.
      eapply HSn; eauto.
    - rewrite lookup_insert_ne in Hsh'; last done.
      eapply HSn; eauto.
  Qed.

  Lemma socket_addresses_coh_update_sblock Sn sh skt r b ip:
    Sn !! sh = Some (skt, r) →
    socket_addresses_coh Sn ip →
    socket_addresses_coh (<[sh:=({|
                                    saddress := saddress skt;
                                    sblock := b |}, r)]> Sn) ip.
  Proof.
    intros HSn Hcoh sh' kt' r' a' Hsh' Hskt'.
    ddeq sh sh'; eapply Hcoh; eauto.
  Qed.

  (** socket_unbound_empty_buf_coh *)
  Lemma socket_unbound_empty_buf_coh_alloc_socket Sn sh ip skt:
    saddress skt = None →
    socket_unbound_empty_buf_coh Sn ip →
    socket_unbound_empty_buf_coh (<[sh:=(skt, [])]> Sn) ip.
  Proof.
    intros Hskt HSn sh' skt' R Hsh' Hskt'.
    destruct (decide (sh = sh')) as [->|].
    - rewrite lookup_insert in Hsh'; simplify_eq; done.
    - rewrite lookup_insert_ne in Hsh'; last done.
      eapply HSn; eauto.
  Qed.

  Lemma socket_unbound_empty_buf_coh_socketbind Sn sh skt a:
    saddress skt = None →
    socket_unbound_empty_buf_coh Sn (ip_of_address a) →
    socket_unbound_empty_buf_coh
      (<[sh:=(skt <|saddress := Some a|> , [])]> Sn) (ip_of_address a).
  Proof.
    intros Hskt HSn sh' skt' R Hsh' Hskt'.
    destruct (decide (sh = sh')) as [->|].
    - rewrite lookup_insert in Hsh'; simplify_eq; done.
    - rewrite lookup_insert_ne in Hsh'; last done.
      eapply HSn; eauto.
  Qed.

  Lemma socket_unbound_empty_buf_coh_update_buffer Sn sh ip skt a R1 R2 :
    Sn !! sh = Some (skt, R1) →
    saddress skt = Some a →
    socket_unbound_empty_buf_coh Sn ip →
    socket_unbound_empty_buf_coh (<[sh:=(skt, R2)]> Sn) ip.
  Proof.
    intros Hsh Hskt HSn sh' skt' R' Hsh' Hskt'.
    destruct (decide (sh = sh')) as [->|].
    - rewrite lookup_insert in Hsh'; simplify_eq; done.
    - rewrite lookup_insert_ne in Hsh'; last done.
      eapply HSn; eauto.
  Qed.

  Lemma socket_unbound_empty_buf_coh_shrink_buffer Sn ip sh skt R1 R2 :
    Sn !! sh = Some (skt, R1 ++ R2) →
    socket_unbound_empty_buf_coh Sn ip →
    socket_unbound_empty_buf_coh (<[sh:=(skt, R1)]> Sn) ip.
  Proof.
    intros Hsn Hcoh sh' skt' r' Hsh' Hskt'. ddeq sh sh'; eauto.
    specialize (Hcoh sh' skt' _ Hsn Hskt').
    by apply app_eq_nil in Hcoh as [??].
  Qed.

  Lemma socket_unbound_empty_buf_coh_update_sblock Sn sh skt r b ip:
    Sn !! sh = Some (skt, r) →
    socket_unbound_empty_buf_coh Sn ip →
    socket_unbound_empty_buf_coh (<[sh:=({| saddress := saddress skt;
                                            sblock := b |}, r)]> Sn) ip.
  Proof.
    intros Hsn Hcoh sh' skt' r' Hsh' Hskt'. ddeq sh sh'; eauto.
  Qed.

  (** network_sockets_coh *)
  Lemma network_sockets_coh_alloc_node Sn ip :
    Sn !! ip = None →
    network_sockets_coh Sn →
    network_sockets_coh (<[ip:=∅]> Sn).
  Proof.
    rewrite /network_sockets_coh.
    intros ? Hcoh ip' ? Hst.
    destruct (decide (ip' = ip)); simplify_eq.
    - apply lookup_insert_rev in Hst. subst. split; done.
    - eapply Hcoh; by rewrite lookup_insert_ne in Hst.
  Qed.

  Lemma network_sockets_coh_init n : network_sockets_coh {[n:= ∅]}.
  Proof.
    rewrite /network_sockets_coh.
    intros n' Sn' HSn.
    ddeq n' n;
      [rewrite lookup_insert in HSn
      |rewrite lookup_insert_ne in HSn];
      rewrite /socket_handlers_coh
              /socket_messages_coh
              /socket_addresses_coh
              /socket_unbound_empty_buf_coh;
      set_solver.
  Qed.

  Lemma network_sockets_coh_update_sblock σ sh skt r ip Sn b :
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    network_sockets_coh (state_sockets σ)  →
    network_sockets_coh
      (<[ip:=<[sh:=({| saddress := saddress skt;
                       sblock := b |}, r)]> Sn]> (state_sockets σ)).
  Proof.
    rewrite /network_sockets_coh.
    intros ?? Hnets ip' Sn' HSn. ddeq ip' ip; [|eauto].
    destruct (Hnets ip Sn) as (?&?&?&?); [done|].
    split; [by eapply socket_handlers_coh_update_sblock|].
    split; [by eapply socket_messages_coh_update_sblock|].
    split; [by eapply socket_addresses_coh_update_sblock |
            by eapply socket_unbound_empty_buf_coh_update_sblock].
  Qed.

  Lemma network_sockets_coh_alloc_socket S Sn n sh skt :
    S !! n = Some Sn →
    Sn !! sh = None →
    saddress skt = None →
    network_sockets_coh S →
    network_sockets_coh (<[n:=<[sh:=(skt, [])]> Sn]> S).
  Proof.
    rewrite /network_sockets_coh.
    intros ??? Hnets n' Sn' HSn. ddeq n' n; [|eauto].
    destruct (Hnets n Sn) as (?&?&?&?); [done|].
    split; [by apply socket_handlers_coh_alloc_socket|].
    split; [by apply socket_messages_coh_update_socket|].
    split; [by apply socket_addresses_coh_alloc_socket |
            by apply socket_unbound_empty_buf_coh_alloc_socket].
  Qed.

  Lemma network_sockets_coh_socketbind S Sn sh skt a :
    let ip := ip_of_address a in
    let S' := <[ip:= <[sh:= (skt <| saddress := Some a |>, [])]> Sn]> S in
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, []) →
    port_not_in_use (port_of_address a) Sn →
    saddress skt = None →
    network_sockets_coh S →
    network_sockets_coh S'.
  Proof.
    rewrite /network_sockets_coh /=.
    intros ???? Hncoh ip Sn' ?.
    assert
      (∀ sh' skt' r' a',
         Sn !! sh' = Some (skt', r') →
         saddress skt' = Some a' →
         port_of_address a' ≠ port_of_address a ).
    { destruct (Hncoh (ip_of_address a) Sn) as
          (HshCoh & HmrCoh & HsaCoh);
        [done|].
      intros ** Hp.
      assert (ip_of_address a' = ip_of_address a) as Heq.
      { eapply HsaCoh; eauto. }
      assert (port_of_address a' ≠ port_of_address a) as Hnp.
      { eapply H1; eauto. }
      set_solver. }
    ddeq ip (ip_of_address a).
    - destruct (Hncoh (ip_of_address a) Sn) as (?&?&?&?); [done|].
      split; [by eapply socket_handlers_coh_socketbind|].
      split; [by eapply socket_messages_coh_update_socket|].
      split; [by eapply socket_addresses_coh_socketbind |].
      apply socket_unbound_empty_buf_coh_socketbind; done.
    - destruct (Hncoh ip Sn') as (HshCoh & HmrCoh & HsaCoh);
      [done|split;[done|split; done]].
  Qed.

  Lemma network_sockets_coh_receive S Sn ip sh skt r m :
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r ++ [m]) →
    network_sockets_coh S →
    network_sockets_coh (<[ip:=<[sh:=(skt, r)]> Sn]> S).
  Proof.
    rewrite /network_sockets_coh.
    intros HS HSn Hnet ip' Sn0 HSn0.
    ddeq ip' ip; [|eauto].
    specialize (Hnet ip Sn HS)
      as (Hshcoh & Hsmcoh & Hsaddrcoh & Hbufcoh).
    split; [by eapply socket_handlers_coh_update_buffer|].
    split; [by eapply socket_messages_coh_shrink_buffer|].
    split; [by eapply socket_addresses_coh_update_buffer|].
    by eapply socket_unbound_empty_buf_coh_shrink_buffer.
  Qed.

  Lemma network_sockets_coh_deliver_message S Sn Sn' ip sh skt a r m :
    m_destination m = a →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    Sn' = <[sh:=(skt, m :: r)]> Sn →
    saddress skt = Some a →
    network_sockets_coh S →
    network_sockets_coh (<[ip:=Sn']> S).
  Proof.
    rewrite /network_sockets_coh.
    intros HM HSn Hsh HSn' Hskt Hnet ip' Sn0 HSn0.
    ddeq ip' ip; [|eauto].
    specialize (Hnet ip Sn HSn)
      as (Hshcoh & Hsmcoh & Hsaddrcoh & Hbufcoh).
    split; [by eapply socket_handlers_coh_update_buffer|].
    split; [by eapply socket_messages_coh_deliver_message|].
    split; [by eapply socket_addresses_coh_update_buffer |].
    by eapply socket_unbound_empty_buf_coh_update_buffer.
  Qed.

End state_interpretation.
