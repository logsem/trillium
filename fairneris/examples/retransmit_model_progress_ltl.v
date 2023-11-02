From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From Paco Require Import paco1 paco2 pacotac.
From fairneris.aneris_lang Require Import ast network.
From fairneris.examples Require Export retransmit_model_base.
From fairneris Require Export trace_utils ltl_lite.

Import derived_laws_later.bi.

Lemma prefix_trans {A} (l1 l2 l3 : list A) :
  l1 `prefix_of` l2 → l2 `prefix_of` l3 → l1 `prefix_of` l3.
Proof. intros [l1' ->] [l2' ->]. by do 2 apply prefix_app_r. Qed.

Lemma suffix_trans {A} (l1 l2 l3 : list A) :
  l1 `suffix_of` l2 → l2 `suffix_of` l3 → l1 `suffix_of` l3.
Proof. intros [l1' ->] [l2' ->]. by do 2 apply suffix_app_r. Qed.

Definition send_filter msg : retransmit_state → option retransmit_label → Prop :=
  λ _ l, option_map label_action l = Some $ inl $ Some msg.
Instance send_filter_decision msg st l : Decision (send_filter msg st l).
Proof. apply make_decision. Qed.

Definition deliver_filter msg : retransmit_state → option retransmit_label → Prop :=
  λ _ l, l = Some $ inr ((),Some msg).
Instance deliver_filter_decision msg st l : Decision (deliver_filter msg st l).
Proof. apply make_decision. Qed.

(* Definition retransmit_fair_network_delivery msg : mtrace → Prop := *)
(*   □ (□◊↓send_filter msg → ◊↓deliver_filter msg). *)
Definition retransmit_fair_network_delivery msg : mtrace → Prop :=
  □ (□◊↓send_filter msg → ◊↓deliver_filter msg).

Definition retransmit_fair_network (mtr : mtrace) : Prop :=
  ∀ msg, retransmit_fair_network_delivery msg mtr.

(* TODO: This should be generalised, and lifted to multiple roles *)
Definition retransmit_terminating_role (ρ : retransmit_node_role) (tr : mtrace) : Prop :=
  (◊↓λ st _, ρ ∉ retransmit_live_roles st) tr ∨ ¬ infinite_trace tr.

Definition retransmit_role_enabled_model (ρ : retransmit_node_role) (s : retransmit_state) : Prop :=
  ρ ∈ retransmit_live_roles s.

Definition retransmit_fair_scheduling_mtr (ρ : retransmit_node_role) : mtrace → Prop :=
  trace_always_eventually_implies_now
    (λ δ _, retransmit_role_enabled_model ρ δ)
    (λ δ ℓ, ¬ retransmit_role_enabled_model ρ δ ∨
              option_map label_role ℓ = Some (inl ρ)).

(* Lemma retransmit_fair_scheduling_mtr_after ℓ tr tr' k : *)
(*   after k tr = Some tr' → *)
(*   retransmit_fair_scheduling_mtr ℓ tr → retransmit_fair_scheduling_mtr ℓ tr'. *)
(* Proof. Admitted. *)

Definition retransmit_fair_scheduling (mtr : mtrace) : Prop :=
  ∀ ρ, retransmit_fair_scheduling_mtr ρ mtr.

(* Lemma retransmit_fair_scheduling_after tr tr' k : *)
(*   after k tr = Some tr' → *)
(*   retransmit_fair_scheduling tr → retransmit_fair_scheduling tr'. *)
(* Proof. *)
(*   intros Hafter Hfair ℓ. specialize (Hfair ℓ). *)
(*   by eapply retransmit_fair_scheduling_mtr_after. *)
(* Qed. *)

Definition mtrace_fair (mtr : mtrace) : Prop :=
  retransmit_fair_scheduling mtr ∧ retransmit_fair_network mtr.

Lemma mtrace_fair_always mtr :
  mtrace_fair mtr ↔ (□ mtrace_fair) mtr.
Proof. 
  split.
  - rewrite /mtrace_fair.
    intros [Hmtr1 Hmtr2].
    rewrite /retransmit_fair_scheduling in Hmtr1.
    rewrite /retransmit_fair_network in Hmtr2.
    rewrite /retransmit_fair_scheduling_mtr in Hmtr1.
    rewrite /retransmit_fair_network_delivery in Hmtr2.
    apply trace_always_forall in Hmtr1.
    apply trace_always_forall in Hmtr2.
    eassert ((□ trace_and _ _) mtr).
    { apply trace_always_and. split; [apply Hmtr1|apply Hmtr2]. }
    apply trace_always_idemp in H.
    revert H. apply trace_always_mono.
    intros tr.
    apply trace_impliesI.
    intros Htr.
    apply trace_always_and in Htr as [Htr1 Htr2].
    split.
    + intros x. revert Htr1. 
      apply trace_always_mono. intros tr'. apply trace_impliesI.
      intros Htr'. done.
    + intros x. revert Htr2. 
      apply trace_always_mono. intros tr'. apply trace_impliesI.
      intros Htr'. done.
  - by intros Hfair%trace_always_elim.
Qed.

(* Good definition? *)
Definition trans_valid (mtr : mtrace) :=
   match mtr with
   | ⟨s⟩ => True
   | (s -[l]-> tr) => retransmit_trans s l (trfirst tr)
   end.

(* Good definition? *)
Definition mtrace_valid (mtr : mtrace) :=
  trace_always trans_valid mtr.

Definition option_lift {S L} (P : S → L → Prop) : S → option L → Prop :=
  λ s ol, ∃ l, ol = Some l ∧ P s l.

Lemma option_lift_Some {S L} (P : S → L → Prop) s l :
  option_lift P s (Some l) → P s l.
Proof. intros (l'&Hl'&HP). by simplify_eq. Qed.

Lemma A_always_live (mtr : mtrace) :
  (□ (trace_now (λ s _, retransmit_role_enabled_model Arole s))) mtr.
Proof. apply trace_always_universal.
  rewrite /pred_at /retransmit_role_enabled_model. intros mtr'.
  by destruct mtr'; set_solver.
Qed.

Lemma retransmit_fair_traces_eventually_A mtr :
  retransmit_fair_scheduling_mtr Arole mtr →
  (◊ (↓ (λ _ ℓ, option_map label_role ℓ = Some $ inl Arole))) mtr.
Proof.
  intros Hfair.
  pose proof (A_always_live mtr) as HA.
  eapply trace_always_eventually_always_implies; [|done].
  eapply trace_always_eventually_always_mono; [| |apply Hfair].
  - intros Htr. apply trace_implies_refl.
  - intros tr.
    apply trace_impliesI.
    apply trace_now_mono.
    intros s l. intros [Htr|Htr]; [|done].
    rewrite /retransmit_role_enabled_model in Htr. set_solver.
Qed.

Lemma retransmit_fair_traces_eventually_mAB mtr :
  mtrace_valid mtr → retransmit_fair_scheduling_mtr Arole mtr →
  (◊ ↓ send_filter mAB) mtr.
Proof.
  intros Hvalid Hfair.
  pose proof (retransmit_fair_traces_eventually_A mtr Hfair) as Htr.
  eapply trace_eventually_mono_strong; [|done].
  intros tr' Htr'.
  eapply trace_always_suffix_of in Hvalid; [|done].
  apply trace_always_elim in Hvalid.
  destruct tr' as [s|s l tr']; [done|].
  apply trace_now_mono_strong.
  intros ???? HP; simplify_eq.
  destruct l; [|done]. destruct r. simpl in *.
  simplify_eq. inversion Hvalid. inversion H1. by simplify_eq.
Qed.

(* Proof by the fact that A is always live, and will eventually be scheduled.
   Needs fairness assumptions *)
Lemma retransmit_fair_traces_always_eventually_mAB mtr :
  mtrace_valid mtr → retransmit_fair_scheduling_mtr Arole mtr →
  (□ ◊ ↓ send_filter mAB) mtr.
Proof.
  intros Hvalid Hfair. eapply trace_always_implies_always;
    [|apply trace_always_and; split; [apply Hvalid|apply Hfair]].
  intros tr' [Hvalid' Hfair']%trace_always_and.
  by apply retransmit_fair_traces_eventually_mAB.
Qed.

Lemma eventually_send_eventually_deliver mtr :
  retransmit_fair_network mtr →
  (□ ◊ ↓ send_filter mAB) mtr →
  (◊ ↓ deliver_filter mAB) mtr.
Proof.
  intros Hfair_network Hsend.
  pose proof (Hfair_network mAB). apply trace_always_elim in H.
  rewrite trace_impliesI in H. apply H. done.
Qed.

(* If a message is delivered, the next state has a message in the buffer *)
(* Proof by validity relation of the model *)
Lemma deliver_next_buffer msg mtr :
  mtrace_valid mtr →
  (↓ deliver_filter msg) mtr →
  (○ ↓ λ s _, ∃ bs, s.2 !!! (m_destination msg) = msg :: bs) mtr.
Proof.
  intros Hvalid%trace_always_elim Hdeliver.
  destruct mtr; [done|].
  exists mtr. split; [done|].
  rewrite /trace_now /deliver_filter /pred_at in Hdeliver.
  simpl in *. simplify_eq.
  inversion Hvalid. simplify_eq.
  destruct mtr.
  - rewrite /trace_now /pred_at. simpl in *. simplify_eq.
    exists (bs !!! m_destination msg).
    simpl. by rewrite lookup_total_insert.
  - rewrite /trace_now /pred_at. simpl in *. simplify_eq.
    exists (bs !!! m_destination msg).
    simpl. by rewrite lookup_total_insert.
Qed.

(* A scheduled B will succeed if there is something in the buffer *)
(* Proof by validity relation of the model *)
Lemma successful_deliver_received bs (mtr : mtrace) :
  mtrace_valid mtr →
  (↓ (λ s _, mAB :: bs `suffix_of` s.2 !!! (m_destination mAB))) mtr →
  (↓ (λ _ l, option_map label_role l = Some (inl Brole))) mtr →
  (○ ↓ (λ s _, s.1.1 = Received)) mtr.
Proof.
  intros Hvalid%trace_always_elim Hbs HB.
  destruct mtr as [?|s l mtr]; [done|].
  simpl in *. destruct l as [|]; [|done].
  exists mtr. split; [done|].
  rewrite /trace_now /pred_at in HB.
  simpl in *. simplify_eq.
  destruct r. simpl in *. simplify_eq.
  inversion Hvalid; simplify_eq; [|]; last first.
  { destruct mtr as [[]|[]]; simpl in *; simplify_eq; done. }
    rewrite /trace_now /pred_at in Hbs. simpl in *.
  rewrite H2 in Hbs. by apply suffix_cons_nil_inv in Hbs.
Qed.

Lemma B_enabled_not_received s :
  retransmit_role_enabled_model Brole s ↔ s.1.1 ≠ Received.
Proof.
  rewrite /retransmit_role_enabled_model /retransmit_live_roles.
  split.
  - intros. destruct s as [[??]?]. simpl in *. intros ->. set_solver.
  - intros. destruct s as [[??]?]. simpl in *.
    apply elem_of_union. right. destruct r; set_solver.
Qed.

Lemma not_B_enabled_received s :
  ¬ retransmit_role_enabled_model Brole s ↔ s.1.1 = Received.
Proof.
  rewrite /retransmit_role_enabled_model /retransmit_live_roles.
  split.
  - intros. destruct s as [[??]?]. simpl in *. destruct r; set_solver.
  - intros. destruct s as [[??]?]. simpl in *. intros Helem.
    simplify_eq. set_solver.
Qed.

Lemma received_or_eventually_B (mtr : mtrace) :
  mtrace_fair mtr →
  (◊↓ λ s _, s.1.1 = Received) mtr ∨
  (◊↓ λ _ l, option_map label_role l = Some $ inl Brole) mtr.
Proof.
  intros Hfair.
  assert ((↓ λ s _, s.1.1 = Received) mtr ∨
         ¬ (↓ λ s _, s.1.1 = Received) mtr).
  { apply ExcludedMiddle. }
  destruct H as [H|H].
  { left. apply trace_eventually_intro. done. }
  apply trace_notI in H. apply trace_now_not in H.
  assert ((↓ (λ s _, retransmit_role_enabled_model Brole s)) mtr) as HB.
  { revert H. apply trace_now_mono.
    intros. by apply B_enabled_not_received. }
  destruct Hfair as [Hfair _].
  specialize (Hfair Brole).
  apply trace_always_elim in Hfair.
  rewrite trace_impliesI in Hfair.
  apply Hfair in HB.
  apply trace_eventually_or. revert HB.
  apply trace_eventually_mono.
  intros tr Htr.
  apply trace_now_or in Htr.
  destruct Htr as [Htr|Htr].
  - left. revert Htr. apply trace_now_mono. intros.
    by apply not_B_enabled_received.
  - by right.
Qed.

(* Need to assume that trace is infinite *)
Lemma retransmit_fair_trace_buffer_grow_next mtr bs :
  infinite_trace mtr →
  mtrace_valid mtr →
  (↓ λ s _, s.2 !!! (m_destination mAB) = bs) mtr →
  (↓ λ _ l, option_map label_role l ≠ Some $ inl Brole) mtr →
  (○ (↓ (λ s _, ∃ bs', bs `suffix_of` bs' ∧
                       s.2 !!! m_destination mAB = bs'))) mtr.
Proof.
  intros Hinf Hvalid Hbs HBrole.
  apply trace_always_elim in Hvalid.
  destruct mtr.
  { specialize (Hinf 1). by apply is_Some_None in Hinf. }
  destruct mtr.
  { specialize (Hinf 2). by apply is_Some_None in Hinf. }
  destruct s as [[??]?].
  rewrite /trace_now /pred_at.
  rewrite /trace_now /pred_at in Hbs.
  rewrite /trace_now /pred_at in HBrole.
  simpl in *.
  apply trace_next_intro.
  inversion Hvalid; simplify_eq.
  - exists (g !!! m_destination mAB). set_solver.
  - exists (g !!! m_destination mAB). set_solver.
  - exists (g !!! m_destination mAB). set_solver.
  - destruct (decide (m_destination msg = saB)) as [->|Hneq].
    + exists (msg :: g !!! m_destination mAB).
      split; [by apply suffix_cons_r|].
      simpl. rewrite lookup_total_insert. done.
    + exists (g !!! m_destination mAB).
      simpl. rewrite lookup_total_insert_ne; [|done].
      set_solver.
Qed.

(* The buffers will only grow until B is scheduled *)
(* Proof by validity relation of the model *)
Lemma retransmit_fair_trace_buffer_grows mtr bs :
  infinite_trace mtr →
  mtrace_valid mtr →
  mtrace_fair mtr →
  (↓ λ s _, s.2 !!! (m_destination mAB) = bs) mtr →
  ((◊trace_and
     (↓ (λ s _, suffix bs (s.2 !!! (m_destination mAB))))
     (↓ (λ _ l, option_map label_role l = Some $ inl Brole))) mtr) ∨
  ((◊↓ λ s _, s.1.1 = Received) mtr).
Proof.
  intros Hinf Hvalid Hfair Hnow.
  (* TODO: Need to assume not received instead *)
  pose proof (received_or_eventually_B mtr Hfair) as [Hreceived|HB].
  { right. done. }
  left.
  revert bs Hnow.
  apply trace_eventually_until in HB.
  induction HB; intros bs Hnow.
  { eapply trace_eventually_mono; [apply trace_now_and|].
    apply trace_eventually_intro.
    pose proof (trace_now_split _ _ _ Hnow H) as Hnow'.
    revert Hnow'. apply trace_now_mono.
    intros s l [H1 H2]. split; [|done]. set_solver. }
  apply trace_eventually_cons.
  assert (∃ bs', bs `suffix_of` bs' ∧
             (↓ (λ s _ , s.2 !!! m_destination mAB = bs'))
               tr) as [bs' [Hbs' Hnow']].
  { assert ((↓ (λ s _, ∃ bs', bs `suffix_of` bs' ∧ s.2 !!! m_destination mAB = bs'))
               tr) as H'; last first.
    { apply trace_now_exists in H' as [bs' H'].
      exists bs'.
      rewrite /trace_now /pred_at.
      rewrite /trace_now /pred_at in H'.
      destruct tr; simpl in *; done. }
    eapply trace_next_elim.
    by apply retransmit_fair_trace_buffer_grow_next. }
    eapply trace_eventually_mono; last first.
  { assert (mtrace_valid tr) as Hvalid' by by eapply trace_always_cons.
    apply mtrace_fair_always in Hfair.
    assert (mtrace_fair tr) as Hfair'.
    { apply mtrace_fair_always. by eapply trace_always_cons. }
    assert (infinite_trace tr) as Hinf'.
    { by eapply infinite_cons. }
    apply (IHHB Hinf' Hvalid' Hfair' bs').
    done. }
  intros tr' H'. apply trace_andI. apply trace_andI in H'.
  destruct H' as [H1 H2].
  split; [|done].
  revert H1. apply trace_now_mono.
  intros ???. by etransitivity.
Qed.

Lemma eventually_deliver_eventually_received mtr :
  infinite_trace mtr → mtrace_valid mtr → mtrace_fair mtr →
  (◊ ↓ deliver_filter mAB) mtr →
  (◊ ↓ λ s _, s.1.1 = Received) mtr.
Proof.
  intros Hinf Hvalid Hfair Hdeliver.
  eapply trace_eventually_mono_strong in Hdeliver; last first.
  { intros tr' Hsuffix. apply deliver_next_buffer. by eapply trace_always_suffix_of. }
  apply trace_eventually_next in Hdeliver.
  apply trace_eventually_idemp.
  revert Hdeliver.
  apply trace_eventually_mono_strong.
  intros mtr' Hsuffix Hdeliver.
  apply trace_now_exists in Hdeliver as [bs Hdeliver].
  assert (infinite_trace mtr') as Hinf'.
  { destruct Hsuffix as [n Hn].
    eapply (infinite_trace_after n) in Hinf.
    by rewrite Hn in Hinf. }
  assert (mtrace_valid mtr') as Hvalid'.
  { by eapply trace_always_suffix_of. }
  assert (mtrace_fair mtr') as Hfair'.
  { apply mtrace_fair_always in Hfair.
    apply mtrace_fair_always. by eapply trace_always_suffix_of. }
  pose proof (retransmit_fair_trace_buffer_grows _ (mAB :: bs) Hinf' Hvalid' Hfair' Hdeliver) as [H'|H']; last first.
  { done. }
  apply trace_eventually_next.
  revert H'.
  apply trace_eventually_mono_strong.
  intros mtr'' Hsuffix' [Hmtr1'' Hmtr2'']%trace_andI.
  assert (mtrace_valid mtr'') by by eapply trace_always_suffix_of.
  by eapply successful_deliver_received.
Qed.

(* Any fair trace terminates on role B *)
Lemma retransmit_fair_traces_terminate mtr :
  mtrace_valid mtr → mtrace_fair mtr →
  retransmit_terminating_role Brole mtr.
Proof.
  intros Hvalid [Hfair1 Hfair2].
  assert (infinite_trace mtr ∨ ¬ infinite_trace mtr) as [Hafter|Hafter];
    [by apply ExcludedMiddle| |]; last first.
  { by right. }
  left.
  pose proof (retransmit_fair_traces_always_eventually_mAB mtr Hvalid (Hfair1 _)).
  apply (eventually_send_eventually_deliver _ Hfair2) in H.
  apply (eventually_deliver_eventually_received) in H; [|done..].
  revert H. apply trace_eventually_mono.
  intros tr. apply trace_now_mono. intros [[]] _ Hreceived.
  rewrite /retransmit_live_roles. simpl in *.
  simplify_eq. set_solver.
Qed.

Definition retransmit_fair_model : FairModel.
Proof.
  refine({|
            fmstate := retransmit_state;
            fmrole := retransmit_node_role;
            fmaction := retransmit_node_action;
            fmconfig := retransmit_network_label;
            fmtrans := retransmit_trans;
            fmfairness := retransmit_fair_network;
            live_roles := retransmit_live_roles;
            fm_live_spec := retransmit_live_spec_holds;
          |}).
Defined.
