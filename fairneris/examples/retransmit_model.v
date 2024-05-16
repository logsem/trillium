From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From Paco Require Import paco1 paco2 pacotac.
From fairneris Require Export trace_utils fairness env_model.
From fairneris.aneris_lang Require Import ast network lang aneris_lang.
From fairneris Require Export trace_utils ltl_lite.

Import derived_laws_later.bi.

Lemma prefix_trans {A} (l1 l2 l3 : list A) :
  l1 `prefix_of` l2 → l2 `prefix_of` l3 → l1 `prefix_of` l3.
Proof. intros [l1' ->] [l2' ->]. by do 2 apply prefix_app_r. Qed.

Lemma suffix_trans {A} (l1 l2 l3 : list A) :
  l1 `suffix_of` l2 → l2 `suffix_of` l3 → l1 `suffix_of` l3.
Proof. intros [l1' ->] [l2' ->]. by do 2 apply suffix_app_r. Qed.

(** The retransmit model states *)
Inductive retransmit_state :=
| Start
| Received
| Done.

#[global] Instance simple_state_eqdec : EqDecision retransmit_state.
Proof. intros ??. apply make_decision. Qed.
#[global] Instance simple_state_inhabited : Inhabited retransmit_state.
Proof. exact (populate Start). Qed.

Inductive retransmit_role := Arole | Brole.

Definition retransmit_node_action : Set := option message.
Definition retransmit_network_action : Set := option message.
Definition retransmit_action : Set :=
  retransmit_node_action + retransmit_network_action.

#[global] Instance retransmit_role_eqdec : EqDecision retransmit_role.
Proof. intros ??. apply make_decision. Qed.
#[global] Instance retransmit_role_inhabited : Inhabited retransmit_role.
Proof. exact (populate (Arole)). Qed.
#[global] Instance retransmit_role_countable : Countable retransmit_role.
Proof.
  refine ({|
             encode s := match s with
                         | Arole => 1
                         | Brole => 2
                         end;
             decode n := match n with
                         | 1 => Some Arole
                         | 2 => Some Brole
                         | _ => None
                         end;
         |})%positive.
  by intros [|].
Qed.

Definition saA : socket_address := SocketAddressInet "0.0.0.0" 80.
Definition saB : socket_address := SocketAddressInet "0.0.0.1" 80.
Definition mAB : message := mkMessage saA saB "Hello".
Definition mDone : message := mkMessage saB saA "Done".

Notation retransmit_label := (retransmit_role * option aneris_action)%type.

Inductive retransmit_trans :
  retransmit_state → retransmit_role * option aneris_action → retransmit_state → Prop :=
| A_Send st :
  retransmit_trans st (Arole, Some (Send mAB)) st
| B_RecvFail :
  retransmit_trans Start (Brole, Some (Recv saB None)) Start
| B_RecvSucc msg :
  retransmit_trans Start (Brole, Some (Recv saB (Some msg))) Received
| B_SendDone :
  retransmit_trans Received (Brole, Some (Send mDone)) Done
.
Notation mtrace := (trace retransmit_state (retransmit_role * option aneris_action)).

Definition retransmit_live_roles (s : retransmit_state) : gset retransmit_role :=
  {[Arole]} ∪
  (match s with Start | Received => {[Brole]} | _ => ∅ end).

Definition retransmit_role_enabled_model (ρ : retransmit_role) (s : retransmit_state) : Prop :=
  ρ ∈ retransmit_live_roles s.

Lemma retransmit_live_spec_holds s ρ α s' :
  retransmit_trans s (ρ,α) s' → ρ ∈ retransmit_live_roles s.
Proof. inversion 1; set_solver. Qed.

Definition send_filter msg : retransmit_label → Prop :=
  λ l, snd l = Some $ Send msg.
Instance send_filter_decision msg l : Decision (send_filter msg l).
Proof. apply make_decision. Qed.

Definition recv_filter msg : retransmit_label → Prop :=
  λ l, snd l = Some $ Recv (m_destination msg) (Some msg).
Instance recv_filter_decision msg l : Decision (recv_filter msg l).
Proof. apply make_decision. Qed.

Definition any_recv_filter sa : retransmit_label → Prop :=
  λ l, exists rcv, snd l = Some $ Recv sa rcv.
Instance any_recv_filter_decision l sa : Decision (any_recv_filter sa l).
Proof. apply make_decision. Qed.

Definition retransmit_fair_network_delivery msg : mtrace → Prop :=
  □ (□◊ℓ↓send_filter msg → □◊ℓ↓ any_recv_filter (m_destination msg) → ◊ℓ↓ recv_filter msg).

Definition retransmit_fair_network (mtr : mtrace) : Prop :=
  ∀ msg, retransmit_fair_network_delivery msg mtr.

(* TODO: This should be generalised, and lifted to multiple roles *)
Definition retransmit_terminating_role (ρ : retransmit_role) (tr : mtrace) : Prop :=
  (◊↓λ st _, ρ ∉ retransmit_live_roles st) tr ∨ ¬ infinite_trace tr.

Definition retransmit_fair_scheduling_mtr (ρ : retransmit_role) : mtrace → Prop :=
  trace_always_eventually_implies_now
    (λ δ _, retransmit_role_enabled_model ρ δ)
    (λ δ (ℓ: option retransmit_label), ¬ retransmit_role_enabled_model ρ δ ∨
              option_map fst ℓ = Some ρ).

Definition retransmit_fair_scheduling (mtr : mtrace) : Prop :=
  ∀ ρ, retransmit_fair_scheduling_mtr ρ mtr.

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

Definition trans_valid (mtr : mtrace) :=
   match mtr with
   | ⟨s⟩ => True
   | (s -[l]-> tr) => retransmit_trans s l (trfirst tr)
   end.

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

Lemma B_always_live_infinite (mtr : mtrace) :
  ¬ retransmit_terminating_role Brole mtr →
  (□ (trace_now (λ s _, retransmit_role_enabled_model Brole s))) mtr.
Proof.
  intros Hnt. apply trace_alwaysI. intros mtr' Hsuff.
  rewrite /trace_now /pred_at /retransmit_role_enabled_model.
  have ? : Brole ∈ retransmit_live_roles (trfirst mtr'); last destruct mtr' =>//=.
  apply NNP_P => Hin. apply Hnt.
  rewrite /retransmit_terminating_role. left.
  eapply (trace_eventually_suffix_of _ mtr') =>//. apply trace_eventually_intro.
  by destruct mtr'.
Qed.

Lemma B_always_live_always_eventually_receive (mtr : mtrace) :
  mtrace_fair mtr →
  mtrace_valid mtr →
  (□ (trace_now (λ s _, s = Start))) mtr →
  (□◊ℓ↓ any_recv_filter saB) mtr.
Proof.
  intros Hf Hval Hae. apply trace_alwaysI. intros mtr' Hsuff.
  have Hfs': retransmit_fair_scheduling mtr'.
  { by apply mtrace_fair_always, (trace_always_suffix_of _ _ _ Hsuff), trace_always_elim in Hf as [??]. }
  rewrite /retransmit_fair_scheduling in Hfs'.
  specialize (Hfs' Brole).
  rewrite /retransmit_fair_scheduling_mtr in Hfs'.
  rewrite /trace_always_eventually_implies_now in Hfs'.
  rewrite /trace_always_eventually_implies in Hfs'.
  have He: (↓ λ s _, s = Start) mtr'.
  { apply trace_always_elim in Hfs'.
    apply (trace_always_suffix_of _ _ _ Hsuff) in Hae.
    by apply trace_always_elim in Hae. }
  have He': (↓ λ s _, retransmit_role_enabled_model Brole s) mtr'.
  { eapply trace_now_mono=>//. move=> s l /= ->.
    rewrite /retransmit_role_enabled_model. set_solver. }
  apply trace_always_elim in Hfs'.
  rewrite trace_impliesI in Hfs'.
  specialize (Hfs' He'). clear He'.
  (* apply trace_eventuallyI in Hfs' as (mtr'' & Hsuff' & Hfs''). *)
  (* apply (trace_eventually_suffix_of _ mtr'') =>//. *)
  (* have Hsuff2: trace_suffix_of mtr'' mtr by eapply trace_suffix_of_trans. *)
  (* have He': retransmit_role_enabled_model Brole (trfirst mtr''). *)
  (* { apply (trace_always_suffix_of _ _ _ Hsuff2) in Hae. *)
  (*   eapply trace_always_elim in Hae. by destruct mtr''. } *)
  (* destruct mtr'' as [|s [ρ α]]; destruct Hfs''=>//. *)
  (* apply trace_eventually_intro=>//=. *)
  (* rewrite /trace_label /pred_at /any_recv_filter /=. *)
  (* apply (trace_always_suffix_of _ _ _ Hsuff2), trace_always_elim in Hval. *)
  (* inversion Hval; simplify_eq; naive_solver. *)
Admitted.

(* Lemma B_always_receives (mtr : mtrace) : *)
(*   mtrace_fair mtr → *)
(*   mtrace_valid mtr → *)
(*   ¬ retransmit_terminating_role Brole mtr → *)
(*   (□◊ℓ↓ any_recv_filter saB) mtr. *)
(* Proof. *)
(*   intros Hf Hval Hnt. *)
(*   apply B_always_live_infinite in Hnt. *)
(*   apply B_always_live_always_eventually_receive in Hnt =>//. *)
(* Qed. *)


(* Lemma retransmit_fair_traces_eventually_A mtr : *)
(*   retransmit_fair_scheduling_mtr Arole mtr → *)
(*   (◊ (↓ (λ _ ℓ, option_map fst ℓ = Some $ Arole))) mtr. *)
(* Proof. *)
(*   intros Hfair. *)
(*   pose proof (A_always_live mtr) as HA. *)
(*   eapply trace_always_eventually_always_implies; [|done]. *)
(*   eapply trace_always_eventually_always_mono; [| |apply Hfair]. *)
(*   - intros Htr. apply trace_implies_refl. *)
(*   - intros tr. *)
(*     apply trace_impliesI. *)
(*     apply trace_now_mono. *)
(*     intros s l. intros [Htr|Htr]; [|done]. *)
(*     rewrite /retransmit_role_enabled_model in Htr. set_solver. *)
(* Qed. *)

(* Lemma retransmit_fair_traces_eventually_mAB mtr : *)
(*   mtrace_valid mtr → retransmit_fair_scheduling_mtr Arole mtr → *)
(*   (◊ ℓ↓ send_filter mAB) mtr. *)
(* Proof. *)
(*   intros Hvalid Hfair. *)
(*   pose proof (retransmit_fair_traces_eventually_A mtr Hfair) as Htr. *)
(*   eapply trace_eventually_mono_strong; [|done]. *)
(*   intros tr' Htr'. *)
(*   eapply trace_always_suffix_of in Hvalid; [|done]. *)
(*   apply trace_always_elim in Hvalid. *)
(*   destruct tr' as [s|s l tr']; [done|]. *)
(*   apply trace_now_mono_strong. *)
(*   intros ???? HP; simplify_eq. *)
(*   destruct l. destruct r=>//. simpl in *. *)
(*   simplify_eq. inversion Hvalid. inversion H1. by simplify_eq. *)
(* Qed. *)

(* Lemma retransmit_fair_traces_always_eventually_mAB mtr : *)
(*   mtrace_valid mtr → retransmit_fair_scheduling_mtr Arole mtr → *)
(*   (□ ◊ ℓ↓ send_filter mAB) mtr. *)
(* Proof. *)
(*   intros Hvalid Hfair. eapply trace_always_implies_always; *)
(*     [|apply trace_always_and; split; [apply Hvalid|apply Hfair]]. *)
(*   intros tr' [Hvalid' Hfair']%trace_always_and. *)
(*   by apply retransmit_fair_traces_eventually_mAB. *)
(* Qed. *)


(* Lemma B_terminates (mtr : mtrace) : *)
(*   mtrace_fair mtr → *)
(*   mtrace_valid mtr → *)
(*   retransmit_terminating_role Brole mtr. *)
(* Proof. *)
(*   intros Hf Hval. apply NNP_P. intros Hnt. *)
(*   have Haer := Hnt. *)
(*   apply B_always_receives in Haer =>//. *)
(*   have Haes: (□ ◊ ℓ↓ send_filter mAB) mtr. *)
(*   { apply retransmit_fair_traces_always_eventually_mAB =>//. destruct Hf =>//. } *)
(*   have Har: (◊ ℓ↓ recv_filter mAB) mtr. *)
(*   { destruct Hf as [Hsf Hnf]. *)
(*     specialize (Hnf mAB). *)
(*     apply trace_always_elim in Hnf. *)
(*     rewrite !trace_impliesI in Hnf. *)
(*     naive_solver. } *)
(*   apply trace_eventuallyI in Har as (mtr' & Hsuff & Hr). *)
(*   destruct mtr' as [| s [ρ α] mtr'']; first naive_solver. *)

(*   apply Hnt. *)
(*   left. apply trace_eventuallyI. exists mtr''. split. *)
(*   { eapply trace_suffix_of_trans=>//. exists 1. done. } *)

(*   apply (trace_always_suffix_of _ _ _ Hsuff), trace_always_elim in Hval. *)
(*   have ? : Brole ∉ retransmit_live_roles (trfirst mtr''). *)
(*   { rewrite /trace_label /pred_at /recv_filter /= in Hr. *)
(*     inversion Hval; simplify_eq; try set_solver. } *)
(*   rewrite /trace_now /pred_at /=. destruct mtr''=>//. *)
(* Qed. *)


Definition retransmit_lts : Lts (retransmit_role * option (action aneris_lang)) :=
  {|
            lts_state := retransmit_state;
            lts_trans := retransmit_trans;
  |}.

Definition retransmit_model : UserModel aneris_lang.
Proof.
  refine({|
            usr_role := retransmit_role;
            usr_lts := retransmit_lts;
            usr_live_roles := retransmit_live_roles;
            usr_live_spec := retransmit_live_spec_holds;
            usr_fl _ := 20;
          |}).
Defined.
