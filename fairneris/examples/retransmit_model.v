From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From Paco Require Import paco1 paco2 pacotac.
From fairneris Require Export trace_utils fairness env_model.
From fairneris.aneris_lang Require Import ast network lang aneris_lang adequacy network_model.
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
| B_RecvSucc :
  retransmit_trans Start (Brole, Some (Recv saB (Some mAB))) Received
| B_SendDone :
  retransmit_trans Received (Brole, Some (Send mDone)) Done
.


Definition retransmit_live_roles (s : retransmit_state) : gset retransmit_role :=
  {[Arole]} ∪
  (match s with Start | Received => {[Brole]} | _ => ∅ end).

Definition retransmit_role_enabled_model (ρ : retransmit_role) (s : retransmit_state) : Prop :=
  ρ ∈ retransmit_live_roles s.

Lemma retransmit_live_spec_holds s ρ α s' :
  retransmit_trans s (ρ,α) s' → ρ ∈ retransmit_live_roles s.
Proof. inversion 1; set_solver. Qed.

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
            usr_fl _ := 25;
          |}).
Defined.

Notation mtrace := (lts_trace retransmit_model).

(* Put somewhere *)
Lemma mtrace_fair_always :
  (usr_fair (M := retransmit_model)) ⇔ (□ usr_fair).
Proof.
  rewrite /usr_fair. intros mtr.
  split; last by intros Hfair%trace_always_elim.
  rewrite /usr_fair /usr_network_fair_send_receive /usr_network_fair_send_receive_of
    /usr_fair_scheduling /usr_fair_scheduling_mtr.
  intros [Hmtr1 Hmtr2].
  apply trace_always_forall in Hmtr1.
  apply trace_always_forall in Hmtr2.
  eassert (mtr ⊩ (□ trace_and _ _)).
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
    intros Htr'. naive_solver.
  + intros x. revert Htr2.
    apply trace_always_mono. intros tr'. apply trace_impliesI.
    intros Htr'. naive_solver.
Qed.

Definition option_lift {S L} (P : S → L → Prop) : S → option L → Prop :=
  λ s ol, ∃ l, ol = Some l ∧ P s l.

Lemma option_lift_Some {S L} (P : S → L → Prop) s l :
  option_lift P s (Some l) → P s l.
Proof. intros (l'&Hl'&HP). by simplify_eq. Qed.

Lemma A_always_live (mtr : mtrace) :
  (mtr ⊩ □ (trace_now (λ s _, retransmit_role_enabled_model Arole s))).
Proof. apply trace_always_universal.
  rewrite /pred_at /retransmit_role_enabled_model. intros mtr'.
  by destruct mtr'; set_solver.
Qed.

Lemma retransmit_fair_traces_eventually_mAB (mtr : mtrace) :
  (mtr ⊩ usr_trace_valid) → (mtr ⊩ usr_fair) →
  (mtr ⊩ ◊ ℓ↓ usr_send_filter mAB).
Proof.
  intros Hvalid [Hfairn Hfairs].
  specialize (Hfairs Arole).
  rewrite /usr_fair_scheduling_mtr in Hfairs.

  apply trace_always_elim in Hfairs.
  rewrite trace_impliesI in Hfairs.
  ospecialize (Hfairs _).
  { rewrite /trace_now /pred_at /=. destruct mtr; simpl; set_solver. }

  eapply trace_eventually_mono_strong; last apply Hfairs.
  intros tr Hsuff Htr.
  rewrite /trace_now /pred_at /= in Htr *.
  destruct tr; simpl.
  { exfalso. destruct Htr; [set_solver | naive_solver]. }
  destruct Htr as [|[act Htr]]; [set_solver |]. simplify_eq.
  eapply trace_always_suffix_of in Hvalid=>//.
  eapply trace_always_elim in Hvalid.
  inversion Hvalid; simplify_eq.
  rewrite /trace_label /pred_at /= /usr_send_filter. naive_solver.
Qed.

Lemma retransmit_fair_traces_always_eventually_mAB (mtr : mtrace) :
  (mtr ⊩ usr_trace_valid) → (mtr ⊩ usr_fair) →
  (mtr ⊩ □ ◊ ℓ↓ usr_send_filter mAB).
Proof.
  intros Hvalid [Hfairn Hfairs]. eapply trace_always_implies_always_strong;
    [|apply trace_always_and; split; [apply Hvalid|apply Hfairn]].
  intros tr' Hsuff [Hvalid' Hfair']%trace_always_and.
  apply retransmit_fair_traces_eventually_mAB=>//. split=>//.
  - intros msg. eapply trace_always_suffix_of in Hfairn=>//.
  - intros ρ. eapply trace_always_suffix_of in Hfairs=>//.
  Unshelve. exact inhabitant.
Qed.

Lemma retransmit_node_B_receives (mtr : mtrace) :
  (mtr ⊩ usr_trace_valid) → (mtr ⊩ usr_fair) →
  (mtr ⊩ ↓ (λ s _, s = Start)) →
  (mtr ⊩ ◊ ℓ↓ usr_any_recv_filter saB).
Proof.
  intros Hval [_ Hfair] Hs.
  have {}Hs : trfirst mtr = Start.
  { rewrite ltl_sat_def /trace_now /pred_at /= in Hs *. destruct mtr; set_solver. }
  specialize (Hfair Brole). apply trace_always_elim in Hfair.
  rewrite trace_impliesI in Hfair. ospecialize (Hfair _).
  { rewrite ltl_sat_def /trace_now /pred_at /= in Hs *. destruct mtr; set_solver. }
  apply trace_eventually_until in Hfair.
  induction Hfair as [tr Hnow|s [ρ α] tr Hlater Hh IH].
  - apply trace_eventually_intro.
    rewrite ltl_sat_def /trace_now /trace_label /pred_at /= in Hnow *.
    destruct tr; first naive_solver set_solver.
    destruct Hnow as [Hnow|[α Hnow]]; first naive_solver set_solver.
    simplify_eq. apply trace_always_elim in Hval.
    rewrite /usr_trans_valid ltl_sat_def /usr_any_recv_filter /= in Hval *.
    inversion Hval; simplify_eq; naive_solver.
  - apply trace_eventually_cons, IH=>//. by apply trace_always_cons in Hval.
    apply trace_always_elim in Hval.
    rewrite /usr_trans_valid ltl_sat_def /usr_any_recv_filter /= in Hval.
    inversion Hval; simplify_eq; try naive_solver. exfalso. apply Hlater.
    right. naive_solver.
Qed.

Lemma retransmit_fair_node_B_receives (mtr : mtrace) :
  (mtr ⊩ usr_trace_valid) → (mtr ⊩ usr_fair) →
  (mtr ⊩ ↓ (λ s _, s = Start)) →
  (mtr ⊩ ◊ ↓ (λ s _, s = Received)).
Proof.
  intros Hval Hfair Hstart. have [Hfairn Hfairs] := Hfair.
  specialize (Hfairn mAB).
  apply trace_always_elim in Hfairn.
  rewrite trace_impliesI in Hfairn.
  ospecialize (Hfairn _).
  { apply retransmit_fair_traces_always_eventually_mAB=>//. }
  apply trace_eventually_next.
  eapply (trace_eventually_mono_strong (ℓ↓ usr_recv_filter mAB)).
  { rewrite /trace_label /trace_now /pred_at /=. move=> [|s l mtr'] Hsuff //.
    rewrite !ltl_sat_def /usr_recv_filter. destruct l as [? [[|] | ]]; simpl.
    1, 3: naive_solver. intros [ρ ?]. simplify_eq; simpl.
    eapply trace_always_suffix_of, trace_always_elim in Hval =>//.
    rewrite ltl_sat_def in Hval. apply trace_next_intro.
    inversion Hval; simplify_eq; simpl. destruct mtr'=>//=. }

  apply trace_anyways.
  intros Hc. trace_push_neg Hc.

  have Ha: (mtr ⊩ □ usr_trans_valid aneris_lang ⋒ ⫬ ℓ↓ usr_recv_filter mAB).
  { apply trace_always_and; naive_solver. }

  have Has: (mtr ⊩ □ ↓ (λ s _, s = Start)).
  { apply (trace_always_next _ _ _ Ha)=>//.
    rewrite /trace_now /trace_label /pred_at /usr_trans_valid /=.
    intros tr Hst [Hval' Hnr]%trace_andI Hnf.
    apply trace_next_elim_inv in Hnf as (s&l&tr'&->&_).
    apply trace_next_intro.
    rewrite !ltl_sat_def in Hnr Hval' Hst *.
    inversion Hval'; simplify_eq=>//; try by destruct tr'=>//.
    exfalso. apply Hnr. rewrite /usr_recv_filter /=. naive_solver. }

  rewrite trace_impliesI in Hfairn. apply Hfairn.
  eapply trace_always_mono_strong; last apply Has.
  intros tr' Hsuff. rewrite trace_impliesI. intros Hs.

  eapply retransmit_node_B_receives=>//.
  eapply trace_always_suffix_of=>//.
  rewrite mtrace_fair_always.
  eapply trace_always_suffix_of; first apply Hsuff.
  rewrite -mtrace_fair_always //.
Qed.

Lemma retransmit_fair_node_B_sends (mtr : mtrace) :
  (mtr ⊩ usr_trace_valid) → (mtr ⊩ usr_fair) →
  (mtr ⊩ ↓ (λ s _, s = Start)) →
  (mtr ⊩ ◊ ℓ↓ usr_send_filter mDone).
Proof.
  intros Hval Hfair Hs.
  have Hr : (mtr ⊩ ◊ ↓ (λ s _, s = Received)).
  { apply retransmit_fair_node_B_receives =>//. }


  rewrite trace_eventuallyI in Hr.
  destruct Hr as (tr & Hsuff & Hr).

  eapply trace_always_suffix_of in Hval=>//.
  rewrite mtrace_fair_always in Hfair.
  eapply trace_always_suffix_of in Hfair; last apply Hsuff.
  rewrite -mtrace_fair_always in Hfair.

  have [Hfairn Hfairs] := Hfair.

  have {}Hr : trfirst tr = Received.
  { rewrite ltl_sat_def /trace_now /pred_at /= in Hr *. destruct tr; set_solver. }
  specialize (Hfairs Brole). apply trace_always_elim in Hfairs.
  rewrite trace_impliesI in Hfairs. ospecialize (Hfairs _).
  { rewrite ltl_sat_def /trace_now /pred_at /= in Hs *. destruct tr; set_solver. }
  apply trace_eventually_until in Hfairs.
  eapply trace_eventually_suffix_of=>//.
  induction Hfairs as [tr Hnow|s [ρ α] tr Hlater Hh IH].
  - apply trace_eventually_intro.
    rewrite ltl_sat_def /trace_now /trace_label /pred_at /= in Hnow *.
    destruct tr; first naive_solver set_solver.
    destruct Hnow as [Hnow|[α Hnow]]; first naive_solver set_solver.
    simplify_eq. apply trace_always_elim in Hval.
    rewrite /usr_trans_valid ltl_sat_def /usr_send_filter /= in Hval *.
    inversion Hval; simplify_eq; naive_solver.
  - apply trace_eventually_cons, IH=>//.
    + apply trace_suffix_of_cons_l in Hsuff. done.
    + by apply trace_always_cons in Hval.
    + eapply trace_always_suffix_of in Hval=>//; last eapply trace_suffix_of_cons_l, trace_suffix_of_refl.
      rewrite mtrace_fair_always in Hfair.
      eapply trace_always_cons in Hfair.
      rewrite -mtrace_fair_always // in Hfair.
    + intros msg. specialize (Hfairn msg). by apply trace_always_cons in Hfairn.
    + apply trace_always_elim in Hval.
      rewrite /usr_trans_valid ltl_sat_def /usr_any_recv_filter /= in Hval.
      inversion Hval; simplify_eq; try naive_solver. exfalso. apply Hlater.
      right. naive_solver.
Qed.
