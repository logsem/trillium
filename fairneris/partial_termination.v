From Paco Require Import pacotac.
From stdpp Require Import finite.
From iris.proofmode Require Import proofmode.
From trillium Require Import adequacy.
From fairneris Require Import fairness retransmit_model_progress_ltl.
From fairneris.aneris_lang Require Import aneris_lang resources.
From fairneris.aneris_lang.state_interp Require Import state_interp_def.
From fairneris.aneris_lang.state_interp Require Import state_interp_config_wp.
From fairneris.aneris_lang.state_interp Require Import state_interp.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From fairneris Require Import from_locale_utils trace_utils ltl_lite.


Definition snd_proj {A1 A2 B1 B2} (l : (A1 * A2) + (B1 * B2)) : (A2 + B2) :=
  sum_map snd snd l.

Definition ex_send_filter msg : cfg aneris_lang → option $ ex_label aneris_lang → Prop :=
  λ _ l, option_map (sum_map snd id) l = Some $ inl $ Some msg.
Instance ex_send_filter_decision msg st l : Decision (ex_send_filter msg st l).
Proof. apply make_decision. Qed.


Definition ex_deliver_filter msg : cfg aneris_lang → option $ ex_label aneris_lang → Prop :=
  λ _ l, option_map (sum_map snd id) l = Some $ inr $ Some msg.
Instance ex_deliver_filter_decision msg st l : Decision (ex_deliver_filter msg st l).
Proof. apply make_decision. Qed.

(* Definition retransmit_fair_network_delivery msg : mtrace → Prop := *)
(*   □ (□◊↓send_filter msg → ◊↓deliver_filter msg). *)
Definition retransmit_fair_network_delivery_ex msg : extrace aneris_lang → Prop :=
  □ (□◊↓ex_send_filter msg → ◊↓ex_deliver_filter msg).

Definition retransmit_fair_network_ex (extr : extrace aneris_lang) : Prop :=
  ∀ msg, retransmit_fair_network_delivery_ex msg extr.

(* TODO: Clean up this definition (annoying to state lemmas about,
         due to separate labels) *)
Definition live_tid (c : cfg aneris_lang) (δ : retransmit_state)
  (ℓ:retransmit_node_role) (ζ:locale aneris_lang) : Prop :=
  roles_match ζ ℓ →
  role_enabled_model (ℓ:fmrole retransmit_fair_model) δ ↔ locale_enabled ζ c.

Definition live_tids (c : cfg aneris_lang) (δ : retransmit_state) : Prop :=
  ∀ ℓ ζ, live_tid c δ ℓ ζ.

Definition live_traces_match : extrace aneris_lang → mtrace → Prop :=
  traces_match labels_match live_tids language.locale_step retransmit_trans.

Lemma traces_match_valid_preserved extr mtr :
  live_traces_match extr mtr → mtrace_valid mtr.
Proof. Admitted.

Definition extrace_fair (extr : extrace aneris_lang) :=
  (∀ ζ, fair_scheduling_ex ζ extr) ∧ retransmit_fair_network_ex extr.

Lemma traces_match_cons_inv {S1 S2 L1 L2}
      (Rℓ: L1 -> L2 -> Prop) (Rs: S1 -> S2 -> Prop)
      (trans1: S1 -> L1 -> S1 -> Prop)
      (trans2: S2 -> L2 -> S2 -> Prop)
      s1 s2 l1 l2 tr1 tr2 :
  traces_match Rℓ Rs trans1 trans2 (s1 -[l1]-> tr1) (s2 -[l2]-> tr2) ->
  Rs s1 s2 ∧ Rℓ l1 l2.
Proof. intros Hm. inversion Hm; done. Qed.

Lemma labels_match_deliver_filter_impl msg s1 s2 ℓ1 ℓ2 extr mtr :
  labels_match ℓ1 ℓ2 →
  (↓ ex_deliver_filter msg) (s1 -[ ℓ1 ]-> extr) →
  (↓ deliver_filter msg) (s2 -[ ℓ2 ]-> mtr).
Proof.
  intros Hmatch Hmtr.
  rewrite /trace_now /pred_at /ex_deliver_filter in Hmtr.
  rewrite /trace_now /pred_at /deliver_filter. simpl in *.
  destruct ℓ1; simplify_eq.
  destruct ℓ2; [done|].
  rewrite /labels_match /locale_retransmit_label in Hmatch.
  by simplify_eq.
Qed.

Lemma labels_match_send_filter_impl msg s1 s2 ℓ1 ℓ2 extr mtr :
  labels_match ℓ1 ℓ2 →
  (↓ send_filter msg) (s2 -[ ℓ2 ]-> mtr) →
  (↓ ex_send_filter msg) (s1 -[ ℓ1 ]-> extr).
Proof.
  intros Hmatch Hmtr.
  rewrite /trace_now /pred_at /send_filter in Hmtr.
  rewrite /trace_now /pred_at /ex_send_filter. simpl in *.
  simplify_eq.
  destruct ℓ2; simplify_eq.
  assert (r.2 = Some msg) as Heq1.
  { destruct r.
    rewrite /label_action /locale_retransmit_label in Hmtr.
    simpl in *. by simplify_eq. }
  destruct ℓ1; simplify_eq; last first.
  { rewrite /labels_match /locale_retransmit_label in Hmatch.
    simplify_eq. }
  assert (l.2 = r.2) as Heq2.
  { rewrite /labels_match /locale_retransmit_label in Hmatch.
    destruct l.
    destruct (locale_retransmit_role l); [|done].
    simpl in *. simplify_eq. simpl. done. }
  simpl. rewrite Heq2 Heq1. done.
Qed.

Lemma fair_network_impl extr mtr :
  live_traces_match extr mtr →
  retransmit_fair_network_ex extr → retransmit_fair_network mtr.
Proof.
  rewrite /retransmit_fair_network_ex /retransmit_fair_network.
  intros Hmatch Hfairex_network.
  assert (mtrace_valid mtr) as Hvalid.
  { by eapply traces_match_valid_preserved. }
  intros msg.
  specialize (Hfairex_network msg).
  rewrite /retransmit_fair_network_delivery_ex in Hfairex_network.
  rewrite trace_alwaysI in Hfairex_network.
  rewrite /retransmit_fair_network_delivery.
  rewrite trace_alwaysI.
  intros mtr' [n Hmtr'].
  pose proof Hmtr' as Hextr'.
  eapply traces_match_after in Hextr'; [|done].
  destruct Hextr' as (extr'&Hextr'&Hmatch').
  specialize (Hfairex_network extr').
  assert (trace_suffix_of extr' extr) as Hsuffix.
  { eexists _. done. }
  apply Hfairex_network in Hsuffix.
  rewrite trace_impliesI.
  rewrite trace_impliesI in Hsuffix.
  intros Hmtr''.
  assert ((□ ◊ ↓ ex_send_filter msg) extr') as Hextr''.
  { rewrite trace_alwaysI.
    intros extr'' [m Hextr''].
    eapply traces_match_flip in Hmatch'.
    pose proof Hextr'' as Hmtr'''.
    eapply traces_match_after in Hmtr'''; [|done].
    destruct Hmtr''' as (mtr''&Hmtr'''&Hmatch'').
    rewrite trace_alwaysI in Hmtr''.
    specialize (Hmtr'' mtr'').
    assert (trace_suffix_of mtr'' mtr') as Hsuffix'.
    { eexists _. done. }
    apply Hmtr'' in Hsuffix'.
    rewrite trace_eventuallyI in Hsuffix'.
    destruct Hsuffix' as [mtr''' [Hsuffix' Hmtr'''']].
    destruct Hsuffix' as [m'' Hsuffix'].
    apply traces_match_flip in Hmatch''.
    eapply traces_match_after in Hmatch''; [|done].
    destruct Hmatch'' as [extr''' [Hextr''' Hmatch''']].
    destruct mtr'''; [done|].
    simpl in *.
    rewrite trace_eventuallyI. exists extr'''.
    split; [eexists _;done|].
    destruct extr'''; [by inversion Hmatch'''|].
    assert (labels_match ℓ0 ℓ) as Hlabels.
    { by eapply traces_match_cons_inv. }
    by eapply labels_match_send_filter_impl. }
  apply Hsuffix in Hextr''.
  rewrite trace_eventuallyI in Hextr''.
  destruct Hextr'' as [extr'' [[m Hsuffix''] Hextr'']].
  rewrite trace_eventuallyI.
  eapply traces_match_flip in Hmatch'.
  eapply traces_match_after in Hmatch'; [|done].
  destruct Hmatch' as [mtr'' [Hmtr''' Hmatch'']].
  exists mtr''. split; [by eexists _|].
  destruct extr''; [done|].
  destruct mtr''; [by inversion Hmatch''|].
  assert (labels_match ℓ ℓ0) as Hlabels.
  { eapply traces_match_cons_inv. apply traces_match_flip. done. }
  by eapply labels_match_deliver_filter_impl.
Qed.

Definition retransmit_role_locale (ρ : retransmit_node_role) : locale aneris_lang :=
  match ρ with
  | Arole => ("0.0.0.0",0)
  | Brole => ("0.0.0.1",0)
  end.

Lemma locale_retransmit_role_cancel ρ :
  locale_retransmit_role (retransmit_role_locale ρ) = Some ρ.
Proof. by destruct ρ. Qed.

Lemma fair_scheduling_impl extr mtr :
  live_traces_match extr mtr →
  (∀ ζ, fair_scheduling_ex ζ extr) → retransmit_fair_scheduling mtr.
Proof.
  rewrite /fair_scheduling_ex /retransmit_fair_scheduling.
  intros Hmatch Hextr ρ.
  rewrite /retransmit_fair_scheduling_mtr.
  rewrite /trace_always_eventually_implies_now.
  rewrite /trace_always_eventually_implies.
  rewrite trace_alwaysI.
  intros mtr' [n Hmtr_after]. rewrite trace_impliesI.
  intros Hρ.
  eapply traces_match_after in Hmatch; [|done].
  destruct Hmatch as [extr' [Hextr_after Hmatch]].
  specialize (Hextr (retransmit_role_locale ρ) n).
  rewrite /pred_at in Hextr.
  rewrite Hextr_after in Hextr.
  assert (match extr' with
          | ⟨ s ⟩ | s -[ _ ]-> _ => locale_enabled (retransmit_role_locale ρ) s
          end) as Hextr'.
  { apply traces_match_first in Hmatch.
    destruct extr'.
    - eapply (Hmatch ρ).
      + destruct ρ; done.
      + rewrite /trace_now /pred_at in Hρ. simpl in *.
        by destruct mtr'.
    - eapply (Hmatch ρ).
      + destruct ρ; done.
      + rewrite /trace_now /pred_at in Hρ. simpl in *.
        by destruct mtr'. }
  apply Hextr in Hextr' as [m Hextr'].
  rewrite after_sum' Hextr_after in Hextr'.
  destruct (after m extr') as [extr''|] eqn:Hextr_after'; last first.
  { rewrite Hextr_after' in Hextr'. done. }
  rewrite Hextr_after' in Hextr'.
  rewrite trace_eventuallyI.
  apply traces_match_flip in Hmatch.
  eapply traces_match_after in Hmatch; [|done].
  destruct Hmatch as [mtr'' [Hmtr_after' Hmatch]].
  exists mtr''. split; [by eexists _|].
  rewrite /trace_now /pred_at=> /=.
  destruct mtr''.
  - destruct extr''; [|by inversion Hmatch].
    destruct Hextr' as [Hextr'|Hextr']; [|done].
    left. intros Hs. apply Hextr'.
    apply traces_match_first in Hmatch.
    eapply (Hmatch ρ).
    + destruct ρ; done.
    + rewrite /trace_now /pred_at in Hρ. simpl in *. done.
  - destruct extr''; [by inversion Hmatch|].
    destruct Hextr' as [Hextr'|Hextr'].
    { left. intros Hs. apply Hextr'.
      apply traces_match_first in Hmatch.
      eapply (Hmatch ρ).
      + destruct ρ; done.
      + rewrite /trace_now /pred_at in Hρ. simpl in *. done. }
    right. simpl in *. simplify_eq.
    apply traces_match_cons_inv in Hmatch as [_ Hmatch].
    rewrite /labels_match in Hmatch.
    destruct ℓ0; [|done].
    simpl in *. destruct l. simpl in *. simplify_eq.
    rewrite locale_retransmit_role_cancel in Hmatch.
    simpl in *. simplify_eq.
    done.
Qed.

Lemma traces_match_fairness_preserved extr mtr :
  live_traces_match extr mtr →
  extrace_fair extr → mtrace_fair mtr.
Proof.
  intros Hmatch [Hfairex_sched Hfairex_network].
  split; [by eapply fair_scheduling_impl|by eapply fair_network_impl].
Qed.

Definition extrace_terminating_locale (ζ : locale aneris_lang) (tr : extrace aneris_lang) : Prop :=
  (◊↓λ st _, ¬ locale_enabled ζ st) tr ∨ ¬ infinite_trace tr.

Lemma terminating_role_preserved ρ ζ mtr extr :
  live_traces_match extr mtr →
  roles_match ζ ρ →
  retransmit_terminating_role ρ mtr →
  extrace_terminating_locale ζ extr.
Proof.
  intros Hmatch Hroles [Hρ|Hinf]; last first.
  { right.
    intros Hinf'. apply Hinf.
    intros n. destruct (Hinf' n) as [extr' Hextr_after].
    apply traces_match_flip in Hmatch.
    eapply traces_match_after in Hmatch; [|done].
    destruct Hmatch as [mtr' [Hmtr_after Hmatch]].
    exists mtr'. done. }
  left.
  rewrite trace_eventuallyI in Hρ.
  destruct Hρ as [mtr' [[n Hmtr_after] Hρ]].
  rewrite trace_eventuallyI.
  eapply traces_match_after in Hmatch; [|done].
  destruct Hmatch as [extr' [Hextr_after Hmatch]].
  exists extr'.
  split; [by eexists _|].
  rewrite /trace_now /pred_at.
  rewrite /trace_now /pred_at in Hρ.
  simpl in *.
  destruct mtr'.
  - destruct extr'; [|by inversion Hmatch].
    apply traces_match_first in Hmatch.
    intros Henabled.
    apply Hρ.
    clear Hρ.
    by eapply Hmatch.
  - destruct extr'; [by inversion Hmatch|].
    apply traces_match_first in Hmatch.
    intros Henabled.
    apply Hρ.
    clear Hρ.
    by eapply Hmatch.
Qed.

Lemma fair_extrace_terminate extr mtr :
  live_traces_match extr mtr →
  extrace_valid extr → extrace_fair extr →
  extrace_terminating_locale localeB extr.
Proof.
  intros Hmatch Hvalid Hfair.
  eapply terminating_role_preserved; [done|done|].
  apply retransmit_fair_traces_terminate;
    [by eapply traces_match_valid_preserved|].
  by eapply traces_match_fairness_preserved.
Qed.
