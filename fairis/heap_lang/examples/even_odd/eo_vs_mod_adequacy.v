From Paco Require Import paco1 paco2 pacotac.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import excl_auth.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination fairness_finiteness trace_utils utils action_model.
From trillium.fairness.heap_lang Require Export lang lifting tactics notation adequacy.
From trillium.fairness.heap_lang.examples Require Import env_am split_model.
From trillium.fairness.heap_lang.examples.even_odd Require Import eo_vs_mod interface thread_progs model_updates.
From stdpp Require Import finite.


Section ModelMono.
(** Proof that any fair execution of model visits all natural numbers *)
  Context {even_impl: EvenModel} {odd_impl: OddModel}.

  Let PM := @prod_model even_impl odd_impl.
  Context {prod_AM_act_dec: ∀ a, Decision (is_action_of PM a)}. 

  Let M := @the_fair_model even_impl odd_impl _ _ EnvUnitAM.
  Let even_AM := @even_AM even_impl. 
  Let odd_AM := @odd_AM odd_impl. 

  Let FM := @full_model even_impl odd_impl UnitAM. 
  (* TODO: work with PM trace only *)
  Definition evenodd_mtrace : Type := mtrace M.

  Definition st2nat' (st: fmstate M) := st2nat st.1.
  
  Definition evenodd_mdl_progress (tr : evenodd_mtrace) :=
    ∀ (i: nat), ∃ n, pred_at tr n (λ s _, st2nat' s i).

  Definition evenodd_mdl_mono (tr : evenodd_mtrace) :=
    ∀ n, ∃ i, pred_at tr n (λ s _, st2nat' s i) ∧
              pred_at tr (S n) (λ s _, ∃ j, st2nat' s j ∧ i ≤ j).
  
  Lemma pred_at_state_trfirst:
  ∀ {St L : Type} (tr : trace St L) (P : St → Prop),
    pred_at tr 0 (λ (st : St) (_ : option L), P st) ↔ P (trfirst tr).
  Proof using. by destruct tr. Qed. 

  (* TODO: look for general version regarding trace length *)
  Lemma pred_at_S_singl:
  ∀ {St L : Type} s P m,
    pred_at (⟨ s ⟩: trace St L) (S m) P <-> False.
  Proof. done. Qed. 

  Let ρEven: fmrole M := inl $ even_role (ρ__e even_impl).
  Let ρOdd: fmrole M := inl $ odd_role (ρ__o odd_impl).

  Lemma prod_matched_by_full: 
    @matched_by PM FM
      (fun st__s '(st__s', st__m) => st__s' = st__s /\ True)
      (inl)
      .
  Proof.
    apply matched_by_prod_l; try by apply _.
    { apply matched_by_unit. }
    done. 
  Qed.

  Lemma full_no_ext_sync (st: amSt FM):
    None ∉ ams_lr st.
  Proof.
    intros IN%ams_lr_spec. destruct IN as (?&?&STEP).
    by inversion STEP. 
  Qed.

  (* None case is hard *)
  (* (* TODO: move *) *)
  (* Lemma prod_indep_acts_dec {AM1 AM2} *)
  (*   (INDEP: models_independent AM1 AM2) *)
  (*   (DEC1: ∀ a, Decision (is_action_of AM1 a)) *)
  (*   (DEC2: ∀ a, Decision (is_action_of AM2 a)): *)
  (*   ∀ a, Decision (is_action_of (ProdAM AM1 AM2) a). *)
  (* Proof.  *)
  (*   intros a. *)
  (*   destruct (DEC1 a). *)
  (*   -  *)
  (*     left. destruct i as (st & oρ & st' & STEP). *)
  (*     set (s := inhabitant $ am_st_inh AM2: amSt AM2).  *)
  (*     exists (st, s). exists (from_option (Some ∘ inl) None oρ), (st', s). *)
  (*     econstructor.  *)
                            

  (* TODO: move *)
  Lemma prod_actions_sub {AM1 AM2} a
    (ACT: is_action_of (ProdAM AM1 AM2) a):
    is_action_of AM1 a \/ is_action_of AM2 a.
  Proof. 
    destruct ACT as (st & oρ & st' & STEP).
    inversion STEP; subst.
    all: try apply action_of_step in STEP1; try apply action_of_step in STEP2.
    all: tauto.
  Qed. 

  Lemma prod_no_ext_sync (st: amSt PM):
    None ∉ ams_lr st.
  Proof.
    intros IN%ams_lr_spec. destruct IN as (?&?&STEP).
    inversion STEP; subst.
    pose proof STEP1 as ACT1%action_of_step%even_acts.
    pose proof STEP2 as ACT2%action_of_step%odd_acts.
    destruct ACT1 as [[k ?] | PRIV1], ACT2 as [[? EQ] | PRIV2]; subst; cycle 1.
    { by apply odd_pub_priv_disj in PRIV2. }
    { by apply even_pub_priv_disj in PRIV1. }
    { by edestruct @even_odd_priv_disj; eauto. }
    apply coPset_nth_inj in EQ. subst.
    apply even_sync_inv in STEP1 as (?&?&?). apply odd_sync_inv in STEP2 as (?&?&?).
    edestruct even_odd_False; eauto.
  Qed.

  Instance full_AM_act_dec: ∀ a : Action, Decision (is_action_of FM a).
  Proof.
    intros. destruct (decide (is_action_of PM a)).
    - left. destruct i as (st & oρ & st' & STEP).
      destruct oρ. 
      2: { edestruct prod_no_ext_sync. eapply ams_lr_spec; eauto. }
      red. do 3 eexists. simpl. eapply pt_inner1; eauto.
      by intros ?%UnitAM_actions.
    - right. intros [? | ?%UnitAM_actions]%prod_actions_sub; done. 
      Unshelve. exact (). 
  Qed. 

  Lemma ρEven_always_live' (st: amSt PM) n
    (CUR: st2nat st n):
    inl $ ρ__e even_impl ∈ AM_live_roles st.
  Proof.
    destruct st as [??]. 
    eapply live_lift. 
    { apply even_matched_by_prod. }
    { simpl. split; eauto. red. eauto. }
    apply ρ__e_always_live.
  Qed.

  Lemma ρOdd_always_live' (st: amSt PM) n
    (CUR: st2nat st n):
    inr $ ρ__o odd_impl ∈ AM_live_roles st.
  Proof.
    destruct st as [??]. 
    eapply live_lift. 
    { apply odd_matched_by_prod. }
    { simpl. split; eauto. red. eauto. }
    apply ρ__o_always_live.
  Qed.

  Lemma ρEven_always_live (st: fmstate M) n
    (CUR: st2nat' st n):
    ρEven ∈ live_roles _ st.
  Proof.
    simpl. destruct st.
    rewrite /ρEven. simpl.
    unshelve eapply (live_lift _ _ a (_: amSt FM)).
    2: { apply prod_matched_by_full. }
    { done. }
    eapply ρEven_always_live'; eauto.
  Qed. 

  Lemma ρOdd_always_live (st: fmstate M) n
    (CUR: st2nat' st n):
    ρOdd ∈ live_roles _ st.
  Proof.
    simpl. destruct st.
    rewrite /ρOdd. simpl.
    unshelve eapply (live_lift _ _ a (_: amSt FM)).
    2: { apply prod_matched_by_full. }
    { done. }
    eapply ρOdd_always_live'; eauto.
  Qed. 

  Lemma st2nat_next st aoρ (st': fmstate M) i j
    (TRANS: amTrans FM st aoρ st')
    (CUR: st2nat' st i)
    (NEXT: st2nat' st' j)
    :
    (* st2nat st' (S i) \/ st2nat st' i. *)
    j = S i \/ j = i.
  Proof.
    destruct aoρ as [a oρ]. destruct NEXT, CUR.
    assert (exists ρ, oρ = Some (inl ρ)) as [ρ ->].
    { inversion TRANS; subst; eauto; done. }
    
    simpl in TRANS. inversion TRANS; subst.
    2: { done. }
    simpl in *. clear TRANS. rename STEP1 into TRANS.  
    inversion TRANS; subst. 
    - right. simpl in *. lia.
    - right. simpl in *. lia.
    - left. simpl in *.
      pose proof STEP1 as [[? ->] | PRIV__e]%action_of_step%even_acts.
      { apply even_step_inv in STEP1. lia. }
      pose proof STEP2 as [[? ->] | PRIV__o]%action_of_step%odd_acts.
      { edestruct even_pub_priv_disj; eauto. }
      edestruct @even_odd_priv_disj; eauto.  
    - left. simpl in *.
      pose proof STEP2 as [[? ->] | PRIV__o]%action_of_step%odd_acts.
      { apply odd_step_inv in STEP2. lia. }
      pose proof STEP1 as [[? ->] | PRIV__e]%action_of_step%even_acts.
      { edestruct odd_pub_priv_disj; eauto. }
      edestruct @even_odd_priv_disj; eauto.
  Qed.

  Definition prod_states_wf (mtr: mtrace M) :=
    trace_always' mtr (fun s _ => exists m, st2nat' s m).

  (* TODO: reuse trace_lookup definitions here *)
  Lemma progress_helper i ρ P
  (mtr : evenodd_mtrace)
  (Hvalid : mtrace_valid mtr)
  (Hfirst : st2nat' (trfirst mtr) i)
  (Pi: P i)
  (m : nat)
  (STEP : pred_at mtr m (λ _ ℓ, ℓ = Some (Some ρ)))
  (INCR : ∀ st__e a st__e', amTrans FM st__e (a, Some ρ) st__e' →
                         st2nat' st__e i → P i → st2nat' st__e' (S i))
  (WF: prod_states_wf mtr)
  :
  ∃ m0, pred_at mtr m0 (λ s _, st2nat' s (S i)).
  Proof.
    generalize dependent mtr. induction m.
    { intros. 
      punfold Hvalid. inversion Hvalid as [| ? ? ? TRANS]; subst. 
      { done. }
      rewrite /pred_at in STEP. simpl in STEP. inversion STEP. subst.
      exists 1. rewrite pred_at_S. apply pred_at_state_trfirst.
      simpl in TRANS. inversion TRANS; subst.
      simpl in Hfirst. eauto. }

    intros.
    destruct mtr.
    { by apply pred_at_S_singl in STEP. }
    pose proof Hvalid as VALID'. eapply mtrace_valid_after with (k := 1) in VALID'.
    2: { simpl. reflexivity. }
    punfold Hvalid. inversion Hvalid as [| ??? TRANS VALID]; subst.
    simpl in TRANS. apply am_fmtrans_action in TRANS as [a TRANS].
    simpl in Hfirst. 

    opose proof * (WF 1) as NEXT. 
    { simpl. apply pred_at_S in STEP. red in STEP.
      destruct after; done. }

    apply pred_at_state_trfirst in NEXT as [m' NEXT].
    ogeneralize * st2nat_next; eauto.
    intros [-> | ->]. 
    { exists 1. rewrite pred_at_S. by apply pred_at_state_trfirst. }
    
    apply pred_at_S in STEP.
    specialize (IHm mtr). ospecialize * IHm; eauto.
    { eapply (trace_always'_after _ _ 1); eauto. done. }  
    destruct IHm as [k ?]. exists (S k). by rewrite pred_at_S.
  Qed.
    

  (* TODO: reuse trace_lookup definitions here *)
  Theorem evenodd_mdl_progresses_Even i (mtr : evenodd_mtrace) :
    infinite_trace mtr → mtrace_valid mtr → (∀ ρ, fair_model_trace ρ mtr) →
    prod_states_wf mtr ->
    st2nat' (trfirst mtr) i → Nat.even i →
    ∃ m, pred_at mtr m (λ s _, st2nat' s (S i)).
  Proof.
    intros Hinf Hvalid Hfair WF Hfirst Heven.

    opose proof (ρEven_always_live (trfirst mtr) _ _); [done| ]. 

    red in Hfair. ospecialize (Hfair ρEven 0 _).
    { by apply pred_at_state_trfirst. }
    
    destruct Hfair as [m FAIR]. rewrite plus_O_n in FAIR.
    destruct FAIR as [DIS | STEP]. 
    { rewrite -(plus_O_n m) in DIS. apply pred_at_sum' in DIS.
      destruct (after m mtr) eqn:A; [| done]. apply pred_at_state_trfirst in DIS.
      eapply trace_always'_state_after in WF as [??]; eauto.  
      destruct DIS. eapply ρEven_always_live; eauto. }

    assert (forall st__e a st__e', amTrans FM st__e (a, Some ρEven) st__e' ->
                          st2nat' st__e i -> Nat.even i ->
                          st2nat' st__e' (S i)) as INCR. 
    { clear -even_AM. intros ??? STEP **. inversion STEP; subst.
      2: { done. }
      clear STEP. rename STEP1 into STEP. inversion STEP; subst. 
      - pose proof STEP1 as [[? ->] | ?]%action_of_step%even_acts.
        + destruct NO0. apply odd_acts. eauto.
        + edestruct even_role_pub_priv_disj; eauto.
          do 1 eexists. eapply even_steppable.
          erewrite (f_equal Nat.even); [| apply H]. 
          done. 
      - pose proof STEP1 as [[? ->] | ?]%action_of_step%even_acts.
        + apply even_step_inv in STEP1. eapply odd_sync_inv in STEP2.
          destruct H. do 2 red. simpl in *. lia.
        + eapply even_priv_odd_noact in H1. destruct H1.
          eapply action_of_step; eauto. } 

    eapply progress_helper; eauto.
  Qed. 
  
  (* TODO: reuse trace_lookup definitions here *)
  Theorem evenodd_mdl_progresses_Odd i (mtr : evenodd_mtrace) :
    infinite_trace mtr → mtrace_valid mtr → (∀ ρ, fair_model_trace ρ mtr) →
    prod_states_wf mtr ->
    st2nat' (trfirst mtr) i → Nat.odd i →
    ∃ m, pred_at mtr m (λ s _, st2nat' s (S i)).
  Proof.
    intros Hinf Hvalid Hfair WF Hfirst Hodd.

    opose proof (ρOdd_always_live (trfirst mtr) _ _); [done| ]. 

    red in Hfair. ospecialize (Hfair ρOdd 0 _).
    { by apply pred_at_state_trfirst. }
    
    destruct Hfair as [m FAIR]. rewrite plus_O_n in FAIR.
    destruct FAIR as [DIS | STEP]. 
    { rewrite -(plus_O_n m) in DIS. apply pred_at_sum' in DIS.
      destruct (after m mtr) eqn:A; [| done]. apply pred_at_state_trfirst in DIS.
      eapply trace_always'_state_after in WF as [??]; eauto.  
      destruct DIS. eapply ρOdd_always_live; eauto. }

    assert (forall st__e a st__e', amTrans FM st__e (a, Some ρOdd) st__e' ->
                          st2nat' st__e i -> Nat.odd i ->
                          st2nat' st__e' (S i)) as INCR. 
    { clear -even_AM. intros ??? STEP **. inversion STEP; subst.
      2: { done. }
      clear STEP. rename STEP1 into STEP. inversion STEP; subst. 
      - pose proof STEP2 as [[? ->] | ?]%action_of_step%odd_acts.
        + destruct NO1. apply even_acts. eauto.
        + edestruct odd_role_pub_priv_disj; eauto.
          do 1 eexists. eapply odd_steppable.
          erewrite (f_equal Nat.odd); [| apply H]. 
          done. 
      - pose proof STEP2 as [[? ->] | ?]%action_of_step%odd_acts.
        + apply even_sync_inv in STEP1. eapply odd_step_inv in STEP2.
          destruct H. do 2 red. simpl in *. lia.
        + eapply odd_priv_even_noact in H1. destruct H1.
          eapply action_of_step; eauto. } 

    eapply progress_helper; eauto.  
  Qed. 
    
  Theorem evenodd_mdl_progresses (mtr : evenodd_mtrace) :
    infinite_trace mtr → mtrace_valid mtr → (∀ ρ, fair_model_trace ρ mtr) →
    prod_states_wf mtr ->
    st2nat' (trfirst mtr) 0 →
    evenodd_mdl_progress mtr.
  Proof.
    intros Hinf Hvalid Hfair WF Hfirst i.
    induction i as [|i IHi].
    { exists 0. rewrite /pred_at. rewrite /trfirst in Hfirst. simpl.
      destruct mtr; done. }
    destruct IHi as [n Hpred].
    rewrite /pred_at in Hpred.
    destruct (after n mtr) as [mtr'|] eqn:Hafter; [|done].
    eapply infinite_trace_after'' in Hinf; [|done].
    eapply mtrace_valid_after in Hvalid; [|done].
    destruct (Nat.even i) eqn:Heqn.
    - assert (∀ ρ : fmrole M, fair_model_trace ρ mtr') as Hfair'.
      { intros. by eapply fair_model_trace_after. }
      assert (st2nat' (trfirst mtr') i) as Hfirst'.
      { rewrite /trfirst. destruct mtr'; done. }
      opose proof * evenodd_mdl_progresses_Even as [m Hpred']; eauto. 
      { eapply trace_always'_after; eauto. }
      exists (n + m).
      rewrite pred_at_sum. rewrite Hafter. done.
    - assert (∀ ρ : fmrole M, fair_model_trace ρ mtr') as Hfair'.
      { intros. by eapply fair_model_trace_after. }
      assert (st2nat' (trfirst mtr') i) as Hfirst'.
      { rewrite /trfirst. destruct mtr'; done. }
      opose proof * evenodd_mdl_progresses_Odd as [m Hpred']; eauto. 
      { eapply trace_always'_after; eauto. }
      { by rewrite -Nat.negb_even Heqn. } 
      exists (n + m).
      rewrite pred_at_sum. rewrite Hafter. done.
  Qed.
  
  Theorem evenodd_mdl_is_mono (mtr : evenodd_mtrace) :
    infinite_trace mtr → mtrace_valid mtr → (∀ ρ, fair_model_trace ρ mtr) →
    prod_states_wf mtr ->
    st2nat' (trfirst mtr) 0 ->
    evenodd_mdl_mono mtr.
  Proof.
    intros Hinf Hvalid Hfair WF Hfirst n.
    pose proof (Hinf n) as [mtr' Hafter].
    destruct mtr' as [|s l mtr'].
    { pose proof (Hinf (S n)) as [mtr'' Hafter'].
      replace (S n) with (n + 1) in Hafter' by lia.
      rewrite after_sum' in Hafter'. rewrite Hafter in Hafter'. done. }

    pose proof WF as WF_. 
    eapply trace_always'_state_after in WF_ as [m CUR__n]; eauto. simpl in CUR__n.
    exists m. rewrite -{1}(Nat.add_0_r n) pred_at_sum Hafter. split; auto.
    ogeneralize * mtrace_valid_after; eauto. intros VALID__n.
    punfold VALID__n. inversion VALID__n. subst.
    simpl in H1. apply am_fmtrans_action in H1 as [? TRANS].
    eapply trace_always'_after in WF; eauto.
    
    (* opose proof * (WF n); [done| ]. apply pred_at_state_trfirst in H as [??].  *)
    ospecialize * (WF 1); [done| ]. apply pred_at_state_trfirst in WF as [??].  

    eapply st2nat_next in TRANS; eauto.
    rewrite -Nat.add_1_r. rewrite pred_at_sum Hafter.
    apply pred_at_S. apply pred_at_state_trfirst.
    eexists. split; eauto. lia. 
  Qed. 
  
End ModelMono.


Section MonoLMPreserved.
  (** Proof that fair progress is preserved through auxiliary trace *)

  Context {even_impl: EvenModel} {odd_impl: OddModel}.

  Let PM := @prod_model even_impl odd_impl.
  Context {prod_AM_act_dec: ∀ a, Decision (is_action_of PM a)}. 

  Let M := @the_fair_model even_impl odd_impl _ _ EnvUnitAM.
  Let LM := @the_model even_impl odd_impl _ _ EnvUnitAM.
  (* Let st2nat := st2nat even_impl odd_impl.  *)
  Let FM := @full_model even_impl odd_impl UnitAM. 

  Definition evenodd_aux_progress (auxtr : auxtrace LM) :=
    ∀ (i: nat), ∃ n, pred_at auxtr n (λ s l, (λ s' _, st2nat' s' i)
                                        (ls_under s) (l ≫= Ul)).
  
  Lemma evenodd_mtr_aux_progress_preserved
    (mtr : mtrace M)
    (auxtr : auxtrace LM) :
    upto_stutter (ls_under ∘ ls_data) Ul auxtr mtr →
    evenodd_mdl_progress mtr → evenodd_aux_progress auxtr.
  Proof.
    intros Hstutter Hmtr n. specialize (Hmtr n).
    by apply (trace_eventually_stutter_preserves
                (ls_under ∘ ls_data) Ul auxtr mtr (λ s' _, st2nat' s' n)).
  Qed.
  
  Definition evenodd_aux_mono (auxtr : auxtrace LM) :=
    ∀ n, ∃ (i: nat), pred_at auxtr n (λ s l, (λ s' _, st2nat' s' i) (ls_under s) (l ≫= Ul)) ∧
                pred_at auxtr (S n) (λ s l, (λ s' _, ∃ j, st2nat' s' j ∧ i ≤ j) (ls_under $ ls_data s) (l ≫= Ul)).
  
  Lemma evenodd_mtr_aux_mono_preserved (mtr : mtrace M)
    (auxtr : auxtrace LM) :
    upto_stutter (ls_under ∘ ls_data) Ul auxtr mtr →
    evenodd_mdl_mono mtr → evenodd_aux_mono auxtr.
  Proof.
    Set Printing Coercions.
    intros Hstutter Hmtr n.
    revert auxtr mtr Hstutter Hmtr.
    induction n as [|n IHn]; intros auxtr mtr Hstutter Hmtr.
    { 
      punfold Hstutter; [|apply upto_stutter_mono].
      induction Hstutter as
        [|auxtr mtr s ℓ Hℓ Hauxtr_first Hmtr_first CIHstutter IHstutter|
          auxtr mtr s ℓ δ ρ Hs Hℓ CIHstutter].
      - by destruct (Hmtr 0) as [? [? Hmtr']].
      - simplify_eq.
        destruct (IHstutter Hmtr) as [i [Hpred ?]].
        rewrite /pred_at in Hpred. simpl in *.
        exists i. rewrite /pred_at. simpl.
        destruct auxtr as [|s' ℓ' auxtr']; [done|].
        rewrite /trfirst in Hauxtr_first. split.
        { congruence. }
        exists i. simplify_eq. split; [|lia]. congruence. 
      - simplify_eq.
        destruct (Hmtr 0) as [i [Hpred1 Hpred2]].
        rewrite /pred_at in Hpred1. simpl in *.
        exists i.
        rewrite /pred_at. split; [done|].
        rewrite /pred_at in Hpred2. simpl in *.
        destruct CIHstutter as [CIHstutter|?]; [|done].
        punfold CIHstutter; [|apply upto_stutter_mono].
        induction CIHstutter as
          [|mtr auxtr ??? Hauxtr_first Hmtr_first ? IHstutter|];
          [done| |by simplify_eq].
        specialize (IHstutter Hmtr Hpred2).        
        destruct mtr.
        * destruct IHstutter as [j [Hj1 Hj2]]. exists j.
          split; try by simplify_eq.
          simpl in Hauxtr_first. congruence. 
        * destruct IHstutter as [j [Hj1 Hj2]]. exists j.
          split; try by simplify_eq.
          simpl in Hauxtr_first. congruence. }
    punfold Hstutter; [|apply upto_stutter_mono].
    induction Hstutter as
      [|auxtr mtr s ℓ Hℓ Hauxtr_first Hmtr_first CIHstutter IHstutter|
        auxtr mtr s ℓ δ ρ Hs Hℓ CIHstutter].
    + by destruct (Hmtr 0) as [? [? Hmtr']].
    + simplify_eq. setoid_rewrite pred_at_S. eapply IHn; [by apply paco2_fold|done].
    + simplify_eq. destruct CIHstutter as [CIHstutter|?]; [|done].
      assert (evenodd_mdl_mono mtr) as Hmtr'.
      { intros m. specialize (Hmtr (S m)). by setoid_rewrite pred_at_S in Hmtr. }
      destruct (IHn auxtr mtr CIHstutter Hmtr') as [i [Hpred1 Hpred2]].
      exists i. by rewrite !pred_at_S.
Qed.

End MonoLMPreserved.

Section ExAuxPropsPreserved.
  (** Proof that progress is preserved between auxilary and execution trace,
      for a specific ξ *)
  
  Context {even_impl: EvenModel} {odd_impl: OddModel}.

  Let PM := @prod_model even_impl odd_impl.
  Context {prod_AM_act_dec: ∀ a, Decision (is_action_of PM a)}. 

  Let M := @the_fair_model even_impl odd_impl _ _ EnvUnitAM.
  Let LM := @the_model even_impl odd_impl _ _ EnvUnitAM.
  (* Let st2nat := st2nat even_impl odd_impl.  *)
  Let FM := @full_model even_impl odd_impl UnitAM. 

  Definition evenodd_ex_progress (l:loc) (extr : heap_lang_extrace) :=
    ∀ (i: nat), ∃ n, pred_at extr n (λ s _, heap s.2 !! l = Some #i).
  
  Definition evenodd_ex_mono (l:loc) (extr : heap_lang_extrace) :=
    ∀ n, ∃ (i: nat),
      pred_at extr n (λ s _, heap s.2 !! l = Some #i) ∧
      pred_at extr (S n) (λ s _, ∃ (j:nat), heap s.2 !! l = Some #j ∧ i ≤ j).  
  
  Definition ξ_evenodd_model_match (l : loc) (c : cfg heap_lang) (δ: M) :=
    ∃ (N:nat), heap c.2 !! l = Some #N ∧ st2nat' δ N.
  
  Definition ξ_evenodd_no_val_steps (c : cfg heap_lang) :=
    (Forall (λ e, is_Some $ to_val e) c.1 → False) ∧
      Forall (λ e, not_stuck e c.2) c.1.
  
  Definition ξ_evenodd (l : loc) (c : cfg heap_lang) (δ : M) :=
    ξ_evenodd_no_val_steps c ∧ ξ_evenodd_model_match l c δ.

  Set Printing Coercions.
  Definition ξ_evenodd_trace (l : loc) (extr : execution_trace heap_lang)
    (mtr : finite_trace M (option (fmrole M))) :=
    ξ_evenodd l (trace_last extr) (trace_last mtr).
  
  Lemma st2nat_uniq st n1 n2 
    (CUR1: @st2nat even_impl odd_impl st n1) (CUR2: st2nat st n2):
    n1 = n2.
  Proof.
    destruct st as [??], CUR1, CUR2. congruence.
  Qed. 

  Lemma evenodd_aux_ex_progress_preserved l (extr: heap_lang_extrace) (auxtr : auxtrace LM):
    traces_match labels_match (λ c (δ: LM), ξ_evenodd l c δ) locale_step
      (lm_ls_trans LM) extr auxtr →
    evenodd_aux_progress auxtr → evenodd_ex_progress l extr.
  Proof.
    intros Hξ Hauxtr n. specialize (Hauxtr n).
    rewrite /pred_at in Hauxtr. destruct Hauxtr as [m Hauxtr].
    destruct (after m auxtr) as [auxtr'|] eqn:Heqn.
    2: { by rewrite Heqn in Hauxtr. }
    eapply traces_match_after in Hξ as [extr' [Hafter' Hextr']]; [|done].
    exists m. rewrite /pred_at. rewrite Hafter'.
    inversion Hextr' as [?? Hξ|??????? Hξ]; simplify_eq.
    - destruct Hξ as (?&k&?&?).
      rewrite Heqn in Hauxtr.
      assert (k = n) as -> by (eapply st2nat_uniq; eauto). 
      by simplify_eq.
    - destruct Hξ as (?&k&?&?).
      rewrite Heqn in Hauxtr.
      assert (k = n) as -> by (eapply st2nat_uniq; eauto). 
      by simplify_eq.
  Qed.
  
  Lemma evenodd_aux_ex_mono_preserved l (extr : heap_lang_extrace) (auxtr : auxtrace LM) :
    traces_match labels_match (λ c (δ: LM), ξ_evenodd l c δ) locale_step
      (lm_ls_trans LM) extr auxtr →
    evenodd_aux_mono auxtr → evenodd_ex_mono l extr.
  Proof.
    intros Hξ Hauxtr n. specialize (Hauxtr n).
    destruct Hauxtr as [i Hauxtr].
    exists i.
    split.
    - destruct Hauxtr as [Hauxtr _].
      rewrite /pred_at in Hauxtr.
      destruct (after n auxtr) as [auxtr'|] eqn:Heqn.
      2: { by rewrite Heqn in Hauxtr. }
      eapply traces_match_after in Hξ as [extr' [Hafter' Hextr']]; [|done].
      rewrite /pred_at. rewrite Hafter'.
      inversion Hextr' as [?? Hξ|??????? Hξ]; simplify_eq.
      + destruct Hξ as (?&k&?&?).
        rewrite Heqn in Hauxtr.
        assert (k = i) as -> by (eapply st2nat_uniq; eauto).
        by simplify_eq.
      + destruct Hξ as (?&k&?&?).
        rewrite Heqn in Hauxtr.
        assert (k = i) as -> by (eapply st2nat_uniq; eauto).
        by simplify_eq.
    - destruct Hauxtr as [_ Hauxtr].
      rewrite /pred_at in Hauxtr.
      destruct (after (S n) auxtr) as [auxtr'|] eqn:Heqn.
      2: { by rewrite Heqn in Hauxtr. } 
      eapply traces_match_after in Hξ as [extr' [Hafter' Hextr']]; [|done].
      rewrite /pred_at. rewrite Hafter'.
      rewrite Heqn in Hauxtr. 
      inversion Hextr' as [?? Hξ|??????? Hξ]; simplify_eq.
      + destruct Hauxtr as [j [ST2 Hle]].
        destruct Hξ as (?&k&?&?). 
        exists j. split; auto.
        assert (k = j) as -> by (eapply st2nat_uniq; eauto).
        by simplify_eq.
      + destruct Hauxtr as [j [ST2 Hle]].
        destruct Hξ as (?&k&?&?).
        exists j. split; auto.
        assert (k = j) as -> by (eapply st2nat_uniq; eauto).
        by simplify_eq.
  Qed.

End ExAuxPropsPreserved.

(** Proof that program refines model up to ξ_evenodd *)

Section Adequacy.
  Context (even_impl: EvenModel) (odd_impl: OddModel).

  Let PM := @prod_model even_impl odd_impl.
  Context {prod_AM_act_dec: ∀ a, Decision (is_action_of PM a)}. 

  Let M := @the_fair_model even_impl odd_impl _ _ EnvUnitAM.
  Let LM := @the_model even_impl odd_impl _ _ EnvUnitAM.
  (* Let st2nat := st2nat even_impl odd_impl.  *)
  Let FM := @full_model even_impl odd_impl UnitAM. 

  Let init_roles: gset (fmrole M) := 
        {[ inl $ even_role (ρ__e even_impl); inl $ odd_role (ρ__o odd_impl) ]}.

  Let start_prog := @start incr_loop_even_prog incr_loop_odd_prog.

  Definition Ns__split := nroot .@ "split".

  Definition eo_inv_main_vs `{!heapGS Σ LM}
    `{sGS: SplitGS Σ PM UnitAM}
    l ns (sr: nat -> iProp Σ):
    inv ns (evenodd_inv_inner EnvUnitAM sr l) ⊢ main_vs sr l ns.
  Proof using.
    rewrite /main_vs. iIntros "#INV". iModIntro.
    iMod (inv_acc with "INV") as "[OPEN CLOS]".
    { apply top_subseteq. }
    iModIntro.
    rewrite /evenodd_inv_inner. iDestruct "OPEN" as (?) "(?&?&?)".
    iFrame.
    iIntros "?". iMod ("CLOS" with "[-]") as "_"; [| done].
    iFrame.
  Qed.

  Lemma start_spec_use Σ
    prog 
    (l : loc)
    (Hinv : heapGS Σ LM)
    (eoΣ: evenoddG Σ)
    (th_preG: threadPreG Σ)
    (sGS: SplitGS Σ PM UnitAM)
    `(SR__e: StateRes Nat.even sr even_at)
    `(SR__o: StateRes Nat.odd sr odd_at)
    (SPEC: even_odd_spec sr even_at odd_at SR__e SR__o prog)
    :
    {{{ inv (Ns__split) (split_inv_inner) ∗ 
        inv (nroot.@"even_odd") (evenodd_inv_inner EnvUnitAM sr l) ∗
        0 ↦M gset_to_gmap 61 init_roles ∗
        even_at 0 ∗
        odd_at 1 ∗
        frag_free_roles_are ∅ }}}
      prog #l @0
      {{{ x, RET x; 0 ↦M ∅ }}}.
  Proof.  
    simpl. rewrite /init_roles.
    rewrite !gset_to_gmap_union_singleton. rewrite gset_to_gmap_singleton. 
    iIntros (Φ) "(#SPLIT & #Hinv & Hf & Heven_at & Hodd_at & FR) HΦ".
    iApply (SPEC with "[Hf Heven_at Hodd_at Hinv SPLIT FR]"); eauto.
    2: { iFrame "#∗". iSplit; [| iSplit].
         - iApply invs_even_vs; [..| by iFrame "#∗"]; [| solve_ndisj].
           apply unit_indep_r.
         - iApply invs_odd_vs; [..| by iFrame "#∗"]; [| solve_ndisj].
           apply unit_indep_r.
         - iApply eo_inv_main_vs. done. }
    set_solver. 
  Qed.
  
  Lemma dom_locales
    (c: cfg heap_lang)
    (fm : gmap (locale heap_lang) (gmap (fmrole M) nat))
    (Htp : fuel_map_preserve_threadpool c.1 fm)
    (HMζ : ∀ i : nat, i < length c.1 → fm !! i = Some ∅):
    dom fm = list_to_set (locales_of_list c.1).
  Proof.
    apply set_eq.
    intros x. rewrite elem_of_dom.
    rewrite elem_of_list_to_set.
    split.
    - intros HSome.
      destruct (decide (x ∈ locales_of_list c.1)) as [|Hnin]; [done|].
      apply Htp in Hnin.
      destruct HSome as [??]. set_solver. 
    - intros Hin. exists ∅. apply HMζ.
      rewrite locales_of_list_indexes in Hin.
      rewrite /indexes in Hin.
      apply elem_of_lookup_imap_1 in Hin as (i&?&->&HSome).
      by apply lookup_lt_is_Some_1.
  Qed.

  Lemma not_all_val `{!heapGS Σ LM} 
    (c : cfg heap_lang) δ e
    (Hsmaller : tids_smaller c.1 δ)
    (fm : gmap (locale heap_lang) (gmap (fmrole M) nat))
    (Hfmle : fuel_map_le fm (ls_map δ))
    (Hfmdead : fuel_map_preserve_dead fm (live_roles M δ))
    (Htp : fuel_map_preserve_threadpool c.1 fm)
    (Hall : Forall (λ e : expr, is_Some (to_val e)) c.1):
    auth_fuel_mapping_is fm -∗
      posts_of c.1  ([λ _ : language.val heap_lang, 0 ↦M ∅] ++
                       ((λ '(tnew, e), fork_post (language.locale_of tnew e)) <$>
                          prefixes_from
                          [e]
                          (drop 1 c.1)))
      -∗
      ⌜ live_roles _ (ls_under δ) = ∅ ⌝.
  Proof.
    iIntros "Hfm Hposts".
    simpl. 
    rewrite !big_sepL_omap !big_sepL_zip_with=> /=.
    iAssert ([∗ list] k↦x ∈ c.1, k ↦M ∅)%I with "[Hposts]" as "Hposts".
    { destruct c as [es σ]=> /=.
      iApply (big_sepL_impl with "Hposts").
      iIntros "!>" (k x HSome) "Hk".
      assert (is_Some (to_val x)) as [v Hv].
      { by eapply (Forall_lookup_1 (λ e : expr, is_Some (to_val e))). }
      rewrite Hv. destruct k; [done|]. destruct es; [done|].
      simpl in *. rewrite drop_0. rewrite list_lookup_fmap.
      erewrite prefixes_from_lookup; [|done].
      simpl. rewrite /locale_of. rewrite take_length.
      assert (k < length es).
      { apply lookup_lt_is_Some_1. by eauto. }
      by replace (k `min` length es) with k by lia. }
    iAssert (⌜∀ i, i < length c.1 → fm !! i = Some ∅⌝)%I as "%HMζ".
    { iIntros (i Hlen).
      assert (is_Some $ c.1 !! i) as [e' HSome].
      { by apply lookup_lt_is_Some_2. }
      iDestruct (big_sepL_delete with "Hposts") as "[Hpost _]"; [done|].
      by iDestruct (has_fuels_agree with "Hfm Hpost") as "?". }
    assert (dom fm = list_to_set $ locales_of_list c.1).
    { subst. apply dom_locales; auto. }
    
    clear -Hfmdead HMζ Hfmle Hsmaller. iPureIntro. 
    apply set_eq. intros i. split; [|done].
    intros (ζ&fs&HSome&Hfs)%Hfmdead.
    assert (fm !! ζ = Some ∅).
    { apply HMζ.
      assert (ζ ∈ dom (ls_map δ)) as Hin.
      { destruct Hfmle as [Hfmle1 Hfmle2].
        rewrite /fuel_map_le_inner map_included_spec in Hfmle1.
        apply Hfmle1 in HSome as (?&?&?).
        by apply elem_of_dom. }
      apply Hsmaller in Hin as [? Hin].
      apply lookup_lt_is_Some_1.
      by apply from_locale_lookup in Hin. }
    set_solver. 
  Qed.
    
  Existing Instance even_AME. 
  Existing Instance odd_AME.

  Lemma eo_rah l `(!heapGS Σ LM) sr
    (eoΣ: evenoddG Σ) `(threadPreG Σ) (sGS: SplitGS Σ PM UnitAM)
    st e h
    (CUR__0: st2nat' st 0)
    :
    inv (nroot.@"even_odd") (evenodd_inv_inner EnvUnitAM sr l) -∗
    inv Ns__split split_inv_inner -∗
      rel_always_holds NotStuck [λ _ : language.val heap_lang, 0 ↦M ∅]
      (λ (extr : execution_trace heap_lang) (atr : auxiliary_trace LM),
        ξ_evenodd_trace l extr (map_underlying_trace atr))
      ([e], h)
      (initial_ls st 0).
  Proof.
    iIntros "#Hinv #SPLIT".
    iIntros (extr auxtr c) "_ _ _ %Hends _ %Hnstuck %Hequiv [_ [Hσ Hδ]] Hposts".
    
    iInv "Hinv" as (N) "(>CUR & >Hn & Hauths)" "Hclose".
    rewrite /cur_st. iDestruct "CUR" as ([st__e st__o]) "[ST %CUR]".
    rewrite {1}/split_inv_inner. simpl. 
    iInv "SPLIT" as ([p ?]) ">(Hmod & PROD)" "_". simpl.
    iDestruct (left_agree with "[$] [$]") as %->.
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose'".
    iDestruct (gen_heap_valid with "Hσ Hn") as %Hn.
    iDestruct (model_state_interp_tids_smaller with "Hδ") as %Hsmaller.
    iDestruct "Hδ" as (fm Hfmle Hfmdead Htp) "[Hδ Hfm]".

    iDestruct (model_agree with "Hδ Hmod") as %Hn'.
    iSplitL; last first.
    { iPureIntro. exists N. split; [done|].
      rewrite trace_last_underlying Hn'. done. }
    rewrite /trace_ends_in in Hends.
    rewrite Hends.
    iSplit.
    - iIntros "%Hall". subst c.
      iPoseProof (not_all_val with "Hfm Hposts") as "%LR0"; eauto.
      rewrite Hn' in LR0.
      opose proof * (ρEven_always_live (_, _)) as LR.
      { apply CUR. }
      Unshelve. 2: exact u. 
      clear -LR LR0. set_solver. 
    - iPureIntro.
      apply Forall_forall.
      intros e' He. by apply Hnstuck.
  Qed.

  Definition evenoddΣ : gFunctors :=
    #[ heapΣ M; GFunctor (excl_authR natO); SplitΣ PM UnitAM ].

  (* TODO: move *)
  Global Instance subG_evenoddΣ' {Σ} : subG evenoddΣ Σ → SplitPreGS Σ PM UnitAM.
  Proof. solve_inG. Qed. 

  Global Instance subG_evenoddΣ {Σ} : subG evenoddΣ Σ → evenoddPreG Σ.
  Proof. Qed.
  (* Proof. solve_inG. Qed. *)

  Definition wholeΣ := #[evenoddΣ; threadΣ]. 

  #[local] Instance proof_irrel_trans s1 x:
    ProofIrrel ((let '(s2, ℓ) := x in fmtrans M s1 ℓ s2): Prop).
  Proof. apply make_proof_irrel. Qed.

  Lemma prod_model_finitary s1:
    Finite
      {'(s2, ℓ) | fmtrans M s1 ℓ s2}. 
  Proof.
    pose (@amfb'_ns PM _) as ns. 
    destruct s1 as [s1 u]. 
    apply (in_list_finite ((fun '(x, y, z) => ((x, u), z ≫= Some ∘ inl)) <$> ns s1)).
    intros [st oρ] STEP. apply am_fmtrans_action in STEP as [? STEP].

    assert (exists ρ, oρ = Some (inl ρ)) as [ρ ->].
    { inversion STEP; subst; eauto; done. }    
    simpl in STEP. inversion STEP; subst.
    2: { done. }

    eapply elem_of_list_fmap. eexists (_, _, _). split.
    2: { by apply amfb'_ns_spec. }
    eauto. 
  Qed.

  (* TODO: find more general versions *)
  Instance the_model_mstate_countable : EqDecision (mstate LM).
  Proof. intros x y. apply make_decision. Qed.
  Instance the_model_mlabel_countable : EqDecision (mlabel LM).
  Proof. solve_decision. Qed.

  Let st0: amSt PM := (even_init even_impl, odd_init odd_impl).
  Let st0': amSt FM := (st0, tt).

  Lemma st0_zero: st2nat st0 0.
  Proof. split; auto using even_init_0, odd_init_0. Qed.

  Lemma st0'_zero: st2nat' st0' 0.
  Proof. split; auto using even_init_0, odd_init_0. Qed.

  Lemma st0_lr: 
    AM_live_roles st0' = init_roles.
  Proof. 
    subst init_roles st0'.
    (* Set Printing Implicit. *)
    (* erewrite prod_indep_live_roles.  *)
    rewrite (@prod_indep_live_roles _ _ (unit_indep_r PM)).
    
    rewrite unit_lr set_map_empty union_empty_r_L.
    erewrite <- !set_map_singleton_L. erewrite <- set_map_union_L.
    f_equal. erewrite !set_map_singleton_L.    

    pose proof (@prod_AM_live_roles even_impl odd_impl).
    ospecialize * H.
    { apply st0_zero. }
    rewrite H.
    rewrite even_init_lr odd_init_lr.
    f_equal; try reflexivity.
    all: rewrite set_map_singleton_L; reflexivity.

    (* TODO: fix that *)
    Unshelve.
    36, 46, 54: by apply gset_singleton.
    all: by apply _. 
  Qed.

  Lemma evenodd_sim prog l
    (SPEC: forall `{!heapGS Σ LM, evenoddG Σ, SplitGS Σ PM UnitAM} st_res even_at odd_at
             (SR__e: StateRes Nat.even st_res even_at)
             (SR__o: StateRes Nat.odd st_res odd_at),
        even_odd_spec st_res even_at odd_at SR__e SR__o prog)
    :
    continued_simulation
      (sim_rel_with_user LM (ξ_evenodd_trace l))
      (trace_singleton ([prog #l], {| heap := {[l:=#0]};  used_proph_id := ∅ |}))
      (trace_singleton (initial_ls (LM := LM) st0' 0)).
  Proof.
    assert (evenoddPreG wholeΣ) as HPreG'.
    { apply _. }
    assert (heapGpreS evenoddΣ LM) as HPreG.
    { apply _. }
    assert (threadPreG wholeΣ) as thPreG.
    { apply _. }
    assert (SplitPreGS wholeΣ PM UnitAM) as sPreG.
    { apply _. }
    eapply (strong_simulation_adequacy NotStuck _ _ _ ∅ (Σ := wholeΣ)).
    2: { simpl. rewrite st0_lr. set_solver. }
    { eapply rel_finitary_sim_rel_with_user_sim_rel.
      eapply valid_state_evolution_finitary_fairness_simple.
      intros ?. simpl. apply prod_model_finitary. }
    iIntros (?) "!> Hσ Hs Hr Hf".

    iMod (st_res_init 0) as "(%st_res & %even_at & %odd_at & SR & E & O & %SR__e & %SR__o)"; [done| ].
    iMod (split_init st0 ((): amSt UnitAM)) as (γ__s) "(PROD & LEFT & RIGHT)".

    set (sGS := {| γ__split := γ__s; spre := sPreG |}). 

    iMod (inv_alloc (nroot .@ "even_odd") _ (evenodd_inv_inner EnvUnitAM st_res l (sGS := sGS)) with "[Hσ LEFT SR]") as "#Hinv".
    { iNext. unfold evenodd_inv_inner.
      rewrite /st0. 
      iExists 0.
      simpl. rewrite big_sepM_singleton. iFrame.
      rewrite /cur_st. 
      iPureIntro. apply st0_zero. }

    iMod (inv_alloc Ns__split _ (split_inv_inner) with "[PROD Hs]") as "#SPLIT".
    { iNext. iFrame. }

    iModIntro.
    iSplitL.
    2: { iApply eo_rah; try done.
         by apply st0_zero. }
    iApply (start_spec_use with "[-]"); try done.
    { eapply SPEC; eauto. done. }
    2: { iNext. by iIntros "**". }
    rewrite subseteq_empty_difference_L; [| done]. 
    rewrite -st0_lr. iFrame "#∗".
    iSplitL "E"; [iApply "E"| iApply "O"].
    Unshelve. all: done. 
  Qed.
  
  CoInductive extrace_maximal {Λ} : extrace Λ → Prop :=
  | extrace_maximal_singleton c :
    (∀ oζ c', ¬ locale_step c oζ c') → extrace_maximal ⟨c⟩
  | extrace_maximal_cons c oζ tr :
    locale_step c oζ (trfirst tr) ->
    extrace_maximal tr →
    extrace_maximal (c -[oζ]-> tr).
  
  Lemma extrace_maximal_valid {Λ} (extr : extrace Λ) :
    extrace_maximal extr → extrace_valid extr.
  Proof.
    revert extr. cofix IH. intros extr Hmaximal. inversion Hmaximal.
    - constructor 1.
    - constructor 2; [done|by apply IH].
  Qed.
  
  Lemma extrace_maximal_after {Λ} n (extr extr' : extrace Λ) :
    extrace_maximal extr → after n extr = Some extr' → extrace_maximal extr'.
  Proof.
    revert extr extr'. induction n; intros extr extr' Hafter Hvalid.
    { destruct extr'; simpl in *; by simplify_eq. }
    simpl in *. destruct extr; [done|]. eapply IHn; [|done]. by inversion Hafter.
  Qed.
  
  Lemma infinite_trace_no_val_steps extr auxtr :
    extrace_maximal extr →
    traces_match
      (labels_match (LM:=LM))
      (λ c _ , ξ_evenodd_no_val_steps c) locale_step
      (lm_ls_trans LM) extr auxtr →
    infinite_trace extr.
  Proof.
    intros Hmaximal Hmatch.
    intros n. induction n as [|n IHn]; [done|].
    destruct IHn as [extr' Hafter].
    apply traces_match_flip in Hmatch.
    eapply traces_match_after in Hmatch; [|done].
    destruct Hmatch as [auxtr' [Hafter' Hmatch]].
    replace (S n) with (n + 1) by lia.
    rewrite after_sum'.
    rewrite Hafter.
    apply traces_match_first in Hmatch.
    destruct Hmatch as [Hξ1 Hξ2].
    eapply extrace_maximal_after in Hmaximal; [|done].
    inversion Hmaximal as [? Hnstep|]; simplify_eq; [|done].
    assert (∃ oζ c', locale_step c oζ c') as Hstep; last first.
    { exfalso. destruct Hstep as (?&?&Hstep). by eapply Hnstep. }
    apply not_Forall_Exists in Hξ1; [|apply _].
    apply Exists_exists in Hξ1 as [e [Hξ11 Hξ12]].
    rewrite Forall_forall in Hξ2.
    specialize (Hξ2 e Hξ11) as [|Hred]; [done|].
    destruct Hred as (e' & σ' & es' & Hred).
    apply elem_of_list_split in Hξ11 as (es1&es2&Hes).
    destruct c; simpl in *.
    eexists (Some _), _.
    econstructor; eauto. simpl in *.
    by f_equiv.
  Qed.
  
  (* Lemma prod_valid_states_wf mtr n *)
  (*   (VALID: mtrace_valid mtr) *)
  (*   (CUR0: st2nat (trfirst mtr) n): *)
  (*   @prod_states_wf even_impl odd_impl mtr. *)
  (* Proof using. *)
  (*   red. intros mtr' i AFTER. *)
  (*   generalize dependent mtr'. induction i. *)
  (*   { simpl. intros ? [=->]. eauto. } *)
  (*   intros. *)
  (*   ogeneralize * after_is_Some_le. *)
  (*   { apply (Nat.le_succ_diag_r i). } *)
  (*   { eauto. } *)
  (*   intros [mtr'' AFTER'']. *)
  (*   ospecialize * IHi; eauto. destruct IHi as [m CUR']. *)
  (*   opose proof * (mtrace_valid_after _ _ i) as VALID'; eauto. *)
  (*   rewrite -Nat.add_1_r after_sum' AFTER'' in AFTER. *)
  (*   destruct mtr'' eqn:T; [done| ]. simpl in AFTER, CUR'. *)
  (*   inversion AFTER. subst t. *)
  (*   punfold VALID'. inversion VALID'. subst. *)
  (*   simpl in H1. apply am_fmtrans_action in H1 as [? TRANS]. *)
  (*   eapply st2nat_next in TRANS; eauto. *)
  (*   destruct TRANS; eauto. *)
  (* Qed. *)

  (* (* TODO: can weaken all requirements except state relation *) *)
  (* Lemma match_evenodd_prod_wf l (etr : heap_lang_extrace) (lmtr : auxtrace LM) *)
  (*   (Hmatch_strong : traces_match labels_match *)
  (*                      (λ (x0 : cfg heap_lang) (x1 : lm_ls LM), *)
  (*                        live_tids x0 x1 ∧ ξ_evenodd l x0 x1) *)
  (*                      locale_step *)
  (*                      (lm_ls_trans LM) *)
  (*                      etr lmtr): *)
  (*   prod_states_wf lmtr.  *)

  Lemma extr_props (l: loc) e
    (extr : heap_lang_extrace)
    (Hmaximal : extrace_maximal extr)
    (Hfair : ∀ tid : locale heap_lang, fair_ex tid extr)
    (Hfirst : trfirst extr = ([e], {| heap := {[l := #0]}; used_proph_id := ∅ |}))
    (auxtr : auxtrace LM)
    (Hmatch_strong : traces_match labels_match
                       (λ (x0 : cfg heap_lang) (x1 : lm_ls LM),
                         live_tids x0 x1 ∧ ξ_evenodd l x0 x1)
                       locale_step
                       (lm_ls_trans LM)
                       extr auxtr):
    evenodd_ex_progress l extr ∧ evenodd_ex_mono l extr.
  Proof. 
    assert (exaux_traces_match extr auxtr) as Hmatch.
    { eapply traces_match_impl; [done| |done]. by intros ??[??]. }
    assert (auxtrace_valid auxtr) as Hstutter.
    { by eapply exaux_preserves_validity. }
    apply can_destutter_auxtr in Hstutter.
    destruct Hstutter as [mtr Hupto].
    assert (infinite_trace extr) as Hinf.
    { eapply infinite_trace_no_val_steps; [done|].
      eapply traces_match_impl; [done| |apply Hmatch_strong].
      by intros s1 s2 [_ [? _]]. }
    pose proof (fairness_preserved extr auxtr Hinf Hmatch Hfair) as Hfairaux.
    have Hvalaux := exaux_preserves_validity extr auxtr Hmatch.
    have Hfairm := upto_stutter_fairness auxtr mtr Hupto Hfairaux.
    have Hmtrvalid := upto_preserves_validity auxtr mtr Hupto Hvalaux.
    pose proof (fairness_preserved extr auxtr Hinf Hmatch Hfair) as Hfair'.
    pose proof (upto_stutter_fairness auxtr mtr Hupto Hfair') as Hfair''.    
    assert (infinite_trace mtr) as Hinf''.
    { eapply upto_stutter_infinite_trace; [done|].
      by eapply traces_match_infinite_trace. }
    assert (mtrace_valid mtr) as Hvalid''.
    { eapply upto_preserves_validity; [done|].
      by eapply exaux_preserves_validity. }
    (* assert (trfirst mtr = 0) as Hfirst''. *)
    assert (st2nat' (trfirst mtr) 0) as Hfirst''.
    { apply traces_match_first in Hmatch_strong.
      destruct Hmatch_strong as [_ [_ [n [Hσ Hmdl]]]].
      rewrite Hfirst in Hσ. simpl in *. rewrite lookup_insert in Hσ.
      simplify_eq. punfold Hupto; [|by apply upto_stutter_mono'].
      (* assert (0 = ls_under (trfirst auxtr)) as Hσ' by lia. *)
      destruct n; [| lia]. clear Hσ.
      inversion Hupto; simplify_eq; simpl in *; congruence. }
    (* trace_always *)      

    (* opose proof (prod_valid_states_wf _ _ _ _) as WF; eauto.   *)
    assert (prod_states_wf mtr) as WF.
    { clear -Hmatch_strong Hupto. 
      eapply upto_preserves_trace_always'_state; eauto. 
      eapply traces_match_trace_always'_state_2. 
      { apply Hmatch_strong. }
      simpl. intros ?? [_ EO]. red in EO.
      apply proj2 in EO. red in EO.
      eapply Morphisms_Prop.ex_impl_morphism; [| apply EO].
      red. intros. red. tauto. }

    split.
    - pose proof (evenodd_mdl_progresses mtr Hinf'' Hvalid'' Hfair'' WF Hfirst'') as Hprogress.
      eapply (evenodd_aux_ex_progress_preserved l _ auxtr).
      { eapply traces_match_impl; [done| |apply Hmatch_strong]. by intros ??[??]. }
      by eapply evenodd_mtr_aux_progress_preserved. 
    - pose proof (evenodd_mdl_is_mono mtr Hinf'' Hvalid'' Hfair'' WF Hfirst'')
        as Hmono.
      eapply (evenodd_aux_ex_mono_preserved l _ auxtr).
      { eapply traces_match_impl; [done| |apply Hmatch_strong]. by intros ??[??]. }
      by eapply evenodd_mtr_aux_mono_preserved.
  Qed. 
  

  (** Proof that the execution trace satisfies the liveness properties *)
  Theorem evenodd_ex_liveness prog
    (SPEC: forall `{!heapGS Σ LM, evenoddG Σ, SplitGS Σ PM UnitAM} st_res even_at odd_at
             (SR__e: StateRes Nat.even st_res even_at)
             (SR__o: StateRes Nat.odd st_res odd_at),
        even_odd_spec st_res even_at odd_at SR__e SR__o prog)
    (l:loc) (extr : heap_lang_extrace)
    :
    extrace_maximal extr →
    (∀ tid, fair_ex tid extr) →
    trfirst extr = ([prog #l], {| heap := {[l:=#0]}; used_proph_id := ∅ |}) →
    evenodd_ex_progress l extr ∧ evenodd_ex_mono l extr.
  Proof.
    intros Hmaximal Hfair Hfirst.
    pose proof Hmaximal as Hvalid%extrace_maximal_valid.
    pose proof (evenodd_sim prog l) as Hsim.
    
    assert (∃ iatr,
               valid_inf_system_trace
                 (continued_simulation (sim_rel_with_user LM (ξ_evenodd_trace l)))
                 (trace_singleton (trfirst extr))
                 (trace_singleton (initial_ls (LM:=LM) st0' 0))
                 (from_trace extr)
                 iatr) as [iatr Hiatr].
    { eexists _. eapply produced_inf_aux_trace_valid_inf. econstructor.
      Unshelve.
      - rewrite Hfirst. apply Hsim; auto. 
      - eapply from_trace_preserves_validity; eauto; first econstructor. }
    
    assert (∃ (auxtr : auxtrace LM),
               traces_match labels_match
                 (live_tids /2\ (ξ_evenodd l))
                 locale_step
                 LM.(lm_ls_trans) extr auxtr) as [auxtr Hmatch_strong].
    { exists (to_trace (initial_ls (LM := LM) st0' 0 ) iatr).
      eapply (valid_inf_system_trace_implies_traces_match_strong
                (continued_simulation (sim_rel_with_user LM (ξ_evenodd_trace l)))); eauto.
      - intros ? ? Hξ%continued_simulation_rel. by destruct Hξ as [[_ Hξ] _].
      - intros ? ? Hξ%continued_simulation_rel. by destruct Hξ as [[Hξ _] _].
      - intros extr' auxtr' Hξ%continued_simulation_rel.
        destruct Hξ as [_ [Hξ1 Hξ2]].
        split; [done|].
        destruct Hξ2 as [n [Hξ21 Hξ22]].
        exists n. split; [done|]. by destruct auxtr'.
      - by apply from_trace_spec.
      - by apply to_trace_spec. }
    
    eapply extr_props; eauto. 
  Qed.

End Adequacy.


Section AdequacyConcrete.

  From trillium.fairness.heap_lang.examples.even_odd Require Import submodels.

  Let PM := @prod_model thread_0_even thread_1_odd.

  Local Instance PM_act_dec: ∀ a, Decision (is_action_of PM a).
  Proof.
    intros a. 
    destruct (decide (a ∈ (↑ pub_ns: coPset))).
    { left. unshelve eapply coPset_nth_surj in e.
      { by apply nclose_infinite. }
      destruct e as [n ->]. red. 
      destruct (even_or_odd n).
      - exists (n, n), (Some $ inl $ ρ__e thread_0_even), (S n, S n).
        econstructor; eauto.
        + econstructor. by rewrite Nat.add_0_r.
        + econstructor. by rewrite odd_plus1_negb Nat.negb_odd.
      - exists (n, n), (Some $ inr $ ρ__o thread_1_odd), (S n, S n).
        econstructor; eauto.
        + econstructor. by rewrite Nat.add_0_r.
        + econstructor. by rewrite even_plus1_negb Nat.negb_even. }
    destruct (even_priv_dec thread_0_even a).
    { left. red. exists (1, 1), (Some $ inl $ ρ__e thread_0_even), (1, 1).
      econstructor.
      { eapply even_priv_odd_noact; eauto. }
      simpl in e. red in e. subst.  
      simpl. by econstructor. }
    destruct (odd_priv_dec thread_1_odd a).
    { left. red. exists (0, 0), (Some $ inr $ ρ__o thread_1_odd), (0, 0). 
      econstructor.
      { eapply odd_priv_even_noact; eauto. }
      simpl in o. red in o. subst.  
      simpl. by econstructor. }

    right. intros ACT%prod_actions_sub.
    rewrite even_acts odd_acts in ACT.
    destruct ACT as [[[? ->]|] | [[? ->]|]]; eauto. 
    all: destruct n; apply coPset_nth_in. 
  Qed.

  Lemma start_adequacy
    (l:loc) (extr : heap_lang_extrace)
    :
    extrace_maximal extr →
    (∀ tid, fair_ex tid extr) →
    trfirst extr = ([(start incr_loop_even_prog incr_loop_odd_prog) #l], {| heap := {[l:=#0]}; used_proph_id := ∅ |}) →
    evenodd_ex_progress l extr ∧ evenodd_ex_mono l extr.
  Proof.
    apply (evenodd_ex_liveness thread_0_even thread_1_odd).
    intros. apply start_spec; eauto.
  Qed. 

  Lemma short_adequacy
    (l:loc) (extr : heap_lang_extrace)
    :
    extrace_maximal extr →
    (∀ tid, fair_ex tid extr) →
    trfirst extr = ([short #l], {| heap := {[l:=#0]}; used_proph_id := ∅ |}) →
    evenodd_ex_progress l extr ∧ evenodd_ex_mono l extr.
  Proof.
    apply (evenodd_ex_liveness thread_0_even thread_1_odd).
    intros. eapply short_spec; eauto.
  Qed. 

End AdequacyConcrete.
