From stdpp Require Import decidable.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination utils.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness.heap_lang.examples.even_odd Require Import action_model interface thread_progs.
Import derived_laws_later.bi.

Open Scope nat.

Set Default Proof Using "Type".


Section Models.
  Context {even_impl: EvenModel}.
  Context {odd_impl: OddModel}.

  Let even_AM := @even_AM even_impl. 
  Let odd_AM := @odd_AM odd_impl. 

  Definition prod_model := ProdAM even_AM odd_AM.

  Definition even_role: amRole even_AM -> amRole prod_model := inl. 
  Definition odd_role: amRole odd_AM -> amRole prod_model := inr.

  Existing Instance even_AME. 
  Existing Instance odd_AME.

  Lemma prod_AM_fin_branch': AM_fin_branch' prod_model.
  Proof. 
    unshelve eapply prod_AM_fin_branch'.
    - apply even_AME. 
    - apply odd_AME. 
  Qed.

  Lemma prod_AM_strong_lr: AM_strong_lr prod_model.
  Proof. 
    apply fin_branch_strong.
    - apply prod_AM_fin_branch'. 
    - unshelve eapply prod_AM_step_dec; try apply _. 
      all: apply even_AME || apply odd_AME. 
  Qed.

  Definition the_fair_model: FairModel.
    unshelve eapply (AM2FM prod_model). 
  Proof using even_impl odd_impl.
    apply prod_AM_strong_lr. 
  Defined.

  Definition the_model: LiveModel heap_lang the_fair_model :=
    {| lm_flm := 61%nat; |}.

End Models.  

Section proof.
  Context {even_impl: EvenModel} {odd_impl: OddModel}.

  Let M := @the_fair_model even_impl odd_impl.
  Let LM := @the_model even_impl odd_impl.
  Context {Σ: gFunctors}. 

  Existing Instance even_AME. 
  Existing Instance odd_AME.

  Definition st2nat (st: fmstate the_fair_model) N :=
    cur_even even_impl st.1 = N /\ cur_odd odd_impl st.2 = N.

  Let even_AM := @even_AM even_impl. 
  Let odd_AM := @odd_AM odd_impl. 
  
  (* TODO: derive from an appropriate "wrapped product" construction *)
  Lemma even_priv_odd_noact a
    (PRIV: even_is_priv_act even_impl a):
    ¬ is_action_of odd_AM a.
  Proof using.
    intros ACT__O%odd_acts. destruct ACT__O as [[k ->] | ?].
    + eapply even_pub_priv_disj; eauto. 
    + eapply even_odd_priv_disj; eauto.
  Qed.

  Lemma odd_priv_even_noact a
    (PRIV: odd_is_priv_act odd_impl a):
    ¬ is_action_of even_AM a.
  Proof using.
    intros ACT__E%even_acts. destruct ACT__E as [[k ->] | ?].
    + eapply odd_pub_priv_disj; eauto. 
    + eapply even_odd_priv_disj; eauto.
  Qed.

  Lemma prod_AM_live_roles st__e st__o n
    (CUR: st2nat (st__e, st__o) n)
    :
    AM_live_roles (@prod_AM_strong_lr even_impl odd_impl) (st__e, st__o) = 
    set_map even_role (AM_live_roles ame_strong st__e) ∪ 
    set_map odd_role (AM_live_roles ame_strong st__o).
  Proof using.
    apply set_eq. intros ρ.
    rewrite elem_of_union !elem_of_map.
    setoid_rewrite <- AM_live_roles_spec.
    destruct CUR as [CUR__e CUR__o]. simpl in *. 
    split.
    { intros (a & st' & STEP). inversion STEP; subst.
      all: set_solver. } 
    intros [(ρ__e & -> & (a__e & st__e' & STEP__e))| (ρ__o & -> & (a__o & st__o' & STEP__o))].
    - pose proof STEP__e as ACT%action_of_step%even_acts.
      destruct ACT as [[k ->] | PRIV]. 
      2: { eexists _, (_, _). eapply @pt_inner1; eauto.
           eapply even_priv_odd_noact; eauto. }        
      ogeneralize * even_step_inv; eauto.
      intros (X & CUR__e' & E). assert (n = k) as -> by congruence. clear X. 
      ogeneralize * odd_syncable; eauto.
      { erewrite @f_equal; [apply E| ]. by f_equal. }
      intros [st__o' STEP__o]. 
      eexists _, (_, _). eapply @pt_sync1; eauto.
      by rewrite CUR__o in STEP__o. 
    - pose proof STEP__o as ACT%action_of_step%odd_acts.
      destruct ACT as [[k ->] | PRIV]. 
      2: { eexists _, (_, _). eapply @pt_inner2; eauto.
           eapply odd_priv_even_noact; eauto. }
      ogeneralize * odd_step_inv; eauto.
      intros (X & CUR__o' & O). assert (n = k) as -> by congruence. clear X. 
      ogeneralize * even_syncable; eauto.
      { erewrite @f_equal; [apply O| ]. by f_equal. }
      intros [st__e' STEP__e]. 
      eexists _, (_, _). eapply @pt_sync2; eauto.
      by rewrite CUR__e.
  Qed.

  Lemma prod_step_lr_nonincr st st' a oρ n n'
    (STEP: amTrans prod_model st (a, oρ) st')
    (CUR: st2nat st n) (NEXT: st2nat st' n'):
      AM_live_roles prod_AM_strong_lr st' ⊆ AM_live_roles prod_AM_strong_lr st.
  Proof.
    destruct st as [st__e st__o], st' as [st__e' st__o'].
    erewrite !prod_AM_live_roles; eauto.
    apply union_subseteq. eapply Morphisms_Prop.and_impl_morphism.
    { red. eapply impl_transitive; [| apply union_subseteq_l'].
      by apply set_map_mono. }
    { red. eapply impl_transitive; [| apply union_subseteq_r'].
      by apply set_map_mono. }
    inversion STEP; subst.
    all: (try apply even_step_lr_nonincr in STEP1);
      (try apply odd_step_lr_nonincr in STEP2); set_solver.
   Qed.

  Let ρEven: fmrole M := even_role (ρ__e even_impl).
  Let ρOdd: fmrole M := odd_role (ρ__o odd_impl).

  Definition cur_st `{!heapGS Σ LM} n: iProp Σ :=
    ∃ st, frag_model_is st ∗ ⌜ st2nat st n ⌝. 

  Lemma mu_even `{!heapGS Σ LM} tid n:
    ⊢ cur_st n -∗ MU__r ρEven ∅ tid
        (cur_st (if Nat.even n then (n + 1)%nat else n)).
  Proof using.
    rewrite /MU__r /cur_st. iIntros "(%st & ST & %CUR)" (f' R) "[MAP %DISJ__R]".
    destruct st as [st__e st__o]. destruct CUR as [CUR__E CUR__O]. simpl in *. 

    enough (exists st', fmtrans the_fair_model (st__e, st__o) (Some ρEven) st' /\
                   st2nat st' (if Nat.even n then (n + 1) else n)) as (st' & TRANS & CUR'). 
    { iApply (MU_wand with "[]").
      2: { iApply (model_step_MU with "[$] [MAP]"); eauto.
           eapply am_fmtrans_action in TRANS as (?&?). 
           eapply prod_step_lr_nonincr; done. }
      iIntros "(MAP & ST)".
      iFrame. done. }
 
    destruct (Nat.even n) eqn:E.
    - opose proof (even_steppable _ st__e) as (st__e' & STEP__e); eauto.
      { set_solver. }
      opose proof * odd_syncable as (st__o' & STEP__o); eauto.
      { erewrite (f_equal Nat.even); eauto. }
      rewrite CUR__E in STEP__e. rewrite CUR__O in STEP__o. 
      eexists (_, _). split; [| split].
      + simpl. econstructor. eapply @pt_sync1; eauto.
      + simpl. eapply even_step_inv; eauto.
      + simpl. eapply odd_sync_inv; eauto.
    - pose proof E as O. rewrite -negb_true_iff Nat.negb_even in O. 
      opose proof (even_stutterable _ st__e) as (st__e' & a__e & PRIV & STEP__e); eauto.
      { rewrite CUR__E. intuition. }
      eexists (_, _). split; [| split].
      + simpl. econstructor. eapply @pt_inner1; eauto.
        eapply even_priv_odd_noact; eauto.
      + simpl. symmetry. rewrite -CUR__E. eapply even_stutter_inv; eauto.
      + done.
  Qed.

  Lemma mu_odd `{!heapGS Σ LM} tid n:
    ⊢ cur_st n -∗ MU__r ρOdd ∅ tid
        (cur_st (if Nat.odd n then (n + 1)%nat else n)).
  Proof using.
    rewrite /MU__r /cur_st. iIntros "(%st & ST & %CUR)" (f' R) "[MAP %DISJ__R]".
    destruct st as [st__e st__o]. destruct CUR as [CUR__E CUR__O]. simpl in *. 

    enough (exists st', fmtrans the_fair_model (st__e, st__o) (Some ρOdd) st' /\
                   st2nat st' (if Nat.odd n then (n + 1) else n)) as (st' & TRANS & CUR'). 
    { iApply (MU_wand with "[]").
      2: { iApply (model_step_MU with "[$] [MAP]"); eauto.
           eapply am_fmtrans_action in TRANS as (?&?). 
           eapply prod_step_lr_nonincr; done. }
      iIntros "(MAP & ST)".
      iFrame. done. }
 
    destruct (Nat.odd n) eqn:O.
    - opose proof (odd_steppable _ st__o) as (st__o' & STEP__o); eauto.
      { rewrite CUR__O. set_solver. }
      opose proof * even_syncable as (st__e' & STEP__e); eauto.
      { erewrite (f_equal Nat.odd); eauto. }
      rewrite CUR__O in STEP__o. rewrite CUR__E in STEP__e. 
      eexists (_, _). split; [| split].
      + simpl. econstructor. eapply @pt_sync2; eauto.
      + simpl. eapply even_sync_inv; eauto.
      + simpl. eapply odd_step_inv; eauto.
    - pose proof O as E. rewrite -negb_true_iff Nat.negb_odd in E. 
      opose proof (odd_stutterable _ st__o) as (st__o' & a__o & PRIV & STEP__o); eauto.
      { rewrite CUR__O. intuition. }
      eexists (_, _). split; [| split].
      + simpl. econstructor. eapply @pt_inner2; eauto.
        eapply odd_priv_even_noact; eauto.
      + done. 
      + simpl. symmetry. rewrite -CUR__O. eapply odd_stutter_inv; eauto.
  Qed. 
    
End proof.
