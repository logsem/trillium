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


(* TODO: move *)
Section MatchedBy.
  Context {M__s M__m: ActionModel}.
  Context (R: amSt M__s -> amSt M__m -> Prop). 

  Definition matched_by := 
    forall st__s st__s' a ρ st__m,
      R st__s st__m -> amTrans _ st__s (a, Some ρ) st__s' -> is_action_of M__m a ->
    exists st__m', amTrans _ st__m (a, None) st__m' /\ R st__s' st__m'.

  Hypothesis (MATCH: matched_by). 

  Lemma matched_by_prod_step_l st__s st__s' a ρ st__m
    (R1: R st__s st__m) (STEP__s: amTrans _ st__s (a, Some ρ) st__s')
    (PRIV_S_R: ¬ (is_action_of M__m a) -> R st__s' st__m)
    {is_act_m_dec: forall a, Decision (is_action_of M__m a)}:
    exists st__m', amTrans (ProdAM M__s M__m) (st__s, st__m) (a, Some (inl ρ)) (st__s', st__m') /\ R st__s' st__m'.
  Proof using MATCH. 
    destruct (decide (is_action_of M__m a)).
    - opose proof * MATCH as (st__m' & STEP__m & R2); eauto.
      eexists. split; eauto. econstructor; eauto.
    - eexists. split; [| by apply PRIV_S_R]. econstructor; eauto.
  Qed. 
    
  Lemma matched_by_prod_step_r st__s st__s' a ρ st__m
    (R1: R st__s st__m) (STEP__s: amTrans _ st__s (a, Some ρ) st__s')
    (PRIV_S_R: ¬ (is_action_of M__m a) -> R st__s' st__m)
    {is_act_m_dec: forall a, Decision (is_action_of M__m a)}:
    exists st__m', amTrans (ProdAM M__m M__s) (st__m, st__s) (a, Some (inr ρ)) (st__m', st__s') /\ R st__s' st__m'.
  Proof using MATCH. 
    destruct (decide (is_action_of M__m a)).
    - opose proof * MATCH as (st__m' & STEP__m & R2); eauto.
      eexists. split; eauto. econstructor; eauto.
    - eexists. split; [| by apply PRIV_S_R]. econstructor; eauto.
  Qed.

  Lemma matched_prod_AM_live_roles_l
    `{Countable (amRole M__s)} {STR__s: AM_strong_lr M__s}
    `{forall a, Decision (is_action_of M__m a)}
    `{Countable (amRole (ProdAM M__s M__m))} {STR__p: AM_strong_lr (ProdAM M__s M__m)}
    st__e st__o
    (R1: R st__e st__o)
    (PRIV_S_R: forall st__e' a ρ, amTrans _ st__e (a, Some ρ) st__e' ->
                           ¬ (is_action_of M__m a) -> R st__e' st__o):    
      set_map inl (AM_live_roles STR__s st__e) ⊆ AM_live_roles STR__p (st__e, st__o).
  Proof using MATCH.
    apply elem_of_subseteq. intros ρ.
    rewrite elem_of_map. setoid_rewrite <- AM_live_roles_spec.
    intros (ρ__e & -> & (a__e & st__e' & STEP__e)).
    ogeneralize * matched_by_prod_step_l; eauto. 
    intros (?&?&?). eexists. eauto.
  Qed. 

  Lemma matched_prod_AM_live_roles_r
    `{Countable (amRole M__s)} {STR__s: AM_strong_lr M__s}
    `{forall a, Decision (is_action_of M__m a)}
    `{Countable (amRole (ProdAM M__m M__s))} {STR__p: AM_strong_lr (ProdAM M__m M__s)}
    st__e st__o
    (R1: R st__e st__o)
    (PRIV_S_R: forall st__e' a ρ, amTrans _ st__e (a, Some ρ) st__e' ->
                           ¬ (is_action_of M__m a) -> R st__e' st__o):    
      set_map inr (AM_live_roles STR__s st__e) ⊆ AM_live_roles STR__p (st__o, st__e).
  Proof using MATCH.
    apply elem_of_subseteq. intros ρ.
    rewrite elem_of_map. setoid_rewrite <- AM_live_roles_spec.
    intros (ρ__e & -> & (a__e & st__e' & STEP__e)).
    ogeneralize * matched_by_prod_step_r; eauto. 
    intros (?&?&?). eexists. eauto.
  Qed. 

  Lemma always_live_lift_l
    `{Countable (amRole M__s)} `{STR__s: AM_strong_lr M__s}
    `{Countable (amRole (ProdAM M__s M__m))} `{STR__p: AM_strong_lr (ProdAM M__s M__m)}
    `{forall a, Decision (is_action_of M__m a)}
    ρ
    (LIVE: forall st__s, ρ ∈ AM_live_roles STR__s st__s)
    (PRIV_S_R: forall st__e st__e' a ρ st__o, amTrans _ st__e (a, Some ρ) st__e' ->
                           ¬ (is_action_of M__m a) -> R st__e' st__o):
    forall st__s st__m, R st__s st__m -> inl ρ ∈ AM_live_roles STR__p (st__s, st__m).
  Proof using MATCH.
    intros. apply singleton_subseteq_l. etrans.
    2: { eapply matched_prod_AM_live_roles_l; eauto. }
    eapply singleton_subseteq_l. by apply elem_of_map_2.
  Qed.
 
End MatchedBy.


(* Lemma matched_prod_AM_live_roles *)
(*   `{MATCH1: @matched_by M__s M__m R} `{MATCH2: @matched_by M__m M__s (flip R)} *)
(*   `{Countable (amRole M__s)} {STR__s: AM_strong_lr M__s} `{forall a, Decision (is_action_of M__s a)} *)
(*   `{Countable (amRole M__m)} {STR__m: AM_strong_lr M__m} `{forall a, Decision (is_action_of M__m a)} *)
(*   `{Countable (amRole (ProdAM M__s M__m))} {STR__p: AM_strong_lr (ProdAM M__s M__m)} *)
(*   st__e st__o *)
(*   (R1: R st__e st__o) *)
(*   (PRIV_S_R: forall st__e' a ρ, amTrans _ st__e (a, Some ρ) st__e' -> *)
(*                          ¬ (is_action_of M__m a) -> R st__e' st__o) *)
(*   (PRIV_M_R: forall st__o' a ρ, amTrans _ st__o (a, Some ρ) st__o' -> *)
(*                          ¬ (is_action_of M__s a) -> R st__e st__o') *)
(*   : *)
(*   AM_live_roles STR__p (st__e, st__o) =  *)
(*     set_map inl (AM_live_roles STR__s st__e) ∪  *)
(*     set_map inr (AM_live_roles STR__m st__o). *)
(* Proof using. *)
(*   apply set_eq. intros ρ. *)
(*   rewrite elem_of_union !elem_of_map. *)
(*   setoid_rewrite <- AM_live_roles_spec. *)
(*   split. *)
(*   { intros (a & st' & STEP). inversion STEP; subst. *)
(*     all: set_solver. }  *)
(*   intros [(ρ__e & -> & (a__e & st__e' & STEP__e))| (ρ__o & -> & (a__o & st__o' & STEP__o))]. *)
(*   - ogeneralize * matched_by_prod_step_l.  *)
(*     { eapply MATCH1. } *)
(*     all: eauto.  *)
(*     intros (?&?&?). eexists. eauto. *)
(*   - ogeneralize * matched_by_prod_step_r.  *)
(*     { eapply MATCH2. } *)
(*     all: eauto.  *)
(*     { intros. eapply PRIV_M_R; eauto. } *)
(*     intros (?&?&?). eexists. eauto. *)
(* Qed. *)


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

  Definition st2nat (st: fmstate the_fair_model) N :=
    cur_even even_impl st.1 = N /\ cur_odd odd_impl st.2 = N.

  Definition the_model: LiveModel heap_lang the_fair_model :=
    {| lm_flm := 61%nat; |}.

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

  Lemma even_matched_by_odd: matched_by (fun st__e st__o => exists N, st2nat (st__e, st__o) N).
  Proof. 
    red. intros st__e st__e' a ρ st__o [n CORR] STEP__e ACT__o.
    pose proof STEP__e as ACT%action_of_step%even_acts.
    destruct ACT as [[k ->] | PRIV]. 
    2: { edestruct even_priv_odd_noact; eauto. }
    destruct CORR as [CUR__e CUR__o]. simpl in *. 
    apply even_step_inv in STEP__e. destruct STEP__e as (<-&?&E).
    opose proof * odd_syncable as (st__o' & STEP__o); eauto.
    { erewrite (f_equal Nat.even); eauto. rewrite CUR__e. eauto. }
    rewrite CUR__o -CUR__e in STEP__o. 
    eexists. split; eauto.
    apply odd_sync_inv in STEP__o as (?&?&?).
    eexists. split; eauto.
  Qed.        

  Lemma odd_matched_by_even: matched_by (fun st__o st__e => exists N, st2nat (st__e, st__o) N).
  Proof. 
  Admitted. 

End Models.  

Section proof.
  Context {even_impl: EvenModel} {odd_impl: OddModel}.

  Let M := @the_fair_model even_impl odd_impl.
  Let LM := @the_model even_impl odd_impl.
  Context {Σ: gFunctors}. 

  Existing Instance even_AME. 
  Existing Instance odd_AME.

  Let even_AM := @even_AM even_impl. 
  Let odd_AM := @odd_AM odd_impl. 
  
  Lemma prod_AM_live_roles st__e st__o n
    (CUR: st2nat (st__e, st__o) n)
    :
    AM_live_roles (@prod_AM_strong_lr even_impl odd_impl) (st__e, st__o) = 
    set_map even_role (AM_live_roles ame_strong st__e) ∪ 
    set_map odd_role (AM_live_roles ame_strong st__o).
  Proof using.
    apply set_eq_subseteq. split.
    { apply elem_of_subseteq. intros ρ. 
      rewrite elem_of_union !elem_of_map.
      setoid_rewrite <- AM_live_roles_spec. 
      intros (a & st' & STEP). inversion STEP; subst.
      all: set_solver. }
    
    apply union_subseteq. split.
    - unshelve eapply matched_prod_AM_live_roles_l; cycle 1. 
      { apply even_matched_by_odd. }
      { apply _. }
      { simpl. eexists. eauto. }
      simpl. intros st__e' a ρ STEP__e NACT__o. 
      pose proof STEP__e as ACT%action_of_step%even_acts.
      destruct ACT as [[k ->] | PRIV].
      { destruct NACT__o. apply odd_acts. eauto. }
      apply even_stutter_inv in STEP__e; eauto.
      eexists. split; eauto. simpl. destruct CUR. simpl in *. congruence.
    - unshelve eapply matched_prod_AM_live_roles_r; cycle 1.
      { apply odd_matched_by_even. }
      { apply _. }
      { simpl. eexists. eauto. }
      simpl. intros st__o' a ρ STEP__o NACT__e. 
      pose proof STEP__o as ACT%action_of_step%odd_acts.
      destruct ACT as [[k ->] | PRIV].
      { destruct NACT__e. apply even_acts. eauto. }
      apply odd_stutter_inv in STEP__o; eauto.
      eexists. split; eauto. simpl. destruct CUR. simpl in *. congruence. 
  Qed. 

  Lemma prod_step_lr_nonincr st st' a oρ n n'
    (STEP: amTrans (@prod_model even_impl odd_impl) st (a, oρ) st')
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

  Lemma mu_even `{!heapGS Σ LM} n:
    ⊢ cur_st n -∗ MU__r ρEven ∅ (cur_st (if Nat.even n then (n + 1)%nat else n)).
  Proof using.
    rewrite /MU__r /cur_st. iIntros "(%st & ST & %CUR)" (tid f' R) "[MAP %DISJ__R]".
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

  Lemma mu_odd `{!heapGS Σ LM} n:
    ⊢ cur_st n -∗ MU__r ρOdd ∅ (cur_st (if Nat.odd n then (n + 1)%nat else n)).
  Proof using.
    rewrite /MU__r /cur_st. iIntros "(%st & ST & %CUR)" (tid f' R) "[MAP %DISJ__R]".
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

  Section Viewshifts.
    Context `{!heapGS Σ LM}.
    
    Context (st_res even_at odd_at: nat -> iProp Σ). 
    Context
      (st_res_SR_even: @StateRes _ Nat.even st_res even_at)
      (st_res_SR_odd: @StateRes _ Nat.odd st_res odd_at). 
    
    Definition evenodd_inv_inner l : iProp Σ :=
      ∃ N, cur_st N ∗ l ↦ #N ∗ st_res N.
    
    Lemma even_vs l ns:
      inv ns (evenodd_inv_inner l) ⊢ eo_vs Nat.even st_res_SR_even l ns ρEven. 
    Proof using st_res_SR_even.
      rewrite /eo_vs. iIntros "#INV". iModIntro.
      iMod (inv_acc with "INV") as "[OPEN CLOS]".
      { apply top_subseteq. }
      
      rewrite {1}/evenodd_inv_inner.
      iDestruct "OPEN" as (m) "(>CUR & >Hn & Hauths)".
      iModIntro.
      iExists _. iSplitL "Hn Hauths".
      { iFrame. }
      
      iApply (MU__r_mask_weaken with "[-]"); [apply empty_subseteq| ]. 
      iApply (MU__r_wand with "[-CUR]").
      2: by iApply mu_even.
      
      rewrite /eo_corr. iIntros "CUR (?&?)".
      iMod ("CLOS" with "[-]") as "_"; [| done].
      rewrite /evenodd_inv_inner. iNext. iFrame.
    Qed.
    
    Lemma odd_vs l ns:
      inv ns (evenodd_inv_inner l) ⊢ eo_vs Nat.odd st_res_SR_odd l ns ρOdd. 
    Proof using st_res_SR_odd.
      rewrite /eo_vs. iIntros "#INV". iModIntro. 
      iMod (inv_acc with "INV") as "[OPEN CLOS]".
      { apply top_subseteq. }
      
      iDestruct "OPEN" as (m) "(>CUR & >Hn & Hauths)".
      iModIntro. iExists _. iSplitL "Hn Hauths".
      { iFrame. }
      simpl.
      
      iApply (MU__r_mask_weaken with "[-]"); [apply empty_subseteq| ]. 
      iApply (MU__r_wand with "[-CUR]").
      2: by iApply mu_odd.
      
      rewrite /eo_corr. iIntros "? (?&?)".
      iMod ("CLOS" with "[-]") as "_"; [| done].
      rewrite /evenodd_inv_inner. iNext. iFrame.
    Qed.

  End Viewshifts.
    
End proof.
