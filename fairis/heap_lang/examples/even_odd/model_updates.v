From stdpp Require Import decidable.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination utils action_model fuel resources.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode iris_inst.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness.heap_lang.examples Require Import env_am split_model mu_role.
From trillium.fairness.heap_lang.examples.even_odd Require Import interface thread_progs.
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

      
  (* doesn't look like there is a way to prove it for arbitrary product.
     Even the interface lemmas don't seem enough *)
  (* Global Instance prod_AM_act_dec: ∀ a : Action, Decision (is_action_of prod_model a). *)
  Context {prod_AM_act_dec: ∀ a, Decision (is_action_of prod_model a)}. 

  Context `(ENV_AM: EnvironmentAM env_AM).

  (* Instance env_AM_strong_lr: AM_strong_lr env_AM. *)
  (* Proof using. apply _. Qed.  *)

  Definition full_model := ProdAM prod_model env_AM.

  (* Instance full_AM_fin_branch': AM_fin_branch' full_model. *)
  (* Proof using ENV_AM. apply _. Qed.  *)

  (* Instance full_AM_strong_lr: AM_strong_lr full_model. *)
  (* Proof using All. apply _. Qed.  *)

  Definition the_fair_model: FairModel.
    unshelve eapply (AM2FM full_model).
  Proof using All. apply _. Defined.  

  Definition the_model: LiveModel heap_lang the_fair_model :=
    {| lm_flm := 61%nat; |}.

  Definition st2nat (st: amSt prod_model) (N: nat) :=
    cur_even even_impl st.1 = N /\ cur_odd odd_impl st.2 = N.

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

  Definition st2nat_ex st__e st__o := exists N, st2nat (st__e, st__o) N.

  Lemma even_synced_by_odd: 
    synced_by st2nat_ex. 
  Proof. 
    red. intros st__e st__e' a ρ st__o [n CORR] ACT__o STEP__e.
    pose proof STEP__e as ACT%action_of_step%even_acts.
    destruct ACT as [[k ->] | PRIV]. 
    2: { edestruct even_priv_odd_noact; eauto. }
    destruct CORR as [CUR__e CUR__o]. simpl in *.
    apply even_step_inv in STEP__e. destruct STEP__e as (<-&?&E).
    opose proof * odd_syncable as (st__o' & STEP__o); eauto.
    { erewrite (f_equal Nat.even); eauto. rewrite CUR__e. eauto. } 

    pose proof STEP__o as (?&?&?)%odd_sync_inv.
    rewrite CUR__o -CUR__e in STEP__o.
    eexists. split; eauto. eexists. split; eauto. simpl. lia. 
  Qed.

  Lemma odd_synced_by_even: synced_by (flip st2nat_ex).
  Proof. 
    red. intros st__o st__o' a ρ st__e [n CORR] ACT__e STEP__o.
    pose proof STEP__o as ACT%action_of_step%odd_acts.
    destruct ACT as [[k ->] | PRIV]. 
    2: { edestruct odd_priv_even_noact; eauto. }
    destruct CORR as [CUR__e CUR__o]. simpl in *.
    apply odd_step_inv in STEP__o. destruct STEP__o as (<-&?&O).
    opose proof * even_syncable as (st__e' & STEP__e); eauto.
    { erewrite (f_equal Nat.odd); eauto. rewrite CUR__o. eauto. } 

    pose proof STEP__e as (?&?&?)%even_sync_inv.
    rewrite CUR__e -CUR__o in STEP__e.
    eexists. split; eauto. eexists. split; eauto. simpl. lia. 
  Qed. 

  Context {Σ: gFunctors}. 

  (* Existing Instance even_AME.  *)
  (* Existing Instance odd_AME. *)

  (* Let even_AM := @even_AM even_impl.  *)
  (* Let odd_AM := @odd_AM odd_impl. *)

  (* Lemma prod_no_ext_sync (st: amSt prod_model): *)
  (*   None ∉ ams_lr st. *)
  (* Proof. *)
  (*   intros IN%ams_lr_spec. destruct IN as (?&?&STEP). *)
  (*   inversion STEP; subst. *)
  (*   pose proof STEP1 as ACT1%action_of_step%even_acts. *)
  (*   pose proof STEP2 as ACT2%action_of_step%odd_acts. *)
  (*   destruct ACT1 as [[k ?] | PRIV1], ACT2 as [[? EQ] | PRIV2]; subst; cycle 1.  *)
  (*   { by apply odd_pub_priv_disj in PRIV2. } *)
  (*   { by apply even_pub_priv_disj in PRIV1. } *)
  (*   { by edestruct @even_odd_priv_disj; eauto. } *)
  (*   apply coPset_nth_inj in EQ. subst. *)
  (*   apply even_sync_inv in STEP1 as (?&?&?). apply odd_sync_inv in STEP2 as (?&?&?). *)
  (*   edestruct even_odd_False; eauto. *)
  (* Qed. *)

  Lemma even_matched_by_prod: 
    @matched_by even_AM prod_model
      (fun st__s '(st__s', st__m) => st__s' = st__s /\ st2nat_ex st__s st__m)
      (inl)
      .
  Proof.
    apply matched_by_prod_l; try by apply _.
    { apply even_synced_by_odd. }
    intros st__e st__e' a ρ st__o [? CUR] STEP__e NACT__o. 
    pose proof STEP__e as ACT%action_of_step%even_acts.
    destruct ACT as [[k ->] | PRIV].
    { destruct NACT__o. apply odd_acts. eauto. }
    apply even_stutter_inv in STEP__e; eauto.
    eexists. split; eauto. simpl. destruct CUR. simpl in *. congruence.
  Qed. 
    
  Lemma odd_matched_by_prod: 
    @matched_by odd_AM prod_model
      (fun st__s '(st__m, st__s') => st__s' = st__s /\ st2nat_ex st__m st__s)
      (inr)
  .
  Proof.
    apply matched_by_prod_r; try by apply _.
    { apply odd_synced_by_even. }
    intros st__o st__o' a ρ st__e [? CUR] STEP__o NACT__o. 
    pose proof STEP__o as ACT%action_of_step%odd_acts.
    destruct ACT as [[k ->] | PRIV].
    { destruct NACT__o. apply even_acts. eauto. }
    apply odd_stutter_inv in STEP__o; eauto.
    eexists. split; eauto. simpl. destruct CUR. simpl in *. congruence.
  Qed. 
  
  Lemma prod_AM_live_roles st__e st__o n
    (CUR: st2nat (st__e, st__o) n)
    :
    AM_live_roles ((st__e, st__o): amSt prod_model) = 
    set_map even_role (AM_live_roles st__e) ∪ 
    set_map odd_role (AM_live_roles st__o).
  Proof using.
    apply set_eq_subseteq. split.
    { apply elem_of_subseteq. intros ρ. 
      rewrite elem_of_union !elem_of_map.
      setoid_rewrite <- AM_live_roles_spec. 
      intros (a & st' & STEP). inversion STEP; subst.
      all: set_solver. }
    
    apply union_subseteq. split.
    - eapply matched_AM_live_roles.
      { apply even_matched_by_prod. }
      simpl. split; eauto. red. eauto. 
    - eapply matched_AM_live_roles.
      { apply odd_matched_by_prod. }
      simpl. split; eauto. red. eauto. 
  Qed.

  Lemma prod_step_lr_nonincr st st' a oρ n n'
    (STEP: amTrans prod_model st (a, oρ) st')
    (CUR: st2nat st n) (NEXT: st2nat st' n'):
      AM_live_roles st' ⊆ AM_live_roles st.
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

  Let LM := the_model.
  Let PM := prod_model.
  Let M := the_fair_model. 

  Let ρEven: fmrole M := inl $ even_role (ρ__e even_impl).
  Let ρOdd: fmrole M := inl $ odd_role (ρ__o odd_impl).

  Context {sGS: SplitGS Σ prod_model env_AM}.
    
  Hypothesis PROD_ENV_INDEP: forall a, is_action_of PM a -> is_action_of env_AM a -> False.

  Definition cur_st n: iProp Σ :=
    (* ∃ (st: fmstate M), frag_model_is st ∗ ⌜ st2nat st.1 n ⌝. *)
    ∃ st, frag_left_st_is st ∗ ⌜ st2nat st n ⌝. 

  Lemma mu_even `{!heapGS Σ LM} n (ns: namespace):
    inv ns (split_inv_inner) ⊢ cur_st n -∗ MU__r ρEven (↑ ns) (cur_st (if Nat.even n then (n + 1)%nat else n)).
  Proof using PROD_ENV_INDEP.
    rewrite /MU__r /cur_st. iIntros "#INV (%st & ST & %CUR)" (tid f' R) "[MAP %DISJ__R]".
    (* destruct st as [[st__e st__o] st__env]. *)
    destruct st as [st__e st__o]. 
    destruct CUR as [CUR__E CUR__O]. simpl in *. 

    enough (exists a st', amTrans PM (st__e, st__o) (a, Some (even_role (ρ__e even_impl))) st' /\
                   st2nat st' (if Nat.even n then (n + 1) else n)) as (a & st' & TRANS & CUR'). 
    { iApply (MU_inv with "[$]"); [done| ].
      (* TODO: avoid unfolding of MU *)
      rewrite /split_inv_inner. iIntros ">(%S & FRAG & PROD)". destruct S.
      simpl. iDestruct (left_agree with "[$] [$]") as %->.

      iMod (update_left st' with "[$] [$]") as "[PROD ST]". 
      iApply (MU_wand with "[ST PROD]").
      2: { iApply (model_step_MU with "[$] [MAP]").
           1, 4: by eauto.
           { simpl. eapply am_fmtrans_action. eexists. 
             eapply pt_inner1; eauto.
             intros ?. edestruct PROD_ENV_INDEP; eauto.
             eapply action_of_step; eauto. }
           simpl. setoid_rewrite @prod_indep_live_roles; eauto.
           apply union_mono; [| done]. apply set_map_mono; [done| ].
           eapply prod_step_lr_nonincr; done. }
      iIntros "(MAP & FRAG)".
      iFrame. done. }
    Unshelve. 2: by apply _. 
    
    destruct (Nat.even n) eqn:E.
    - opose proof (even_steppable _ st__e) as (st__e' & STEP__e); eauto.
      { set_solver. }
      opose proof * odd_syncable as (st__o' & STEP__o); eauto.
      { erewrite (f_equal Nat.even); eauto. }
      rewrite CUR__E in STEP__e. rewrite CUR__O in STEP__o. 
      eexists _, (_, _). split; [| split].
      + simpl. eapply @pt_sync1; eauto.
      + simpl. eapply even_step_inv; eauto.
      + simpl. eapply odd_sync_inv; eauto.
    - pose proof E as O. rewrite -negb_true_iff Nat.negb_even in O. 
      opose proof (even_stutterable _ st__e) as (st__e' & a__e & PRIV & STEP__e); eauto.
      { rewrite CUR__E. intuition. }
      eexists _, (_, _). split; [| split].
      + simpl. eapply @pt_inner1; eauto.
        eapply even_priv_odd_noact; eauto.
      + simpl. symmetry. rewrite -CUR__E. eapply even_stutter_inv; eauto.
      + done.
  Qed.

  Lemma mu_odd `{!heapGS Σ LM} n ns:
    inv ns (split_inv_inner) ⊢ cur_st n -∗ MU__r ρOdd (↑ ns) (cur_st (if Nat.odd n then (n + 1)%nat else n)).
  Proof using PROD_ENV_INDEP.
    rewrite /MU__r /cur_st. iIntros "#INV (%st & ST & %CUR)" (tid f' R) "[MAP %DISJ__R]".
    destruct st as [st__e st__o]. destruct CUR as [CUR__E CUR__O]. simpl in *.

    enough (exists a st',
               amTrans PM (st__e, st__o) (a, Some (odd_role (ρ__o odd_impl))) st' /\
               st2nat st' (if Nat.odd n then (n + 1) else n)) as (a & st' & TRANS & CUR').
    { iApply (MU_inv with "[$]"); [done| ].
      (* TODO: avoid unfolding of MU *)
      rewrite /split_inv_inner. iIntros ">(%S & FRAG & PROD)". destruct S.
      simpl. iDestruct (left_agree with "[$] [$]") as %->.

      iMod (update_left st' with "[$] [$]") as "[PROD ST]". 
      iApply (MU_wand with "[ST PROD]").
      2: { iApply (model_step_MU with "[$] [MAP]").
           1, 4: by eauto.
           { simpl. eapply am_fmtrans_action. eexists.
             eapply pt_inner1; eauto.
             intros ?. edestruct PROD_ENV_INDEP; eauto.
             eapply action_of_step; eauto. }
           simpl. setoid_rewrite @prod_indep_live_roles; eauto.
           apply union_mono; [| done]. apply set_map_mono; [done| ].
           eapply prod_step_lr_nonincr; done. }
      iIntros "(MAP & FRAG)".
      iFrame. done. }
    Unshelve. 2: by apply _.
 
    destruct (Nat.odd n) eqn:O.
    - opose proof (odd_steppable _ st__o) as (st__o' & STEP__o); eauto.
      { rewrite CUR__O. set_solver. }
      opose proof * even_syncable as (st__e' & STEP__e); eauto.
      { erewrite (f_equal Nat.odd); eauto. }
      rewrite CUR__O in STEP__o. rewrite CUR__E in STEP__e.
      eexists _, (_, _). split; [| split].
      + simpl. eapply @pt_sync2; eauto.
      + simpl. eapply even_sync_inv; eauto.
      + simpl. eapply odd_step_inv; eauto.
    - pose proof O as E. rewrite -negb_true_iff Nat.negb_odd in E.
      opose proof (odd_stutterable _ st__o) as (st__o' & a__o & PRIV & STEP__o); eauto.
      { rewrite CUR__O. intuition. }
      eexists _, (_, _). split; [| split].
      + simpl. eapply @pt_inner2; eauto.
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
    
    Lemma invs_even_vs l ns1 ns2
      (DISJ: ns1 ## ns2)
      :
      inv ns1 (evenodd_inv_inner l) ∗
      inv ns2 (split_inv_inner)
      ⊢
      even_vs st_res_SR_even l ns1 ρEven.
    Proof using st_res_SR_even PROD_ENV_INDEP.
      clear st_res_SR_odd odd_at. 
      rewrite /eo_vs. iIntros "#[INV1 INV2]". iModIntro.
      iMod (inv_acc with "INV1") as "[OPEN CLOS]".
      { apply top_subseteq. }
      
      rewrite {1}/evenodd_inv_inner.
      iDestruct "OPEN" as (m) "(>CUR & >Hn & Hauths)".
      iModIntro.
      iExists _. iSplitL "Hn Hauths".
      { iFrame. }
      
      iApply (MU__r_mask_weaken (↑ ns2) with "[-]").
      { set_solver. }
      iApply (MU__r_wand with "[-CUR]").
      2: by iApply mu_even.
      
      rewrite /eo_corr. iIntros "CUR (?&?)".
      iMod ("CLOS" with "[-]") as "_"; [| done].
      rewrite /evenodd_inv_inner. iNext. iFrame.
    Qed.
    
    Lemma invs_odd_vs l ns1 ns2
      (DISJ: ns1 ## ns2):
      inv ns1 (evenodd_inv_inner l) ∗ inv ns2 (split_inv_inner) ⊢ 
      odd_vs st_res_SR_odd l ns1 ρOdd. 
    Proof using st_res_SR_odd PROD_ENV_INDEP.
      clear st_res_SR_even even_at.

      rewrite /eo_vs. iIntros "#[INV1 INV2]". iModIntro. 
      iMod (inv_acc with "INV1") as "[OPEN CLOS]".
      { apply top_subseteq. }
      
      iDestruct "OPEN" as (m) "(>CUR & >Hn & Hauths)".
      iModIntro. iExists _. iSplitL "Hn Hauths".
      { iFrame. }
      simpl.
      
      iApply (MU__r_mask_weaken (↑ ns2) with "[-]").
      { set_solver. }
      iApply (MU__r_wand with "[-CUR]").
      2: { by iApply mu_odd. }
      
      rewrite /eo_corr. iIntros "? (?&?)".
      iMod ("CLOS" with "[-]") as "_"; [| done].
      rewrite /evenodd_inv_inner. iNext. iFrame.
    Qed.

    (* Definition eo_inv_main_vs l ns: *)
    (*   inv ns (evenodd_inv_inner l) ⊢ main_vs ns. *)
    (* Proof using. *)
    (*   rewrite /main_vs. iIntros "#INV". iModIntro.  *)
    (*   iMod (inv_acc with "INV") as "[OPEN CLOS]". *)
    (*   { apply top_subseteq. } *)
    (*   iModIntro.  *)
    (*   rewrite /evenodd_inv_inner. iDestruct "OPEN" as (?) "(?&?&?)". *)
    (*   iFrame. *)
    (*   iIntros "?". iMod ("CLOS" with "[-]") as "_"; [| done]. *)
    (*   iFrame. *)
    (* Qed.  *)

  End Viewshifts.
    
End Models.
