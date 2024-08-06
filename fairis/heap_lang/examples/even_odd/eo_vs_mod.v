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

(** The CMRAs we need. *)
Class evenoddPreG (Σ: gFunctors) := {
}.

Class evenoddG (Σ: gFunctors) := EvenoddG {
  eoPreG :> evenoddPreG Σ;
 }.

Section proof.
  Context {even_impl: EvenModel} {odd_impl: OddModel}.

  Let M := @the_fair_model even_impl odd_impl.
  Let LM := @the_model even_impl odd_impl.
  Context `{!heapGS Σ LM, !evenoddG Σ}.
  Context {th_preG: threadPreG Σ}. 

  Existing Instance even_AME. 
  Existing Instance odd_AME.

  Let Ns := nroot .@ "even_odd".

  (* Local Instance evenThreadG: threadG Σ := {| th_name := even_name |}.  *)
  (* Local Instance oddThreadG: threadG Σ := {| th_name := odd_name |}.  *)

  (* Definition even_at := (@th_at _ evenThreadG).  *)
  (* Definition odd_at := (@th_at _ oddThreadG).  *)

  (* Definition auth_even_at := (@auth_th_at _ evenThreadG).  *)
  (* Definition auth_odd_at := (@auth_th_at _ oddThreadG).   *)

  Definition st2nat (st: fmstate the_fair_model) N :=
    cur_even even_impl st.1 = N /\ cur_odd odd_impl st.2 = N.

  Context (st_res even_at odd_at: nat -> iProp Σ). 
  Context
    (st_res_SR_even: @StateRes _ Nat.even st_res even_at)
    (st_res_SR_odd: @StateRes _ Nat.odd st_res odd_at). 

  Definition evenodd_inv_inner l : iProp Σ :=
    ∃ st N,
      frag_model_is st ∗ ⌜ st2nat st N ⌝ ∗ 
      l ↦ #N ∗
      st_res N.

  Definition evenodd_inv n := inv Ns (evenodd_inv_inner n).

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
    clear dependent st_res.
    clear evenoddG0. 
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
    clear dependent st_res.
    clear evenoddG0 odd_at even_at. 
    destruct st as [st__e st__o], st' as [st__e' st__o'].
    (* opose proof * st2nat_step_ex as [n' CUR']; eauto. *)
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

  Lemma mu_even tid st n (CUR: st2nat st n):
    ⊢ frag_model_is st -∗ MU__r ρEven ∅ tid
        (∃ st', frag_model_is st' ∗ ⌜ st2nat st' (if Nat.even n then (n + 1)%nat else n) ⌝).
  Proof using.
    clear st_res_SR_odd st_res_SR_even st_res odd_at evenoddG0 even_at. 
    rewrite /MU__r. iIntros "ST "(f' R) "[MAP %DISJ__R]".
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

  Lemma even_spec_use tid l (N : nat) f (Hf: f > 40) (ep: EvenProg):
    {{{ evenodd_inv l ∗ tid ↦M {[ ρEven := f ]} ∗ even_at N }}}
      (e_prog ep) #l #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using st_res_SR_even.
    clear st_res_SR_odd evenoddG0 odd_at. 
    iIntros (Φ) "(#Hinv & Hf & Heo) Hk".
    
    iApply (@e_spec ep the_fair_model _ _ _ _ _ st_res_SR_even
             with "[$Hf $Heo]"); [lia| simpl; lia | |done].
    rewrite /eo_vs. iModIntro.
    iMod (inv_acc with "Hinv") as "[OPEN CLOS]".
    { apply top_subseteq. }
  
    iDestruct "OPEN" as ([st__e st__o] m) "(>Hmod & [>%CUR__E >%CUR__O] & >Hn & Hauths)".
    iModIntro.
    iExists _. iSplitL "Hn Hauths".
    { iFrame. }

    iApply (MU__r_mask_weaken with "[-]"); [apply empty_subseteq| ]. 
    iApply (MU__r_wand with "[-Hmod]").
    2: by iApply mu_even.

    rewrite /eo_corr. iIntros "[%st' (MAP & %ST)] (?&?)".
    iMod ("CLOS" with "[-]") as "_"; [| done].
    rewrite /evenodd_inv_inner. iNext. iFrame.
    destruct (Nat.even m) eqn:E; try done.
  Qed.

  Lemma mu_odd tid st n (CUR: st2nat st n):
    ⊢ frag_model_is st -∗ MU__r ρOdd ∅ tid
        (∃ st', frag_model_is st' ∗ ⌜ st2nat st' (if Nat.odd n then (n + 1)%nat else n) ⌝).
  Proof using st_res_SR_odd.
    clear st_res_SR_even evenoddG0 even_at.
    rewrite /MU__r. iIntros "ST" (f' R) "[MAP %DISJ__R]".
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
    
  Lemma odd_spec_use tid l (N : nat) f (Hf: f > 40) (op: OddProg):
    {{{ evenodd_inv l ∗ tid ↦M {[ ρOdd := f ]} ∗ odd_at N }}}
      (o_prog op) #l #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using st_res_SR_odd.
    clear st_res_SR_even.
    clear evenoddG0.
    clear even_at. 
    iIntros (Φ) "(#Hinv & Hf & Heo) Hk".
    
    iApply (@o_spec op the_fair_model _ _ _ _ _ st_res_SR_odd
             with "[$Hf $Heo]"); [lia| simpl; lia | |done].
    rewrite /eo_vs. iModIntro.
    iMod (inv_acc with "Hinv") as "[OPEN CLOS]".
    { apply top_subseteq. }
  
    iDestruct "OPEN" as ([st__e st__o] m) "(>Hmod & [>%CUR__E >%CUR__O] & >Hn & Hauths)".
    iModIntro. iExists _. iSplitL "Hn Hauths".
    { iFrame. }
    simpl.

    iApply (MU__r_mask_weaken with "[-]"); [apply empty_subseteq| ]. 
    iApply (MU__r_wand with "[-Hmod]").
    2: by iApply mu_odd.

    rewrite /eo_corr. iIntros "[%st' (MAP & %ST)] (?&?)".
    iMod ("CLOS" with "[-]") as "_"; [| done].
    rewrite /evenodd_inv_inner. iNext. iFrame.
    destruct (Nat.odd m) eqn:O; try done.
  Qed.

End proof.

Section proof_start.
  Context {even_impl: EvenModel} {odd_impl: OddModel}.

  Let M := @the_fair_model even_impl odd_impl.
  Let LM := @the_model even_impl odd_impl.

  Context (ep: EvenProg) (op: OddProg). 

  Context `{!heapGS Σ LM, !evenoddG Σ}.
  Context {th_preG: threadPreG Σ}. 
  Let Ns := nroot .@ "even_odd".

  (* TODO: move *)
  Lemma frag_free_roles_are_sep: forall fr1 fr2 (DISJ: fr1 ## fr2), 
        frag_free_roles_are (fr1 ∪ fr2) ⊣⊢ frag_free_roles_are fr1 ∗ frag_free_roles_are fr2.
  Proof.
    intros. rewrite /frag_free_roles_are /frag_free_roles_are.    
    rewrite -gset.gset_op.
    rewrite -gset.gset_disj_union; auto. 
    rewrite -own_op. by rewrite -auth_frag_op.
  Qed. 

  Let ρEven: fmrole M := even_role (ρ__e even_impl).
  Let ρOdd: fmrole M := odd_role (ρ__o odd_impl).

  Definition start : val :=
    λ: "l",
      let: "x" := !"l" in
      (Fork ((e_prog ep) "l" "x") ;;
       Fork ((o_prog op) "l" ("x"+#1))).

  Existing Instance even_AME. 
  Existing Instance odd_AME.

  Context (st_res even_at odd_at: nat -> iProp Σ). 
  Context
    (st_res_SR_even: @StateRes _ Nat.even st_res even_at)
    (st_res_SR_odd: @StateRes _ Nat.odd st_res odd_at). 

  Lemma start_spec tid n N1 N2 f (Hf: f > 60) (EVEN: N1 < N2)
    :
    {{{ evenodd_inv st_res n ∗ 
        tid ↦M {[ ρEven := f; ρOdd := f ]} ∗
        even_at N1 ∗ odd_at N2 ∗ frag_free_roles_are ∅ }}}
      start #n @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using All.
    iIntros (Φ) "(#Hinv & Hf & Heven_at & Hodd_at & HFR) HΦ". unfold start.
    rewrite <- (union_empty_l_L ∅). 
    wp_pures.
    wp_bind (Load _).
    iApply wp_atomic.
    iInv Ns as ([st__e st__o] m) "(>Hmod & [>%CUR__E >%CUR__O] & >Hn & Hauths)" "Hclose".
    iIntros "!>". wp_load. iIntros "!>".
    
    (* rewrite /st_res. rewrite if_arg2_comm !if_arg_comm. *)
    (* iDestruct "Hauths" as "[Heven Hodd]". *)
    (* iDestruct (th_agree with "Heven_at Heven") as %<-. *)
    (* iDestruct (th_agree with "Hodd_at Hodd") as %<-. *)
    iDestruct (sr_agree _ _ _ st_res_SR_even with "[$] [$]") as %->.
    iDestruct (sr_agree _ _ _ st_res_SR_odd with "[$] [$]") as %->.
    rewrite -Nat.negb_even in EVEN. destruct (Nat.even m) eqn:E; simpl in EVEN; [| lia].

    iMod ("Hclose" with "[-Hf Heven_at Hodd_at HΦ]") as "_".
    { iIntros "!>". iExists _. iFrame. done. }
    iIntros "!>". wp_pures. wp_bind (Fork _).
    iApply (wp_role_fork _ tid _ _ _ {[ρOdd := _]} {[ρEven := _]}
             with "[Hf ] [Heven_at]"). 
    { apply map_disjoint_dom. rewrite !dom_singleton.
      destruct (Nat.even m); set_solver. }
    { intros Hempty%map_positive_l. set_solver. }
    { rewrite has_fuels_gt_1; last solve_fuel_positive.
      rewrite !fmap_insert fmap_empty //.
      iApply has_fuels_proper; [..| by iFrame]; auto.
      rewrite !insert_union_singleton_l map_union_empty.
      rewrite map_union_comm; [reflexivity| ].
      rewrite map_disjoint_dom. set_solver. }
    { iIntros (tid') "!> Hf".
      iApply (even_spec_use _ _ st_res_SR_even with "[-]").
      2: { iFrame "#∗". }
      { lia. }
      intuition. }

    iIntros "!> Hf".
    iIntros "!>".
    wp_pures.
    iApply (wp_role_fork _ tid _ _ _ ∅ _ with "[Hf] [Hodd_at]").
    { apply map_disjoint_dom. apply map_disjoint_dom. apply map_disjoint_empty_l. }
    2: { rewrite has_fuels_gt_1; last solve_fuel_positive.
         rewrite !fmap_insert fmap_empty //.
         rewrite insert_union_singleton_l. 
         rewrite map_union_comm; [done|].
         apply map_disjoint_dom. set_solver. }
    { rewrite map_empty_union. set_solver. }
    { iIntros (tid') "!> Hf".
      wp_pures.
      replace (Z.of_nat m + 1)%Z with (Z.of_nat (m + 1)) by lia.
      iApply (odd_spec_use _ _ st_res_SR_odd with "[-]").
      2: { rewrite -Nat.negb_even E. iFrame "#∗". }
      { lia. }
      intuition. }

    iIntros "!> Hf". by iApply "HΦ".
  Qed. 

End proof_start.
