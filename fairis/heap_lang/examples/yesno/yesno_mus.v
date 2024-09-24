From stdpp Require Import decidable.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination fuel sswp_rules resources action_model utils.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode notation iris_inst.
From trillium.fairness.heap_lang.examples Require Import env_am split_model mu_role.
From trillium.fairness.heap_lang.examples.yesno Require Import yesno_model yesno_threads.


Section FullModel.
  Context `(ENV_AM: EnvironmentAM env_AM).

  Definition FM := ProdAM env_AM yn_AM.
  
  Definition the_fair_model: FairModel := AM2FM FM _. 
  
  Definition the_model: LiveModel heap_lang the_fair_model :=
    {| lm_flm := 61%nat; |}.
  
  Definition yesnoΣ : gFunctors :=
    #[ heapΣ the_fair_model; GFunctor (excl_authR natO) ; GFunctor (excl_authR boolO) ].

  Global Instance subG_yesnoΣ {Σ} : subG yesnoΣ Σ → yesnoPreG Σ.
  Proof. solve_inG. Qed.

End FullModel.


Section MUs.

  Context `(ENV_AM: EnvironmentAM env_AM).
  Context {INDEP: models_independent env_AM yn_AM}.

  Let M := the_fair_model ENV_AM.
  Let LM := the_model ENV_AM. 
  Let PM := @FM env_AM. 

  Context `{!heapGS Σ LM, !yesnoG Σ, SplitGS Σ env_AM yn_AM}.

  Let Ns := nroot .@ "yes_no".

  Lemma they_finished_update γ (n m P: bool) :
    own γ (●E n) ∗ own γ (◯E m) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.

  Definition yesno_inv_inner b : iProp Σ :=
    ∃ n B,
      yn_corr b n B ∗
      frag_right_st_is (n, B). 

  Let yn_role (ρ: YN): amRole PM := inr ρ.

  Lemma mu_yes n (b: bool) (ns: namespace)
    (NB: if b then n > 0 else n > 1):
    inv ns (split_inv_inner) ⊢ frag_right_st_is (n, b) -∗ 
      MU__r (yn_role Y) (↑ ns) (frag_right_st_is $ if b then (n, false) else (n, false)).
  Proof using INDEP.
    rewrite /MU__r. iIntros "#INV ST" (tid f' R) "[MAP %DISJ__R]".

    enough (exists a, amTrans yn_AM (n, b) (a, Some Y) (if b then (n, false) else (n, false))) as (a & TRANS). 
    { iApply (MU_inv with "[$]"); [done| ].
      (* TODO: avoid unfolding of MU *)
      rewrite /split_inv_inner. simpl. iIntros ">(%S & FRAG & PROD)". destruct S.
      simpl. iDestruct (right_agree with "[$] [$]") as %->.

      iMod (update_right ((if b then (n, false) else (n, false)): amSt yn_AM) with "[$] [$]") as "[PROD ST]".
      iApply (MU_wand with "[ST PROD]").
      2: { iApply (model_step_MU with "[$] [MAP]").
           1, 4: by eauto.
           { simpl. eapply am_fmtrans_action. eexists. 
             eapply pt_inner2; eauto.
             intros ?. edestruct INDEP; eauto.
             eapply action_of_step; eauto. }
           simpl. setoid_rewrite @prod_indep_live_roles; eauto.
           apply union_mono; [done| ]. apply set_map_mono; [done| ].
           erewrite !yn_AM_live_roles'.
           simpl. destruct b, n as [|[|]]; set_solver. }
      iIntros "(MAP & FRAG)".
      iFrame. }
    Unshelve. 2: by apply _.

    exists yn_act. simpl. destruct b; by constructor. 
  Qed.

  Lemma mu_no n (b: bool) (ns: namespace)
    (NB: if b then n > 0 else n > 0)
    :
    inv ns (split_inv_inner) ⊢ frag_right_st_is (n, b) -∗ 
      MU__r (yn_role No) (↑ ns) (frag_right_st_is $ if b then (n, true) else (n - 1, true)).
  Proof using INDEP.
    rewrite /MU__r. iIntros "#INV ST" (tid f' R) "[MAP %DISJ__R]".

    enough (exists a, amTrans yn_AM (n, b) (a, Some No) (if b then (n, true) else (n - 1, true))) as (a & TRANS). 
    { iApply (MU_inv with "[$]"); [done| ].
      (* TODO: avoid unfolding of MU *)
      rewrite /split_inv_inner. simpl. iIntros ">(%S & FRAG & PROD)". destruct S.
      simpl. iDestruct (right_agree with "[$] [$]") as %->.

      iMod (update_right ((if b then (n, true) else (n - 1, true)): amSt yn_AM) with "[$] [$]") as "[PROD ST]".
      iApply (MU_wand with "[ST PROD]").
      2: { iApply (model_step_MU with "[$] [MAP]").
           1, 4: by eauto.
           { simpl. eapply am_fmtrans_action. eexists. 
             eapply pt_inner2; eauto.
             intros ?. edestruct INDEP; eauto.
             eapply action_of_step; eauto. }
           simpl. setoid_rewrite @prod_indep_live_roles; eauto.
           apply union_mono; [done| ]. apply set_map_mono; [done| ].
           erewrite !yn_AM_live_roles'.
           simpl. destruct b, n as [|[|]]; simpl; try set_solver.
           destruct n; done. }
      iIntros "(MAP & FRAG)".
      iFrame. }
    Unshelve. 2: by apply _.

    assert (n > 0) by (by destruct b). destruct n; [lia| ].
    simpl. rewrite Nat.sub_0_r. 
    exists yn_act. simpl. destruct b; by constructor. 
  Qed.

  Lemma dealloc_yes n (b: bool) (ns: namespace)
    (NB: n = 0 /\ b = true \/ n = 1 /\ b = false):
    inv ns (split_inv_inner) ⊢ frag_right_st_is (n, b) -∗
        MU__drop (yn_role Y) (↑ ns) (frag_right_st_is (n, b)). 
  Proof using INDEP. 
    rewrite /MU__drop. iIntros "#INV ST" (tid f' R) "[MAP %DISJ__R]".

    iApply (pre_step_inv with "[$]"); [done| ].
    rewrite /split_inv_inner. simpl. iIntros "(%S & FRAG & PROD)". destruct S.
    iApply fupd_pre_step. iMod "FRAG". iMod "PROD". iModIntro. 
    simpl. iDestruct (right_agree with "[$] [$]") as %->.

    iMod (has_fuels_dealloc _ _ _ (yn_role Y: fmrole M) with "FRAG MAP") as "[FRAG MAP]".
    { simpl. rewrite prod_indep_live_roles. apply not_elem_of_union.
      split; [set_solver| ].
      intros IN%elem_of_map_inj_gset; [| by apply _].
      rewrite yn_AM_live_roles in IN.
      destruct NB as [[-> ->]|[-> ->]]; set_solver. }

    iModIntro. rewrite -insert_union_singleton_l delete_insert_dom.
    2: set_solver.
    by iFrame.
  Qed. 

  Lemma dealloc_no n (b: bool) (ns: namespace)
    (NB: n = 0):
    inv ns (split_inv_inner) ⊢ frag_right_st_is (n, b) -∗
        MU__drop (yn_role No) (↑ ns) (frag_right_st_is (n, b)). 
  Proof using INDEP. 
    rewrite /MU__drop. iIntros "#INV ST" (tid f' R) "[MAP %DISJ__R]".

    iApply (pre_step_inv with "[$]"); [done| ].
    rewrite /split_inv_inner. simpl. iIntros "(%S & FRAG & PROD)". destruct S.
    iApply fupd_pre_step. iMod "FRAG". iMod "PROD". iModIntro. 
    simpl. iDestruct (right_agree with "[$] [$]") as %->.

    iMod (has_fuels_dealloc _ _ _ (yn_role No: fmrole M) with "FRAG MAP") as "[FRAG MAP]".
    { simpl. rewrite prod_indep_live_roles. apply not_elem_of_union.
      split; [set_solver| ].
      intros IN%elem_of_map_inj_gset; [| by apply _].
      rewrite yn_AM_live_roles in IN.
      subst. destruct b; set_solver. }

    iModIntro. rewrite -insert_union_singleton_l delete_insert_dom.
    2: set_solver.
    by iFrame.
  Qed. 

  Definition yesno_inv b := inv Ns (yesno_inv_inner b).

  Definition Ns__split := nroot .@ "split".

  Lemma yes_vs_from_invs l:
    yesno_inv l ∗ split_inv Ns__split  ⊢ yes_vs l Ns (yn_role Y).
  Proof using INDEP.
    rewrite /yes_vs. iIntros "#[INV1 INV2]". iModIntro.
    iMod (inv_acc with "INV1") as "[OPEN CLOS]".
    { apply top_subseteq. }
    
    rewrite {1}/yesno_inv_inner. rewrite {1}/yn_corr.  
    iDestruct "OPEN" as (n b) "((>%NEQ & >LOC & AUTHS) & >RIGHT)".
    iModIntro.
    iExists _, _. iSplitL "LOC AUTHS".
    { by iFrame. }

    iSplit. 
    - iIntros "%B". 
      iApply (MU__r_mask_weaken (↑ Ns__split) with "[-]").
      { assert (Ns__split ## Ns) by solve_ndisj. set_solver. }
      iApply (MU__r_wand with "[-RIGHT]").
      2: { by iApply (mu_yes with "[$] [$]"). }
      iIntros "RIGHT CORR".
      iMod ("CLOS" with "[-]"); [| done].
      rewrite /yesno_inv_inner. iNext.
      (* some redundancy to ease subsequent "No" proofs *)
      iExists (if b then n else n), (if b then false else false).
      destruct b; iFrame.
    - iIntros "%NB". 
      iApply (MU__drop_mask_weaken (↑ Ns__split) with "[-]").
      { assert (Ns__split ## Ns) by solve_ndisj. set_solver. }
      iApply (MU__drop_wand with "[-RIGHT]"). 
      2: { by iApply (dealloc_yes with "[$]"). }
      iIntros "RIGHT CORR".
      iMod ("CLOS" with "[-]"); [| done].
      rewrite /yesno_inv_inner. iNext.
      iFrame. 
  Qed.

  Lemma no_vs_from_invs l:
    yesno_inv l ∗ split_inv Ns__split  ⊢ no_vs l Ns (yn_role No).
  Proof using INDEP.
    rewrite /no_vs. iIntros "#[INV1 INV2]". iModIntro.
    iMod (inv_acc with "INV1") as "[OPEN CLOS]".
    { apply top_subseteq. }
    
    rewrite {1}/yesno_inv_inner. rewrite {1}/yn_corr.  
    iDestruct "OPEN" as (n b) "((>%NEQ & >LOC & AUTHS) & >RIGHT)".
    iModIntro.
    iExists _, _. iSplitL "LOC AUTHS".
    { by iFrame. }

    iSplit. 
    - iIntros "%B". 
      iApply (MU__r_mask_weaken (↑ Ns__split) with "[-]").
      { assert (Ns__split ## Ns) by solve_ndisj. set_solver. }
      iApply (MU__r_wand with "[-RIGHT]").
      2: { by iApply (mu_no with "[$] [$]"). }
      iIntros "RIGHT CORR".
      iMod ("CLOS" with "[-]"); [| done].
      rewrite /yesno_inv_inner. iNext.
      iExists (if b then n else n - 1), true.
      destruct b; iFrame.
    - iIntros "%NB". 
      iApply (MU__drop_mask_weaken (↑ Ns__split) with "[-]").
      { assert (Ns__split ## Ns) by solve_ndisj. set_solver. }
      iApply (MU__drop_wand with "[-RIGHT]"). 
      2: { by iApply (dealloc_no with "[$]"). }
      iIntros "RIGHT CORR".
      iMod ("CLOS" with "[-]"); [| done].
      rewrite /yesno_inv_inner. iNext.
      iFrame. 
  Qed.

End MUs.
