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

Import derived_laws_later.bi.

Open Scope nat.

Definition go_impl (b: bool): val :=
  rec: "go_impl" "n" "b" :=
    (if: CAS "b" #(b) #(negb b) then "n" <- !"n" - #1 else #());;
    if: #0 < !"n" then "go_impl" "n" "b" else #().

Definition yes_go : val := go_impl true.

Definition yes : val :=
  λ: "N" "b", let: "n" := Alloc "N" in yes_go "n" "b".

Definition no_go : val := go_impl false .

Definition no : val :=
  λ: "N" "b", let: "n" := Alloc "N" in no_go "n" "b".

Definition start : val :=
  λ: "N", let: "b" := Alloc #true in (Fork (yes "N" "b") ;; Fork (no "N" "b")).

  
Section proof.
  
  (* Context `(ENV_AM: EnvironmentAM env_AM). *)
  (* Context {INDEP: models_independent env_AM yn_AM}. *)

  (* Let M := the_fair_model ENV_AM. *)
  (* Let LM := the_model ENV_AM.  *)
  (* Let PM := @FM env_AM.  *)

  (* Context `{!heapGS Σ LM, !yesnoG Σ, SplitGS Σ env_AM yn_AM}. *)

  (* Let yn_role (ρ: YN): amRole PM := inr ρ. *)

  Context `{LM: LiveModel heap_lang M}.
  Context `{!heapGS Σ LM, !yesnoG Σ}. 

  Lemma insert_empty_fmap_helper `{Countable K} {A: Type} (k: K) (a: A) (f: A -> A):
    (<[ k := a ]> ∅: gmap K A) = {[ k := a ]} ∪ (f <$> ∅).
  Proof.
    rewrite insert_union_singleton_l. f_equiv. done.
  Qed. 

  Lemma yes_go_spec_vs Ns tid n b (N: nat) f (Hf: f > 40) ρ
    (FLM: lm_flm LM >= 60):
    {{{ yes_vs b Ns ρ ∗
        tid ↦M {[ ρ := f ]} ∗ n ↦ #N ∗ ⌜N > 0⌝%nat ∗
        yes_at N }}}
      yes_go #n #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using.
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ) "(#VS & Hf & HnN & %HN & Hyes) Hk". unfold yes_go, go_impl.
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    iApply wp_atomic.

    iPoseProof "VS" as "-#V". 
    iMod "V" as "(%m & %B & ((>%Hnever & >Bb & Hauths) & V))".
    iDestruct (bi.and_elim_l with "V") as "MU_y".       

    simpl. 

    rewrite if_arg2_comm. iDestruct "Hauths" as "[Hay Han]". 
    rewrite !if_arg_comm. iMod "Hay". iMod "Han".
    iDestruct (yes_agree with "Hyes Hay") as %Heq.
    
    destruct B. 
    - destruct (decide (m= 0)) as [->|Nneq]; first lia.
      iModIntro.
      subst N.

      iApply sswp_MU_wp; [done| ].
      iApply (wp_cmpxchg_suc with "[$]"); try done.
      iIntros "!> Hb". 

      iApply (MU_wand with "[-Hf MU_y]").
      2: { iSpecialize ("MU_y" with "[] [Hf]").
           { iPureIntro. lia. }
           2: { by iFrame. }
           iSplitL. 
           { erewrite insert_empty_fmap_helper. by iFrame. }
           iPureIntro. set_solver. }

      iIntros "[Hf CLOS]".

      iMod (yes_update (m - 1) with "[$]") as "[Hay Hyes]".
      wp_pures.
      iModIntro. 
      iMod ("CLOS" with "[Hb Hay Han]") as "_".
      { iNext. iFrame. iPureIntro. by intros [=]. }
      iModIntro.

      rewrite map_union_empty. 
      simpl in *.
      wp_load. wp_store. wp_load. wp_pure _.
      destruct m; [lia| ].
      destruct m. 
      + rewrite bool_decide_eq_false_2; [| lia]. 
        iApply wp_atomic.

        iPoseProof "VS" as "-#V".
        clear Hnever. 
        iMod "V" as "(%m & %B & ((>%Hnever & >Bb & Hauths) & V))".
        iDestruct (bi.and_elim_r with "V") as "DEALLOC".

        rewrite if_arg2_comm. iDestruct "Hauths" as "[Hay Han]". 
        rewrite !if_arg_comm. iMod "Hay". iMod "Han".
        iDestruct (yes_agree with "Hyes Hay") as %Heq.
        
        iAssert (⌜ m = 0 /\ B = true \/ m = 1 /\ B = false ⌝)%I as %EQ.
        { iPureIntro. destruct B; [tauto| ]. 
          right. split; [| done].
          destruct m as [|[|]]; try lia. done. }
        iModIntro.

        iApply wp_pre_step. wp_pure _. 
        iApply fupd_mask_intro; [done|].
        iIntros "Hclose'".

        iSpecialize ("DEALLOC" with "[//] [Hf]").
        { iSplitL.
          { erewrite insert_empty_fmap_helper. by iFrame. }
          iPureIntro. rewrite dom_fmap. set_solver. }
        Unshelve. 2: exact id. 
 
        iApply (pre_step_mono with "[-DEALLOC] [$]").
        iIntros "[MAP CORR]".
        iMod ("CORR" with "[Bb Hay Han]").
        { iNext. iFrame. iSplit; [done| ].
          destruct B; iFrame. }
        by iApply "Hk". 
      + rewrite bool_decide_eq_true_2 //; last lia.
        wp_pure _.
        iApply ("Hg" with "[] [Hf Hyes HnN] [$]"); last first.
        { iFrame "∗#". iSplit; last by iPureIntro; lia.
          by rewrite Nat2Z.inj_sub; [| lia]. }
        iPureIntro; lia.
    - have HM: m> 0 by lia.
      iModIntro.

      iApply sswp_MU_wp; [done| ].
      iApply (wp_cmpxchg_fail with "[$]"); try done.
      iIntros "!> Hb".
 
      iApply (MU_wand with "[-MU_y Hf]").
      2: { iSpecialize ("MU_y" with "[] [Hf]").
           { iPureIntro. lia. }
           2: by iFrame.
           iSplitL.
           { erewrite insert_empty_fmap_helper; by iFrame. }
           iPureIntro. set_solver. }

      iIntros "[Hf CLOS]".
      wp_pures. iModIntro.
      iMod ("CLOS" with "[Hb Hay Han]").
      { iNext. iFrame. done. }
      iModIntro.
      rewrite map_union_empty. 
      simpl. wp_load. wp_pure _. rewrite bool_decide_eq_true_2; last lia.
      wp_pure _.
      iApply ("Hg" with "[] [Hyes HnN Hf] [$]"); last first.
      { iFrame "∗#". iPureIntro; lia. }
      iPureIntro; lia.
  Time Qed.
  
  Lemma no_go_spec_vs Ns tid n b (N: nat) f (Hf: f > 40) ρ
    (FLM: lm_flm LM >= 60):
    {{{ no_vs b Ns ρ ∗
        tid ↦M {[ ρ := f ]} ∗ n ↦ #N ∗ ⌜N > 0⌝%nat ∗
        no_at N }}}
      no_go #n #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using.
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ) "(#VS & Hf & HnN & %HN & HNo) Hk". unfold no_go, go_impl.
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    iApply wp_atomic.

    iPoseProof "VS" as "-#V". 
    iMod "V" as "(%m & %B & ((>%Hnever & >Bb & Hauths) & V))".
    iDestruct (bi.and_elim_l with "V") as "MU_no".

    simpl. 

    rewrite if_arg2_comm. iDestruct "Hauths" as "[Hay Han]". 
    rewrite !if_arg_comm. iMod "Hay". iMod "Han".
    iDestruct (no_agree with "HNo Han") as %Heq.
    
    destruct B; revgoals.
    - destruct (decide (m= 0)) as [->|Nneq]; [lia| ]. 
      iModIntro.
      subst N.

      iApply sswp_MU_wp; [done| ].
      iApply (wp_cmpxchg_suc with "[$]"); try done.
      iIntros "!> Hb". 

      iApply (MU_wand with "[-Hf MU_no]").
      2: { iSpecialize ("MU_no" with "[] [Hf]").
           { iPureIntro. lia. }
           2: { by iFrame. }
           iSplitL. 
           { erewrite insert_empty_fmap_helper. by iFrame. }
           iPureIntro. set_solver. }

      iIntros "[Hf CLOS]".

      iMod (no_update (m - 1) with "[$]") as "[Han Hno]".
      wp_pures.
      iModIntro. 
      iMod ("CLOS" with "[Hb Hay Han]") as "_".
      { iNext. iFrame. iPureIntro. by intros [=]. }
      iModIntro.

      rewrite map_union_empty. 
      simpl in *. wp_load. wp_store. wp_load. wp_pure _.
      destruct m; [lia| ]. 
      destruct m. 
      + rewrite bool_decide_eq_false_2; [| lia]. 
        iApply wp_atomic.

        iPoseProof "VS" as "-#V".
        clear Hnever. 
        iMod "V" as "(%m & %B & ((>%Hnever & >Bb & Hauths) & V))".
        iDestruct (bi.and_elim_r with "V") as "DEALLOC".

        rewrite if_arg2_comm. iDestruct "Hauths" as "[Hay Han]". 
        rewrite !if_arg_comm. iMod "Hay". iMod "Han".
        iDestruct (no_agree with "Hno Han") as %Heq.
        
        iAssert (⌜ m = 0 /\ B = true ⌝)%I as %EQ.
        { iPureIntro. destruct B; [tauto| ]. set_solver. }
        iModIntro. 
        
        iApply wp_pre_step. wp_pure _. 
        iApply fupd_mask_intro; [done|].
        iIntros "Hclose'".

        destruct EQ as [-> ->]. 
        iSpecialize ("DEALLOC" with "[//] [Hf]").
        { iSplitL.
          { erewrite insert_empty_fmap_helper. by iFrame. }
          iPureIntro. rewrite dom_fmap. set_solver. }
        Unshelve. 2: exact id. 
 
        iApply (pre_step_mono with "[-DEALLOC] [$]").
        iIntros "[MAP CORR]".
        iMod ("CORR" with "[Bb Hay Han]").
        { iNext. iFrame. done. }
        by iApply "Hk". 
      + rewrite bool_decide_eq_true_2 //; [| lia].
        wp_pure _.
        iApply ("Hg" with "[] [Hf Hno HnN] [$]"); last first.
        { iFrame "∗#". iSplit; last by iPureIntro; lia.
          by rewrite Nat2Z.inj_sub; [| lia]. }
        iPureIntro; lia.
    - have HM: m> 0 by lia.
      iModIntro.

      iApply sswp_MU_wp; [done| ].
      iApply (wp_cmpxchg_fail with "[$]"); try done.
      iIntros "!> Hb".
 
      iApply (MU_wand with "[-MU_no Hf]").
      2: { iSpecialize ("MU_no" with "[] [Hf]").
           { iPureIntro. lia. }
           2: by iFrame.
           iSplitL.
           { erewrite insert_empty_fmap_helper; by iFrame. }
           iPureIntro. set_solver. }

      iIntros "[Hf CLOS]".
      wp_pures. iModIntro.
      iMod ("CLOS" with "[Hb Hay Han]").
      { iNext. iFrame. done. }
      iModIntro.
      rewrite map_union_empty. 
      simpl. wp_load. wp_pure _. rewrite bool_decide_eq_true_2; last lia.
      wp_pure _.
      iApply ("Hg" with "[] [HNo HnN Hf] [$]"); last first.
      { iFrame "∗#". iPureIntro; lia. }
      iPureIntro; lia.
  Qed.  

  Lemma yes_spec tid b (N: nat) f (Hf: f > 50) Ns ρ
    (FLM: lm_flm LM >= 60):
    {{{
          (* split_inv Ns__split ∗ yesno_inv ENV_AM b ∗ *)
         yes_vs b Ns ρ ∗    
        tid ↦M {[ ρ := f ]} ∗ ⌜N > 0⌝ ∗ yes_at N }}}
      yes #N #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using.
    iIntros (Φ) "(#VS & Hf & %HN & Hyes) Hk". unfold yes.
    wp_pures.
    wp_bind (Alloc _).
    iApply (wp_step_fuel with "[Hf]").
    { apply map_non_empty_singleton. }
    { rewrite has_fuels_gt_1; last by solve_fuel_positive.
      rewrite fmap_insert fmap_empty. done. }
    iApply wp_alloc. iNext. iIntros (n) "HnN _ Hf". wp_pures. iModIntro. wp_pures.
    iApply (yes_go_spec_vs with "[-Hk]"); try iFrame; auto.
    lia.
  Qed.

  Lemma no_spec tid b (N: nat) f (Hf: f > 50) Ns ρ
    (FLM: lm_flm LM >= 60):
    {{{
        (* split_inv Ns__split ∗ yesno_inv ENV_AM b ∗ *)
        no_vs b Ns ρ ∗
        tid ↦M {[ ρ := f ]} ∗ ⌜N > 0⌝ ∗ no_at N }}}
      no #N #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using.
    iIntros (Φ) "(#VS & Hf & %HN & Hno) Hk". unfold no.
    wp_pures.
    wp_bind (Alloc _).
    iApply (wp_step_fuel with "[Hf]").
    { apply map_non_empty_singleton. }
    { rewrite has_fuels_gt_1; last by solve_fuel_positive.
      rewrite fmap_insert fmap_empty. done. }
    iApply wp_alloc. iNext. iIntros (n) "HnN _ Hf". wp_pures. iModIntro. wp_pures.
    iApply (no_go_spec_vs with "[-Hk]"); try iFrame; auto.
    lia.
  Qed. 

End proof.

Section proof_start.
  (* Context `(ENV_AM: EnvironmentAM env_AM). *)
  (* Context {INDEP: models_independent env_AM yn_AM}. *)

  (* Let M := the_fair_model ENV_AM. *)
  (* Let LM := the_model ENV_AM.  *)
  (* Let PM := @FM env_AM.  *)

  (* Context `{!heapGS Σ LM, !yesnoPreG Σ, SplitGS Σ env_AM yn_AM}. *)
  (* Let Ns := nroot .@ "yes_no". *)

  (* Let yn_role (ρ: YN): amRole PM := inr ρ.     *)

  Context `{LM: LiveModel heap_lang M}.
  Context `{!heapGS Σ LM, !yesnoPreG Σ}. 

  Lemma start_spec tid (N: nat) f (Hf: f > 60) Ns ρ1 ρ2
    (NEQ: ρ1 ≠ ρ2)
    (FLM: lm_flm LM >= 60):
    {{{
        (* split_inv Ns__split ∗ *)

        (* frag_right_st_is (N, true) ∗ *)
        (∀ l, l ↦ #true ==∗ ∃ (_: yesnoG Σ),
                yes_vs l Ns ρ1 ∗ no_vs l Ns ρ2 ∗ yes_at N ∗ no_at N) ∗
        (* frag_free_roles_are ∅ ∗ *)
        tid ↦M {[  ρ1 := f; ρ2 := f ]} ∗ ⌜N > 0⌝ }}}
      start #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using All.
    (* iIntros (Φ) "[#SPLIT [Hst [HFR [Hf %HN]]]] Hkont". *)
    iIntros (Φ) "(VS & Hf & %HN) Hkont". 
    unfold start.
    wp_pures. wp_bind (Alloc _).
    iApply (wp_step_fuel with "[Hf]").
    2: { rewrite has_fuels_gt_1; last by solve_fuel_positive.
         rewrite !fmap_insert fmap_empty. done. }
    { rewrite insert_union_singleton_l.
      intros ?%map_positive_l. set_solver. }
    iApply wp_alloc. iNext. iIntros (l) "HnN _ Hf". wp_pures. iModIntro. wp_pures.

    iMod ("VS" with "[$]") as (yG) "(VS1 & VS2 & Y & N)". 
    
    (* (* Allocate the invariant. *) *)
    (* iMod (own_alloc (●E N  ⋅ ◯E N))%nat as (γ_yes_at) "[Hyes_at_auth Hyes_at]". *)
    (* { apply auth_both_valid_2; eauto. by compute. } *)
    (* iMod (own_alloc (●E N  ⋅ ◯E N))%nat as (γ_no_at) "[Hno_at_auth Hno_at]". *)
    (* { apply auth_both_valid_2; eauto. by compute. } *)
    (* pose (the_names := {| *)
    (*  yes_name := γ_yes_at; *)
    (*  no_name := γ_no_at; *)
    (* |}). *)
    (* iApply fupd_wp. *)
    (* iMod (inv_alloc Ns _ (yesno_inv_inner ENV_AM l) with "[-Hkont Hf Hyes_at Hno_at]") as "#Hinv". *)
    (* { iNext. unfold yesno_inv_inner. iExists N, true. iFrame. done. } *)
    (* iModIntro. *)

    wp_bind (Fork _).
    iApply (wp_role_fork _ tid _ _ _ {[ρ2 := _]} {[ρ1 := _]}
             with "[Hf] [VS1 Y]").
    { apply map_disjoint_dom. rewrite !dom_singleton. set_solver. }
    { intros Hempty%map_positive_l. set_solver. }
    { rewrite has_fuels_gt_1; last solve_fuel_positive.
      rewrite !fmap_insert fmap_empty //.
      rewrite insert_union_singleton_l.
      rewrite map_union_comm; [done|].
      apply map_disjoint_dom. set_solver. }
    { iIntros (tid') "!> Hf". iApply (yes_spec with "[-]"); last first.
      + by eauto.
      + iFrame "#∗". iPureIntro. lia.
      + lia.
      + lia. }
    iIntros "!> Hf !>". wp_pures.
    iApply (wp_role_fork _ tid _ _ _ ∅ {[ρ2 := _]} with "[Hf] [VS2 N] [Hkont]").
    { apply map_disjoint_dom. rewrite !dom_singleton. set_solver. }
    { rewrite map_union_comm.
      - intros Hempty%map_positive_l. set_solver.
      - apply map_disjoint_dom. rewrite dom_singleton. set_solver. }
    { rewrite has_fuels_gt_1; last solve_fuel_positive.
      rewrite !fmap_insert fmap_empty //.
      rewrite insert_union_singleton_l.
      rewrite map_union_comm; [done|].
      apply map_disjoint_dom. set_solver. }
    { iIntros (tid') "!> Hf". iApply (no_spec with "[-]"); last first.
      + by eauto.
      + by iFrame "#∗".
      + lia. 
      + lia. }
    iNext. iIntros "Hf". by iApply "Hkont".
  Qed.

End proof_start.
