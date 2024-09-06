From stdpp Require Import decidable.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination utils action_model resources.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation sswp_rules iris_inst.
From trillium.fairness.heap_lang.examples Require Import env_am split_model.
From trillium.fairness.heap_lang.examples.even_odd Require Import interface thread_progs model_updates.
Import derived_laws_later.bi.

Open Scope nat.

Set Default Proof Using "Type".

(** TODO: 
    At this point all gFunctors requirements are handled by other parts of proof.
    Should we keep these empty classes just for the sake of uniformness? *)
Class evenoddPreG (Σ: gFunctors) := {
}.
Class evenoddG (Σ: gFunctors) := EvenoddG {
  eoPreG :> evenoddPreG Σ;
 }.



Section proof_start.
  Context {even_impl: EvenModel} {odd_impl: OddModel}.
  Context `(ENV_AM: EnvironmentAM env_AM).

  Let PM := @prod_model even_impl odd_impl.
  Context {prod_AM_act_dec: ∀ a, Decision (is_action_of PM a)}.

  Let M := @the_fair_model even_impl odd_impl prod_AM_act_dec _ ENV_AM.
  Let LM := @the_model even_impl odd_impl prod_AM_act_dec _ ENV_AM.

  Hypothesis PROD_ENV_INDEP: forall a, is_action_of PM a -> is_action_of env_AM a -> False.

  Context `{hGS: !heapGS Σ LM, !evenoddG Σ, SplitGS Σ PM env_AM}.

  Context (st_res even_at odd_at: nat -> iProp Σ). 
  Context
    (st_res_SR_even: @StateRes _ Nat.even st_res even_at)
    (st_res_SR_odd: @StateRes _ Nat.odd st_res odd_at). 

  Definition Ns__eo := nroot .@ "even_odd".
  Definition Ns__split := nroot .@ "split".
  Definition evenodd_inv n := inv Ns__eo (evenodd_inv_inner ENV_AM st_res n).

  Let ρEven: fmrole M := inl $ even_role (ρ__e even_impl).
  Let ρOdd: fmrole M := inl $ odd_role (ρ__o odd_impl).

  Definition even_odd_spec (prog: val): Prop :=
    forall tid n N1 N2 f (Hf: f > 60) (EVEN: N1 < N2), 
    {{{ split_inv Ns__split ∗ evenodd_inv n ∗ 
        tid ↦M {[ ρEven := f; ρOdd := f ]} ∗
        even_at N1 ∗ odd_at N2 ∗ frag_free_roles_are ∅ }}}
      prog #n @ tid
    {{{ RET #(); tid ↦M ∅ }}}.

  Context (ep: EvenProg) (op: OddProg). 

  Definition start : val :=
    λ: "l",
      let: "x" := !"l" in
      (Fork ((e_prog ep) "l" "x") ;;
       Fork ((o_prog op) "l" ("x"+#1))).

  Existing Instance even_AME. 
  Existing Instance odd_AME.

  Lemma start_spec: even_odd_spec start. 
  Proof using All.
    rewrite /even_odd_spec. iIntros (tid n N1 N2 f Hf EVEN). 
    iIntros (Φ) "(#SPLIT & #Hinv & Hf & Heven_at & Hodd_at & HFR) HΦ". unfold start.
    rewrite <- (union_empty_l_L ∅). 
    wp_pures.
    wp_bind (Load _).
    iApply wp_atomic.
    iInv Ns__eo as (m) "(>CUR & >Hn & Hauths)" "Hclose".
    iIntros "!>". wp_load. iIntros "!>".
    
    iDestruct (sr_agree _ _ _ st_res_SR_even with "[$] [$]") as %->.
    iDestruct (sr_agree _ _ _ st_res_SR_odd with "[$] [$]") as %->.
    rewrite -Nat.negb_even in EVEN. destruct (Nat.even m) eqn:E; simpl in EVEN; [| lia].

    iMod ("Hclose" with "[-Hf Heven_at Hodd_at HΦ]") as "_".
    { iIntros "!>". iExists _. iFrame. }
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
      iApply (@e_spec ep M _ _ _ _ _ st_res_SR_even
               with "[$Hf $Heven_at]"); [lia| simpl; lia | ..].
      2: { by iIntros "!> ?". }
      iApply even_vs; eauto. solve_ndisj. }

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
      rewrite -Nat.negb_even E. 
      iApply (@o_spec op M _ _ _ _ _ st_res_SR_odd
               with "[$Hf $Hodd_at]"); [lia| simpl; lia | ..].
      2: { by iIntros "!> ?". }
      iApply odd_vs; eauto. solve_ndisj. }

    iIntros "!> Hf". by iApply "HΦ". 
  Qed. 

End proof_start.


Section short_prog.
  Context {even_impl: EvenModel} {odd_impl: OddModel}.
  Context `(ENV_AM: EnvironmentAM env_AM).

  Let PM := @prod_model even_impl odd_impl.
  Context {prod_AM_act_dec: ∀ a, Decision (is_action_of PM a)}. 

  Let M := @the_fair_model even_impl odd_impl prod_AM_act_dec _ ENV_AM.
  Let LM := @the_model even_impl odd_impl prod_AM_act_dec _ ENV_AM.

  Hypothesis PROD_ENV_INDEP: forall a, is_action_of PM a -> is_action_of env_AM a -> False.

  Context `{hGS: !heapGS Σ LM, !evenoddG Σ, SplitGS Σ PM env_AM}.

  Context (st_res even_at odd_at: nat -> iProp Σ). 
  Context
    (st_res_SR_even: @StateRes _ Nat.even st_res even_at)
    (st_res_SR_odd: @StateRes _ Nat.odd st_res odd_at). 

  Definition short: val :=
    rec: "short" "l" :=
      "l" <- !"l" + #1 ;;
      "short" "l"
  .
  
  Let ρEven: fmrole M := inl $ even_role (ρ__e even_impl).
  Let ρOdd: fmrole M := inl $ odd_role (ρ__o odd_impl).

  Lemma sub_helper: forall y, y >= 1 -> S (y - 1) = y.
  Proof. lia. Qed. 

  Lemma add_helper: forall y d, y >= d -> (y - d) + d = y.
  Proof. lia. Qed.

  (* Definition Ns := nroot .@ "eo". *)
  (* Definition split_inv: iProp Σ := inv Ns (split_inv_inner (hGS := hGS)). *)

  Lemma short_spec_impl tid n N1 N2 
    (ev := Nat.ltb N1 N2)
    (d := 10)
    (b := 40)
    f1 f2 (Hf1: f1 > b) (Hf2: f2 > b)
    :
    {{{ split_inv Ns__split ∗ evenodd_inv ENV_AM st_res n ∗ 
        tid ↦M {[ ρEven := f1 + (if ev then 0 else d); ρOdd := f2 + (if ev then d else 0) ]} ∗
        even_at N1 ∗ odd_at N2 ∗ frag_free_roles_are ∅
    }}}
      short #n @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using All.
    subst ev. 
    iLöb as "Hg" forall (N1 N2 f1 Hf1 f2 Hf2).
    iIntros (Φ) "(#SPLIT & #Hinv & Hf & Heven_at & Hodd_at & HFR) HΦ". 
    rewrite /short.

    wp_lam.
    wp_bind (!_)%E. iApply wp_atomic.
    iInv Ns__eo as (m) "(>CUR & >Hn & Hauths)" "Hclose".
    iIntros "!>". wp_load. iIntros "!>".
    iDestruct (sr_agree _ _ _ st_res_SR_even with "[$] [$]") as %->.
    iDestruct (sr_agree _ _ _ st_res_SR_odd with "[$] [$]") as %->.
    rewrite -Nat.negb_even.
    iMod ("Hclose" with "[Hauths CUR Hn]") as "_".
    { iFrame. }
    iModIntro.

    wp_pures.
    wp_bind (_ <- _)%E. iApply wp_atomic.

    destruct (Nat.even m) eqn:E; simpl.  
    - erewrite (proj2 (Nat.ltb_lt _ _)); [| lia].
      iPoseProof (even_vs  _ _ _ _ st_res_SR_even with "[$]") as "#VS".
      { solve_ndisj. }
      rewrite /eo_vs. iMod "VS".
      iDestruct "VS" as (m') "[CORR MU]".
      rewrite {1}/eo_corr. iDestruct "CORR" as "[CNT ST]".
      iModIntro. Unshelve. 2: by apply PROD_ENV_INDEP. 
      iSpecialize ("MU" with "[Hf]").
      { iSplitL.
        { iApply has_fuels_proper; [reflexivity| | by iFrame].
          rewrite insert_union_singleton_l. f_equiv.
          erewrite map_fmap_singleton. rewrite insert_empty.
          f_equiv. apply sub_helper. lia. }
        set_solver. }
      iApply sswp_MU_wp; [done| ]. 
      iApply (wp_store with "[$]"). iIntros "!> CNT".
      iApply (MU_wand with "[-MU] MU").
      iIntros "[MAP CLOS]". iApply wp_value.

      iAssert (⌜ m' = m ⌝)%I as %->.
      { iDestruct (sr_agree _ _ _ st_res_SR_even with "[$] [$]") as %EQ1.
        iDestruct (sr_agree _ _ _ st_res_SR_odd with "[$] [$]") as %EQ2.
        rewrite -Nat.negb_even in EQ2.
        destruct (Nat.even m') eqn:E'. 
        all: simpl in EQ2; done || lia. }
      rewrite E.

      iMod (sr_upd _ _ _ with "Heven_at ST") as "[EVEN ST]"; eauto.
      rewrite E. iMod ("CLOS" with "[ST CNT]") as "_".
      { iFrame. by rewrite Nat2Z.inj_add. }
      iModIntro. 

      simpl. rewrite -insert_union_singleton_l.
      simpl_has_fuels.
      (* --- TODO: why does it break? *)
      (* wp_pure _. *)

      (* fold ρEven. *)

      (* Set Printing Implicit. *)
      replace (@inl (amRole (even_AM even_impl) + amRole (odd_AM odd_impl))
                     _
                     (even_role (ρ__e even_impl))) with ρEven by done. 

      do 2 wp_pure _. 

      iApply ("Hg" with "[] [] [-HΦ]"); [..| done]. 
      3: { iFrame "Hodd_at EVEN Hinv SPLIT HFR". 
           iApply has_fuels_proper; [reflexivity| | iFrame].
           rewrite insert_empty. erewrite (proj2 (Nat.ltb_ge _ _)); [| lia]. 
           f_equiv; [| f_equiv]. 
           all: apply add_helper; lia. }
      all: iPureIntro; lia.
    - erewrite (proj2 (Nat.ltb_ge _ _)); [| lia].       
      iPoseProof (odd_vs _ _ _ _ st_res_SR_odd with "[$]") as "#VS".
      { solve_ndisj. } 
      rewrite /eo_vs. iMod "VS".
      iDestruct "VS" as (m') "[CORR MU]".
      rewrite {1}/eo_corr. iDestruct "CORR" as "[CNT ST]".
      iModIntro. Unshelve. 2: by apply PROD_ENV_INDEP. 
      iSpecialize ("MU" with "[Hf]").
      { iSplitL.
        { iApply has_fuels_proper; [reflexivity| | by iFrame].
          rewrite insert_commute; [| done]. 
          rewrite insert_union_singleton_l. f_equiv.
          erewrite map_fmap_singleton. rewrite insert_empty.
          f_equiv. apply sub_helper. lia. }
        set_solver. }
      iApply sswp_MU_wp; [done| ]. 
      iApply (wp_store with "[$]"). iIntros "!> CNT".
      iApply (MU_wand with "[-MU] MU").
      iIntros "[MAP CLOS]". iApply wp_value.

      iAssert (⌜ m' = m ⌝)%I as %->.
      { iDestruct (sr_agree _ _ _ st_res_SR_even with "[$] [$]") as %EQ1.
        iDestruct (sr_agree _ _ _ st_res_SR_odd with "[$] [$]") as %EQ2.
        rewrite -Nat.negb_even in EQ2.
        destruct (Nat.even m') eqn:E'. 
        all: simpl in EQ2; done || lia. }      
      rewrite -Nat.negb_even E.

      iMod (sr_upd _ _ _ with "Hodd_at ST") as "[ODD ST]"; eauto.
      rewrite -Nat.negb_even E. iMod ("CLOS" with "[ST CNT]") as "_".
      { iFrame. by rewrite Nat2Z.inj_add. }
      iModIntro. 

      simpl. rewrite -insert_union_singleton_l.
      simpl_has_fuels.
      (* fold ρOdd. *)
      replace (@inl (amRole (even_AM even_impl) + amRole (odd_AM odd_impl))
                 _
                 (odd_role (ρ__o odd_impl))) with ρOdd by done. 

      do 2 wp_pure _. 

      iApply ("Hg" with "[] [] [-HΦ]"); [..| done]. 
      3: { iFrame "Heven_at ODD Hinv SPLIT HFR". 
           iApply has_fuels_proper; [reflexivity| | iFrame].
           rewrite insert_commute; [| done].  
           rewrite insert_empty.
           erewrite (proj2 (Nat.ltb_lt _ _)); [| lia]. 
           f_equiv; [| f_equiv]. 
           all: apply add_helper; lia. }
      all: iPureIntro; lia.      
  Qed.

  Lemma short_spec: even_odd_spec ENV_AM st_res even_at odd_at short.
  Proof using All. 
    rewrite /even_odd_spec. iIntros (tid n N1 N2 f Hf EVEN). 
    iIntros (Φ) "(#SPLIT & #INV & Hf & EVEN & ODD & FR) HΦ". unfold short.
    iApply (short_spec_impl with "[-HΦ]"); [..| done]. 
    3: { iFrame "EVEN ODD FR SPLIT INV". iApply has_fuels_proper; [reflexivity| | by iFrame].
         erewrite (proj2 (Nat.ltb_lt _ _)); [| lia].
         f_equiv; [| f_equiv].
         all: apply add_helper; lia. }
    all: lia.
  Qed.    

End short_prog. 
