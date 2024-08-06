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
From trillium.fairness.heap_lang.examples.even_odd Require Import action_model interface thread_progs model_updates.
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

Section proof.
  Context {even_impl: EvenModel} {odd_impl: OddModel}.
  Let PM := @prod_model even_impl odd_impl. 
  Let M := @the_fair_model even_impl odd_impl.
  Let LM := @the_model even_impl odd_impl.

  Context `{!heapGS Σ LM, !evenoddG Σ}.

  Let Ns := nroot .@ "even_odd".
  
  Let ρEven: fmrole M := even_role (ρ__e even_impl).
  Let ρOdd: fmrole M := odd_role (ρ__o odd_impl).

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
