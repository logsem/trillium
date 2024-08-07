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


Section proof_start.
  Context {even_impl: EvenModel} {odd_impl: OddModel}.

  Let M := @the_fair_model even_impl odd_impl.
  Let LM := @the_model even_impl odd_impl.

  Context (ep: EvenProg) (op: OddProg). 

  Context `{!heapGS Σ LM, !evenoddG Σ}.

  Context (st_res even_at odd_at: nat -> iProp Σ). 
  Context
    (st_res_SR_even: @StateRes _ Nat.even st_res even_at)
    (st_res_SR_odd: @StateRes _ Nat.odd st_res odd_at). 

  Let Ns := nroot .@ "even_odd".
  Definition evenodd_inv n := inv Ns (evenodd_inv_inner st_res n).

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

  Lemma start_spec tid n N1 N2 f (Hf: f > 60) (EVEN: N1 < N2)
    :
    {{{ evenodd_inv n ∗ 
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
    iInv Ns as (m) "(>CUR & >Hn & Hauths)" "Hclose".
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
      iApply (@e_spec ep the_fair_model _ _ _ _ _ st_res_SR_even
               with "[$Hf $Heven_at]"); [lia| simpl; lia | ..].
      2: { by iIntros "!> ?". }
      by iApply even_vs. }

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
      iApply (@o_spec op the_fair_model _ _ _ _ _ st_res_SR_odd
               with "[$Hf $Hodd_at]"); [lia| simpl; lia | ..].
      2: { by iIntros "!> ?". }
      by iApply odd_vs. }

    iIntros "!> Hf". by iApply "HΦ".
  Qed. 

End proof_start.
