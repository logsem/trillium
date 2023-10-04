From stdpp Require Import finite decidable.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness Require Import fairness fair_termination fairness_finiteness.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness.examples Require Import choose_nat.

Import derived_laws_later.bi.

Set Default Proof Using "Type".

(** Construct inverse mapping of program state to model state,
    to compute finite relation *)
Definition Z_CN (v : val) : CN :=
  match v with
  | LitV (LitInt z) =>
      match z with
      | Z0 => N 0
      | Zpos p => N (Pos.to_nat p)
      | Zneg _ => Start         (* Error case when z < -1 *)
      end
  | _ => Start                  (* Error case *)
  end.

Lemma Z_CN_CN_Z cn : Z_CN #(CN_Z cn) = cn.
Proof. destruct cn; [done|]; destruct n; [done|]=> /=; f_equal; lia. Qed.

(** Derive that program is related to model by
    [sim_rel_with_user cn_model (ξ_cn l) using Trillium adequacy *)
Lemma choose_nat_sim l :
  continued_simulation
    (sim_rel_with_user cn_model (ξ_cn l))
    (trace_singleton ([choose_nat_prog l #()],
                        {| heap := {[l:=#-1]};
                           used_proph_id := ∅ |}))
    (trace_singleton (initial_ls (LM := cn_model) Start 0%nat)).
Proof.
  assert (heapGpreS choose_natΣ cn_model) as HPreG.
  { apply _. }
  eapply (strong_simulation_adequacy
            choose_natΣ _ NotStuck _ _ _ ∅); [|set_solver|].
  { clear.
    apply rel_finitary_sim_rel_with_user_ξ.
    intros extr atr c' oζ.
    eapply finite_smaller_card_nat=> /=.
    eapply (in_list_finite [(Z_CN (heap c'.2 !!! l), None);
                            (Z_CN (heap c'.2 !!! l), Some ())]).
    (* TODO: Figure out why this does not unify with typeclass *)
    Unshelve. 2: intros x; apply make_proof_irrel.
    intros [cn o] [cn' [Hextr Hatr]].
    rewrite Hextr Z_CN_CN_Z -Hatr. destruct o; [destruct u|]; set_solver. }
  iIntros (?) "!> Hσ Hs Hr Hf".
  iMod (own_alloc) as (γ) "He"; [apply (excl_auth_valid (-1)%Z)|].
  iDestruct "He" as "[He● He○]".
  iMod (inv_alloc Ns ⊤ (choose_nat_inv_inner γ l) with "[He● Hσ Hs]") as "#IH".
  { iIntros "!>". iExists _. iFrame. by rewrite big_sepM_singleton. }
  iModIntro.
  iSplitL.
  { iApply (choose_nat_spec _ _ _ 40 with "IH [Hr Hf He○]");
      [lia|lia| |by eauto]=> /=.
    replace (∅ ∖ {[()]}) with (∅:gset unit) by set_solver.
    rewrite has_fuel_fuels gset_to_gmap_set_to_map. iFrame. }
  iIntros (ex atr c Hvalid Hex Hatr Hends Hξ Hstuck) "Hσ _".
  iInv Ns as ">H".
  iDestruct "H" as (cn) "(Hf & Hl & H●)".
  iDestruct "Hσ" as (Hvalid') "[Hσ Hs]".
  iDestruct (gen_heap_valid with "Hσ Hl") as %Hlookup%lookup_total_correct.
  iDestruct (model_agree' with "Hs Hf") as %Hlast.
  iModIntro. iSplitL; [by iExists _; iFrame|].
  iApply fupd_mask_intro; [set_solver|]. iIntros "_".
  iPureIntro. exists cn.
  split; [done|].
  subst. by destruct atr.
Qed.

Theorem choose_nat_terminates l extr :
  trfirst extr = ([choose_nat_prog l #()],
                    {| heap := {[l:=#-1]};
                      used_proph_id := ∅ |}) →
  extrace_fairly_terminating extr.
Proof.
  intros Hexfirst.
  eapply heap_lang_continued_simulation_fair_termination; eauto.
  rewrite Hexfirst. eapply choose_nat_sim.
Qed.
