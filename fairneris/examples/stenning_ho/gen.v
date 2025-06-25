From stdpp Require Import list fin_maps.
From iris.algebra Require Import excl_auth.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From trillium.program_logic Require Import ectx_lifting.
From fairneris Require Import fairness fair_resources fuel.
From fairneris.examples Require Import stenning_ho_model.
From fairneris.aneris_lang Require Import proofmode.
From fairneris.aneris_lang.state_interp Require Import state_interp state_interp_events.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From fairneris.aneris_lang.lib Require Import serialization_code.
From fairneris.lib Require Import gen_heap_light.

Definition new_gen : val :=
  λ: <>,
    let: "l" := ref #0 in
    λ: <>, let: "x" := !"l" in "l" <- "x"+#2;; "x".

Section with_Σ.
  Context `{anerisG _ _ (live_model_of_user stenning_model net_model) Σ}.
  Context `{!stenningG Σ}.

  Definition is_gen ip tid f (v:val) Φ : iProp Σ :=
    ∃ P,
    (∀ ρ f',
       ⌜f' > f⌝ →
      {{{ (ip, tid) ↦M {[ ρ := f' ]} ∗ P }}}
        mkExpr ip (v #()) @ (ip,tid)
      {{{ w, RET mkVal ip w; Φ w ∗ (ip, tid) ↦M {[ ρ := f'-f ]} ∗ P }}}) ∗
      P.

  Lemma nat_plus_minus x y z : x - y - z = x - (y + z).
  Proof. lia. Qed.
  Tactic Notation "simpl_arith" := repeat rewrite nat_plus_minus.
  Tactic Notation "wp_pures" := (wp_pures; simpl_arith).
  
  Lemma new_gen_spec ip tid f :
    f > 5 →
    {{{ is_node ip ∗ (ip, tid) ↦M {[ Arole := f ]} }}}
      mkExpr ip (new_gen #()) @ (ip,tid)
    {{{ w, RET mkVal ip w; is_gen ip tid 8 w (λ w, ∃ (x:Z), ⌜w = #x⌝ ∗ ⌜Z.even x⌝) ∗
                           (ip, tid) ↦M {[ Arole := f-5 ]} }}}.
  Proof.
    iIntros (Hf Φ) "[#Hn Hf] HΦ".
    rewrite /new_gen.
    wp_pures.
    wp_bind (Alloc _ _).
    iApply sswp_MU_wp.
    iApply wp_alloc; [done|].
    iIntros (l) "Hl".
    mu_fuel.
    iApply wp_value. wp_pures.
    iApply wp_value.
    iApply "HΦ". iFrame.
    iAssert (∃ x, ⌜Z.even x⌝ ∗ l ↦[ip] #x)%I with "[Hl]" as "Hl".
    { iExists _. iFrame. done. }
    iExists (∃ x : Z, ⌜Z.even x⌝ ∗ l ↦[ip] #x)%I. iFrame.
    iIntros (ρ). iIntros (f' Hf' Ψ) "!> [Hf Hl] HΦ".
    iDestruct "Hl" as (x Heven) "Hl".
    wp_pures.
    wp_bind (Load _).
    iApply sswp_MU_wp.
    iApply (wp_load with "Hl").
    iIntros "!> Hl".
    mu_fuel.
    iApply wp_value.
    wp_pures.
    wp_bind (Store _ _).
    iApply sswp_MU_wp.
    iApply (wp_store with "Hl").
    iIntros "!> Hl".
    mu_fuel.
    iApply wp_value.
    wp_pures.
    iApply wp_value.
    iApply "HΦ".
    iSplitR.
    - iExists _. done.
    -  iFrame. iExists _. iFrame. iPureIntro.
      rewrite Z.even_add.
      by destruct (Z.even x).
  Qed.

  Lemma is_gen_spec ip tid f f' v Φ :
    f' > f →
    {{{ is_gen ip tid f v Φ ∗ (ip, tid) ↦M {[ Arole := f' ]} }}}
      mkExpr ip (v #()) @ (ip,tid)
    {{{ w, RET mkVal ip w; Φ w ∗ is_gen ip tid f v Φ ∗
                           (ip, tid) ↦M {[ Arole := f'-f ]} }}}.
  Proof.
    iIntros (Hf Ψ) "[Hv Hf] HΨ".
    iDestruct "Hv" as (P) "[#Hgen HP]".
    iApply ("Hgen" with "[//] [$HP $Hf]").
    iIntros "!>" (w) "[HΦ [Hf HP]]". iApply "HΨ".
    iFrame. iExists _. iFrame "#∗".
  Qed.

End with_Σ.
