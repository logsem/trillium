From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl.
From iris.base_logic Require Export gen_heap.
From trillium.prelude Require Import classical_instances.
From trillium.program_logic Require Export ectx_lifting.
From heap_lang Require Export sswp_logic locales_helpers_hl.
From fairis Require Export fuel resources heap_lang_lm
  (* fair_termination fuel fuel_termination *)
.
(* From trillium.program_logic Require Import ectx_lifting. *)
(* From trillium.fairness.heap_lang Require Export lang. *)
(* From trillium.fairness.heap_lang Require Import tactics notation. *)

Set Default Proof Using "Type".

(* Canonical Structure ModelO (M : FairModel) := leibnizO M. *)
(* Canonical Structure RoleO (M : FairModel) := leibnizO (M.(fmrole)). *)

Section lifting.
Context `{LM:LiveModel heap_lang M}.
Context `{!heapGS Σ LM}.

Lemma has_fuels_decr E tid fs :
  tid ↦M++ fs -∗ |~{E}~| tid ↦M fs.
Proof.
  iIntros "Hf". rewrite weakestpre.pre_step_unseal.
  iIntros (extr atr) "[%Hvse [Hσ Hm]]".
  iMod (model_state_interp_has_fuels_decr with "Hm Hf") as "[$ $]". by iFrame.
Qed.

Lemma has_fuels_dealloc E tid fs ρ δ :
  ρ ∉ live_roles _ δ → frag_model_is δ -∗ tid ↦M fs -∗
  |~{E}~| frag_model_is δ ∗ tid ↦M (delete ρ fs).
Proof.
  iIntros (Hnin) "Hst Hf". rewrite weakestpre.pre_step_unseal.
  iIntros (extr atr) "[%Hvse [Hσ Hm]]".
  iMod (model_state_interp_has_fuels_dealloc with "Hm Hst Hf") as "[Hm Hf]";
    [done|by iFrame].
Qed.

(* Rule from the Trillium article *)
Lemma wp_role_dealloc s tid E e fs ρ δ Φ :
  ρ ∉ live_roles _ δ → frag_model_is δ -∗ tid ↦M fs -∗
  (frag_model_is δ -∗ tid ↦M (delete ρ fs) -∗ WP e @ s; tid; E {{ Φ }}) -∗
  WP e @ s; tid; E {{ Φ }}.
Proof.
  iIntros (Hnin) "HM Hfuels Hwp".
  iMod (has_fuels_dealloc with "HM Hfuels") as "[HM Hfuels]"; [done|].
  by iApply ("Hwp" with "HM Hfuels").
Qed.

Lemma wp_step_model s tid ρ (f1 : nat) fs fr s1 s2 E e Φ :
  TCEq (to_val e) None →
  fmtrans M s1 (Some ρ) s2 →
  M.(live_roles) s2 ⊆ M.(live_roles) s1 →
  ρ ∉ dom fs →
  ▷ frag_model_is s1 -∗
  ▷ tid ↦M ({[ρ:=f1]} ∪ fmap S fs) -∗
  ▷ frag_free_roles_are fr -∗
  sswp s E e (λ e', frag_model_is s2 -∗
                    tid ↦M ({[ρ:=(LM.(lm_fl) s2)]} ∪ fs) -∗
                    frag_free_roles_are fr -∗
                    WP e' @ s; tid; E {{ Φ }} ) -∗
  WP e @ s; tid; E {{ Φ }}.
Proof.
  iIntros (Hval Htrans Hlive Hdom) ">Hst >Hfuel1 >Hfr Hwp".
  rewrite wp_unfold /wp_pre.
  rewrite /sswp. simpl. rewrite Hval.
  iIntros (extr atr K tp1 tp2 σ1 Hvalid Hloc Hexend) "(% & Hsi & Hmi)".
  iMod ("Hwp" with "Hsi") as (Hred) "Hwp". iIntros "!>".
  iSplitR; [by rewrite Hexend in Hred|]. iIntros (????). rewrite Hexend.
  iMod ("Hwp" with "[//]") as "Hwp". iIntros "!>!>". iMod "Hwp". iIntros "!>".
  iApply step_fupdN_intro; [done|]. iIntros "!>".
  iMod "Hwp" as "[Hσ [Hwp ->]]".
  iDestruct (model_agree' with "Hmi Hst") as %Hmeq. iFrame.
  rewrite /trace_ends_in in Hexend. rewrite -Hexend.
  iMod (update_model_step with "Hfuel1 Hst Hmi") as
    (δ2 Hvse) "(Hfuel & Hst & Hmod)"; eauto.
  - rewrite -Hloc. eapply locale_step_atomic; eauto. by apply fill_step.
  - iModIntro; iExists δ2, (Take_step ρ tid). rewrite big_sepL_nil. iFrame.
    iSplit; [done|]. iDestruct ("Hwp" with "Hst Hfuel Hfr") as "Hwp". by iFrame.
Qed.

Lemma wp_step_model_singlerole s tid ρ (f1 : nat) fr s1 s2 E e Φ :
  TCEq (to_val e) None →
  fmtrans M s1 (Some ρ) s2 →
  M.(live_roles) s2 ⊆ M.(live_roles) s1 →
  ▷ frag_model_is s1 -∗ ▷ tid ↦M {[ρ := f1]} -∗ ▷ frag_free_roles_are fr -∗
  sswp s E e (λ e', frag_model_is s2 -∗
                    tid ↦M {[ρ := (LM.(lm_fl) s2)]} -∗
                    frag_free_roles_are fr -∗
                    WP e' @ s; tid; E {{ Φ }} ) -∗
  WP e @ s; tid; E {{ Φ }}.
Proof.
  iIntros (Hval Htrans Hlive) ">Hst >Hfuel1 >Hfr Hwp".
  replace ({[ρ := f1]}) with ({[ρ := f1]} ∪ (fmap S ∅:gmap _ _)); last first.
  { rewrite fmap_empty. rewrite right_id_L. done. }
  iApply (wp_step_model with "Hst Hfuel1 Hfr"); [done|set_solver|done|].
  iApply (sswp_wand with "[] Hwp"). iIntros (e') "Hwp Hst Hfuel1 Hfr".
  rewrite right_id_L. iApply ("Hwp" with "Hst Hfuel1 Hfr").
Qed.

Lemma wp_step_fuel s tid E e fs Φ :
  fs ≠ ∅ → ▷ tid ↦M++ fs -∗
  sswp s E e (λ e', tid ↦M fs -∗ WP e' @ s; tid; E {{ Φ }} ) -∗
  WP e @ s; tid; E {{ Φ }}.
Proof.
  iIntros (?) ">HfuelS Hwp". rewrite wp_unfold /wp_pre /sswp /=.
  destruct (to_val e).
  { iMod (has_fuels_decr with "HfuelS") as "Hfuel".
    iDestruct ("Hwp" with "Hfuel") as "Hwp".
    iDestruct (wp_value_inv with "Hwp") as "Hwp". by iMod "Hwp". }
  iIntros (extr atr K tp1 tp2 σ1 Hvalid Hloc Hends) "(%Hvalid' & Hsi & Hmi)".
  rewrite Hends. iMod ("Hwp" with "Hsi") as (Hred) "Hwp". iModIntro.
  iSplit; [done|]. iIntros (e2 σ2 efs Hstep).
  iMod ("Hwp" with "[//]") as "Hwp".
  iIntros "!>!>". iMod "Hwp". iIntros "!>".
  iApply step_fupdN_intro; [done|]. iIntros "!>". iMod "Hwp". rewrite -Hends.
  iMod (update_fuel_step with "HfuelS Hmi") as (δ2) "(%Hvse & Hfuel & Hmod)" =>//.
  { rewrite Hends -Hloc. eapply locale_step_atomic; eauto. by apply fill_step. }
  iIntros "!>". iDestruct "Hwp" as "[Hsi [Hwp ->]]".
  iExists _, (Silent_step tid). iFrame. iSplit; [done|].
  iDestruct ("Hwp" with "Hfuel") as "Hwp". iSplit; [|done].
  iApply (wp_wand with "Hwp"). iIntros (v) "HΦ'". by iFrame.
Qed.

Lemma wp_role_fork s tid E e Φ R1 R2 (Hdisj: R1 ##ₘ R2) (Hnemp: R1 ∪ R2 ≠ ∅):
  tid ↦M++ (R1 ∪ R2) -∗
  (∀ tid', ▷ (tid' ↦M R2 -∗ WP e @ s; tid'; ⊤ {{ _, tid' ↦M ∅ }})) -∗
  ▷ (tid ↦M R1 ={E}=∗ Φ (LitV LitUnit)) -∗
  WP Fork e @ s; tid; E {{ Φ }}.
Proof.
  iIntros "Htid He HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "(% & Hsi & Hmi)".
  iMod (update_fork_step R1 R2 _
       (tp1 ++ ectx_language.fill K (Val $ LitV LitUnit) :: tp2 ++ [e])
       _ _ _ e _ σ1 with "Htid Hmi") as
    (δ2 Hvse) "(Hfuels1 & Hfuels2 & Hmi)".
  { done. }
  { done. }
  { rewrite /trace_ends_in in Hexend. rewrite Hexend. done. }
  { rewrite -Hloc. rewrite -(language.locale_fill _ _ K).
    rewrite /trace_ends_in in Hexend. rewrite Hexend.
    econstructor 1 =>//.
    apply fill_step, head_prim_step. econstructor. }
  { list_simplifier. exists (tp1 ++ fill K #() :: tp2).
    rewrite /trace_ends_in in Hexend. rewrite Hexend.
    split; first by list_simplifier.
    apply heap_lang_locales_equiv_length. simpl.
    rewrite !length_app //=. }
  iModIntro. iSplit. iPureIntro; first by eauto. iNext.
  iIntros (e2 σ2 efs Hstep).
  have [-> [-> ->]] : σ2 = σ1 ∧ efs = [e] ∧ e2 = Val $ LitV LitUnit by inv_head_step.
  iMod ("HΦ" with "Hfuels1") as "HΦ". iModIntro. iExists δ2, (Silent_step tid).
  iFrame. rewrite Hexend /=. iFrame "Hsi". iSplit; [by iPureIntro|].
  iSplit; [|done]. iApply "He". by list_simplifier.
Qed.

End lifting.
