From iris.proofmode Require Import tactics.
From trillium.fairness Require Import action_model resources fuel.
From trillium.fairness.heap_lang Require Import notation iris_inst.


Section MuRole.
  Context `{LM: LiveModel heap_lang M}.
  Context `{hG: !heapGS Σ LM}.
  
  Definition MU__r ρ E P: iProp Σ :=  
    ∀ τ f R, τ ↦M ({[ ρ := f ]} ∪ (S <$> R)) ∗ ⌜ ρ ∉ dom R ⌝ -∗
              MU E τ (τ ↦M ({[ ρ := lm_flm LM ]} ∪ R) ∗ P) (LM := LM).

  Lemma MU__r_wand E ρ (P Q: iProp Σ):
    (P -∗ Q) -∗ MU__r ρ E P -∗ MU__r ρ E Q.
  Proof.
    iIntros "HPQ HMU". rewrite /MU__r. iIntros "**".
    iSpecialize ("HMU" with "[$]"). 
    iApply (MU_wand with "[HPQ] [$]"). iFrame.
    iIntros "[??]". iFrame. by iApply "HPQ". 
  Qed.

  Lemma MU__r_mask_weaken E1 E2 ρ (P: iProp Σ)
    (SUB: E1 ⊆ E2):
    MU__r ρ E1 P -∗ MU__r ρ E2 P.
  Proof.
    iIntros "MU". rewrite /MU__r. iIntros "**".
    iApply MU_mask_weaken; eauto.
    by iApply "MU".
  Qed.

End MuRole.
