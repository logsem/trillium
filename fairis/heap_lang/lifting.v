From iris.proofmode Require Import tactics.
From trillium.program_logic Require Import ectx_lifting.
From trillium.fairness.heap_lang Require Import iris_inst.
From trillium.fairness Require Import action_model fuel.
From trillium.fairness.lm_rules Require Import lm_rules.
From trillium.fairness.heap_lang Require Export lang tactics notation locales_lemmas.

Section lifting.
Context `{LM: LiveModel heap_lang M}.
Context `{hG: !heapGS Σ LM}.

Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.
Implicit Types tid : nat.



Lemma has_fuels_decr E tid fs :
  tid ↦M++ fs -∗ |~{E}~| tid ↦M fs.
Proof.
  iIntros "Hf". rewrite weakestpre.pre_step_unseal.
  iIntros (extr atr) "[%Hvse [Hσ Hm]]".
  iMod (model_state_interp_has_fuels_decr with "Hm Hf") as "[$ $]". by iFrame.
Qed.

Lemma has_fuels_dealloc E tid fs (ρ: fmrole M) (δ: fmstate M) :
  ρ ∉ live_roles _ δ → frag_model_is δ -∗ tid ↦M fs -∗
  |~{E}~| frag_model_is δ ∗ tid ↦M (delete (ρ) fs).
Proof using.
  iIntros (Hnin) "Hst Hf". rewrite weakestpre.pre_step_unseal.
  iIntros (extr atr) "[%Hvse [Hσ Hm]]".
  iMod (model_state_interp_has_fuels_dealloc with "Hm Hst Hf") as "[Hm Hf]";
    [done|by iFrame].
Qed.

(* Rule from the Trillium article *)
Lemma wp_role_dealloc s tid E e fs ρ δ Φ :
  ρ ∉ live_roles _ δ → frag_model_is δ -∗ tid ↦M fs -∗
  (frag_model_is δ -∗ tid ↦M (delete (ρ) fs) -∗ WP e @ s; tid; E {{ Φ }}) -∗
  WP e @ s; tid; E {{ Φ }}.
Proof using.
  iIntros (Hnin) "HM Hfuels Hwp".
  iMod (has_fuels_dealloc with "HM Hfuels") as "[HM Hfuels]"; [done|].
  by iApply ("Hwp" with "HM Hfuels").
Qed.

(* TODO: move? *)
Lemma model_step_MU tid E s1 s2 ρ f1 fs
  (Hdom: ρ ∉ dom fs)
  (TRANS: fmtrans M s1 (Some ρ) s2)
  (LR: M.(live_roles) s2 ⊆ M.(live_roles) s1):
  frag_model_is s1 -∗
  tid ↦M ({[ρ := f1]} ∪ (S <$> fs)) -∗
  MU E tid (frag_model_is s2 ∗
           tid ↦M ({[ρ := lm_flm LM]} ∪ fs)) (LM := LM).
Proof using.
  iIntros "Hst Hfuel1".
  rewrite /MU /HL_LM_trace_interp'. iIntros (extr lmtr) "X".
  destruct extr; [done| ].
  iDestruct "X" as "(HEAP & MSI & %TS & -> & %STEP)".
  iMod (update_model_step with "Hfuel1 Hst MSI") as
    (δ2 Hvse) "(Hfuel & Hst & Hmod)"; eauto.
  iModIntro. iFrame. iExists _. iPureIntro. done. 
Qed. 
  
(* TODO: move? *)
Lemma model_step_singlerole_MU tid E s1 s2 ρ f1
  (TRANS: fmtrans M s1 (Some ρ) s2)
  (LR: M.(live_roles) s2 ⊆ M.(live_roles) s1):
  frag_model_is s1 -∗
  tid ↦M ({[ρ := f1]}) -∗
  MU E tid (frag_model_is s2 ∗ tid ↦M ({[ρ := lm_flm LM]})).
Proof using.
  iIntros "Hst FS".
  iApply MU_wand.
  2: { iApply (model_step_MU with "[$] [FS]"); eauto.       
       2: { iApply has_fuels_proper; [reflexivity| | by iFrame].
            rewrite -insert_union_singleton_l -insert_empty.
            f_equiv; [done| ]. apply leibniz_equiv_iff, fmap_empty. }
       set_solver. }
  rewrite map_union_empty. set_solver.
Qed.
  

Lemma wp_step_model s tid ρ (f1 : nat) fs s1 s2 E e Φ :
  TCEq (to_val e) None →
  fmtrans M s1 (Some ρ) s2 →
  M.(live_roles) s2 ⊆ M.(live_roles) s1 →
  ρ ∉ dom fs →
  ▷ frag_model_is s1 -∗
  ▷ tid ↦M ({[ρ:=f1]} ∪ fmap S fs) -∗
  sswp s E e (λ e', frag_model_is s2 -∗
                    tid ↦M ({[ρ:=(LM.(lm_flm))]} ∪ fs) -∗
                    WP e' @ s; tid; E {{ Φ }} ) (LM := LM) -∗
  WP e @ s; tid; E {{ Φ }}.
Proof using.
  iIntros (Hval Htrans Hlive Hdom) ">Hst >Hfuel1 Hwp".
  iApply sswp_MU_wp.
  { by inversion Hval. }
  iApply (sswp_wand with "[-Hwp]"); [| by iFrame].
  simpl. iIntros (e') "POST".
  iApply (MU_wand with "[POST]").
  2: { iApply (model_step_MU with "[$] [$]"); eauto. }
  iIntros "(?&?)". by iApply ("POST" with "[$] [$]").
Qed. 


Lemma wp_step_model_singlerole s tid ρ (f1 : nat) s1 s2 E e Φ :
  TCEq (to_val e) None →
  fmtrans M s1 (Some ρ) s2 →
  M.(live_roles) s2 ⊆ M.(live_roles) s1 →
  ▷ frag_model_is s1 -∗ ▷ tid ↦M {[ρ := f1]} -∗
  sswp s E e (λ e', frag_model_is s2 -∗
                    tid ↦M {[ρ := (LM.(lm_flm))]} -∗
                    WP e' @ s; tid; E {{ Φ }} ) (LM := LM) -∗
  WP e @ s; tid; E {{ Φ }}.
Proof using.
  iIntros (Hval Htrans Hlive) ">Hst >Hfuel1 Hwp".
  replace ({[ρ := f1]}) with ({[(ρ: fmrole M) := f1]} ∪ (fmap S ∅:gmap _ _)); last first.
  { rewrite fmap_empty. rewrite right_id_L. done. }
  iApply (wp_step_model with "Hst Hfuel1"); [done|set_solver|done|].
  iApply (sswp_wand with "[] Hwp"). iIntros (e') "Hwp Hst Hfuel1".
  rewrite right_id_L. iApply ("Hwp" with "Hst Hfuel1").
Qed.

Lemma wp_step_fuel s tid E e fs Φ :
  fs ≠ ∅ → ▷ tid ↦M++ fs -∗
  sswp s E e (λ e', tid ↦M fs -∗ WP e' @ s; tid; E {{ Φ }} ) (LM := LM)-∗
  WP e @ s; tid; E {{ Φ }}.
Proof using.
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
    rewrite !app_length //=. }
  iModIntro. iSplit.
  { iPureIntro. by eauto. }
  iIntros (e2 σ2 efs Hstep).
  have [-> [-> ->]] : σ2 = σ1 ∧ efs = [e] ∧ e2 = Val $ LitV LitUnit by inv_head_step.
  iNext. 
  iMod ("HΦ" with "Hfuels1") as "HΦ". iModIntro. iExists δ2, (Silent_step tid).
  iFrame. rewrite Hexend /=. iFrame "Hsi". iSplit; [by iPureIntro|].
  iSplit; [|done]. iApply "He". by list_simplifier.
Qed.

End lifting.
