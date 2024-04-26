From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From trillium.program_logic Require Export language traces.
From trillium.bi Require Export weakestpre.
From iris.prelude Require Import options.

Class irisG (Λ : language) (M : Model) (Σ : gFunctors) := IrisG {
  iris_invGS :> invGS_gen HasNoLc Σ;

  (** The state interpretation is an invariant that should hold in between each
  step of reduction. Here [Λstate] is the global state, [list Λobservation] are
  the remaining observations, and [nat] is the number of forked-off threads
  (not the total number of threads, which is one higher because there is always
  a main thread). *)
  (* TODO: Consider redefining as [option (locale Λ → option (action Λ))] arg *)
  state_interp_opt : (option (locale Λ * option (action Λ))) → execution_trace Λ → auxiliary_trace M → iProp Σ;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
  fork_post : locale Λ → val Λ → iProp Σ;
}.
Global Opaque iris_invGS.

Notation state_interp := (state_interp_opt None).

(* TODO: Move this *)
Definition pre_step_def `{!irisG Λ M Σ} E1 E2 (P:iProp Σ) : iProp Σ :=
  ∀ extr atr, state_interp extr atr ={E1,E2}=∗
              state_interp extr atr ∗ P.
Local Definition pre_step_aux : seal (@pre_step_def).
Proof. by eexists. Qed.
Definition pre_step := pre_step_aux.(unseal).
Global Arguments pre_step {Λ M Σ _}.
Local Lemma pre_step_unseal `{!irisG Λ M Σ} : pre_step = pre_step_def.
Proof. rewrite -pre_step_aux.(seal_eq) //. Qed.

Notation "|~{ E1 , E2 }~| P" := (pre_step E1 E2 P)%I
                                            (at level 99, P at level 200, format "'[  ' |~{  E1  ,  E2  }~|  '/' P ']'").
Notation "|~{ E }~| P" := (|~{E,E}~| P)%I
                                     (at level 99, P at level 200, format "'[  ' |~{  E  }~|  '/' P ']'").
Notation "|~~| P" := (|~{⊤}~| P)%I
                                     (at level 99, P at level 200, format "'[  ' |~~|  '/' P ']'").

Section pre_step.
  Context `{!irisG Λ M Σ}.

  Lemma pre_step_intro E P :
    P -∗ |~{E}~| P.
  Proof.
    rewrite pre_step_unseal.
    iIntros "HP". iIntros (extr atr) "Hwp". by iFrame.
  Qed.

  Lemma pre_step_comm E P Q :
    (|~{E}~| P) -∗ (|~{E}~| Q) -∗ |~{E}~| P ∗ Q.
  Proof.
    rewrite pre_step_unseal.
    iIntros "HP HQ".
    iIntros (extr atr) "Hσ".
    iMod ("HP" with "Hσ") as "[Hσ HP]".
    iMod ("HQ" with "Hσ") as "[Hσ HQ]".
    by iFrame.
  Qed.

  Lemma pre_step_mono E P Q :
    (P -∗ Q) -∗ (|~{E}~| P) -∗ |~{E}~| Q.
  Proof.
    rewrite pre_step_unseal.
    iIntros "HPQ HP".
    iIntros (extr atr) "Hσ".
    iMod ("HP" with "Hσ") as "[Hσ HP]". iFrame. by iApply "HPQ".
  Qed.

  Lemma fupd_pre_step_fupd E P : (|={E}=> |~{E}~| |={E}=> P) -∗ |~{E}~| P.
  Proof.
    rewrite pre_step_unseal.
    iIntros "HP".
    iIntros (extr atr) "Hσ".
    iMod "HP". iMod ("HP" with "Hσ") as "[Hσ >HP]".
    by iFrame.
  Qed.

  Lemma pre_step_fupd E P : (|~{E}~| |={E}=> P) -∗ |~{E}~| P.
  Proof. iIntros "HP". iApply fupd_pre_step_fupd. by iModIntro. Qed.

  Lemma fupd_pre_step E P : (|={E}=> |~{E}~| P) -∗ |~{E}~| P.
  Proof.
    iIntros "HP". iApply fupd_pre_step_fupd. iMod "HP".
    iModIntro. iApply (pre_step_mono with "[] HP"). by iIntros "HP!>".
  Qed.

  Lemma pre_step_elim extr atr E P :
    state_interp extr atr -∗ (|~{E}~| P) ={E}=∗ state_interp extr atr ∗ P.
  Proof. rewrite pre_step_unseal. iIntros "Hσ HP". by iApply "HP". Qed.

  #[global] Instance pre_step_ne n : Proper ((≡) ==> (≡) ==> (dist n) ==> (dist n)) pre_step.
  Proof. rewrite pre_step_unseal. solve_proper. Qed.
  #[global] Instance pre_step_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) pre_step.
  Proof. rewrite pre_step_unseal. solve_proper. Qed.

  Class IntoPreStep E (P Q : iProp Σ) := into_pre_step : P ⊢ |~{E}~| Q.
  #[global] Instance into_pre_step_id E P : IntoPreStep E (|~{E}~| P) P | 0.
  Proof. rewrite /IntoPreStep. by iIntros "HP". Qed.
  #[global] Instance into_pre_step_intro E P : IntoPreStep E P P | 1.
  Proof. rewrite /IntoPreStep. by iApply pre_step_intro. Qed.

  Lemma modality_pre_step_mixin E :
    modality_mixin (@pre_step Λ M Σ _ E E)
                   (MIEnvId) (MIEnvTransform (IntoPreStep E)).
  Proof.
    split; simpl.
    - iIntros (P). by iApply pre_step_intro.
    - rewrite /IntoPreStep. iIntros (P Q HPQ) "HP". by iApply HPQ.
    - iIntros "H". by iApply pre_step_intro.
    - iIntros (P Q HPQ) "HP". iApply (pre_step_mono with "[] HP"). iApply HPQ.
    - iIntros (P Q) "[HP HQ]".
      by iDestruct (pre_step_comm with "HP HQ") as "HPQ".
  Qed.
  Definition modality_pre_step E :=
    Modality _ (modality_pre_step_mixin E).
  #[global] Instance from_modality_pre_step E P :
    FromModal True (modality_pre_step E) (|~{E}~| P) (|~{E}~| P) P.
  Proof. by rewrite /FromModal /=. Qed.

  #[global] Instance elim_modal_pre_step_pre_step p E1 E2 E3 P Q :
    ElimModal True p false (|~{E1,E2}~| P) P (|~{E1,E3}~| Q) (|~{E2,E3}~| Q).
  Proof.
    destruct p.
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]". iDestruct "HP" as "#HP".
      rewrite pre_step_unseal.
      iIntros (extr atr) "Hσ". iMod ("HP" with "Hσ") as "[Hσ HP']".
      iMod ("HPQ" with "HP' Hσ") as "HQ". iFrame. done.
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]".
      rewrite pre_step_unseal.
      iIntros (extr atr) "Hσ". iMod ("HP" with "Hσ") as "[Hσ HP']".
      iMod ("HPQ" with "HP' Hσ") as "HQ". iFrame. done.
  Qed.

  #[global] Instance elim_modal_pre_step_fupd p E1 E2 E3 P Q :
    ElimModal True p false (|={E1,E2}=> P) P (|~{E1,E3}~| Q) (|~{E2,E3}~| Q).
  Proof.
    destruct p.
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]". iDestruct "HP" as "#HP".
      rewrite pre_step_unseal.
      iIntros (extr atr) "Hσ". iMod "HP".
      iMod ("HPQ" with "HP Hσ") as "HQ". by iFrame.
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]".
      rewrite pre_step_unseal.
      iIntros (extr atr) "Hσ". iMod "HP".
      iMod ("HPQ" with "HP Hσ") as "HQ". by iFrame.
  Qed.

  Lemma pre_step_mask_subseteq {E1} E2 : E2 ⊆ E1 → ⊢ |~{E1,E2}~| |~{E2,E1}~| True.
  Proof.
    iIntros (HE).
    rewrite pre_step_unseal.
    iIntros (??) "$".
    iMod (fupd_mask_subseteq) as "Hclose"; [done|].
    iModIntro.
    iIntros (??) "$". iApply "Hclose".
  Qed.

  #[global] Instance elim_modal_pre_step_bupd p E1 E2 P Q :
    ElimModal True p false (|==> P) P (|~{E1,E2}~| Q) (|~{E1,E2}~| Q).
  Proof.
    destruct p.
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]". iDestruct "HP" as "#HP".
      rewrite pre_step_unseal.
      iIntros (extr atr) "Hσ". iMod "HP".
      iMod ("HPQ" with "HP Hσ") as "HQ". by iFrame.
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]".
      rewrite pre_step_unseal.
      iIntros (extr atr) "Hσ". iMod "HP".
      iMod ("HPQ" with "HP Hσ") as "HQ". by iFrame.
  Qed.

End pre_step.

Definition wp_pre `{!irisG Λ AS Σ} (s : stuckness)
    (wp : coPset -d> locale Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> locale Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E ζ e1 Φ,
  match to_val e1 with
  | Some v => |~{E}~| Φ v
  | None => ∀ (extr : execution_trace Λ) (atr : auxiliary_trace AS) K tp1 tp2 σ1,
      ⌜valid_exec extr⌝ -∗
      ⌜locale_of tp1 (ectx_fill K e1) = ζ⌝ -∗
      ⌜trace_ends_in extr (tp1 ++ ectx_fill K e1 :: tp2, σ1)⌝ -∗
      state_interp extr atr ={E,∅}=∗
       ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
       ∀ α e2 σ2 efs,
         ⌜prim_step e1 σ1 α e2 σ2 efs⌝ ={∅}▷=∗^(S $ trace_length extr) |={∅,E}=>
         ∃ δ2 ℓ,
           state_interp
             (trace_extend extr (inl (ζ,α)) (tp1 ++ ectx_fill K e2 :: tp2 ++ efs, σ2))
             (trace_extend atr ℓ δ2) ∗
           wp E ζ e2 Φ ∗
           [∗ list] i ↦ ef ∈ efs,
              wp ⊤ (locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef) ef
                (fork_post (locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef))
  end%I.

#[local] Instance wp_pre_contractive `{!irisG Λ AS Σ} s : Contractive (wp_pre s).
Proof.
  rewrite /wp_pre=> n wp wp' Hwp E e1 ζ Φ /=.
  do 28 (f_contractive || f_equiv).
  induction trace_length as [|k IH]; simpl.
  - repeat (f_contractive || f_equiv); apply Hwp.
  - by rewrite -IH.
Qed.

Definition wp_def `{!irisG Λ AS Σ} : Wp Λ (iProp Σ) stuckness :=
  λ s : stuckness, fixpoint (wp_pre s).
Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Arguments wp' {Λ AS Σ _}.
#[global] Existing Instance wp'.
Lemma wp_eq `{!irisG Λ AS Σ} : wp = @wp_def Λ AS Σ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!irisG Λ AS Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types ζ : locale Λ.

(* Weakest pre *)
Lemma wp_unfold s E e ζ Φ :
  WP e @ s; ζ; E {{ Φ }} ⊣⊢ wp_pre s (wp (PROP:=iProp Σ) s) E ζ e Φ.
Proof. rewrite wp_eq. apply (fixpoint_unfold (wp_pre s)). Qed.

#[global] Instance wp_ne s E ζ e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E ζ e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /=.
  do 29 (f_contractive || f_equiv).
  induction trace_length as [|k IHk]; simpl; [|by rewrite IHk].
  do 7 (f_contractive || f_equiv).
  rewrite IH; [done|lia|]. intros v. eapply dist_lt; eauto.
Qed.
#[global] Instance wp_proper s E ζ e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E ζ e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.
#[global] Instance wp_contractive s E ζ e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E ζ e).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He /=.
  do 29 (f_contractive || f_equiv).
  induction trace_length as [|k IHk]; simpl; [|by rewrite IHk].
  by repeat f_equiv.
Qed.

Lemma wp_value' s E ζ Φ v : Φ v ⊢ WP of_val v @ s; ζ; E {{ Φ }}.
Proof.
  iIntros "HΦ". rewrite wp_unfold /wp_pre to_of_val. by iIntros "!>".
Qed.
Lemma wp_value_inv' s E ζ Φ v :
  WP of_val v @ s; ζ; E {{ Φ }} -∗ |~{E}~| Φ v.
Proof. rewrite wp_unfold /wp_pre to_of_val pre_step_unseal. by eauto. Qed.

Lemma wp_strong_mono s1 s2 E1 E2 ζ e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WP e @ s1; ζ; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s2; ζ; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ". iLöb as "IH" forall (e ζ E1 E2 HE Φ Ψ).
  rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:?.
  { iMod (pre_step_mask_subseteq E1) as "Hclose"; [done|].
    iMod "H". iMod "Hclose". iMod ("HΦ" with "H") as "HΨ". by iModIntro. }
  iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hloc Hexe) "Hsi".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[//] [//] [//] [$]") as "[% H]".
  iModIntro. iSplit; [by iPureIntro; destruct s1, s2|].
  iIntros (α e2 σ2 efs Hstep). simpl.
  iMod ("H" with "[//]") as "H". iIntros "!> !>".
  iMod "H" as "H". iIntros "!>".
  iApply (step_fupdN_wand with "[H]"); first by iApply "H".
  iIntros "H". iMod "H" as (δ2 ℓ) "(Hσ & H & Hefs)".
  iMod "Hclose" as "_". iModIntro.
  iExists δ2, ℓ.
  iFrame "Hσ". iSplitR "Hefs".
  - iApply ("IH" with "[//] H HΦ").
  - iApply (big_sepL_impl with "Hefs"); iIntros "!>" (k ef _).
    iIntros "H". iApply ("IH" with "[] H"); auto.
Qed.

Lemma fupd_wp s E ζ e Φ : (|={E}=> WP e @ s; ζ; E {{ Φ }}) ⊢ WP e @ s; ζ; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iMod "H". iApply "H"; done.
Qed.
Lemma wp_fupd s E ζ e Φ : WP e @ s; ζ; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; ζ; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono s s E with "H"); auto. Qed.

Class AllowsStuttering := {
  stuttering_label: mlabel AS;
  allows_stuttering :
    ∀ (extr : execution_trace Λ) (atr : auxiliary_trace AS) c δ oζ,
      valid_exec extr →
      trace_ends_in extr c →
      trace_ends_in atr δ →
      locale_step c oζ c →
      state_interp extr atr ==∗
      state_interp (trace_extend extr oζ c) (trace_extend atr stuttering_label δ);
  }.

Class AllowsPureStep := {
  pure_label: mlabel AS;
  allows_pure_step :
    ∀ (extr : execution_trace Λ) (atr : auxiliary_trace AS)  tp tp' σ δ oζ,
      valid_exec extr →
      trace_ends_in extr (tp, σ) →
      trace_ends_in atr δ →
      locale_step (tp, σ) oζ (tp', σ) →
      state_interp extr atr ==∗
      state_interp (trace_extend extr oζ (tp', σ)) (trace_extend atr pure_label δ);
  }.

#[global] Instance AllowsPureStep_AllowsStuttering :
  AllowsPureStep → AllowsStuttering.
Proof.
  intros Haps. refine ({| stuttering_label := pure_label |}).
  iIntros (extr atr [tp σ] δ oζ ? ? ? ?) "Hsi".
  iApply allows_pure_step; done.
Qed.

Lemma wp_stuttering_atomic s E1 E2 ζ e Φ
      `{!AllowsStuttering}
      `{!StutteringAtomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; ζ; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; ζ; E1 {{ Φ }}.
Proof.
  iIntros "H".
  iLöb as "IH".
  rewrite {2}(wp_unfold s E1 e) /wp_pre.
  rewrite !(wp_unfold s E2 e) /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { iMod "H". iMod "H". iMod "H". by iIntros "!>". }
  iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hlocale Hexe) "Hsi".
  iAssert ((|={E1}=> ⌜match s with
                      | NotStuck => reducible e σ1
                      | MaybeStuck => True
                      end⌝ ∗
            state_interp extr atr ∗ _)%I) with "[H Hsi]" as
      ">(Hnstuck & Hsi & H)".
  { iApply fupd_plain_keep_l.
    iSplitR; last (iFrame "Hsi"; iExact "H").
    iIntros "[Hsi H]".
    iApply fupd_plain_mask.
    iMod "H".
    iMod ("H" with "[//] [//] [//] Hsi") as "[? _]".
    iModIntro; done. }
  iPoseProof (fupd_mask_intro_subseteq E1 ∅ True%I with "[]") as "Hmsk";
    [set_solver|done|].
  iMod "Hmsk".
  iModIntro.
  iSplitL "Hnstuck"; first done.
  iIntros (α e2 σ2 efs Hstep).
  destruct (stutteringatomic _ _ _ _ _ Hstep) as [(?&?&?)|Hs]; simplify_eq/=.
  - iModIntro; iNext.
    iMod (allows_stuttering with "Hsi") as "Hsi"; [done|done|done| |].
    { econstructor 1; [done| |by apply fill_step]; by rewrite app_nil_r. }
    iIntros "!>". iApply step_fupdN_intro; [done|]. iIntros "!>".
    iMod "Hmsk" as "_"; iModIntro.
    rewrite app_nil_r.
    iExists (trace_last atr), stuttering_label; iFrame "Hsi".
    iSplitL; last done.
    iApply "IH"; done.
  - iClear "IH".
    iMod "Hmsk" as "_".
    iMod "H". iMod ("H" with "[//] [//] [//] Hsi") as "[_ H]".
    iMod ("H" with "[//]") as "H". iIntros "!>!>".
    iMod "H" as "H". iIntros "!>".
    iApply (step_fupdN_wand with "[H]"); first by iApply "H".
    iIntros "H".
    iMod "H" as (δ2 ℓ) "(Hσ & H & Hefs)". destruct s.
    + rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
      * iMod (pre_step_elim with "Hσ H") as "[Hσ >H]".
        iModIntro; iExists _, _. iFrame.
        rewrite !wp_unfold /wp_pre He2.
        iIntros "!>". done.
      * iMod ("H" with "[] [] [] [$]") as "[H _]".
        { iPureIntro. eapply extend_valid_exec; [done|done|].
          econstructor; [done|done|].
          apply fill_step; done. }
        { by erewrite <-locale_fill_step. }
        { done. }
        iDestruct "H" as %(? & ? & ? & ? & ?%Hs); done.
    + destruct Hs as [v <-%of_to_val].
      rewrite !wp_unfold /wp_pre to_of_val.
      iMod (pre_step_elim with "Hσ H") as "[Hσ >H]".
      iExists _, _.
      rewrite !wp_unfold /wp_pre to_of_val. iFrame.
      by iIntros "!>!>".
Qed.

Lemma wp_stutteringatomic_take_step
      s E1 E2 ζ e Φ
      `{!AllowsStuttering}
      `{!StutteringAtomic (stuckness_to_atomicity s) e} :
  TCEq (to_val e) None →
  (|={E1,E2}=>
   ∀ extr atr c1 δ1 ζ',
     ⌜trace_ends_in extr c1⌝ -∗
     ⌜trace_ends_in atr δ1⌝ -∗
     ⌜ζ = ζ'⌝ -∗
     state_interp extr atr ={E2}=∗
     ∃ Q R,
       state_interp extr atr ∗
       (∀ α c2 δ2 ℓ,
           ∃ δ',
           state_interp
             (trace_extend extr (inl (ζ', α)) c2)
             (trace_extend atr ℓ δ2) ∗ Q ={E2}=∗
           state_interp
             (trace_extend extr (inl (ζ',α)) c2)
             (trace_extend atr stuttering_label δ') ∗ R) ∗
       (state_interp extr atr ={E2}=∗ state_interp extr atr ∗ Q) ∗
   WP e @ s; ζ; E2 {{ v, R ={E2,E1}=∗ Φ v }}) ⊢ WP e @ s; ζ; E1 {{ Φ }}.
Proof.
  iIntros (He) "H".
  iLöb as "IH".
  rewrite {2}wp_unfold /wp_pre He.
  iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hlocale Hexe) "Hsi".
  iAssert ((|={E1}=> ⌜match s with
                      | NotStuck => reducible e σ1
                      | MaybeStuck => True
                      end⌝ ∗
            state_interp extr atr ∗ _)%I) with "[H Hsi]" as
      ">(Hnstuck & Hsi & H)".
  { iApply fupd_plain_keep_l.
    iSplitR; last (iFrame "Hsi"; iExact "H").
    iIntros "[Hsi H]".
    iApply fupd_plain_mask.
    iMod "H".
    iMod ("H" with "[//] [//] [//] Hsi") as (Q R) "[Hsi (_&_&H)]".
    rewrite !wp_unfold /wp_pre He.
    iMod ("H" with "[] [] [] Hsi") as "[? _]"; done. }
  iMod (fupd_mask_intro_subseteq E1 ∅ True%I with "[]") as "Hmsk";
    [set_solver|done|].
  iModIntro.
  iSplit; first done.
  iIntros (α e2 σ2 efs Hstep).
  pose proof Hstep as  [(?&?&?)|HSA]%stutteringatomic; simplify_eq/=.
  - iModIntro; iNext.
    iMod (allows_stuttering with "Hsi") as "Hsi"; [done|done|done| |].
    { econstructor 1; [done| |by apply fill_step]; by rewrite app_nil_r. }
    iIntros "!>". iApply step_fupdN_intro; [done|]. iIntros "!>".
    iMod "Hmsk" as "_"; iModIntro.
    rewrite app_nil_r.
    iExists (trace_last atr), stuttering_label; iFrame "Hsi".
    iSplitL; last done.
    iApply "IH"; done.
  - iMod "Hmsk" as "_".
    iMod ("H" with "[//] [//] [//] Hsi") as ">H".
    iDestruct "H" as (Q R) "(Hsi & Hupdate & Htrans & H)".
    rewrite (wp_unfold s E2 e) /wp_pre He.
    iMod ("Htrans" with "Hsi") as "(Hsi & HQ)".
    iMod ("H" with "[//] [//] [//] Hsi") as "[_ H]".
    iMod ("H" with "[//]") as "H". iIntros "!>!>".
    iMod "H" as "H". iIntros "!>".
    iApply (step_fupdN_wand with "[H]"); first by iApply "H".
    iIntros "H".
    iMod "H" as (δ3 ℓ) "(Hsi & H & Hefs)".
    iDestruct ("Hupdate" $! α (tp1 ++ ectx_fill K e2 :: tp2 ++ efs, σ2) δ3 ℓ)
      as (δ') "Hupdate".
    iMod ("Hupdate" with "[$HQ $Hsi]") as "(Hsi & HR)".
    destruct s.
    + rewrite (wp_unfold _ E2 e2); rewrite /wp_pre.
      destruct (to_val e2) as [v2|] eqn:He2.
      * iMod (pre_step_elim with "Hsi H") as "[Hsi H]".
        iDestruct ("H" with "HR") as ">H".
        iModIntro; iExists _, _; iFrame.
        rewrite -(of_to_val _ _ He2) -wp_value'; done.
      * iMod ("H" with "[] [] [] Hsi") as "[% _]"; try done.
        { iPureIntro. eapply extend_valid_exec; [done|done|].
          econstructor; [done|done|].
          apply fill_step; done. }
        { by erewrite locale_fill_step. }
        exfalso; simpl in *; eapply not_reducible; eauto.
    + simpl in *.
      destruct HSA as [v <-%of_to_val].
      iDestruct (wp_value_inv' with "H") as "H".
      iMod (pre_step_elim with "Hsi H") as "[Hsi H]".
      iDestruct ("H" with "HR") as ">H".
      iModIntro. iExists _, _.
      iFrame "Hsi Hefs". by iApply wp_value'.
Qed.

Lemma wp_atomic s E1 E2 ζ e Φ
      `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; ζ; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; ζ; E1 {{ Φ }}.
Proof.
  iIntros "H".
  rewrite (wp_unfold s E1 e) /wp_pre.
  rewrite !(wp_unfold s E2 e) /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { iDestruct "H" as ">>>H". by iIntros "!>". }
  iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hlocale exe) "Hsi".
  iMod "H".
  iMod ("H" with "[//] [//] [//] Hsi") as "[% H]".
  iModIntro.
  iSplit; first by iPureIntro.
  iIntros (α e2 σ2 efs Hstep).
  pose proof (atomic _ _ _ _ _ Hstep) as Hs; simplify_eq/=.
  iMod ("H" with "[//]") as "H". iIntros "!>!>".
  iMod "H" as "H". iIntros "!>".
  iApply (step_fupdN_wand with "[H]"); first by iApply "H".
  iIntros "H".
  iMod "H" as (δ2 ℓ) "(Hσ & H & Hefs)". destruct s.
  - rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iMod (pre_step_elim with "Hσ H") as "[Hσ >H]".
      iModIntro; iExists _, _.
      iFrame.
      rewrite !wp_unfold /wp_pre He2; by iIntros "!>".
    + iMod ("H" with "[] [] [] [$]") as "[H _]"; try done.
      { iPureIntro. eapply extend_valid_exec; [done|done|].
        econstructor; [done|done|].
        apply fill_step; done. }
      { by erewrite <-locale_fill_step. }
      iDestruct "H" as %(? & ? & ? & ? & ?%Hs); done.
  - destruct Hs as [v <-%of_to_val].
    rewrite !wp_unfold /wp_pre to_of_val.
    iMod (pre_step_elim with "Hσ H") as "[Hσ >H]"; iModIntro.
    iExists _, _.
    rewrite !wp_unfold /wp_pre to_of_val. iFrame. by iIntros "!>".
Qed.

Lemma wp_atomic_take_step
      s E1 E2 ζ e Φ
      `{!Atomic (stuckness_to_atomicity s) e} :
  TCEq (to_val e) None →
  (|={E1,E2}=>
   ∀ extr atr c1 δ1 ζ',
     ⌜trace_ends_in extr c1⌝ -∗
     ⌜trace_ends_in atr δ1⌝ -∗
     ⌜ζ = ζ'⌝ -∗
     state_interp extr atr ={E2}=∗
     ∃ Q R,
       state_interp extr atr ∗
       (∀ α c2 δ2 ℓ,
           ∃ δ' ℓ',
           state_interp
             (trace_extend extr (inl (ζ',α)) c2)
             (trace_extend atr ℓ δ2) ∗ Q ={E2}=∗
           state_interp
             (trace_extend extr (inl (ζ',α)) c2)
             (trace_extend atr ℓ' δ') ∗ R) ∗
       (state_interp extr atr ={E2}=∗ state_interp extr atr ∗ Q) ∗
   WP e @ s; ζ; E2 {{ v, R ={E2,E1}=∗ Φ v }}) ⊢ WP e @ s; ζ; E1 {{ Φ }}.
Proof.
  iIntros (He) "H".
  rewrite wp_unfold /wp_pre He.
  iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hlocale Hexe) "Hsi".
  iMod ("H" with "[//] [//] [//] Hsi") as ">H".
  iDestruct "H" as (Q R) "(Hsi & Hupdate & Htrans & H)".
  rewrite (wp_unfold s E2 e) /wp_pre He.
  iMod ("Htrans" with "Hsi") as "(Hsi & HQ)".
  iMod ("H" with "[//] [//] [//] Hsi") as "[% H]".
  iModIntro.
  iSplit; first by iPureIntro.
  iIntros (α e2 σ2 efs Hstep).
  pose proof (atomic _ _ _ _ _ Hstep) as Hs; simplify_eq/=.
  iMod ("H" with "[//]") as "H". iIntros "!>!>".
  iMod "H" as "H". iIntros "!>".
  iApply (step_fupdN_wand with "[H]"); first by iApply "H".
  iIntros "H".
  iMod "H" as (δ3 ℓ) "(Hsi & H & Hefs)".
  iDestruct ("Hupdate" $! α (tp1 ++ ectx_fill K e2 :: tp2 ++ efs, σ2) δ3 ℓ)
      as (δ' ℓ') "Hupdate".
  iMod ("Hupdate" with "[$HQ $Hsi]") as "(Hsi & HR)".
  destruct s.
  - rewrite (wp_unfold _ E2 e2); rewrite /wp_pre.
    destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct (pre_step_elim with "Hsi H") as ">[Hσ H]".
      iDestruct ("H" with "HR") as "> H".
      iModIntro; iExists _,_; iFrame.
      rewrite -(of_to_val _ _ He2) -wp_value'; done.
    + iMod ("H" with "[] [] [] Hsi") as "[% _]"; try done.
      { iPureIntro. eapply extend_valid_exec; [done|done|].
        econstructor; [done|done|].
        apply fill_step; done. }
      { by erewrite <-locale_fill_step. }
      exfalso; simpl in *; eapply not_reducible; eauto.
  - simpl in *.
    destruct Hs as [v <-%of_to_val].
    iDestruct (wp_value_inv' with "H") as "H".
    iMod (pre_step_elim with "Hsi H") as "[Hsi H]".
    iDestruct ("H" with "HR") as ">H".
    iModIntro. iExists _, _.
    iFrame "Hsi Hefs". by iApply wp_value'.
Qed.

(** In this stronger version of [wp_step_fupdN], the masks in the
   step-taking fancy update are a bit weird and somewhat difficult to
   use in practice. Hence, we prove it for the sake of completeness,
   but [wp_step_fupdN] is just a little bit weaker, suffices in
   practice and is easier to use.

   See the statement of [wp_step_fupdN] below to understand the use of
   ordinary conjunction here. *)
Lemma wp_step_fupdN_strong n s ζ E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ extr atr, state_interp extr atr
       ={E1,∅}=∗ ⌜n ≤ S (trace_length extr)⌝) ∧
  ((|={E1,E2}=> |={∅}▷=>^n |={E2,E1}=> P) ∗
    WP e @ s; ζ; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  WP e @ s; ζ; E1 {{ Φ }}.
Proof.
  destruct n as [|n].
  { iIntros (_ ?) "/= [_ [HP Hwp]]".
    iApply (wp_strong_mono with "Hwp"); [done..|].
    iIntros (v) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP". }
  rewrite !wp_unfold /wp_pre /=. iIntros (-> ?) "H".
  iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hlocale Hexe) "Hσ".
  destruct (decide (n ≤ trace_length extr)) as [Hn|Hn]; first last.
  { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ") as %?. lia. }
  iDestruct "H" as "[_ [>HP Hwp]]".
  iMod ("Hwp" with "[//] [//] [//] [$]") as "[$ H]". iMod "HP".
  iIntros "!>" (α e2 σ2 efs Hstep). iMod ("H" $! α e2 σ2 efs with "[% //]") as "H".
  iIntros "!>!>". iMod "H". iMod "HP". iModIntro.
  revert n Hn. generalize (trace_length extr)=>n0 n Hn.
  iInduction n as [|n] "IH" forall (n0 Hn).
  - iApply (step_fupdN_wand with "H").
    iIntros "H". iMod "H" as "H". iDestruct "H" as (δ2 ℓ) "(Hσ & Hwp & Hwp')".
    iMod "HP". iModIntro. iExists _, _. iFrame "Hσ Hwp'".
    iApply (wp_strong_mono with "Hwp"); [done|set_solver|].
    iIntros (v) "HΦ". iApply ("HΦ" with "HP").
  - destruct n0 as [|n0]; [lia|]=>/=. iMod "HP". iMod "H". iIntros "!> !>".
    iMod "HP". iMod "H". iModIntro. iApply ("IH" with "[] HP H").
    auto with lia.
Qed.

Lemma wp_step_fupdN n s ζ E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ extr atr, state_interp extr atr
       ={E1,∅}=∗ ⌜n ≤ S (trace_length extr)⌝) ∧
  ((|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> P) ∗
    WP e @ s; ζ; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  WP e @ s; ζ; E1 {{ Φ }}.
Proof.
  iIntros (??) "H". iApply (wp_step_fupdN_strong with "[H]"); [done|].
  iApply (bi.and_mono_r with "H"). apply bi.sep_mono_l. iIntros "HP".
  iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|].
  iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first.
  { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. }
  iModIntro. iApply (step_fupdN_wand with "HP"). iIntros "H".
  iApply fupd_mask_frame; [|iMod "H"; iModIntro]; [set_solver|].
  by rewrite difference_empty_L (comm_L (∪)) -union_difference_L.
Qed.
Lemma wp_step_fupd s E1 E2 ζ e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; ζ; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; ζ; E1 {{ Φ }}.
Proof.
  iIntros (??) "HR H".
  iApply (wp_step_fupdN_strong 1 _ _ E1 E2 with "[-]"); [done|..]. iSplit.
  - iIntros (??) "_". iMod (fupd_mask_subseteq ∅) as "_"; [set_solver+|].
    auto with lia.
  - iFrame "H". iMod "HR" as "$". auto.
Qed.

Lemma pre_step_wp_pre_step s E ζ e Φ :
  (|~{E}~| WP e @ s; ζ; E {{ v, |~{E}~| Φ v }}) ⊢
  WP e @ s; ζ; E {{ Φ }}.
Proof.
  iLöb as "IH" forall (s E ζ e Φ).
  iIntros "H".
  iEval (rewrite wp_unfold /wp_pre).
  destruct (to_val e) eqn:Heqn.
  { iEval (rewrite wp_unfold /wp_pre) in "H". rewrite Heqn.
    iDestruct "H" as ">>>H". by iIntros "!>". }
  iIntros (?????????) "Hσ".
  iMod (pre_step_elim with "Hσ H") as "[Hσ H]".
  iEval (rewrite wp_unfold /wp_pre) in "H".
  rewrite Heqn.
  iMod ("H" with "[//] [//] [//] Hσ") as (Hstuck) "H". iModIntro.
  iSplit; [done|].
  iIntros (?????).
  iDestruct ("H" with "[//]") as "H"=> /=.
  iMod "H". iIntros "!>!>". iMod "H". iIntros "!>".
  iApply (step_fupdN_wand with "H").
  iIntros "H". iMod "H". iIntros "!>".
  iDestruct "H" as (δ2 ℓ) "(Hσ&Hwp&Hwps)".
  iExists _, _.
  iDestruct (pre_step_intro with "Hwp") as "Hwp".
  iDestruct ("IH" with "Hwp") as "Hwp".
  iFrame.
Qed.

Lemma pre_step_wp s E ζ e Φ :
  (|~{E}~| WP e @ s; ζ; E {{ v, Φ v }}) ⊢
  WP e @ s; ζ; E {{ Φ }}.
Proof.
  iIntros "H".
  iApply pre_step_wp_pre_step. iIntros "!>".
  iApply (wp_strong_mono with "H"); [done|done|].
  by iIntros (v) "H!>!>".
Qed.

Lemma wp_pre_step s E ζ e Φ :
  (WP e @ s; ζ; E {{ v, |~{E}~| Φ v }}) ⊢
  WP e @ s; ζ; E {{ Φ }}.
Proof.
  iIntros "H".
  iApply pre_step_wp_pre_step. iIntros "!>".
  iApply (wp_strong_mono with "H"); [done|done|].
  by iIntros (v) "H!>!>".
Qed.

Lemma wp_bind K s E ζ e Φ :
  WP e @ s; ζ; E {{ v, WP ectx_fill K (of_val v) @ s; ζ; E {{ Φ }} }} ⊢
  WP ectx_fill K e @ s; ζ; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e ζ Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply pre_step_wp. }
  rewrite wp_unfold /wp_pre fill_not_val; last done.
  iIntros (extr atr K' tp1 tp2 σ1 Hexvalid Hlocale Hexe) "Hsi".
  iMod ("H" $! _ _ (ectx_comp K' K) with "[//] [] [] [$]") as "[% H]".
  { rewrite ectx_comp_comp; done. }
  { rewrite ectx_comp_comp; done. }
  iModIntro; iSplit.
  { iPureIntro. destruct s; first apply reducible_fill; done. }
  iIntros (α e2 σ2 efs Hstep).
  destruct (fill_step_inv K e σ1 α e2 σ2 efs) as (e2'&->&?);
    [done|done|].
  iMod ("H" with "[//]") as "H". iIntros "!>!>".
  iMod "H" as "H". iIntros "!>".
  iApply (step_fupdN_wand with "[H]"); first by iApply "H".
  iIntros "H".
  iMod "H" as (δ2 ℓ) "(Hσ & H & Hefs)".
  rewrite !ectx_comp_comp.
  iModIntro; iExists δ2, ℓ.
  iFrame "Hefs Hσ". by iApply "IH".
Qed.

(** * Derived rules *)
Lemma wp_mono s E ζ e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; ζ; E {{ Φ }} ⊢ WP e @ s; ζ; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_stuck_mono s1 s2 E ζ e Φ :
  s1 ⊑ s2 → WP e @ s1; ζ; E {{ Φ }} ⊢ WP e @ s2; ζ; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_stuck_weaken s E ζ e Φ :
  WP e @ s; ζ; E {{ Φ }} ⊢ WP e @ ζ; E ?{{ Φ }}.
Proof. apply wp_stuck_mono. by destruct s. Qed.
Lemma wp_mask_mono s E1 E2 ζ e Φ : E1 ⊆ E2 → WP e @ s; ζ; E1 {{ Φ }} ⊢ WP e @ s; ζ; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
#[global] Instance wp_mono' s E ζ e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E ζ e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
#[global] Instance wp_flip_mono' s E ζ e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E ζ e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value s E Φ  ζ e v : IntoVal e v → Φ v ⊢ WP e @ s; ζ; E {{ Φ }}.
Proof. intros <-. by apply wp_value'. Qed.
Lemma wp_value_fupd' s E ζ Φ v : (|={E}=> Φ v) ⊢ WP of_val v @ s; ζ; E {{ Φ }}.
Proof. intros. by rewrite -wp_fupd -wp_value'. Qed.
Lemma wp_value_fupd s E Φ ζ e v `{!IntoVal e v} :
  (|={E}=> Φ v) ⊢ WP e @ s; ζ;  E {{ Φ }}.
Proof. intros. rewrite -wp_fupd -wp_value //. Qed.
Lemma wp_value_inv s E Φ ζ e v :
  IntoVal e v → WP e @ s; ζ; E {{ Φ }} -∗ |~{E}~| Φ v.
Proof. intros <-. by apply wp_value_inv'. Qed.

Lemma wp_frame_l s E ζ e Φ R : R ∗ WP e @ s; ζ; E {{ Φ }} ⊢ WP e @ s; ζ; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r s E ζ e Φ R : WP e @ s; ζ; E {{ Φ }} ∗ R ⊢ WP e @ s; ζ; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

Lemma wp_frame_step_l s E1 E2 ζ e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ s; ζ; E2 {{ Φ }} ⊢ WP e @ s; ζ; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r s E1 E2 ζ e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ s; ζ; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; ζ; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' s E ζ e Φ R :
  TCEq (to_val e) None → ▷ R ∗ WP e @ s; ζ; E {{ Φ }} ⊢ WP e @ s; ζ; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' s E ζ e Φ R :
  TCEq (to_val e) None → WP e @ s; ζ; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; ζ; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma wp_wand s E ζ e Φ Ψ :
  WP e @ s; ζ; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; ζ; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s E ζ e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; ζ; E {{ Φ }} ⊢ WP e @ s; ζ; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E ζ e Φ Ψ :
  WP e @ s; ζ; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; ζ; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand_l s E ζ e Q Φ :
  Q ∗ WP e @ s; ζ; E {{ v, Q -∗ Φ v }} -∗ WP e @ s; ζ; E {{ Φ }}.
Proof.
  iIntros "[HQ HWP]". iApply (wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End wp.

#[global] Arguments AllowsStuttering {_} _ _ {_}.
#[global] Arguments AllowsPureStep {_} _ _ {_}.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisG Λ AS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  #[global] Instance frame_wp p s E ζ e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; ζ; E {{ Φ }}) (WP e @ s; ζ; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  #[global] Instance is_except_0_wp s E ζ e Φ : IsExcept0 (WP e @ s; ζ; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  #[global] Instance elim_modal_bupd_wp p s E ζ e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; ζ; E {{ Φ }}) (WP e @ s; ζ; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  #[global] Instance elim_modal_fupd_wp p s E ζ e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; ζ; E {{ Φ }}) (WP e @ s; ζ; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  #[global] Instance elim_modal_fupd_wp_stutteringatomic p s E1 E2 ζ e P Φ :
    AllowsStuttering AS Σ →
    StutteringAtomic (stuckness_to_atomicity s) e →
    ElimModal True p false (|={E1,E2}=> P) P
            (WP e @ s; ζ; E1 {{ Φ }}) (WP e @ s; ζ; E2 {{ v, |={E2,E1}=> Φ v }})%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r wp_stuttering_atomic.
  Qed.

  #[global] Instance add_modal_fupd_wp s E ζ e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; ζ; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_wp. Qed.

  #[global] Instance elim_acc_wp_stuttering {X} E1 E2 ζ α β γ e s Φ :
    AllowsStuttering AS Σ →
    StutteringAtomic (stuckness_to_atomicity s) e →
    ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; ζ; E1 {{ Φ }})
            (λ x, WP e @ s; ζ; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    intros ? ? _.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  #[global] Instance elim_modal_fupd_wp_atomic p s E1 E2 ζ e P Φ :
    Atomic (stuckness_to_atomicity s) e →
    ElimModal True p false (|={E1,E2}=> P) P
            (WP e @ s; ζ; E1 {{ Φ }}) (WP e @ s; ζ; E2 {{ v, |={E2,E1}=> Φ v }})%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r wp_atomic.
  Qed.

  #[global] Instance elim_acc_wp_atomic {X} E1 E2 ζ α β γ e s Φ :
    Atomic (stuckness_to_atomicity s) e →
    ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; ζ; E1 {{ Φ }})
            (λ x, WP e @ s; ζ; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    intros ? _.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  #[global] Instance elim_acc_wp_nonatomic {X} E ζ α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; ζ; E {{ Φ }})
            (λ x, WP e @ s; ζ; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    rewrite /ElimAcc.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  #[global] Instance elim_modal_pre_step_wp p s E ζ e P Φ :
    ElimModal True p false (|~{E}~| P) P
              (WP e @ s; ζ; E {{ Φ }}) (WP e @ s; ζ; E {{ v, Φ v }})%I.
  Proof.
    destruct p.
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]". iDestruct "HP" as "#HP".
      iApply pre_step_wp. iMod "HP". iModIntro. by iApply "HPQ".
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]".
      iApply pre_step_wp. iMod "HP". iModIntro. by iApply "HPQ".
  Qed.

End proofmode_classes.

Notation state_interp_oos ζ α := (state_interp_opt (Some (ζ,α))).

Definition sswp `{!irisG Λ M Σ} (s : stuckness)
           E ζ e1 (Φ : expr Λ → option (action Λ) → iProp Σ) : iProp Σ :=
  ⌜TCEq (to_val e1) None⌝ ∧
  ∀ (extr : execution_trace Λ) (atr : auxiliary_trace M) K tp1 tp2 σ1,
  ⌜valid_exec extr⌝ -∗
  ⌜locale_of tp1 (ectx_fill K e1) = ζ⌝ -∗
  ⌜trace_ends_in extr (tp1 ++ ectx_fill K e1 :: tp2, σ1)⌝ -∗
  state_interp extr atr ={E,∅}=∗
  ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
  ∀ α e2 σ2 efs,
  ⌜prim_step e1 σ1 α e2 σ2 efs⌝ ={∅}▷=∗^(S $ trace_length extr) |={∅,E}=>
  state_interp_oos ζ α
    (trace_extend extr (inl (ζ,α)) (tp1 ++ ectx_fill K e2 :: tp2, σ2))
    atr ∗ Φ e2 α ∗ ⌜efs = []⌝.

Definition MU `{!irisG Λ M Σ} E ζ α (P : iProp Σ) : iProp Σ :=
  ∀ (extr : execution_trace Λ) (atr : auxiliary_trace M),
  state_interp_oos  ζ α extr atr ={E}=∗
  ∃ δ2 ℓ, state_interp extr (trace_extend atr ℓ δ2) ∗ P.

Lemma sswp_MU_wp_fupd `{!irisG Λ M Σ} s E E' ζ e Φ :
  (|={E,E'}=> sswp s E' ζ e (λ e' α, MU E' ζ α ((|={E',E}=> WP e' @ s; ζ; E {{ Φ }}))))%I -∗
  WP e @ s; ζ; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre.
  iIntros "Hsswp".
  destruct (to_val e) eqn:Heqn.
  { iMod "Hsswp" as (Hval) "_". inversion Hval. by simplify_eq. }
  iIntros (extr atr K tp1 tp2 σ1 Hvalid Hζ Hextr) "Hσ".
  iMod "Hsswp" as "[_ Hsswp]".
  iMod ("Hsswp" with "[//] [//] [//] Hσ") as (Hs) "Hsswp".
  iModIntro. iSplit; [done|].
  iIntros (α e2 σ2 efs Hstep).
  iDestruct ("Hsswp" with "[//]") as "Hsswp".
  iApply (step_fupdN_wand with "Hsswp"). iIntros ">(Hσ & HMU & ->)".
  iMod ("HMU" with "Hσ") as (??) "[Hσ Hwp]". iMod "Hwp". iModIntro.
  iExists _, _. rewrite right_id_L. by iFrame.
Qed.

Lemma sswp_wand `{!irisG Λ M Σ} s E ζ e
      (Φ Ψ : expr Λ → option (action Λ) → iProp Σ) :
  (∀ e α, Φ e α -∗ Ψ e α) -∗ sswp s E ζ e Φ -∗ sswp s E ζ e Ψ.
Proof.
  rewrite /sswp. iIntros "HΦΨ [%Hval Hsswp]".
  iSplit; [done|].
  iIntros (extr atr K tp1 tp2 σ1 Hvalid Hζ Hextr) "Hσ".
  iMod ("Hsswp" with "[//] [//] [//] Hσ") as (Hs) "Hsswp".
  iModIntro. iSplit; [done|].
  iIntros (α e2 σ2 efs Hstep).
  iDestruct ("Hsswp" with "[//]") as "Hsswp".
  iApply (step_fupdN_wand with "Hsswp"). iIntros ">(Hσ & HMU & ->)".
  iFrame. iModIntro. iSplit; [|done]. by iApply "HΦΨ".
Qed.

Lemma MU_wand `{!irisG Λ M Σ} E ζ α (P Q : iProp Σ) :
  (P -∗ Q) -∗ MU E ζ α P -∗ MU E ζ α Q.
Proof.
  rewrite /MU. iIntros "HPQ HMU".
  iIntros (extr atr) "Hσ".
  iMod ("HMU" with "Hσ") as (??) "[Hσ HP]". iModIntro.
  iExists _, _. iFrame. by iApply "HPQ".
Qed.

Lemma sswp_MU_wp `{!irisG Λ m Σ} s E ζ e (Φ : val Λ → iProp Σ) :
  sswp s E ζ e (λ e' α, MU E ζ α (WP e' @ s; ζ;  E {{ Φ }})) -∗
  WP e @ s; ζ; E {{ Φ }}.
Proof.
  iIntros "Hsswp". iApply sswp_MU_wp_fupd. iModIntro.
  iApply (sswp_wand with "[] Hsswp").
  iIntros (??) "HMU". iApply (MU_wand with "[] HMU"). by iIntros "$ !>".
Qed.
