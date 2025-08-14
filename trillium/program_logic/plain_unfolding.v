From stdpp Require Export coPset.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fixpoint_mono.
From iris.base_logic.lib Require Export own fancy_updates.
From iris.base_logic.lib Require Import wsat.
From iris.base_logic Require Export later_credits physical_step derived.
From iris.prelude Require Import options.
Import le_upd_if.

Section plain_unfolding.

  Local Lemma lc_incr_supply `{!lcGS Σ} n m :
    later_credits.lc_supply n ⊢ |==> later_credits.lc_supply (n + m) ∗ £ m.
  Proof.
    iIntros "H". iMod lc_zero as "H'". iCombine "H H'" as "H".
    rewrite later_credits.lc_unseal /later_credits.lc_def later_credits.lc_supply_unseal /later_credits.lc_supply_def -!own_op.
    iApply (own_update with "[$]").
    eapply auth_update. eapply nat_local_update; lia.
  Qed.

  Definition lc_generator_aux `{lcGS Σ} (rec : unit → iProp Σ) (_ : unit) : iProp Σ :=
    ∀ (P : iProp Σ) n, (£ n -∗ rec () -∗ P) ==∗ P.
  
  Definition lc_generator `{lcGS Σ} :=
    bi_greatest_fixpoint lc_generator_aux.

  Instance lc_generator_aux_bi_mono `{lcGS Σ} :
    BiMonoPred (lc_generator_aux).
  Proof.
    split.
    - iIntros (Φ Ψ HΦne HΨne) "#H". iIntros (E1) "HE". iIntros (P E2) "HP".
      iApply "HE". iIntros "? ?"; iApply ("HP" with "[$]"); by iApply "H".
    - iIntros (Φ HΦne). by intros ??? ->%leibniz_equiv.
  Qed.
  Lemma lc_generator_unfold `{lcGS Σ} :
    lc_generator () ≡ lc_generator_aux lc_generator ().
  Proof. by rewrite /lc_generator greatest_fixpoint_unfold. Qed.

  Lemma lc_generator_soundness_no_lc `{!lcGpreS Σ} (Q : iProp Σ) :
    (∀ `{!lcGS Σ}, lc_generator () -∗ Q) → ⊢ |==> Q.
  Proof.
    iIntros (Hfupd).
    iMod (later_credits.le_upd.lc_alloc 0) as (Hc) "[H _]".
    iApply Hfupd. iModIntro.
    assert (NonExpansive (λ (u : unit), ∃ n, later_credits.lc_supply n)%I).
    { by intros ??? ->%leibniz_equiv. }
    iApply (greatest_fixpoint_coiter _ (λ (u : unit), ∃ n, later_credits.lc_supply n)%I with "[] [$H]").
    iIntros "!> % (%n&Hsup) %P %m HP". iMod (lc_incr_supply with "[$]") as "[H£ Hrest]".
    iApply ("HP" with "[$] [$]").
  Qed.

  Definition fupd_to_bupd_aux `{invGS_gen hlc Σ}
           (rec : coPset → iProp Σ) (E1 : coPset) : iProp Σ :=
    ∀ (P : iProp Σ) E2, ((|={E1,E2}=> rec E2 -∗ P) ==∗ ◇ P).

  Definition fupd_to_bupd `{invGS_gen hlc Σ} :=
    bi_greatest_fixpoint fupd_to_bupd_aux.

  Instance fupd_to_bupd_aux_bi_mono `{invGS_gen hlc Σ} :
    BiMonoPred (fupd_to_bupd_aux).
  Proof.
    split.
    - iIntros (Φ Ψ HΦne HΨne) "#H". iIntros (E1) "HE". iIntros (P E2) "HP".
      iApply "HE"; iMod "HP"; iModIntro. by iIntros; iApply "HP"; iApply "H".
    - iIntros (Φ HΦne). by intros ??? ->%leibniz_equiv.
  Qed.

  Lemma fupd_to_bupd_unfold `{invGS_gen hlc Σ} E :
    fupd_to_bupd E ≡ fupd_to_bupd_aux fupd_to_bupd E.
  Proof. by rewrite /fupd_to_bupd greatest_fixpoint_unfold. Qed.

  Lemma fupd_to_bupd_except0 `{invGS_gen hlc Σ} E E' P `{!IsExcept0 P} :
    fupd_to_bupd E -∗ (|={E, E'}=> fupd_to_bupd E' -∗ P) ==∗ P.
  Proof.
    iIntros "HE HP". rewrite fupd_to_bupd_unfold.
    iApply (is_except_0 P). iApply ("HE" with "[$]").
  Qed.

  Lemma fupd_to_bupd_except0_plain `{invGS_gen hlc Σ} E E' P `{!IsExcept0 P} `{!Plain P} :
    fupd_to_bupd E -∗ (|={E, E'}=> fupd_to_bupd E' -∗ P) -∗ P.
  Proof.
    iIntros "HE HP". iApply bupd_elim. iApply (fupd_to_bupd_except0 with "[$] [$]").
  Qed.

  Lemma fupd_to_bupd_soundness_no_lc `{!invGpreS Σ} (Q : iProp Σ) :
    (∀ `{Hinv: !invGS_gen HasNoLc Σ}, lc_generator () -∗
      fupd_to_bupd ⊤ -∗ Q) → ⊢ |==> Q.
  Proof.
    iIntros (Hfupd). iApply bupd_trans.
    iApply (@lc_generator_soundness_no_lc _ invGpreS_lc).
    iIntros (Hc) "Hgen".
    iMod ( @wsat_alloc _ (invGpreS0.(invGpreS_wsat))) as (Hw) "[Hw HE]".
    set (Hi := InvG HasNoLc _ Hw Hc).
    iApply ( @Hfupd Hi with "Hgen").
    assert (NonExpansive (λ E, wsat ∗ ownE E)%I).
    { by intros ??? ->%leibniz_equiv. }
    iApply (greatest_fixpoint_coiter _ (λ E, wsat ∗ ownE E)%I with "[] [$Hw $HE]").
    iIntros "!>" (E1) "?".
    iIntros (P E2) "HP".
    rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def /=.
    iMod ("HP" with "[$]") as ">(Hw & HE & HP)".
    do 2 iModIntro; iApply "HP"; iFrame.
  Qed.

  (* TODO: Make this opaque *)
  Definition step_count `{!tr_generation} (ns : nat) : nat :=
    S $ f $ physical_step.tr_per_step 0 ns.

  Definition physical_step_to_laters_aux `{!tr_generation} `{invGS_gen HasNoLc Σ} `{trGS Σ} (rec : nat → iProp Σ) (ns : nat) : iProp Σ :=
    ∀ (P : iProp Σ) (E : coPset), (fupd_to_bupd E -∗ (|={E}⧗=> fupd_to_bupd E -∗ rec (S ns) -∗ ◇■ P) -∗ ▷^(step_count ns) ◇■ P).
  
  Definition physical_step_to_laters `{!tr_generation} `{invGS_gen HasNoLc Σ} `{trGS Σ} :=
    bi_greatest_fixpoint physical_step_to_laters_aux.
  
  Instance physical_step_to_laters_aux_bi_mono `{!tr_generation} `{invGS_gen HasNoLc Σ} `{trGS Σ} :
    BiMonoPred (physical_step_to_laters_aux).
  Proof.
    split.
    - iIntros (Φ Ψ HΦne HΨne) "#H". iIntros (n) "Hn". iIntros (P E) "HE HP".
      iApply ("Hn" with "[$]"). iApply (physical_step_wand with "[$]"). iIntros "HP ? ?".
      iApply ("HP" with "[$]"). by iApply "H".
    - iIntros (Φ HΦne). by intros ??? ->%leibniz_equiv.
  Qed.

  Lemma physical_step_to_laters_unfold `{!tr_generation} `{invGS_gen HasNoLc Σ} `{trGS Σ} ns :
    physical_step_to_laters ns ≡ physical_step_to_laters_aux physical_step_to_laters ns.
  Proof. by rewrite /physical_step_to_laters greatest_fixpoint_unfold. Qed.

  Lemma physical_step_to_laters_except0_plain `{!tr_generation} `{invGS_gen HasNoLc Σ} `{trGS Σ} ns E P `{!IsExcept0 P} `{!Plain P} :
    physical_step_to_laters ns -∗ fupd_to_bupd E -∗ (|={E}⧗=> fupd_to_bupd E -∗ physical_step_to_laters (S ns) -∗ P) -∗ ▷^(step_count ns) P.
  Proof.
    iIntros "Hsteps Hfupd HP".
    iApply (bi.laterN_wand _ (◇■ P)%I).
    { iNext. iIntros. iApply is_except_0. iApply plainly_elim. by iApply except_0_plainly_1. }
    rewrite physical_step_to_laters_unfold. iApply ("Hsteps" with "[$]").
    iApply (physical_step_wand with "[$]"). iIntros "HP ? ?".
    iApply bi.except_0_intro. iApply plain. by iApply ("HP" with "[$] [$]").
  Qed.

  Lemma foo `{invGS_gen HasNoLc Σ} {E} E' n P :
    fupd_to_bupd E -∗ (|={E, E'}=> fupd_to_bupd E' -∗ |==> ▷^n ◇ P) -∗ |==> ▷^n ◇ P.
  Proof.
    iIntros "HE HP".
    destruct n as [|n]; simpl.
    - iApply bi.except_0_idemp. iApply bupd_trans. iApply except_0_bupd.
      iApply (fupd_to_bupd_unfold with "HE"). iMod "HP". iIntros "!> HE".
      by iApply "HP".
    - iApply bi.except_0_later. iApply bi.except_0_idemp. iApply bupd_trans. iApply except_0_bupd.
      iApply (fupd_to_bupd_unfold with "HE"). iMod "HP". iIntros "!> HE".
      iApply bi.except_0_intro.
      by iApply "HP".
  Qed.

  Lemma bar `{invGS_gen Σ} n Q `{!Plain Q} `{!IsExcept0 Q} :
    fupd_to_bupd ∅  -∗ (|={∅}▷=>^n fupd_to_bupd ∅ -∗ Q) -∗ (▷^n Q).
  Proof.
    iIntros "HFtB HP".
    iInduction n as [|n] "IHn".
    { simpl. 
      iApply is_except_0.
      iApply bupd_elim.
      rewrite {1}fupd_to_bupd_unfold.
      iApply "HFtB". iApply "HP". }
    simpl.
    iApply bi.except_0_later.
    iApply bupd_elim.
    rewrite {3}fupd_to_bupd_unfold.
    iApply "HFtB".
    iMod "HP".
    iIntros "!> HFtB !>".
    iApply is_except_0.
    { by destruct n; apply _. }
    iApply bupd_elim.
    rewrite {4}fupd_to_bupd_unfold.
    iApply "HFtB".
    iMod "HP".
    iIntros "!> HFtB".
    iApply ("IHn" with "HFtB HP").
  Qed.

  Lemma except_0_laterN `{invGS_gen HasNoLc Σ} n (P : iProp Σ) :
    n ≥ 1 →
    ◇ ▷^n P ⊢ ▷^n P.
  Proof.
    intros ?. destruct n; [lia|].
    simpl. apply bi.except_0_later.
  Qed.  

  
  Lemma physical_step_to_laters_soundness_no_lc  `{!tr_generation} `{!invGpreS Σ} `{trGpreS Σ} (Q : iProp Σ) :
    (∀ `{invGS_gen HasNoLc Σ} `{trGS Σ}, fupd_to_bupd ⊤ -∗ physical_step_to_laters 0 -∗ Q) →
    ⊢ |==> Q.
  Proof.
    iIntros (Hfupd). iApply bupd_trans. iApply fupd_to_bupd_soundness_no_lc.
    iIntros (Hinv) "Hlc Hfupd".
    iMod (tr_supply_alloc 0) as "(%Htr & Hsup & H⧗)"; simpl.
    iApply ( @Hfupd _ _ with "[$]").
    assert (NonExpansive (λ n, lc_generator () ∗ tr_supply (physical_step.tr_per_step 0 n))%I).
    { intros ????; repeat f_equiv; eauto. }
    iApply (greatest_fixpoint_coiter _
      (λ n, lc_generator () ∗ tr_supply (physical_step.tr_per_step 0 n))%I with "[] [Hlc Hsup]"); [|iFrame].
    iIntros "!>" (n) "[Hlc Htr]". rewrite /physical_step_to_laters_aux.
    iIntros (P E) "HE HP". rewrite physical_step.physical_step_unseal /physical_step_def.
    iApply bupd_elim. iApply (foo ∅ with "HE"). iMod "HP". iIntros "!> HE".
    iMod tr_zero as "H⧗". iMod (tr_persistent_zero) as "H⧖".
    iApply bupd_trans. iApply (lc_generator_unfold with "Hlc"). iIntros "H£ Hlc".
    iSpecialize ("HP" $! _ _ _ with "[$] [$] [$] [$]").
    (* rewrite Nat.sub_0_r. fold (step_count n). iModIntro. *)
    iApply (bar with "[$]"). iApply (step_fupdN_wand with "[$]").
    iIntros "!> (Hsup&_&_&_&HP) HE".
    iApply bupd_elim. iApply (foo E 0 with "HE"). iMod "HP". iIntros "!> HE !>".
    iApply ("HP" with "[$] [$]").
  Qed.

End plain_unfolding.
