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

  Global Instance is_except_0_laterN {Σ} n (P : iProp Σ) :
    IsExcept0 P →
    IsExcept0 (▷^n P).
  Proof.
    destruct n; [done|].
    simpl; tc_solve.
  Qed.

  Local Lemma lc_incr_supply `{!lcGS Σ} n m :
    later_credits.lc_supply n ⊢ |==> later_credits.lc_supply (n + m) ∗ £ m.
  Proof.
    iIntros "H". iMod lc_zero as "H'". iCombine "H H'" as "H".
    rewrite later_credits.lc_unseal /later_credits.lc_def later_credits.lc_supply_unseal /later_credits.lc_supply_def -!own_op.
    iApply (own_update with "[$]").
    eapply auth_update. eapply nat_local_update; lia.
  Qed.


  (* In case of no later credit update. *)

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

  (* In case of later credit update *)

  Definition le_upd_to_bupd_aux `{!lcGS Σ}
      (rec : nat → iProp Σ) (n : nat) : iProp Σ :=
    ∀ (P : iProp Σ) `(!Plain P) `(!IsExcept0 P) m, ((£ m -∗ |==£> ∀ k, rec k -∗ ▷^k P) -∗ ▷^(n+m) P).
  
  Definition le_upd_to_bupd `{!lcGS Σ} n :=
    bi_greatest_fixpoint le_upd_to_bupd_aux n.
  
  Instance le_upd_to_bupd_aux_bi_mono `{!lcGS Σ} :
    BiMonoPred (le_upd_to_bupd_aux).
  Proof.
    split.
    - iIntros (Φ Ψ HΦne HΨne) "#H". iIntros (n) "Hn". iIntros (P ? ? m) "HP /=".
      iApply "Hn"; try (iPureIntro; tc_solve). iIntros "?".
      iMod ("HP" with "[$]") as "HP". iIntros "!> %k HΦ"; iApply "HP"; by iApply "H".
    - iIntros (Φ HΦne). by intros ??? ->.
  Qed.

  Lemma le_upd_to_bupd_unfold `{!lcGS Σ} n :
    le_upd_to_bupd n ≡ le_upd_to_bupd_aux le_upd_to_bupd n.
  Proof. by rewrite /le_upd_to_bupd greatest_fixpoint_unfold. Qed.


  Definition le_upd_to_bupd_use `{!lcGS Σ} n m P `{!IsExcept0 P} `{!Plain P} :
    le_upd_to_bupd n -∗ (£ m -∗ |==£> ∀ k, le_upd_to_bupd k -∗ ▷^k P) -∗ ▷^(n + m) P.
  Proof.
    iIntros "Hn HP". rewrite le_upd_to_bupd_unfold.
    iApply ("Hn" with "[] [] HP"); try (iPureIntro; tc_solve).
  Qed.
  
  Lemma le_upd_to_bupd_soundness_lc `{!lcGpreS Σ} P `{!IsExcept0 P} `{!Plain P} :
    (∀ `{Hlc: !lcGS Σ}, le_upd_to_bupd 0 -∗ P) → ⊢ P.
  Proof.
    iIntros (Hfupd).
    iMod (later_credits.le_upd.lc_alloc 0) as (Hc) "[H _]".
    iApply (Hfupd _). generalize 0 => n.
    iApply (greatest_fixpoint_coiter _ later_credits.lc_supply with "[] [$H]").
    iIntros "!> % Hsup %Q % % %m HQ". iApply bupd_elim.
    iMod (lc_incr_supply _ m with "Hsup") as "[Hsup Hlc]".
    iSpecialize ("HQ" with "Hlc"). clear n. generalize (y + m) => n. clear y m.
    iLöb as "IH" forall (n).
    iEval (rewrite later_credits.le_upd.le_upd_unfold) in "HQ".
    iMod ("HQ" with "[$]") as "[[Hsup Hrest]|(%m&%Hmle&Hsup&Hnext)]".
    - iModIntro. iApply is_except_0.
      iDestruct ("Hrest" with "[$]") as "$".
    - destruct n as [|n]; [lia|simpl].
      do 2 iModIntro.
      iApply (bi.laterN_le m); [lia|].
      iApply bupd_elim.
      iApply ("IH" with "[$] [$]").
  Qed.

  (* Either *)

  Local Definition le_upd_if_to_bupd_def `{!lcGS Σ} (hlc : has_lc) n :=
    match hlc with
    | HasLc => le_upd_to_bupd n
    | HasNoLc => lc_generator ()
    end.
  Local Definition le_upd_if_to_bupd_aux : seal (@le_upd_if_to_bupd_def). Proof. by eexists. Qed.
  Definition le_upd_if_to_bupd := le_upd_if_to_bupd_aux.(unseal).
  Local Definition le_upd_if_to_bupd_unseal :
    @le_upd_if_to_bupd = @le_upd_if_to_bupd_def := le_upd_if_to_bupd_aux.(seal_eq).
  Global Arguments le_upd_if_to_bupd {_ _} hlc n.

  Definition has_lc_to_bool (hlc : has_lc) :=
    match hlc with
    | HasLc => true
    | HasNoLc => false
    end.

  Definition le_upd_if_to_bupd_use `{!lcGS Σ} hlc n m P `{!IsExcept0 P} `{!Plain P} :
    le_upd_if_to_bupd hlc n -∗ (£ m -∗ le_upd_if (has_lc_to_bool hlc) (∀ k, le_upd_if_to_bupd hlc k -∗ ▷^k P)) -∗ ▷^(m + n) P.
  Proof.
    rewrite (comm _ m n). rewrite le_upd_if_to_bupd_unseal.
    destruct hlc; [by apply le_upd_to_bupd_use|].
    simpl. iIntros "Hgen Hupd".
    iApply bupd_elim. iEval (rewrite lc_generator_unfold) in "Hgen".
    iApply "Hgen". iIntros "H£ Hgen".
    iMod ("Hupd" with "[$]") as "Hupd".
    by iApply "Hupd".
  Qed.

  Lemma le_upd_if_to_bupd_soundness `{!lcGpreS Σ} hlc P `{!IsExcept0 P} `{!Plain P} :
    (∀ `{Hlc: !lcGS Σ}, le_upd_if_to_bupd hlc 0 -∗ P) → ⊢ P.
  Proof.
    rewrite le_upd_if_to_bupd_unseal.
    destruct hlc; [by apply le_upd_to_bupd_soundness_lc|].
    intros. iApply bupd_elim. by iApply lc_generator_soundness_no_lc.
  Qed.


  Definition fupd_to_bupd_aux `{invGS_gen hlc Σ}
           (rec : coPset → iProp Σ) (E1 : coPset) : iProp Σ :=
    ∀ (P : iProp Σ) `(!Plain P) `(!IsExcept0 P) n E2, le_upd_if_to_bupd hlc n -∗ ((|={E1,E2}=> ∀ k, le_upd_if_to_bupd hlc k -∗ rec E2 -∗ ▷^k P) -∗ ▷^n P).

  Definition fupd_to_bupd `{invGS_gen hlc Σ} E1 :=
    bi_greatest_fixpoint fupd_to_bupd_aux E1.

  Instance fupd_to_bupd_aux_bi_mono `{invGS_gen hlc Σ} :
    BiMonoPred (fupd_to_bupd_aux).
  Proof.
    split.
    - iIntros (Φ Ψ HΦne HΨne) "#H". iIntros (E1) "HE". iIntros (P ? ? n E2) "Hle HP /=".
      iApply ("HE" with "[] [] Hle"); try (iPureIntro; tc_solve); iMod "HP"; iModIntro.
      iIntros; iApply ("HP" with "[$]"); by iApply "H".
    - iIntros (Φ HΦne). by intros ??? ->%leibniz_equiv.
  Qed.

  Lemma fupd_to_bupd_unfold `{invGS_gen hlc Σ} E :
    fupd_to_bupd E ≡ fupd_to_bupd_aux fupd_to_bupd E.
  Proof. by rewrite /fupd_to_bupd greatest_fixpoint_unfold. Qed.

  (* Lemma fupd_to_bupd_except0 `{invGS_gen hlc Σ} E E' P `{!IsExcept0 P} :
    fupd_to_bupd E -∗ (|={E, E'}=> fupd_to_bupd E' -∗ P) ==∗ P.
  Proof.
    iIntros "HE HP". rewrite fupd_to_bupd_unfold.
    iApply (is_except_0 P). iApply ("HE" with "[$]").
  Qed. *)

  Lemma fupd_to_bupd_except0_plain `{invGS_gen hlc Σ} n E E' P `{!IsExcept0 P} `{!Plain P} :
    fupd_to_bupd E -∗ le_upd_if_to_bupd hlc n -∗ (|={E, E'}=> ∀ k, le_upd_if_to_bupd hlc k -∗ fupd_to_bupd E' -∗ ▷^k P) -∗ ▷^n P.
  Proof.
    iIntros "HE Hle HP". rewrite fupd_to_bupd_unfold.
    iDestruct ("HE" with "[] [] Hle HP") as "H"; by try (iPureIntro; tc_solve).
  Qed.

  Lemma fupd_to_bupd_soundness `{!invGpreS Σ} hlc P `{!IsExcept0 P} `{!Plain P} :
    (∀ `{Hinv: !invGS_gen hlc Σ}, le_upd_if_to_bupd hlc 0 -∗
      fupd_to_bupd ⊤ -∗ P) → ⊢ P.
  Proof.
    iIntros (Hfupd). iApply bupd_elim.
    iApply (@le_upd_if_to_bupd_soundness _ invGpreS_lc).
    iIntros (Hc) "Hgen".
    iMod ( @wsat_alloc _ (invGpreS0.(invGpreS_wsat))) as (Hw) "[Hw HE]".
    set (Hi := InvG hlc _ Hw Hc).
    iApply ( @Hfupd Hi with "Hgen").
    assert (NonExpansive (λ E, wsat ∗ ownE E)%I).
    { by intros ??? ->%leibniz_equiv. }
    iApply (greatest_fixpoint_coiter _ (λ E, wsat ∗ ownE E)%I with "[] [$Hw $HE]").
    iIntros "!>" (E1) "?". clear.
    iIntros (P ? ? ? E2) "Hle HP".
    rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def /=.
    iApply (le_upd_if_to_bupd_use _ _ 0 with "[$]"). iIntros "H".
    iMod ("HP" with "[$]") as "Hrest".
    iIntros "!> %k Hle". iMod "Hrest" as "(?&?&Hclose)".
    iApply ("Hclose" with "[$Hle] [$]").
  Qed.

  (* TODO: Make this opaque *)
  Definition step_count `{!tr_generation} (ns : nat) : nat :=
    let trs := physical_step.tr_per_step 0 ns in
    (f $ S $ trs) + (S $ f $ trs).

  Definition physical_step_to_laters_aux `{!tr_generation} `{invGS_gen hlc Σ} `{trGS Σ} (rec : nat → iProp Σ) (ns : nat) : iProp Σ :=
    ∀ (P : iProp Σ) `(!Plain P) `(!IsExcept0 P) n (E : coPset), (fupd_to_bupd E -∗ le_upd_if_to_bupd hlc n -∗ (|={E}⧗=> ∀ k, fupd_to_bupd E -∗ le_upd_if_to_bupd hlc k -∗ rec (S ns) -∗ ▷^k P) -∗ ▷^(step_count ns + n) P).
  
  Definition physical_step_to_laters `{!tr_generation} `{invGS_gen hlc Σ} `{trGS Σ} :=
    bi_greatest_fixpoint physical_step_to_laters_aux.
  
  Instance physical_step_to_laters_aux_bi_mono `{!tr_generation} `{invGS_gen hlc Σ} `{trGS Σ} :
    BiMonoPred (physical_step_to_laters_aux).
  Proof.
    split.
    - iIntros (Φ Ψ HΦne HΨne) "#H". iIntros (ns) "Hns". iIntros (P ? ? n E) "HE Hle HP".
      iApply ("Hns" with "[] [] [$] [$]"); try (iPureIntro; tc_solve).
      iApply (physical_step_wand with "[$]"). iIntros "HP %k ? ? ?".
      iApply ("HP" with "[$] [$]"). by iApply "H".
    - iIntros (Φ HΦne). by intros ??? ->%leibniz_equiv.
  Qed.

  Lemma physical_step_to_laters_unfold `{!tr_generation} `{invGS_gen hlc Σ} `{trGS Σ} ns :
    physical_step_to_laters ns ≡ physical_step_to_laters_aux physical_step_to_laters ns.
  Proof. by rewrite /physical_step_to_laters greatest_fixpoint_unfold. Qed.

  Lemma physical_step_to_laters_except0_plain `{!tr_generation} `{invGS_gen hlc Σ} `{trGS Σ} ns n E P `{!IsExcept0 P} `{!Plain P} :
    physical_step_to_laters ns -∗ fupd_to_bupd E -∗ le_upd_if_to_bupd hlc n -∗ (|={E}⧗=>  ∀ k, fupd_to_bupd E -∗ le_upd_if_to_bupd hlc k -∗ physical_step_to_laters (S ns) -∗ ▷^k P) -∗ ▷^(step_count ns + n) P.
  Proof.
    iIntros "Hsteps Hfupd Hle HP".
    rewrite physical_step_to_laters_unfold.
    iApply ("Hsteps" with "[] [] [$] [$]"); try (iPureIntro; tc_solve).
    iApply (physical_step_wand with "[$]"). iIntros "$".
  Qed.

  (* Lemma foo `{invGS_gen HasNoLc Σ} {E} E' n P :
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
  Qed. *)

  Lemma bar `{invGS_gen hlc Σ} n m Q `{!Plain Q} `{!IsExcept0 Q} :
    fupd_to_bupd ∅ -∗ le_upd_if_to_bupd hlc m -∗ (|={∅}▷=>^n fupd_to_bupd ∅ -∗ ∀ k, le_upd_if_to_bupd hlc k -∗ ▷^k Q) -∗ (▷^(n + m) Q).
  Proof.
    rewrite (comm _ n m).
    iIntros "HFtB Hle HP".
    iInduction n as [|n] "IHn" forall (m).
    { rewrite Nat.add_0_r. iApply ("HP" with "[$] [$]"). }
    iEval (rewrite bi.laterN_add).
    iApply (fupd_to_bupd_except0_plain with "[$] [$]"). iMod "HP". clear m.
    iIntros "!> %m Hle HFtB". rewrite -bi.laterN_later bi.later_laterN.
    iNext.
    iApply (fupd_to_bupd_except0_plain with "[$] [$]"). iMod "HP". clear m.
    iIntros "!> %m Hle HFtB". rewrite -bi.laterN_add.
    iApply ("IHn" with "[$] [$] [$]").
  Qed.

  
  Lemma physical_step_to_laters_soundness  `{!tr_generation} `{!invGpreS Σ} `{trGpreS Σ} hlc Q `{!Plain Q} `{!IsExcept0 Q} :
    (∀ `{invGS_gen hlc Σ} `{trGS Σ}, fupd_to_bupd ⊤ -∗ le_upd_if_to_bupd hlc 0 -∗ physical_step_to_laters 0 -∗ Q) →
    ⊢ Q.
  Proof.
    iIntros (Hfupd).
    iApply (fupd_to_bupd_soundness hlc).
    iIntros (Hinv) "Hlc Hfupd".
    iMod (tr_supply_alloc 0) as "(%Htr & Hsup & H⧗)"; simpl.
    iApply ( @Hfupd _ _ with "[$] [$]").
    assert (NonExpansive (λ n, tr_supply (physical_step.tr_per_step 0 n))%I).
    { intros ????; repeat f_equiv; eauto. }
    iApply (greatest_fixpoint_coiter _
      (λ n, tr_supply (physical_step.tr_per_step 0 n))%I with "[] [Hsup]"); [|iFrame].
    iIntros "!>" (n) "Htr". rewrite /physical_step_to_laters_aux.
    iIntros (P ? ? m E) "HE Hlc HP". rewrite physical_step.physical_step_unseal /physical_step_def.
    unfold step_count. rewrite -assoc (comm _ _ m) assoc bi.laterN_add.
    iApply (le_upd_if_to_bupd_use with "[$]"). iIntros "Hlc !> %k Hlc'".
    iApply (fupd_to_bupd_except0_plain with "[$] [$]").
    iMod "HP". clear k. iIntros "!> %k Hle HE".
    iMod tr_zero as "H⧗". iMod (tr_persistent_zero) as "H⧖".
    iSpecialize ("HP" $! _ _ _ with "[$] [$] [$] [$]").
    rewrite -bi.later_laterN -bi.laterN_add (comm _ k).
    iApply (bar with "[$] [$]"). iApply (step_fupdN_wand with "[$]").
    clear k. iIntros "(Hsup&_&_&_&HP) HE %k Hle".
    iApply (fupd_to_bupd_except0_plain with "[$] [$]"). iMod "HP".
    clear k. iIntros "!> %k Hle HE".
    iApply ("HP" with "[$] [$] [$]").
  Qed.

End plain_unfolding.
