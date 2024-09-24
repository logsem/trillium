From stdpp Require Import decidable.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness utils action_model resources fuel.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation iris_inst lifting sswp_rules.
From trillium.fairness.heap_lang.examples Require Import mu_role.
Close Scope Z. 


(** The CMRAs we need. *)
Class yesnoG Σ := YesnoG {
  yes_name: gname;
  no_name: gname;
  yesno_n_G :> inG Σ (excl_authR natO);
  yesno_f_G :> inG Σ (excl_authR boolO);
 }.
Class yesnoPreG Σ := {
  yesno_PreG :> inG Σ (excl_authR natO);
  yesno_f_PreG :> inG Σ (excl_authR boolO);
 }.


Section Threads.
  Context `{LM: LiveModel heap_lang M}.
  Context `{!heapGS Σ LM}.
  Context `{yesnoG Σ}. 
  
  Definition yes_at (n: nat) := own yes_name (◯E n).
  Definition no_at (n: nat) := own no_name (◯E n).

  Definition auth_yes_at (n: nat) := own yes_name (●E n).
  Definition auth_no_at (n: nat) := own no_name (●E n).

  Lemma they_agree γ (n m: nat) :
    own γ (◯E n) -∗ own γ (●E m) -∗ ⌜ m = n ⌝.
  Proof.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.
  Lemma yes_agree n m :
    yes_at n -∗ auth_yes_at m -∗ ⌜ m = n ⌝.
  Proof. apply they_agree. Qed.
  Lemma no_agree n m :
    no_at n -∗ auth_no_at m -∗ ⌜ m = n ⌝.
  Proof. apply they_agree. Qed.

  Lemma they_update γ (n m P: nat) :
    own γ (●E n) ∗ own γ (◯E m) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.
  Lemma yes_update P n m :
     auth_yes_at m ∗ yes_at n ==∗ auth_yes_at P ∗ yes_at P.
  Proof. apply they_update. Qed.
  Lemma no_update P n m :
     auth_no_at m ∗ no_at n ==∗ auth_no_at P ∗ no_at P.
  Proof. apply they_update. Qed.

  Definition yn_corr l n b: iProp Σ := 
      (⌜(n, b) ≠ (0, false)⌝ ∗
      (* frag_right_st_is (n, b) ∗ *)
      l ↦ #b ∗
      if b
      then auth_yes_at n ∗ auth_no_at n
      else auth_yes_at (n-1) ∗ auth_no_at n)%I.

  Definition yes_vs l ι (ρ: fmrole M): iProp Σ :=
    □ |={⊤, ⊤ ∖ ↑ι}=> ∃ n b,
      (▷ yn_corr l n b) ∗
      ((⌜ if b then n > 0 else n > 1 ⌝ -∗ MU__r ρ (⊤ ∖ ↑ι)
         (* redundancy to ease subsequent adaptation for No thread *)
           (▷ (if b then yn_corr l n false else yn_corr l n false) ={⊤ ∖ ↑ι, ⊤}=∗ True)
       ) ∧
       (⌜ n = 0 /\ b = true \/ n = 1 /\ b = false ⌝ -∗ 
        MU__drop ρ (⊤ ∖ ↑ι) (▷ yn_corr l n b ={⊤ ∖ ↑ι, ⊤}=∗ True))
      ).

  Definition no_vs l ι (ρ: fmrole M): iProp Σ :=
    □ |={⊤, ⊤ ∖ ↑ι}=> ∃ n b,
      (▷ yn_corr l n b) ∗
      ((⌜ if b then n > 0 else n > 0 ⌝ -∗ MU__r ρ (⊤ ∖ ↑ι)
           (▷ (if b then yn_corr l n true else yn_corr l (n - 1) true) ={⊤ ∖ ↑ι, ⊤}=∗ True)
       ) ∧
       (
         ⌜ n = 0 ⌝ -∗
        MU__drop ρ (⊤ ∖ ↑ι) (▷ yn_corr l n b ={⊤ ∖ ↑ι, ⊤}=∗ True))
      ).

End Threads.
