From stdpp Require Import decidable.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness.heap_lang.examples.even_odd Require Import action_model utils. 

Close Scope Z. 


Class threadG Σ := ThreadG {
  th_name: gname;
  th_n_G :> inG Σ (excl_authR natO);
}.

Class threadPreG Σ := {
  thread_PreG :> inG Σ (excl_authR natO);
}.


Section ThreadGLemmas.
  Context `{!threadG Σ}.

  Definition th_at (n: nat) := own th_name (◯E n).
  Definition auth_th_at (n: nat) := own th_name (●E n).
  
  Lemma th_agree γ (N M: nat) :
    own γ (◯E N) -∗ own γ (●E M) -∗ ⌜ M = N ⌝.
  Proof.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.
  
  Lemma th_update γ (N M P: nat) :
    own γ (●E N) ∗ own γ (◯E M) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.

End ThreadGLemmas.


Section ProofsGen.  
  Context `{LM__p: LiveModel heap_lang M__p}.
  Context `{!heapGS Σ LM__p}.
  (* Context (d: nat).  *)
  Context (cond: nat -> bool).
  Hypothesis (COND_S_NEG: forall n, cond (S n) = negb (cond n)). 
  
  Context `{!threadG Σ}.
  
  Definition incr_loop : val :=
    rec: "incr_loop" "l" "n" :=
      (if: CAS "l" "n" ("n"+ #1)
       then "incr_loop" "l" ("n" + #2)
       else "incr_loop" "l" "n").
  
  Definition eo_corr l (st: fmstate M__p) (N: nat): iProp Σ :=
    frag_model_is st ∗ l ↦ #N ∗
    (* own th_name (●E (if Nat.even (N + d) then N else (N + 1))). *)
    own th_name (●E (if cond N then N else (N + 1))).
    
  Definition eo_vs l ι (ρ: fmrole M__p) tid : iProp Σ :=
    □ |={⊤, ⊤ ∖ ↑ι}=> ∃ st__p N,
    (▷ eo_corr l st__p N) ∗
      (∀ f, tid ↦M {[ ρ := f ]} -∗ frag_model_is st__p -∗ frag_free_roles_are ∅ -∗
              MU (⊤ ∖ ↑ι) tid (
                ∃ st__p' f', tid ↦M {[ ρ := f' ]}  ∗ frag_model_is st__p' ∗ frag_free_roles_are ∅ ∗ ⌜ f' > 43 ⌝ ∗
                                                                                                               (▷ (eo_corr l st__p' (if cond N then N + 1 else N)) ={⊤ ∖ ↑ι, ⊤}=∗ True))).
  
  Lemma eo_go_spec (tid: locale heap_lang) n ρ (N: nat) f (Hf: f > 40) ι
    (FL: forall st, lm_fl LM__p st >= 61):
    {{{  eo_vs n ι ρ tid ∗
           has_fuels tid {[ ρ := f ]} ∗ own th_name (◯E N) ∗
           frag_free_roles_are ∅
    }}}
      incr_loop #n #N @ tid
      {{{ RET #(); has_fuels tid ∅ }}}.
  Proof using COND_S_NEG.
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ). iIntros "(#VS & Hf & Heven & HFR) Hk".
                   
    rewrite /incr_loop.
    wp_lam.
    wp_pures. wp_bind (CmpXchg _ _ _). iApply wp_atomic.
    iPoseProof "VS" as "-#V". iMod "V" as "(%st & %M & (>Hmod & >Hn & >Hauths) & CLOS)".

    (* destruct (Nat.even (M + d)) eqn:Heqn. *)
    destruct (cond M) eqn:Heqn.
    - iDestruct (th_agree with "Heven Hauths") as "->".
      iModIntro.
      iSpecialize ("CLOS" with "[$] [$] [$]"). 
      iApply sswp_MU_wp; [done| ].
      iApply (wp_cmpxchg_suc with "[$]"); try done.  
      iIntros "!> Hb".
      iApply (MU_wand with "[-CLOS] [$]"). 
      iIntros "(%st' & %f' & (Hf& Hmod& HFR & %FUEL' & CLOS))".

      iMod (th_update _ _ _ (N + 2) with "[$]") as "[Hay Heven]".
      wp_pures.
      iModIntro. 
      iMod ("CLOS" with "[Hmod Hay Hb]") as "_". 
      { replace (Z.of_nat N + 1)%Z with (Z.of_nat (N + 1)) by lia.
        iFrame.
        rewrite Nat.add_1_r COND_S_NEG Heqn. simpl.
        by rewrite Nat.add_succ_r. }
      iModIntro. simpl.

      pose proof (FL st').
      do 3 wp_pure _.
      replace (Z.of_nat N + 2)%Z with (Z.of_nat (N + 2)) by lia.
      iApply ("Hg" with "[] [Heven Hf HFR] [$]"); last first.
      { iFrame "∗#". }
      iPureIntro; lia.
    - iDestruct (th_agree with "Heven Hauths") as "%Heq". rewrite -> Heq in *.
      iModIntro.
      subst.

      iSpecialize ("CLOS" with "[$] [$] [$]"). 
      iApply sswp_MU_wp; [done| ].
      iApply (wp_cmpxchg_fail with "[$]"); [| done| ].
      { assert (M ≠ M + 1) by lia. set_solver. }
      iIntros "!> Hb".
      iApply (MU_wand with "[-CLOS] [$]"). 
      iIntros "(%st' & %f' & (Hf& Hmod& HFR & %FUEL' & CLOS))".

      iMod (th_update _ _ _ (M + 1) with "[$]") as "[Hay Heven]".
      wp_pures.
      iModIntro. 
      iMod ("CLOS" with "[Hmod Hay Hb]") as "_". 
      { iFrame. by rewrite Heqn. }
      iModIntro. simpl.

      pose proof (FL st').
      do 2 wp_pure _.
      iApply ("Hg" with "[] [Heven Hf HFR] [$]"); last first.
      { iFrame "∗#". }
      iPureIntro; lia.
  Qed.
    
End ProofsGen.


Definition even_spec `{LM__p: LiveModel heap_lang M__p} `{!heapGS Σ LM__p, !threadG Σ}:=
    eo_go_spec Nat.even even_succ_negb. 

Definition odd_spec `{LM__p: LiveModel heap_lang M__p} `{!heapGS Σ LM__p, !threadG Σ}:=
    eo_go_spec Nat.odd odd_succ_negb.
