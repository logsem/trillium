From stdpp Require Import decidable.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness utils.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness.heap_lang.examples.even_odd Require Import action_model. 

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


(* exposing the new fuel amount, since lm_fl depends on the new M state which is not available *)
Definition MU__r `{LM: LiveModel heap_lang M} `{!heapGS Σ LM} ρ E τ P: iProp Σ :=  
  ∀ f R, τ ↦M ({[ ρ := f ]} ∪ (S <$> R)) ∗ ⌜ ρ ∉ dom R ⌝ -∗
          MU E τ (τ ↦M ({[ ρ := lm_flm LM ]} ∪ R) ∗ P).


Record StateRes `{!threadG Σ} (cond: nat -> bool) := {
    sr: nat -> iProp Σ;
    sr_th_agree: ∀ n m, th_at n -∗ sr m -∗ 
                         ⌜ n = (if cond m then m else m + 1)%nat ⌝;
    sr_th_upd: ∀ n, th_at n -∗ sr n ==∗
                                 th_at (if cond n then n + 2 else n) ∗
                                 sr (if cond n then n + 1 else n);
}.
Arguments sr {_ _ _}. 


Section ProofsGen.  
  Context `{LM__p: LiveModel heap_lang M__p}.
  Context `{!heapGS Σ LM__p}.
  Context (cond: nat -> bool).
  Hypothesis (COND_S_NEG: forall n, cond (S n) = negb (cond n)). 
  
  Context `{!threadG Σ}.
  
  Definition incr_loop : val :=
    rec: "incr_loop" "l" "n" :=
      (if: CAS "l" "n" ("n"+ #1)
       then "incr_loop" "l" ("n" + #2)
       else "incr_loop" "l" "n").

  Definition eo_corr (SR: StateRes cond) l (N: nat): iProp Σ :=
    l ↦ #N ∗
    sr SR N.
    (* own th_name (●E (if cond N then N else (N + 1))). *)
  
  Definition eo_vs SR l ι (ρ: fmrole M__p) tid : iProp Σ :=
    □ |={⊤, ⊤ ∖ ↑ι}=> ∃ N,
      (▷ eo_corr SR l N) ∗
      (MU__r ρ (⊤ ∖ ↑ι) tid
         (▷ (eo_corr SR l (if cond N then N + 1 else N)) ={⊤ ∖ ↑ι, ⊤}=∗ True)
      ).

  Definition eo_spec (prog: val) :=
    forall SR (tid: locale heap_lang) n ρ (N: nat) f (Hf: f > 40) ι
    (FL: lm_flm LM__p >= 61),
    ⊢ {{{ eo_vs SR n ι ρ tid ∗ has_fuels tid {[ ρ := f ]} ∗ own th_name (◯E N) }}}
        prog #n #N @ tid
      {{{ RET #(); has_fuels tid ∅ }}}.    
  
  Lemma eo_spec_incr_loop: eo_spec incr_loop.
  Proof using COND_S_NEG.
    red. intros SR tid n ρ N f Hf ι FL.
    iIntros "!>". 
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ). iIntros "(#VS & Hf & Heven) Hk".
                   
    rewrite /incr_loop.
    wp_lam.
    wp_pures. wp_bind (CmpXchg _ _ _). iApply wp_atomic.
    iPoseProof "VS" as "-#V". iMod "V" as "(%M & (>Hn & SR) & CLOS)".

    iSpecialize ("CLOS" with "[Hf]").
    { iSplitL.
      { iApply has_fuels_proper; [reflexivity| | by iFrame].
        rewrite insert_union_singleton_l. f_equiv; [reflexivity| ].
        apply leibniz_equiv_iff. apply fmap_empty. }
      set_solver. }
    rewrite map_union_empty.

    iAssert (▷ ⌜ _ ⌝)%I with "[Heven SR]" as "#EQ".
    { iNext. iApply (sr_th_agree with "[$] [$]"). }
    iMod "EQ" as "%".
            
    destruct (cond M) eqn:Heqn.
    - iModIntro. subst. 
      iApply sswp_MU_wp; [done| ].
      iApply (wp_cmpxchg_suc with "[$]"); try done.  
      iIntros "!> Hb".
      iApply (MU_wand with "[-CLOS] [$]"). 
      iIntros "(Hf & CLOS)". 

      iMod (sr_th_upd _ with "[$] [$]") as "[Heven Hay]". rewrite Heqn. 
      wp_pures.
      iModIntro. 
      iMod ("CLOS" with "[Hay Hb]") as "_". 
      { replace (Z.of_nat M + 1)%Z with (Z.of_nat (M + 1)) by lia.
        iFrame. }
      iModIntro. simpl. 

      do 3 wp_pure _.
      replace (Z.of_nat M + 2)%Z with (Z.of_nat (M + 2)) by lia.
      iApply ("Hg" with "[] [Heven Hf] [$]"); last first.
      { iFrame "∗#". }
      iPureIntro; lia.
    - iModIntro.
      subst.

      iApply sswp_MU_wp; [done| ].
      iApply (wp_cmpxchg_fail with "[$]"); [| done| ].
      { assert (M ≠ M + 1) by lia. set_solver. }
      iIntros "!> Hb".
      iApply (MU_wand with "[-CLOS] [$]"). 
      iIntros "(Hf & CLOS)". 

      wp_pures.
      iModIntro. 
      iMod ("CLOS" with "[SR Hb]") as "_". 
      { iFrame. }
      iModIntro. simpl.

      do 2 wp_pure _.
      iApply ("Hg" with "[] [Heven Hf] [$]"); last first.
      { iFrame "∗#". }
      iPureIntro; lia.
  Qed.
    
End ProofsGen.

(* TODO: define these interfaces separately? *)

Record EvenProg := {
    e_prog: val;
    e_spec `{LM__p: LiveModel heap_lang M__p} `{!heapGS Σ LM__p, !threadG Σ}:
      eo_spec Nat.even e_prog;
}.

Record OddProg := {
    o_prog: val;
    o_spec `{LM__p: LiveModel heap_lang M__p} `{!heapGS Σ LM__p, !threadG Σ}:
      eo_spec Nat.odd o_prog;
}.


Program Definition incr_loop_even_prog: EvenProg := {| e_prog := incr_loop |}.
Next Obligation.
  intros. apply eo_spec_incr_loop. 
  intros. apply even_succ_negb.
Qed. 

Program Definition incr_loop_odd_prog: OddProg := {| o_prog := incr_loop |}.
Next Obligation.
  intros. apply eo_spec_incr_loop. 
  intros. apply odd_succ_negb.
Qed. 
