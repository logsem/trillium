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


Record StateRes {Σ: gFunctors} (cond: nat -> bool) (sr_auth sr_frag: nat -> iProp Σ) := {    
    sr_agree: ∀ n m, sr_frag n -∗ sr_auth m -∗ 
                      ⌜ n = (if cond m then m else m + 1)%nat ⌝;
    sr_upd: ∀ n, sr_frag n -∗ sr_auth n ==∗
                   sr_frag (if cond n then n + 2 else n) ∗
                   sr_auth (if cond n then n + 1 else n);
}.


Section StResImpl.
  Class threadG Σ := ThreadG {
    th_name: gname;
    th_n_G :> inG Σ (excl_authR natO);
  }.

  Section OneImpl.
    Class threadPreG Σ := {
        thread_PreG :> inG Σ (excl_authR natO);
    }.

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

  End OneImpl.
  
  Context `{!threadPreG Σ}.

  Lemma th_alloc (M: nat):
    ⊢ |==> ∃ γ, own γ (◯E M) ∗ own γ (●E M).
  Proof.
    iStartProof.
    iMod (own_alloc (●E M  ⋅ ◯E _))%nat as (γ) "[AUTH FRAG]".
    { apply auth_both_valid_2; eauto. by compute. }
    by iFrame.
  Qed. 
  
  Section Impl.
    Context (even_name odd_name: gname).
    
    Local Instance evenThreadG: threadG Σ := {| th_name := even_name |}. 
    Local Instance oddThreadG: threadG Σ := {| th_name := odd_name |}. 
    
    Local Definition even_at := (@th_at _ evenThreadG). 
    Local Definition odd_at := (@th_at _ oddThreadG). 
    
    Local Definition auth_even_at := (@auth_th_at _ evenThreadG). 
    Local Definition auth_odd_at := (@auth_th_at _ oddThreadG).  
    
    Local Definition st_res N: iProp Σ :=
      if Nat.even N
      then (auth_even_at N ∗ auth_odd_at (N+1))%I
      else (auth_even_at (N+1) ∗ auth_odd_at N)%I.
    
    Lemma st_res_SR_even: @StateRes _ Nat.even st_res even_at.
    Proof. 
      split.
      - rewrite /st_res. setoid_rewrite if_arg2_comm. iIntros (??) "TH [EVEN ODD]".
        rewrite !if_arg_comm.
        by iDestruct (th_agree with "[$] [$]") as %->.
      - rewrite /st_res. setoid_rewrite if_arg2_comm. iIntros (?) "TH [EVEN ODD]".
        rewrite !if_arg_comm.
        destruct (Nat.even n) eqn:E.
        2: { rewrite E. by iFrame. }
        rewrite even_plus1_negb E -Nat.add_assoc. simpl.
        iMod (th_update with "[EVEN TH]") as "[??]"; by iFrame.
    Qed.
    
    Lemma st_res_SR_odd: @StateRes _ Nat.odd st_res odd_at.
    Proof.
      split.
      - rewrite /st_res. setoid_rewrite if_arg2_comm. iIntros (??) "TH [EVEN ODD]".
        rewrite !if_arg_comm.
        rewrite -(negb_if _ _ _ (Nat.odd m)) Nat.negb_odd.
        by iDestruct (th_agree with "[$] [$]") as %->.
      - rewrite /st_res. setoid_rewrite if_arg2_comm. iIntros (?) "TH [EVEN ODD]".
        rewrite if_arg_comm.
        rewrite -!(negb_if _ _ _ (Nat.odd n)) Nat.negb_odd.
        destruct (Nat.even n) eqn:E.
        { rewrite E. by iFrame. }
        rewrite even_plus1_negb E -Nat.add_assoc. simpl.
        iMod (th_update with "[ODD TH]") as "[??]"; by iFrame.
    Qed.

  End Impl.

  (* we only use it for even n, but generalization for arbitrary n is possible *)
  Lemma st_res_init n (EVEN: Nat.even n):
    ⊢ |==> ∃ st_res even_at odd_at,
        st_res n ∗ even_at n ∗ odd_at (n + 1) ∗
          ⌜ @StateRes Σ Nat.even st_res even_at ⌝ ∗
          ⌜ @StateRes Σ Nat.odd st_res odd_at ⌝.
  Proof using threadPreG0.
    iMod (th_alloc n) as (γ1) "[AUTH1 FRAG1]". 
    iMod (th_alloc (n + 1)) as (γ2) "[AUTH2 FRAG2]".
    iModIntro. do 3 iExists _. rewrite !bi.sep_assoc.
    iSplitL.
    2: { iPureIntro. apply (st_res_SR_odd γ1 γ2). }
    iSplitL.
    2: { iPureIntro. apply (st_res_SR_even γ1 γ2). }
    apply Is_true_true_1 in EVEN. rewrite /st_res EVEN. iFrame. 
  Qed. 

End StResImpl. 


Definition MU__r `{LM: LiveModel heap_lang M} `{!heapGS Σ LM} ρ E P: iProp Σ :=  
  ∀ τ f R, τ ↦M ({[ ρ := f ]} ∪ (S <$> R)) ∗ ⌜ ρ ∉ dom R ⌝ -∗
          MU E τ (τ ↦M ({[ ρ := lm_flm LM ]} ∪ R) ∗ P).


Lemma MU__r_wand `{LM: LiveModel heap_lang M} `{!heapGS Σ LM} E ρ (P Q : iProp Σ) :
  (P -∗ Q) -∗ MU__r ρ E P -∗ MU__r ρ E Q.
Proof.
  iIntros "HPQ HMU". rewrite /MU__r. iIntros "**".
  iSpecialize ("HMU" with "[$]"). 
  iApply (MU_wand with "[HPQ] [$]"). iFrame.
  iIntros "[??]". iFrame. by iApply "HPQ". 
Qed.


Lemma MU__r_mask_weaken `{LM: LiveModel heap_lang M} `{!heapGS Σ LM}
  E1 E2 ρ (P: iProp Σ)
  (SUB: E1 ⊆ E2):
  MU__r ρ E1 P -∗ MU__r ρ E2 P.
Proof.
  iIntros "MU". rewrite /MU__r. iIntros "**".
  iApply MU_mask_weaken; eauto.
  by iApply "MU".
Qed.


Section ProofsGen.  
  Context `{LM__p: LiveModel heap_lang M__p}.
  Context `{!heapGS Σ LM__p}.
  Context (cond: nat -> bool).
  Hypothesis (COND_S_NEG: forall n, cond (S n) = negb (cond n)). 
  
  Definition incr_loop : val :=
    rec: "incr_loop" "l" "n" :=
      (if: CAS "l" "n" ("n"+ #1)
       then "incr_loop" "l" ("n" + #2)
       else "incr_loop" "l" "n").

  Definition eo_corr `(SR: StateRes cond sr frag) l (N: nat): iProp Σ :=
    l ↦ #N ∗
    sr N.
    (* own th_name (●E (if cond N then N else (N + 1))). *)
  
  Definition eo_vs `(SR: StateRes cond sr frag) l ι (ρ: fmrole M__p) : iProp Σ :=
    □ |={⊤, ⊤ ∖ ↑ι}=> ∃ N,
      (▷ eo_corr SR l N) ∗
      (MU__r ρ (⊤ ∖ ↑ι)
         (▷ (eo_corr SR l (if cond N then N + 1 else N)) ={⊤ ∖ ↑ι, ⊤}=∗ True)
      ).

  Definition eo_spec (prog: val) :=
    forall `(SR: StateRes cond sr frag) (tid: locale heap_lang) n ρ (N: nat) f (Hf: f > 40) ι
    (FL: lm_flm LM__p >= 61),
    ⊢ {{{ eo_vs SR n ι ρ ∗ has_fuels tid {[ ρ := f ]} ∗ frag N }}}
        prog #n #N @ tid
      {{{ RET #(); has_fuels tid ∅ }}}.    
  
  Lemma eo_spec_incr_loop: eo_spec incr_loop.
  Proof using COND_S_NEG.
    red. intros sr frag SR tid n ρ N f Hf ι FL.
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
    { iNext. iApply (sr_agree _ _ _ SR with "[$] [$]"). }
    iMod "EQ" as "%".
            
    destruct (cond M) eqn:Heqn.
    - iModIntro. subst. 
      iApply sswp_MU_wp; [done| ].
      iApply (wp_cmpxchg_suc with "[$]"); try done.  
      iIntros "!> Hb".
      iApply (MU_wand with "[-CLOS] [$]"). 
      iIntros "(Hf & CLOS)". 

      iMod (sr_upd _ _ _ SR with "[$] [$]") as "[Heven Hay]". rewrite Heqn. 
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
    e_spec `{LM__p: LiveModel heap_lang M__p} `{!heapGS Σ LM__p}:
      eo_spec Nat.even e_prog;
}.

Record OddProg := {
    o_prog: val;
    o_spec `{LM__p: LiveModel heap_lang M__p} `{!heapGS Σ LM__p}:
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
