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

Inductive PubA := step_sync (k: nat).

Global Instance PubA_EqDec: EqDecision PubA.
Proof.
  intros [x] [y]. destruct (decide (x = y)); [left | right]; set_solver.
Qed. 

Section ThreadModel.
  Context (d: nat).
  
  Definition PrivA := unit.
  Let step_loop: PrivA := (). 
  
  Definition TA: Type := PubA + PrivA. 
  Definition TR := unit.
  Definition ρT: TR := ().
  
  Definition TS := nat. 
  
  Inductive thread_trans: TS -> TA * option TR -> TS -> Prop :=
  | thread_step n : Nat.even (n + d) → thread_trans n (inl (step_sync n), Some ρT) (S n)
  | thread_loop n : Nat.odd (n + d) → thread_trans n (inr step_loop, Some ρT) n
  | thread_env n : Nat.odd (n + d) → thread_trans n (inl (step_sync n), None) (S n)
  .
  
  Definition thread_model: ActionModel := {| amTrans := thread_trans |}.
  
  (* Global Instance TR_eqdec: EqDecision TR. *)
  (* apply _.  *)
  (* Qed.  *)
  
  Lemma thread_AM_fin_branch': AM_fin_branch' thread_model.
  Proof.
    red. exists (fun n => n' ← [n; S n]; 
                  a ← [inl $ step_sync n; inr step_loop];
                  ρ ← [Some ρT; None]; mret (n', a, ρ)).
    intros * STEP.
    repeat (setoid_rewrite elem_of_list_bind).
    setoid_rewrite elem_of_list_ret.
    eexists. apply and_comm. rewrite -ex_and_comm.
    eexists. apply and_comm. rewrite -!and_assoc. apply and_comm. rewrite -ex_and_comm.
    eexists. apply and_comm. rewrite -!and_assoc.
    split; [reflexivity| ].
    inversion STEP; subst; set_solver.
  Qed.
  
  Lemma thread_AM_step_dec: AM_step_dec thread_model.
  Proof.
    red. intros.
    Local Ltac contra := right; intros TRANS; inversion TRANS; subst; try tauto; try lia.
    destruct (decide (Nat.even (s1 + d))).
    - destruct (decide (s2 = S s1 /\ oρ = Some ρT /\ a = inl (step_sync s1))) as [(-> & -> & ->)|?].
      + left. by econstructor.
      + contra; rewrite -Nat.negb_even in H3; by apply negb_prop_elim in H3.
    - pose proof n as n'. 
      apply negb_prop_intro in n. rewrite Nat.negb_even in n.
      destruct (decide (s2 = s1 /\ oρ = Some ρT /\ a = inr step_loop)) as [(-> & -> & ->)|?].
      + left. by econstructor.
      + destruct (decide (s2 = S s1 /\ oρ = None /\ a = inl (step_sync s1))) as [(-> & -> & ->)|?].
        * left. by econstructor.
        * contra.
  Qed.
  
  Lemma thread_AM_strong: AM_strong_lr thread_model.
  Proof. 
    apply fin_branch_strong; auto using thread_AM_step_dec, thread_AM_fin_branch'.
  Qed.


  Section Proofs. 
    Context `{LM__p: LiveModel heap_lang M__p}.
    Context `{!heapGS Σ LM__p}. 

    Class threadG Σ := ThreadG {
        th_name: gname;
        th_n_G :> inG Σ (excl_authR natO);
    }.

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

    Definition incr_loop : val :=
      rec: "incr_loop" "l" "n" :=
        (if: CAS "l" "n" ("n"+ #1)
         then "incr_loop" "l" ("n" + #2)
         else "incr_loop" "l" "n").

    Context (proj_st: fmstate M__p -> amSt thread_model).
    Context (lift_role: amRole thread_model -> fmrole M__p). 

    Definition eo_corr l (st: fmstate M__p): iProp Σ :=
      let N := proj_st st in
      frag_model_is st ∗ l ↦ #(N: nat) ∗
      own th_name (●E (if Nat.even (N + d) then N else (N + 1))).
    
    Definition eo_vs l ι ρ__t: iProp Σ :=
      □ |={⊤, ⊤ ∖ ↑ι}=> ∃ st,
      (▷ eo_corr l st) ∗
      (* (▷ (eo_corr l (if (Nat.even (N + d)) then (N + 1) else N) γ d) ={⊤ ∖ ↑ι, ⊤}=∗ True). *)
      (let N := proj_st st in
       (⌜ Nat.even (N + d) ⌝ →
        ⌜ amTrans _ N (inl $ step_sync N, Some ρ__t) (N + 1)%nat ⌝ →
        ∃ (* a *) st', ⌜ proj_st st' = (N + 1)%nat ⌝ ∗ 
                       ⌜ fmtrans M__p st (Some $ lift_role ρ__t) st' ⌝ ∗
                       ⌜ live_roles M__p st' ⊆ live_roles M__p st ⌝ ∗
                       (▷ (eo_corr l st') ={⊤ ∖ ↑ι, ⊤}=∗ True)
      ) ∗
       (⌜ Nat.odd (N + d) ⌝ →
        ∀ a, ⌜ amTrans _ N (inr a, Some ρ__t) N ⌝ →
        ∃ (* a *) st', ⌜ proj_st st' = N ⌝ ∗ 
                       ⌜ fmtrans M__p st (Some $ lift_role ρ__t) st' ⌝ ∗
                       ⌜ live_roles M__p st' ⊆ live_roles M__p st ⌝ ∗
                       (▷ (eo_corr l st') ={⊤ ∖ ↑ι, ⊤}=∗ True)
      ) 
      ).

  (* TODO: can we make it work with non-trivial set of roles? *)
  Local Lemma thread_roles_equal (ρ1 ρ2: amRole thread_model):
    ρ1 = ρ2.
  Proof. 
    by destruct ρ1, ρ2.
  Qed. 

  Lemma eo_go_spec (tid: locale heap_lang) n ρ__t (N: nat) f (Hf: f > 40) ι
    (FL: forall st, lm_fl LM__p st >= 61):
    {{{  eo_vs n ι ρ__t ∗
         has_fuels tid {[ lift_role ρ__t := f ]} ∗ own th_name (◯E N) ∗
         frag_free_roles_are ∅
    }}}
      incr_loop #n #N @ tid
    {{{ RET #(); has_fuels tid ∅ }}}.
  Proof.
    rewrite !(thread_roles_equal ρ__t ρT). clear ρ__t.  
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ). iIntros "(#VS & Hf & Heven & HFR) Hk".

    rewrite /incr_loop.
    wp_lam.
    wp_pures. wp_bind (CmpXchg _ _ _). iApply wp_atomic.
    iPoseProof "VS" as "-#V". iMod "V" as "(%st & (>Hmod & >Hn & >Hauths) & CLOS)".

    remember (proj_st st) as M.

    destruct (Nat.even (M + d)) eqn:Heqn.
    - iDestruct (th_agree with "Heven Hauths") as "->".
      iModIntro.
      iDestruct "CLOS" as "[CLOS _]". iSpecialize ("CLOS" with "[]"); [done| ].
      iSpecialize ("CLOS" with "[]").
      { iPureIntro. rewrite Nat.add_1_r. simpl. econstructor. intuition. }
      iDestruct "CLOS" as (st') "(%ST'&%STEP&%LR&CLOS)".
      iApply (wp_step_model_singlerole with "Hmod Hf HFR"); eauto. 
      iApply (wp_cmpxchg_suc with "Hn"); [by do 3 f_equiv|done|].
      iIntros "!> Hb Hmod Hf HFR".
      iMod (th_update _ _ _ (N + 2) with "[$]") as "[Hay Heven]".
      wp_pures.
      iModIntro.
      iMod ("CLOS" with "[Hmod Hay Hb]") as "_". 
      { replace (Z.of_nat N + 1)%Z with (Z.of_nat (N + 1)) by lia. rewrite -ST'. 
        iFrame.
        rewrite ST'. rewrite Nat.add_shuffle0. rewrite Nat.even_add.
        rewrite Heqn. simpl. 
        rewrite -Nat.add_assoc. done. }
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
      iDestruct "CLOS" as "[_ CLOS]". iSpecialize ("CLOS" with "[]").
      { iPureIntro. by rewrite -Nat.negb_even Heqn. } 
      iSpecialize ("CLOS" with "[]").
      { iPureIntro. simpl. econstructor. by rewrite -Nat.negb_even Heqn. }
      iDestruct "CLOS" as (st') "(%ST'&%STEP&%LR&CLOS)".
 
      iApply (wp_step_model_singlerole with "Hmod Hf HFR"); eauto. 
      iApply (wp_cmpxchg_fail with "Hn"); [intros Hne; simplify_eq; lia|done|].
      iIntros "!> Hb Hmod Hf HFR".
      wp_pures.
      iModIntro. 
      iMod ("CLOS" with "[Hmod Hb Hauths]").
      { rewrite -ST'. iFrame.
        by rewrite ST' Heqn. }  
      iModIntro. simpl.
      (* wp_pures. *)
      pose proof (FL st').
      do 2 wp_pure _. 
      iApply ("Hg" with "[] [Heven Hf HFR] [$]"); last first.
      { iFrame "∗#". }
      iPureIntro; lia.
  Qed.
    
  End Proofs.
  
End ThreadModel.



(* ******************** *)
Global Opaque PrivA.
Global Opaque TR.
Global Opaque incr_loop.   
