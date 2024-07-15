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
From trillium.fairness.heap_lang.examples.even_odd Require Import action_model utils interface.

Close Scope Z. 

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
  
  Global Instance TR_inh: Inhabited TR. 
  apply _.
  Defined. 

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
  
  Lemma thread_roles_equal (ρ1 ρ2: amRole thread_model):
    ρ1 = ρ2.
  Proof. 
    by destruct ρ1, ρ2.
  Qed.

  Instance thread_extra: ActionModelExtra thread_model.
  Proof.
    unshelve esplit; try by apply _.
    - apply thread_AM_fin_branch'.
    - apply thread_AM_step_dec. 
  Qed. 

  Lemma thread_AM_lr_exact n: AM_live_roles ame_strong n = {[ ρT ]}.
  Proof.
    apply set_eq. intros ρ. rewrite elem_of_singleton. 
    rewrite -AM_live_roles_spec. pose proof (thread_roles_equal ρ ρT) as ->.
    split; auto. intros _.
    destruct (decide (Nat.even (n + d))).
    - do 2 eexists. econstructor. eauto.
    - apply negb_prop_intro in n0. rewrite Nat.negb_even in n0. 
      do 2 eexists. by eapply thread_loop.
  Qed. 

  Lemma thread_syncable n (EVEN: Nat.odd (n + d)):
    amTrans thread_model n (inl (step_sync n), None) (n + 1).
  Proof.
    rewrite Nat.add_1_r. by econstructor.
  Qed. 

  Lemma thread_sync_step_inv n n' k ρ
      (STEP: amTrans thread_model n (inl (step_sync k), Some ρ) n'):
      k = n /\ Nat.even (n + d).
  Proof. 
    inversion STEP; subst; eauto.
  Qed.

  Lemma thread_sync_lr_nonincr n n' M
      (STEP: amTrans thread_model n (inl (step_sync M), None) n'):
    AM_live_roles ame_strong n' ⊆ AM_live_roles ame_strong n.
  Proof. 
    rewrite !thread_AM_lr_exact. done.
  Qed.
 
  Definition cur_n (st: amSt thread_model) (n: nat) := st = n. 

  Lemma thread_steppable (n: nat) st (EVEN: Nat.even (n + d)) (CUR: cur_n st n):
    exists st' ρ, amTrans thread_model st (inl (step_sync n), Some ρ) st' /\ cur_n st' (n + 1).
  Proof.
    red in CUR. subst.
    rewrite Nat.add_1_r. 
    do 2 eexists. split; [econstructor| ]; done.
  Qed. 

  Lemma thread_stutterable (n: nat) st (EVEN: Nat.odd (n + d)) (CUR: cur_n st n):
    exists st' a ρ, amTrans thread_model st (inr a, Some ρ) st' /\ cur_n st' n.
  Proof.
    red in CUR. subst.
    do 3 eexists. split; [econstructor| ]; done.
  Qed.

End ThreadModel.


Definition thread_0_even: EvenModel.
  refine {| cur_even := cur_n 0 |}.
  - intros. red in CUR. subst st.
    rewrite (plus_n_O n) in ODD. 
    eapply thread_syncable in ODD.
    eexists. split; eauto. done.
  - intros. red in CUR. subst st__e.
    simpl in *.
    apply thread_sync_step_inv in STEP as [-> STEP]. 
    rewrite -plus_n_O in STEP. done.
  - intros. simpl.  
    eapply thread_sync_lr_nonincr; eauto.
  - exact ρT.
(* Qed. *)
Defined.

    
Definition thread_1_odd: OddModel.
  refine {| cur_odd := cur_n 1 |}.
  - intros. red in CUR. subst st.
    rewrite -Nat.negb_odd -odd_plus1_negb in ODD. 
    eapply thread_syncable in ODD.
    eexists. split; eauto. done.
  - intros. red in CUR. subst st__e.
    simpl in *.
    apply thread_sync_step_inv in STEP as [-> STEP]. 
    rewrite even_plus1_negb Nat.negb_even in STEP. done.
  - intros.
    eapply thread_sync_lr_nonincr; eauto.
  - exact ρT.
(* Qed.  *)
Defined. 
