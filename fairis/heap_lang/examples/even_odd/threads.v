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

  Definition cur_n (st: amSt thread_model) := st. 

End ThreadModel.


Definition thread_0_even: EvenModel.
  unshelve refine {| cur_even := cur_n 0 |}.
  4: apply (thread_extra 0).
  all: cycle 1; simpl in *; unfold cur_n in *. 
  - intros. inversion STEP; subst; auto.
    rewrite Nat.add_0_r in H3. repeat split; lia || auto.
  - intros. inversion STEP; subst; auto.
    rewrite Nat.add_0_r in H1. repeat split; lia || auto.
  - intros. inversion STEP; subst; auto.
  - intros. eexists. econstructor. by rewrite Nat.add_0_r.
  - intros. eexists. econstructor. by rewrite Nat.add_0_r.
  - intros. do 2 eexists. econstructor. by rewrite Nat.add_0_r.
  - intros. by rewrite !thread_AM_lr_exact.
Qed. 

Definition thread_1_odd: OddModel.
  unshelve refine {| cur_odd := cur_n 1 |}.
  4: apply (thread_extra 1).
  all: cycle 1; simpl in *; unfold cur_n in *. 
  - intros. inversion STEP; subst; auto.
    rewrite even_plus1_negb Nat.negb_even in H3. repeat split; lia || auto.
  - intros. inversion STEP; subst; auto.
    rewrite odd_plus1_negb Nat.negb_odd in H1. repeat split; lia || auto.
  - intros. inversion STEP; subst; auto.
  - intros. eexists. econstructor. by rewrite even_plus1_negb Nat.negb_even.
  - intros. eexists. econstructor. by rewrite odd_plus1_negb Nat.negb_odd.
  - intros. do 2 eexists. econstructor. by rewrite odd_plus1_negb Nat.negb_odd.
  - intros. by rewrite !thread_AM_lr_exact.
Qed.    
