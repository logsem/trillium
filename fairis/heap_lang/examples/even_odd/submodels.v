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
From trillium.fairness.heap_lang.examples.even_odd Require Import action_model interface.

Close Scope Z. 

Section ThreadModel.
  Context (d: nat).
  
  Definition PrivA := unit.
  Let step_loop: PrivA := (). 
  
  (* Definition TA: Type := PubA + PrivA.  *)
  Definition TR := unit.
  Definition ρT: TR := ().
  
  Definition TS := nat.

  (* Let priv_ns := nroot .@ "priv". *)
  Context (priv_ns: namespace).
  (* Let pub_act (s: PubA) := pick_act pub_ns s. *)
  Let pub_act '(step_sync k) := ns_nth pub_ns k. 
  Let priv_act (s: PrivA) := pick_act priv_ns s.
  
  Inductive thread_trans: TS -> Action * option TR -> TS -> Prop :=
  | thread_step n : Nat.even (n + d) → 
                    thread_trans n (pub_act (step_sync n), Some ρT) (S n)
  | thread_loop n : Nat.odd (n + d) → 
                    thread_trans n (priv_act step_loop, Some ρT) n
  | thread_env n : Nat.odd (n + d) → 
                   thread_trans n (pub_act (step_sync n), None) (S n)
  .
  
  Definition thread_model: ActionModel := {| amTrans := thread_trans |}.
  
  Global Instance TR_inh: Inhabited TR. 
  apply _.
  Defined. 

  Lemma thread_AM_fin_branch': AM_fin_branch' thread_model.
  Proof.
    red. exists (fun n => n' ← [n; S n]; 
                  a ← [pub_act $ step_sync n; priv_act step_loop];
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
    - destruct (decide (s2 = S s1 /\ oρ = Some ρT /\ a = pub_act (step_sync s1))) as [(-> & -> & ->)|?].
      + left. by econstructor.
      + contra; rewrite -Nat.negb_even in H3; by apply negb_prop_elim in H3.
    - pose proof n as n'. 
      apply negb_prop_intro in n. rewrite Nat.negb_even in n.
      destruct (decide (s2 = s1 /\ oρ = Some ρT /\ a = priv_act step_loop)) as [(-> & -> & ->)|?].
      + left. by econstructor.
      + destruct (decide (s2 = S s1 /\ oρ = None /\ a = pub_act (step_sync s1))) as [(-> & -> & ->)|?].
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
    amTrans thread_model n (pub_act (step_sync n), None) (n + 1).
  Proof.
    rewrite Nat.add_1_r. by econstructor.
  Qed. 

  Lemma thread_sync_step_inv n n' k ρ
      (STEP: amTrans thread_model n (pub_act (step_sync k), Some ρ) n')
      (DISJ: priv_ns ## pub_ns):
      k = n /\ Nat.even (n + d).
  Proof. 
    inversion STEP; subst. 
    - split; auto. symmetry. apply coPset_nth_inj in H. congruence.
    - apply pick_act_ns_nth_disj_neq in H; [done| ]. solve_ndisj.  
  Qed. 

  Definition cur_n (st: amSt thread_model) := st.

  Definition thread_is_priv (a: Action) := a = priv_act step_loop.

  Lemma thread_is_action_of:
    ∀ a, is_action_of thread_model a ↔
          (∃ k, a = pub_act (step_sync k)) ∨ thread_is_priv a.
  Proof.
    intros a. split.
    + intros (?&?&?&STEP). inversion STEP; subst; eauto.
      right. done.
    + intros [[? ->] | ->]; try by econstructor.
      2: { exists (d + 1), (Some ρT), (d + 1). econstructor.
           replace (d + 1 + d) with (1 + 2 * d) by lia.
           by rewrite Nat.odd_add_mul_2. }
      destruct (even_or_odd (x + d)); do 3 eexists; by econstructor.
  Qed.     

End ThreadModel.


Definition thread_0_even: EvenModel.
  unshelve refine {| 
               cur_even := cur_n 0 (nroot .@ "priv_even");
               even_is_priv_act := thread_is_priv (nroot .@ "priv_even");
             |}.
  1: apply (thread_extra 0).
  1, 2: apply _. 
  all: cycle 2; simpl in *; unfold cur_n in *.
  - apply thread_is_action_of.
  - intros ??%eq_sym%pick_act_ns_nth_disj_neq; solve_ndisj.
  - intros ?->. apply pick_act_dom.
  - rewrite /thread_is_priv. solve_decision. 
  - intros. inversion STEP; subst; auto.
    2: { apply pick_act_ns_nth_disj_neq in H; [done| ].
         solve_ndisj. }
    apply coPset_nth_inj in H. inversion H. subst.  
    rewrite Nat.add_0_r in H3. repeat split; lia || auto.
  - intros. inversion STEP; subst; auto.
    apply coPset_nth_inj in H. inversion H. subst.  
    rewrite Nat.add_0_r in H1. repeat split; lia || auto.
  - intros. inversion STEP; subst; auto.
    edestruct @pick_act_ns_nth_disj_neq; eauto. solve_ndisj.  
  - intros. eexists. econstructor. by rewrite Nat.add_0_r.
  - intros. eexists. econstructor. by rewrite Nat.add_0_r.
  - intros. do 2 eexists. split; [| apply thread_loop].
    { reflexivity. }
    by rewrite Nat.add_0_r.
  - intros. by rewrite !thread_AM_lr_exact.
  - reflexivity.
  - by rewrite !thread_AM_lr_exact.
  - intros ? (?&?&T1) (?&?&?&T2).
    inversion T1.
    2: { symmetry in H0. apply eq_sym, pick_act_ns_nth_disj_neq in H0; [done | solve_ndisj]. }
    inversion T2; subst. 
    { red in H. symmetry in H. 
      edestruct @pick_act_ns_nth_disj_neq; [| apply H]. solve_ndisj. }
    subst. edestruct even_odd_False; eauto.
Qed. 

Definition thread_1_odd: OddModel.
  unshelve refine {| 
               cur_odd := cur_n 1 (nroot .@ "priv_odd");
               odd_is_priv_act := thread_is_priv (nroot .@ "priv_odd");
             |}.
  1: apply (thread_extra 1).
  1, 2: apply _. 
  all: cycle 2; simpl in *; unfold cur_n in *.
  - apply thread_is_action_of.
  - intros ??%eq_sym%pick_act_ns_nth_disj_neq; solve_ndisj.
  - intros ?->. apply pick_act_dom.
  - rewrite /thread_is_priv. solve_decision. 
  - intros. inversion STEP; subst; auto.
    2: { apply pick_act_ns_nth_disj_neq in H; [done| solve_ndisj]. }
    apply coPset_nth_inj in H. inversion H. subst.
    rewrite even_plus1_negb Nat.negb_even in H3. 
    repeat split; lia || auto.
  - intros. inversion STEP; subst; auto.
    apply coPset_nth_inj in H. inversion H. subst.
    rewrite odd_plus1_negb Nat.negb_odd in H1. 
    repeat split; lia || auto.
  - intros. inversion STEP; subst; auto.
    red in PRIV. symmetry in PRIV.
    apply pick_act_ns_nth_disj_neq in PRIV; try solve_ndisj. done.  
  - intros. eexists. econstructor.
    by rewrite even_plus1_negb Nat.negb_even.
  - intros. eexists. econstructor.
    by rewrite odd_plus1_negb Nat.negb_odd.
  - intros. do 2 eexists. split; [| apply thread_loop].
    { reflexivity. }
    by rewrite odd_plus1_negb Nat.negb_odd.
  - intros. by rewrite !thread_AM_lr_exact.
  - reflexivity.
  - by rewrite !thread_AM_lr_exact.
  - intros ? (?&?&T1) (?&?&?&T2).
    inversion T1.
    2: { symmetry in H0. apply eq_sym, pick_act_ns_nth_disj_neq in H0; [done | solve_ndisj]. }
    inversion T2; subst. 
    { red in H. symmetry in H. 
      edestruct @pick_act_ns_nth_disj_neq; [| apply H]. solve_ndisj. }
    subst. edestruct even_odd_False; eauto.
Qed. 
