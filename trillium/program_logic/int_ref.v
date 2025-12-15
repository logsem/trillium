From iris.proofmode Require Import tactics.
From trillium.traces Require Export inftraces trace trace_utils.


Section IntRef.
  Context {St1 L1 St2 L2: Type}. 
  Context (R: finite_trace St1 L1 -> finite_trace St2 L2 -> Prop). 
  
  (* TODO: find existing? *)
  Definition int_ref_inf (tr1: trace St1 L1) (tr2: trace St2 L2) :=
    forall i, R (trace_take_fwd i tr1) (trace_take_fwd i tr2).

  Lemma int_ref_int_singleton (s1: St1) (s2: St2)
    (REL0: R (trace_singleton s1) (trace_singleton s2)):
    int_ref_inf ⟨ s1 ⟩ ⟨ s2 ⟩.
  Proof using.
    red. intros.
    destruct i.
    { done. }
    do 2 (erewrite trace_take_fwd_short' with (i := S _) (j := 0); [| by rewrite from_trace_simpl| lia]). 
    by rewrite !trace_take_fwd_0_first.
  Qed.

End IntRef.


Section IntRefOne.
  Context {St1 L1: Type}.
  Context (R: finite_trace St1 L1 -> Prop). 

  Definition int_ref_inf_one tr := forall i, R (trace_take_fwd i tr).


End IntRefOne.


Lemma int_ref_inf_impl {St1 L1 St2 L2}
  (R Q: finite_trace St1 L1 -> finite_trace St2 L2 -> Prop)
  (tr1: trace St1 L1) (tr2: trace St2 L2)
  (IMPL: forall tr1 tr2, R tr1 tr2 -> Q tr1 tr2):
  int_ref_inf R tr1 tr2 -> int_ref_inf Q tr1 tr2. 
Proof using. intros ? ?. by apply IMPL. Qed. 

Lemma int_ref_inf_proj_one {St1 L1 St2 L2} (R: finite_trace St1 L1 -> Prop)
  (tr1: trace St1 L1) (tr2: trace St2 L2):
  int_ref_inf (fun tr' _ => R tr') tr1 tr2 -> int_ref_inf_one R tr1.
Proof using. done. Qed.
