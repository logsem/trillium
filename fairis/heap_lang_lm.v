From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
(* From fairness Require Import fairness. *)
From fairis Require Import fuel resources.
From heap_lang Require Export lang tactics notation heap_lang_defs.


Class heapGpreS Σ `(LM: LiveModel heap_lang M) := HeapPreG {
  heapGpreS_inv :: invGpreS Σ;
  heapGpreS_gen_heap :: heap1GpreS Σ;
  heapGpreS_fairness :: fairnessGpreS LM Σ;
}.

Class heapGS Σ `(LM:LiveModel heap_lang M) := HeapG {
  heap_inG :: heapGpreS Σ LM;
  heap_invGS : invGS_gen HasNoLc Σ;
  heap_gen_heapGS :: heap1GS Σ;
  heap_fairnessGS :: fairnessGS LM Σ;
}.

Definition heapΣ (M : FairModel) : gFunctors :=
  #[ invΣ; heap1Σ; fairnessΣ heap_lang M ].

Global Instance subG_heapPreG {Σ} `{LM : LiveModel heap_lang M} :
  subG (heapΣ M) Σ → heapGpreS Σ LM.
Proof. solve_inG. Qed.


#[global] Instance heapG_irisG `{LM:LiveModel heap_lang M} `{!heapGS Σ LM} : irisG heap_lang LM Σ := {
    iris_invGS := heap_invGS;
    state_interp extr auxtr :=
      (⌜valid_state_evolution_fairness extr auxtr⌝ ∗
       gen_heap_interp (trace_last extr).2.(heap) ∗
       model_state_interp (trace_last extr).1 (trace_last auxtr))%I ;
    fork_post tid := λ _, (tid ↦M ∅)%I;
}.
