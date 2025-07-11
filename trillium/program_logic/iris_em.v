From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre execution_model.

(** Language that is supposed to be used along with ExecutionModel *)

Class LangEM (Λ: language) := {
    lgem_GpreS: gFunctors -> Set;
    lgem_GS: gFunctors -> Set;
    lgem_Σ: gFunctors;
    lgem_Σ_subG: forall Σ, subG lgem_Σ Σ -> lgem_GpreS Σ;

    lgem_si {Σ} `{lgem_GS Σ}: state Λ -> iProp Σ;

    lgem_init_resource {Σ: gFunctors} `{lgem_GS Σ}: cfg Λ → iProp Σ;
    lgem_initialization Σ `{lgem_GpreS Σ}: 
    forall (c: cfg Λ),
      ⊢ (|==> ∃ iemGS: lgem_GS Σ, @lgem_init_resource _ iemGS c ∗ @lgem_si _ iemGS c.2)
}.

Section IEM.
  Context {Λ M} (lg_em: LangEM Λ) (em: ExecutionModel Λ M).
  Local Existing Instance lg_em.
  Local Existing Instance em.
  
  (* TODO: the missing fact of em_GS etc. being typeclasses *)
  (*    hardens automatic resolution of their instances *)
  Class IEMGpreS Σ := IEMPreG {
    iemGpreS_inv :: invGpreS Σ;
    iemGpreS_phys :: lgem_GpreS Σ;
    iemGpreS_em :: em_preGS Σ;
  }.

  Class IEMGS Σ := IEMG {
    iem_inG :: IEMGpreS Σ;
    iem_invGS :: invGS_gen HasNoLc Σ;
    iem_phys :: lgem_GS Σ;
    iem_fairnessGS :: em_GS Σ;
  }.

  Definition iemΣ : gFunctors :=
    #[ invΣ; lgem_Σ; em_Σ ].

  (* TODO: automatize *)
  Global Instance subG_IEMPreG {Σ}:
    subG iemΣ Σ → IEMGpreS Σ.
  Proof.
    intros.
    assert (em_preGS Σ).
    { apply em_Σ_subG. solve_inG. }
    assert (lgem_GpreS Σ).
    { apply lgem_Σ_subG. solve_inG. }
    solve_inG. 
  Qed.

  #[global] Instance IEM_irisG `{iemGS: IEMGS Σ}:
  irisG Λ M Σ := {
    state_interp extr auxtr :=
      (⌜em_valid_state_evolution_fairness extr auxtr⌝ ∗
       lgem_si (trace_last extr).2 (lgem_GS0 := iem_phys) ∗
       em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := iem_fairnessGS))%I ;
    fork_post := em_thread_post (em_GS0 := iem_fairnessGS);
}.

End IEM.
