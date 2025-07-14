From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From trillium.traces Require Export traces_match trace_utils exec_traces trace_len.
From trillium.program_logic Require Export weakestpre adequacy iris_em.


Section adequacy.
  Context `{EM: ExecutionModel Λ M}.
  Context {LG_EM: LangEM Λ}.
  Context (R: execution_trace Λ → auxiliary_trace M → Prop). 
  
  Definition wp_premise
    (Σ: gFunctors)
    (s: stuckness) (e: expr Λ) σ1 (s1: mstate M)
    (p: em_init_param)
    := 
    (∀ `{Hinv : @IEMGS _ _ LG_EM EM Σ},
        let _ := IEM_irisG LG_EM EM in
        let eGS := iem_fairnessGS _ _ in
        ⊢ (lgem_init_resource ([e], σ1) (lgem_GS0 := iem_phys _ _) ∗
             em_init_resource s1 p (em_GS0 := iem_fairnessGS _ _)
           ={⊤}=∗
              config_wp ∗
              WP e @ s; locale_of [] e; ⊤ {{ v, em_thread_post (locale_of [] e) v (em_GS0 := eGS) }} ∗
              rel_always_holds0 R s state_interp (fun v => em_thread_post (locale_of [] e) v (em_GS0 := eGS)) e σ1 s1)).

  Definition wp_premise_multiple
    (Σ: gFunctors)
    (s: stuckness) es σ1 (s1: mstate M)
    (p: em_init_param)
    := 
    (∀ `{Hinv : @IEMGS _ _ LG_EM EM Σ},
        let _ := IEM_irisG LG_EM EM in
        ⊢ (lgem_init_resource (es, σ1) (lgem_GS0 := iem_phys _ _) ∗
             em_init_resource s1 p (em_GS0 := iem_fairnessGS _ _)
           ={⊤}=∗
              let Φs := map (fun τ v => em_thread_post τ v (em_GS0 := iem_fairnessGS _ _)) (locales_of_list es) in
              config_wp ∗
              wptp s es Φs ∗
              rel_always_holds s Φs R (es, σ1) s1)).

  Lemma wp_premise_single Σ
    s (e1: expr Λ) σ1 s1 p:
    wp_premise Σ s e1 σ1 s1 p -> wp_premise_multiple Σ s [e1] σ1 s1 p.
  Proof using.
    rewrite /wp_premise /wp_premise_multiple.
    iIntros "%WP1 % [HEAP INIT]".
    iMod (WP1 Hinv with "[$HEAP $INIT]") as "(CWP & WP1 & RAH)".
    iFrame. set_solver. 
  Qed.

  Theorem strong_simulation_adequacy_general_multiple
    `{hPre: @IEMGpreS _ _ LG_EM EM Σ}
    (s: stuckness) es σ1 (s1: M)
    (p: em_init_param)    
    :
    length es ≥ 1 ->
    rel_finitary R →
    em_is_init_st (es, σ1) s1 ->
    em_valid_state_evolution_fairness {tr[ (es, σ1) ]} {tr[ s1 ]} ->
    (wp_premise_multiple Σ s es σ1 s1 p) ->
    continued_simulation R (trace_singleton (es, σ1)) (trace_singleton s1).
  Proof.
    intros LEN Hfin INIT VALID1 WPS.
    apply (wp_strong_adequacy_multiple_with_trace_inv Λ M Σ s); try done.

    iIntros (?) "".

    (* iMod (gen_heap_init (heap σ1)) as (genheap)" [Hgen [Hσ _]]".   *)
    iMod (lgem_initialization Σ (es, σ1)) as (pGS) "[PHYS INIT]".
    Unshelve. 2: by apply hPre.
    iMod (em_initialization _ s1 (es, σ1) p) as (fGS) "[LM_INIT MSI]"; [done| ].
    Unshelve. 2: by apply hPre. 

    set (iemG := {| iem_fairnessGS := fGS; iem_phys := pGS |}).
    iPoseProof (WPS iemG) as "Hwp". clear WPS.
    
    iExists state_interp, (λ _ _, ⌜ True ⌝%I), _, (em_thread_post).

    iMod ("Hwp" with "[$PHYS $LM_INIT]") as "(CWP & WP & RAH)". 
    iModIntro. simpl.
    (* iFrame "INIT MSI WP CWP". *)

    iFrame "INIT MSI CWP WP".

    (* TODO: make a lemma *)
    iIntros (??????????) "SI POSTS".
    rewrite /rel_always_holds. iDestruct ("RAH" with "[][][][][][][] SI POSTS") as "R".
    all: try by done.
    iSplit. 
    - iModIntro; iIntros "[$ ?]"; done.
    - eauto. 
  Qed.

  Theorem strong_simulation_adequacy_inftraces_multiple Σ
    `{hPre: @IEMGpreS _ _ LG_EM EM Σ} (s: stuckness) 
    es σ1 (s1: M)
    (p: em_init_param)
    (iex : inf_execution_trace Λ)
    (Hvex : valid_inf_exec (trace_singleton (es, σ1)) iex)
    :
    length es ≥ 1 ->
    rel_finitary R →
    em_is_init_st (es, σ1) s1 ->
    (wp_premise_multiple Σ s es σ1 s1 p) ->
    exists iatr,
      @valid_inf_system_trace _ M
        (@continued_simulation Λ M R)
        (trace_singleton (es, σ1))
        (trace_singleton s1)
        iex
        iatr.
  Proof.
    intros LEN Hfin Hwp.
    eexists.
    eapply produced_inf_aux_trace_valid_inf.
    Unshelve.
    - econstructor.
    - eapply (strong_simulation_adequacy_general_multiple s) => //.
    - done.
  Qed.
  
  Theorem strong_simulation_adequacy_traces_multiple Σ
    `{hPre: @IEMGpreS _ _ LG_EM EM Σ} (s: stuckness) 
    es σ1 (s1: M)
    (p: em_init_param)
    extr
    (Hvex : extrace_valid extr)
    (Hexfirst : trfirst extr = (es, σ1))

    (valid_step: cfg Λ -> olocale Λ → cfg Λ → 
                 mstate M → mlabel M → mstate M -> Prop)
    (state_rel: cfg Λ -> mstate M -> Prop)
    (lbl_rel: olocale Λ -> mlabel M -> Prop)
    (STEP_LBL_REL: forall c1 oζ c2 δ1 ℓ δ2,
                 valid_step c1 oζ c2 δ1 ℓ δ2 ->
                 lbl_rel oζ ℓ)
    (STEP_MTRANS: forall c1 oζ c2 δ1 ℓ δ2,
                 valid_step c1 oζ c2 δ1 ℓ δ2 ->
                 mtrans δ1 ℓ δ2)
    (R_ST: forall extr mtr, R extr mtr -> state_rel (trace_last extr) (trace_last mtr))
    (R_STEP: forall extr mtr, R extr mtr -> valid_state_evolution_fairness valid_step extr mtr)

    :
    length es ≥ 1 ->
    rel_finitary R →
    em_is_init_st (es, σ1) s1 ->
    (wp_premise_multiple Σ s es σ1 s1 p) ->
    ∃ (mtr : trace (mstate M) (mlabel M)), 
      traces_match lbl_rel state_rel locale_step (@mtrans M) extr mtr /\
      trfirst mtr = s1. 
  Proof.
    intros ? Hfin INIT Hwp.
    have [iatr MATCH] : exists iatr,
        @valid_inf_system_trace
          Λ M
          (@continued_simulation
             Λ
             M
             R)
          (trace_singleton (es, (trfirst extr).2))
          (trace_singleton s1)
          (from_trace extr)
          iatr.
    { eapply (strong_simulation_adequacy_inftraces_multiple _ s); eauto.
      1: eapply from_trace_preserves_validity; eauto; first econstructor.
      all: try by rewrite Hexfirst. }
    rewrite Hexfirst in MATCH. simpl in *. 
    exists (to_trace s1 iatr).

    split.
    2: { by rewrite to_trace_trfirst. }

    eapply vist_impl in MATCH.
    2: { apply continued_simulation_rel. }
    
    eapply (valid_inf_system_trace_implies_traces_match
                       valid_step                       
                       state_rel
                       lbl_rel
                       ltac:(idtac)
                       ltac:(idtac)
                       R) in MATCH; cycle 1.
    { intros ?? ?. eauto. }
    { intros ?? ?. eauto. }
    { apply from_trace_spec. simpl.
      rewrite Hexfirst. done. }
    { apply to_trace_spec. }
    Unshelve. 2,3: by eauto.
    
    apply MATCH. 
  Qed.
  
  Theorem strong_simulation_adequacy_traces Σ
    `{hPre: @IEMGpreS _ _ LG_EM EM Σ} (s: stuckness) 
    (e: expr Λ) σ1 (s1: M)
    (p: em_init_param)
    extr
    (Hvex : extrace_valid extr)
    (Hexfirst : trfirst extr = ([e], σ1))

    (valid_step: cfg Λ -> olocale Λ → cfg Λ → 
                 mstate M → mlabel M → mstate M -> Prop)
    (state_rel: cfg Λ -> mstate M -> Prop)
    (lbl_rel: olocale Λ -> mlabel M -> Prop)
    (STEP_LBL_REL: forall c1 oζ c2 δ1 ℓ δ2,
                 valid_step c1 oζ c2 δ1 ℓ δ2 ->
                 lbl_rel oζ ℓ)
    (STEP_MTRANS: forall c1 oζ c2 δ1 ℓ δ2,
                 valid_step c1 oζ c2 δ1 ℓ δ2 ->
                 mtrans δ1 ℓ δ2)
    (R_ST: forall extr mtr, R extr mtr -> state_rel (trace_last extr) (trace_last mtr))
    (R_STEP: forall extr mtr, R extr mtr -> valid_state_evolution_fairness valid_step extr mtr)

    :
    rel_finitary R →
    em_is_init_st ([e], σ1) s1 ->
    (wp_premise Σ s e σ1 s1 p) ->
    ∃ (mtr : trace (mstate M) (mlabel M)), 
      traces_match lbl_rel state_rel locale_step (@mtrans M) extr mtr /\
      trfirst mtr = s1. 
  Proof.
    intros. eapply strong_simulation_adequacy_traces_multiple; last first.
    { by eapply wp_premise_single. }
    all: by eauto.
  Qed.

End adequacy.
