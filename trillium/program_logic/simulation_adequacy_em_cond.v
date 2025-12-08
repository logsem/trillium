From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From trillium.traces Require Export traces_match trace_utils exec_traces trace_len.
From trillium.program_logic Require Export weakestpre adequacy_cond iris_em.


Section AdequacyGen.
  Context `{EM: ExecutionModel Λ M}.
  Context {LG_EM: LangEM Λ}.
  Context (R: execution_trace Λ → auxiliary_trace M → Prop). 

  Context (C: execution_trace Λ -> Prop).
  Context {C_DEC: ∀ ex, Decision (C ex)} {ML_INH: Inhabited (mlabel M)}.
  Context (FILTER_PCL: filter_pref_closed C). 
                       
  Definition PR_premise_multiple
    (Σ: gFunctors)
    (s: stuckness) es σ1 (s1: mstate M)
    (p: em_init_param)
    := 
    (∀ `{Hinv : @IEMGS _ _ LG_EM EM Σ},
        let _ := IEM_irisG LG_EM EM in
        ⊢ (lgem_init_resource (es, σ1) (lgem_GS0 := iem_phys _ _) ∗
             em_init_resource s1 p (em_GS0 := iem_fairnessGS _ _)
           ={⊤}=∗
              let Φs := map (em_thread_post (em_GS0 := iem_fairnessGS _ _)) (locales_of_list es) in              
              ∃ trace_inv
                (PR: ProgressResource state_interp trace_inv fork_post C),
              config_wp ∗
              PR s (trace_singleton (es, σ1)) Φs ∗
              trace_inv {tr[ (es, σ1) ]} {tr[ s1 ]} ∗
              rel_always_holds_with_trace_inv s trace_inv Φs R (es, σ1) s1)).

  (* TODO: move *)
  Lemma trace_always_holds_with_True `{Hinv : @IEMGS _ _ LG_EM EM Σ}
    s Φs c δ:
    rel_always_holds_with_trace_inv s (fun _ _ => ⌜ True ⌝) Φs R c δ ⊣⊢ 
    rel_always_holds s Φs R c δ.
  Proof using.
    clear. 
    rewrite /rel_always_holds /rel_always_holds_with_trace_inv.
    repeat (iApply bi.forall_proper; red; intros).
    repeat (iApply bi.wand_proper; [done| ]).
    iSplit; [| set_solver]. iIntros "X". by iApply "X". 
  Qed.

  (* TODO: ? move this and PR_premise_multiple to adequacy_cond *)
  Theorem PR_strong_simulation_adequacy_general_multiple
    `{hPre: @IEMGpreS _ _ LG_EM EM Σ}
    (s: stuckness) es σ1 (s1: M)
    (p: em_init_param)    
    :
    length es ≥ 1 ->
    rel_finitary R →
    em_is_init_st (es, σ1) s1 ->
    em_valid_state_evolution_fairness {tr[ (es, σ1) ]} {tr[ s1 ]} ->
    (PR_premise_multiple Σ s es σ1 s1 p) ->
    continued_simulation_cond R C (trace_singleton (es, σ1)) (trace_singleton s1).
  Proof.
    intros LEN Hfin INIT VALID1 PRP.
    apply (wp_strong_adequacy_multiple_with_trace_inv Λ M Σ s); try done.

    iIntros (?) "".

    (* iMod (gen_heap_init (heap σ1)) as (genheap)" [Hgen [Hσ _]]".   *)
    iMod (lgem_initialization Σ (es, σ1)) as (pGS) "[PHYS INIT]".
    Unshelve. 2: by apply hPre.
    iMod (em_initialization _ s1 (es, σ1) p) as (fGS) "[LM_INIT MSI]"; [done| ].
    Unshelve. 2: by apply hPre. 

    set (iemG := {| iem_fairnessGS := fGS; iem_phys := pGS |}).
    iPoseProof (PRP iemG) as "PRP". clear PRP.
    
    iMod ("PRP" with "[$PHYS $LM_INIT]") as (ti PR) "(CWP & PR & TI & RAH)".
    iModIntro.
    iExists state_interp, ti.
    iExists (map em_thread_post (locales_of_list es)), em_thread_post.
    simpl. iFrame "INIT MSI PR CWP TI".
    done. 
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
    (PR_premise_multiple Σ s es σ1 s1 p) ->
    exists iatr,
      @valid_inf_system_trace _ M
        (@continued_simulation_cond Λ M R C)
        (trace_singleton (es, σ1))
        (trace_singleton s1)
        iex
        iatr.
  Proof.
    intros LEN Hfin Hwp.
    eexists.
    eapply produced_inf_aux_trace_valid_inf_cond. 
    Unshelve.
    - econstructor.
    - apply FILTER_PCL. 
    - eapply (PR_strong_simulation_adequacy_general_multiple s) => //.
    - done.
  Qed.

  Lemma vist_equiv_impl X etr atr:
    Proper (inflist_equiv ==> inflist_equiv ==> impl) (@valid_inf_system_trace Λ M X etr atr). 
  Proof using.
    (* red. intros ????.  *)
    generalize dependent etr. generalize dependent atr.
    cofix CIH.
    intros. red. intros ???????.
    inversion H1; subst.
    { inversion H. inversion H0. subst. done. }
    inversion H. inversion H0. subst.
    econstructor; eauto.
    eapply CIH; eauto.
  Qed.

  (* Definition test_trace: trace nat nat := *)
  (*   0 -[ 0 ]-> (1 -[ 1 ]-> (2 -[ 2 ]-> (3 -[ 3 ]-> ⟨ 4 ⟩))). *)
  (* Compute (trace_take 3 test_trace). *)
  (* Compute (trace_take_fwd 3 test_trace). *)

  (* TODO: move *)
  Lemma vist_strenghten extr atr
  (PASS: ∀ x, C (trace_take_fwd x extr))
  (MATCH :
    valid_inf_system_trace
      (λ (etr : execution_trace Λ) (atr : auxiliary_trace M), R etr atr ∨ ¬ C etr)
      (trace_take_fwd 0 extr) (trace_take_fwd 0 atr)
      (from_trace extr) (from_trace atr)):
    valid_inf_system_trace
      (λ (etr : execution_trace Λ) (atr : auxiliary_trace M), R etr atr)
      (trace_take_fwd 0 extr) (trace_take_fwd 0 atr)
      (from_trace extr) (from_trace atr).
  Proof using.
    revert MATCH.
    replace (from_trace extr) with (inflist_drop 0 (from_trace extr)) by done.
    replace (from_trace atr) with (inflist_drop 0 (from_trace atr)) by done.

    generalize 0.
    cofix CIH.
    intros. inversion MATCH; subst; simpl in *.
    { clear CIH. 
      econstructor. destruct H3; eauto.
      by destruct H0. }

    destruct H1.
    2: { destruct H1. eauto. }

    econstructor; eauto. 
    move CIH at bottom.
    specialize (CIH (S n)).
    do 2 (erewrite ttf_inf_prepend_rewrite in CIH; eauto).
    do 2 (erewrite inflist_drop_next in CIH; eauto).
  Qed.

  (* TODO: move *)
  Lemma from_trace_cons_simpl {St L: Type} tr (s: St) (l: L):
    from_trace (s -[l]-> tr) = infcons (l, trfirst tr) (from_trace tr). 
  Proof using.
    by rewrite (inflist_unfold_fold (from_trace (s -[ l ]-> tr))).
  Qed.

  (* TODO: move *)
  Lemma trace_take_fwd_short {St L: Type} (tr: trace St L) j
    (SHORT: inflist_drop j (from_trace tr) = infnil):
  trace_take_fwd (S j) tr = trace_take_fwd j tr.
  Proof using.
    clear -SHORT.
    revert SHORT. generalize dependent tr. induction j.
    { intros. rewrite inflist_drop_0 in SHORT.
      destruct tr; try done.
      simpl in SHORT. by rewrite from_trace_cons_simpl in SHORT. }
    intros. destruct tr; try done.
    rewrite trace_take_fwd_step. rewrite IHj.
    2: { done. }
    simpl. done.
  Qed. 

  (* TODO: move *)
  Lemma trace_take_fwd_short' {St L: Type} (tr: trace St L) j i
    (SHORT: inflist_drop j (from_trace tr) = infnil)
    (LE: j <= i):
  trace_take_fwd i tr = trace_take_fwd j tr.
  Proof using.
    clear -SHORT LE. apply Nat.le_sum in LE as [d ->].    
    generalize dependent j. induction d.
    { intros. by rewrite Nat.add_0_r. }
    intros.

    specialize (IHd j ltac:(eauto)).
    rewrite -IHd.
    rewrite Nat.add_succ_r. apply trace_take_fwd_short.
    rewrite Nat.add_comm inflist_drop_add SHORT.
    destruct d; done. 
  Qed.

  (* TODO: move, find existing? *)
  Definition int_ref_inf {St1 L1 St2 L2}  (tr1: trace St1 L1) (tr2: trace St2 L2)
    (R: finite_trace St1 L1 -> finite_trace St2 L2 -> Prop) :=
    forall i, R (trace_take_fwd i tr1) (trace_take_fwd i tr2).    

  (* TODO: ? move *)
  Lemma vist_int_ref_inf etr mtr
    (MATCH:
    valid_inf_system_trace
      (λ (etr : execution_trace Λ) (atr : auxiliary_trace M), R etr atr)
      (trace_take_fwd 0 etr) (trace_take_fwd 0 mtr) (from_trace etr)
      (from_trace mtr)):
    int_ref_inf etr mtr R.
  Proof using.
    red. 
    intros. clear -i MATCH.

    revert MATCH.
    replace (from_trace etr) with (inflist_drop 0 (from_trace etr)) by done.
    replace (from_trace mtr) with (inflist_drop 0 (from_trace mtr)) by done.
    
    remember 0 as j. assert (j <= i) by lia. clear Heqj.
    apply Nat.le_sum in H as [d ->].
    
    generalize dependent etr.
    generalize dependent mtr. 
    generalize dependent j.
    induction d.
    - intros. rewrite Nat.add_0_r.
      eapply valid_inf_system_trace_inv; eauto. 
    - intros. inversion MATCH; subst; try done.
      + do 2 (erewrite trace_take_fwd_short' with (i := j + S d); [| by eauto| lia]).
        done.           
      + replace (j + S d) with (S j + d) by lia.
        erewrite <- ttf_inf_prepend_rewrite in H6; [| done]. 
        erewrite <- ttf_inf_prepend_rewrite in H6; [| done].
        apply inflist_drop_next in H, H0.
        subst.
        eauto.
  Qed.

  Theorem PR_strong_simulation_adequacy_traces_multiple Σ
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
    (PR_premise_multiple Σ s es σ1 s1 p) ->
    (∃ (mtr : trace (mstate M) (mlabel M)), 
      traces_match lbl_rel state_rel locale_step (@mtrans M) extr mtr /\ 
      trfirst mtr = s1 /\
      int_ref_inf extr mtr R
    ) \/
    exists k, ¬ C (trace_take_fwd k extr). 
  Proof.
    intros ? Hfin INIT Hwp.
    have [iatr MATCH] : exists iatr,
        @valid_inf_system_trace
          Λ M
          (@continued_simulation_cond Λ M R C)
          (trace_singleton (es, (trfirst extr).2))
          (trace_singleton s1)
          (from_trace extr)
          iatr.
    { eapply (strong_simulation_adequacy_inftraces_multiple _ s); eauto.
      1: eapply from_trace_preserves_validity; eauto; first econstructor.
      all: try by rewrite Hexfirst. }
    rewrite Hexfirst in MATCH. simpl in *. 

    Require Import Coq.Logic.Classical.
    destruct (classic (exists k, ¬ C (trace_take_fwd k extr))) as [| PASS0]; [tauto| ]. 
    left.
    pose proof (@not_exists_forall_not _ _ PASS0) as PASS. clear PASS0. simpl in PASS.

    exists (to_trace s1 iatr).    

    assert ({tr[ (es, σ1) ]} = trace_take 0 extr).
    { simpl. destruct extr; simpl in *; by rewrite Hexfirst. }
    assert ({tr[ s1 ]} = trace_take 0 (to_trace s1 iatr)).
    { inversion MATCH; subst; done. }
    rewrite H0 H1 in MATCH.

    eapply vist_impl in MATCH.
    2: { intros.
         apply continued_simulation_cond_rel in H2; [| done].
         pattern etr, atr in H2. apply H2. }

    eapply vist_equiv_impl in MATCH.
    3: { eapply (from_to_trace_equiv _ s1). }
    2: by apply inflist_equiv_refl. 

    apply vist_strenghten in MATCH.
    2: { intros. apply NNP_P. eauto. }

    apply and_assoc. split.
    2: { by apply vist_int_ref_inf. }

    eapply (valid_inf_system_trace_implies_traces_match
                       valid_step                       
                       state_rel
                       lbl_rel
                       ltac:(idtac)
                       ltac:(idtac)
                       R) in MATCH; cycle 1.  
    { done. }
    { done. }
    { apply from_trace_spec. simpl.
      by destruct extr. }
    { apply to_trace_spec. }
    Unshelve. 2,3: by eauto.

    pose proof (to_trace_trfirst s1 iatr).
    split; [| done].
    rewrite trace_take_fwd_0_first in MATCH. rewrite H2 in MATCH.
    simpl in MATCH.
    eapply traces_match_inflist_equiv_impl; [| done].
    symmetry. apply from_to_trace_equiv. 
  Qed.

End AdequacyGen.


Section adequacy.
  Context `{EM: ExecutionModel Λ M}.
  Context {LG_EM: LangEM Λ}.
  Context (R: execution_trace Λ → auxiliary_trace M → Prop). 

  Context (C: execution_trace Λ -> Prop).
  Context {C_DEC: ∀ ex, Decision (C ex)} {ML_INH: Inhabited (mlabel M)}.
  Context (FILTER_PCL: filter_pref_closed C). 
                       
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
              let Φs := map (em_thread_post (em_GS0 := iem_fairnessGS _ _)) (locales_of_list es) in
              config_wp ∗
              wptp s es Φs ∗
              rel_always_holds s Φs R (es, σ1) s1)).
  
  Program Definition WptpPR {Σ} {Hinv : @IEMGS _ _ LG_EM EM Σ}
    (iG := IEM_irisG LG_EM EM)
    : ProgressResource state_interp (fun _ _ => ⌜ True ⌝%I) fork_post C :=
    {| pr_pr := (fun s etr Φs => wptp s (trace_last etr).1 Φs) |}. 
  Next Obligation. 
    intros. simpl.
    iIntros "WPS TI".
    iPoseProof (wptp_of_val_post with "WPS") as "PP".
    iMod (pre_step_elim with "[$TI] [$]") as "(TI & POSTS & CLOS)".
    iModIntro. iFrame.  
  Qed.
  Next Obligation. 
    clear R FILTER_PCL C_DEC.
    intros. rewrite H0.
    iIntros "? WPS".
    iMod (wptp_not_stuck_same _ _ _ _ [] with "[$] [WPS]") as "(?&?&%NS)". 
    3: by iFrame.
    { eauto. }
    { erewrite app_nil_l, app_nil_r.
      erewrite <- surjective_pairing. apply trace_ends_in_last. }
    iModIntro. iFrame.
    iPureIntro. intros. subst. rewrite -H0.
    eapply NS; eauto.
    apply last_eq_trace_ends_in in H0. rewrite H0. simpl. set_solver.
  Qed.
  Final Obligation. 
    intros.
    iIntros "?? _ ? _". (** for usual wptp with the same TI, trivial trace invariant and any trace condition don't matter *)
    iMod (take_step with "[$] [$] [$]") as "X".
    1, 2: by eauto.
    { by rewrite H0. }
    iModIntro. iApply (step_fupdN_mono with "[$]").
    iIntros "X". iMod "X" as "(?&?)". iModIntro. iFrame. 
    setoid_rewrite bi.True_sep'. by rewrite H0.
  Qed.

  Lemma wp_PR_premise Σ s es σ1 s1 p:
    wp_premise_multiple Σ s es σ1 s1 p -> PR_premise_multiple R C Σ s es σ1 s1 p.
  Proof using.
    rewrite /wp_premise_multiple /PR_premise_multiple.
    iIntros (WPS ?) "(?&?)".
    iMod (WPS with "[-]") as "(?&?&?)"; [by iFrame| ].
    iModIntro. iExists _, WptpPR. iFrame.
    iSplit; [done| ].
    by iDestruct (trace_always_holds_with_True with "[$]") as "foo".
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
    (∃ (mtr : trace (mstate M) (mlabel M)), 
      traces_match lbl_rel state_rel locale_step (@mtrans M) extr mtr /\
      trfirst mtr = s1 /\
      int_ref_inf extr mtr R) \/
    exists k, ¬ C (trace_take_fwd k extr). 
  Proof.
    intros. apply wp_PR_premise in H2.
    eapply PR_strong_simulation_adequacy_traces_multiple; eauto.
  Qed.

End adequacy.
