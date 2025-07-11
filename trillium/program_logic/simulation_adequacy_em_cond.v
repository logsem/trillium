From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From trillium.traces Require Export traces_match trace_utils exec_traces trace_len.
From trillium.program_logic Require Export weakestpre adequacy_cond iris_em.


(* TODO: move *)
Section TraceUtils.
  Context {A B: Type}. 

  Lemma from_trace_simpl (a: A):
    from_trace (⟨ a ⟩: trace A B) = (infnil: inflist (B * A)).
  Proof using.
    by rewrite (inflist_unfold_fold (from_trace ⟨ a ⟩)).
  Qed.

  Fixpoint ft_prepend (ft: finite_trace A B) s ℓ :=
    match ft with
    | {tr[ a ]} => {tr[ s ]} :tr[ℓ]: a
    | ft' :tr[ b ]: a => (ft_prepend ft' s ℓ) :tr[ b ]: a
    end.

  Fixpoint trace_take_fwd (n : nat) (tr : trace A B) : finite_trace A B :=
    match tr with
    | ⟨s⟩ => {tr[ s ]}
    | s -[ℓ]-> r => match n with
                  | 0 => {tr[s]}
                  | S n => ft_prepend (trace_take_fwd n r) s ℓ
                  end
    end.

  
  Fixpoint ft_reverse (ft: finite_trace A B) :=
    match ft with
    | {tr[ a ]} => {tr[ a ]}
    | ft' :tr[ ℓ ]: a => ft_prepend (ft_reverse ft') a ℓ
    end.  

  Lemma trace_take_0_first (tr: trace A B):
    trace_take 0 tr = {tr[ trfirst tr ]}.
  Proof using.
    destruct tr; done.
  Qed. 

  Lemma trace_take_step (tr: trace A B) n a b:
    trace_take (S n) (a -[ b ]-> tr) = (trace_take n tr) :tr[ b ]: a.
  Proof. done. Qed. 

  Lemma trace_take_fwd_0_first (tr: trace A B):
    trace_take_fwd 0 tr = {tr[ trfirst tr ]}.
  Proof using.
    destruct tr; done.
  Qed. 

  Lemma trace_take_fwd_step (tr: trace A B) n a b:
    trace_take_fwd (S n) (a -[ b ]-> tr) = ft_prepend (trace_take_fwd n tr) a b.
  Proof. done. Qed. 

  Lemma inflist_drop_0 (ietr: inflist (B * A)): inflist_drop 0 ietr = ietr.
  Proof. done. Qed. 

  Lemma ttf_inf_prepend_rewrite (tr: trace A B) (ietr: inflist (B * A)) a b n
    (EQ: (infcons (b, a) ietr) = inflist_drop n (from_trace tr)):
    trace_take_fwd (S n) tr = (trace_take_fwd n tr) :tr[ b ]: a.
  Proof using.
    generalize dependent a. generalize dependent b. generalize dependent tr. generalize dependent ietr.
    induction n.
    { intros. rewrite trace_take_fwd_0_first.
      rewrite inflist_drop_0 in EQ.
      destruct tr.
      { rewrite from_trace_simpl in EQ. done. }
      simpl in EQ.
      rewrite (inflist_unfold_fold (from_trace (s -[ ℓ ]-> tr))) in EQ. simpl in EQ.
      inversion EQ. subst.
      rewrite trace_take_fwd_step. rewrite trace_take_fwd_0_first. done. }
    intros.
    destruct tr.
    { rewrite (inflist_unfold_fold (from_trace ⟨ s ⟩)) in EQ. done. }
    simpl in EQ. apply IHn in EQ.
    rewrite !trace_take_fwd_step.
    by rewrite EQ.
  Qed.

  Lemma inflist_drop_next (iex: inflist (B * A)) a b irest n
    (DROP: infcons (b, a) irest = inflist_drop n iex):
    inflist_drop (S n) iex = irest.
  Proof using.
    replace (S n) with (1 + n) by lia. 
    rewrite inflist_drop_add. rewrite -DROP.
    done.
  Qed.

  CoInductive inflist_equiv: inflist (B * A) -> inflist (B * A) -> Prop :=
  | ie_nil: inflist_equiv infnil infnil
  | ie_cons il1 il2 a b (EQ: inflist_equiv il1 il2):
    inflist_equiv (infcons (b, a) il1) (infcons (b, a) il2)
  .

  Lemma from_to_trace_equiv (il: inflist (B * A)) a:
    inflist_equiv il (from_trace (to_trace a il)).
  Proof using. 
    generalize dependent il. generalize dependent a.
    cofix CIH.
    intros. destruct il.
    { clear CIH.
      rewrite (inflist_unfold_fold (from_trace (to_trace a infnil))). simpl.
      constructor. }
    destruct x.
    rewrite (trace_unfold_fold (to_trace a (infcons (b, a0) il))). simpl.
    rewrite (inflist_unfold_fold (from_trace (a -[ b ]-> to_trace a0 il))). simpl.
    destruct il.
    { econstructor; eauto. }
    destruct x. econstructor. eauto.
  Qed.

  Global Instance inflist_equiv_refl:
    Reflexive inflist_equiv.
  Proof using.
    red. cofix CIH.
    intros. destruct x; [by constructor| ].
    destruct x. constructor. done.
  Qed.

  Lemma trfirst_to_trace a (itr: inflist (B * A)):
    trfirst (to_trace a itr) = a.
  Proof using.
    destruct itr; try done. simpl.
    by destruct x.
  Qed.

  Lemma traces_match_inflist_equiv_impl {U V: Type} (etr: trace U V) ST1 ST2 L1 L2 s1:
    Proper (inflist_equiv ==> impl) (fun atr => @traces_match _ B _ A ST1 ST2 L1 L2 etr (to_trace s1 atr)).
  Proof using.
    generalize dependent etr. generalize dependent s1.
    cofix CIH.
    intros. red. intros ????.
    inversion H0; subst.
    { rewrite (trace_unfold_fold (to_trace s1 x)) in H1. 
      destruct x; try done.
      2: { destruct x. done. }
      simpl in H1. inversion H1. subst. by inversion H. }
    rewrite (trace_unfold_fold (to_trace s1 x)) in H1. 
    destruct x; try done.
    simpl in H1. destruct x. inversion H1. subst. 
    inversion H. subst.
    rewrite (trace_unfold_fold (to_trace s1 (infcons (b, a) il2))). simpl.
    econstructor.
    5: { eapply CIH; eauto. }
    all: eauto.
    rewrite trfirst_to_trace in H5. by rewrite trfirst_to_trace. 
  Qed.

  Global Instance inflist_equiv_sym:
    Symmetric inflist_equiv. 
  Proof using.
    red. cofix CIH.
    intros. inversion H; subst; try done.
    constructor. by apply CIH. 
  Qed. 

End TraceUtils.


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
              let Φs := map (fun i _ => em_thread_post i%nat (em_GS0 := iem_fairnessGS _ _)) (locales_of_list es) in
              config_wp ∗
              wptp s es Φs ∗
              rel_always_holds s Φs R (es, σ1) s1)).

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
    continued_simulation_cond R C (trace_singleton (es, σ1)) (trace_singleton s1).
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
    
    iExists state_interp, (λ _ _, ⌜ True ⌝%I), _, (fun τ _ => em_thread_post τ).

    iMod ("Hwp" with "[$PHYS $LM_INIT]") as "(CWP & WP & RAH)". 
    iModIntro. simpl. iFrame "INIT MSI WP CWP".

    (* TODO: make a lemma *)
    iIntros (??????) "SI POSTS".
    rewrite /rel_always_holds. iDestruct ("RAH" with "[][][]SI POSTS") as "R".
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
    - eapply (strong_simulation_adequacy_general_multiple s) => //.
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

  Definition test_trace: trace nat nat :=
    0 -[ 0 ]-> (1 -[ 1 ]-> (2 -[ 2 ]-> (3 -[ 3 ]-> ⟨ 4 ⟩))).
  Compute (trace_take 3 test_trace).
  Compute (trace_take_fwd 3 test_trace).


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
      traces_match lbl_rel state_rel locale_step (@mtrans M) extr mtr /\ trfirst mtr = s1) \/
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
  
End adequacy.
