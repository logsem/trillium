From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl.
From iris.base_logic Require Export gen_heap.
From trillium.prelude Require Import classical_instances.
From trillium.program_logic Require Import weakestpre adequacy.
From trillium.fairness Require Export fairness fair_termination fairness_finiteness fuel fuel_termination map_included_utils resources.
From trillium.program_logic Require Import ectx_lifting.
From trillium.fairness.heap_lang Require Import lang.
From trillium.fairness.heap_lang Require Import tactics notation.
From trillium.fairness.heap_lang Require Import lifting.
Set Default Proof Using "Type".

Section adequacy.

Lemma posts_of_empty_mapping `{heapGS Σ M} (e1 e: expr) v (tid : nat) (tp : list expr):
  tp !! tid = Some e ->
  to_val e = Some v ->
  posts_of tp ((λ (_ : val), 0%nat ↦M ∅) ::  (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [e1] (drop (length [e1]) tp)))) -∗
  tid ↦M ∅.
Proof.
  intros Hsome Hval. simpl.
  rewrite (big_sepL_elem_of (λ x, x.2 x.1) _ (v, (λ _: val, tid ↦M ∅)%I) _) //.
  apply elem_of_list_omap.
  exists (e, (λ _: val, tid ↦M ∅)%I); split; last first.
  - simpl. apply fmap_Some. exists v. split; done.
  - destruct tp as [|e1' tp]; first set_solver. simpl.
    apply elem_of_cons.
    destruct tid as [|tid]; [left|right]; first by simpl in Hsome; simplify_eq.
    apply elem_of_lookup_zip_with. eexists tid, e, _. do 2 split =>//.
    rewrite /locale_of /=.
    rewrite list_lookup_fmap fmap_Some. simpl in Hsome.
    exists (e1 :: take tid tp, e). rewrite drop_0. split.
    + erewrite prefixes_from_lookup =>//.
    + rewrite /locale_of /= take_length_le //.
      assert (tid < length tp)%nat; last lia. by eapply lookup_lt_Some.
Qed.

Lemma from_locale_from_lookup tp0 tp tid e :
  from_locale_from tp0 tp tid = Some e <-> (tp !! (tid - length tp0)%nat = Some e ∧ (length tp0 <= tid)%nat).
Proof.
  split.
  - revert tp0 tid. induction tp as [| e1 tp1 IH]; intros tp0 tid.
    { unfold from_locale. simpl. done. }
    unfold from_locale. simpl.
    destruct (decide (locale_of tp0 e1 = tid)).
    + intros ?; simplify_eq. rewrite /locale_of /= Nat.sub_diag.
      split; [done|lia].
    + intros [H Hlen]%IH. rewrite app_length /= in H.
      rewrite app_length /= in Hlen.
      destruct tid as [|tid]; first lia.
      assert (Heq1 : (length tp0 + 1 = S (length tp0))%nat) by lia.
      rewrite Heq1 in Hlen.
      assert (length tp0 ≤ tid)%nat by lia.
      assert (Heq : (S tid - length tp0)%nat = (S ((tid - (length tp0))))%nat) by lia.
      rewrite Heq /=. split.
      * rewrite -H. f_equal. lia.
      * transitivity tid; try lia. assumption.
  - revert tp0 tid. induction tp as [|e1 tp1 IH]; intros tp0 tid.
    { set_solver. }
    destruct (decide (tid = length tp0)) as [-> | Hneq].
    + rewrite Nat.sub_diag /=. intros  [? _]. simplify_eq.
      rewrite decide_True //.
    + intros [Hlk Hlen]. assert (length tp0 < tid)%nat as Hle by lia.
      simpl. rewrite decide_False //. apply IH. split.
      * assert (tid - length tp0 = S ((tid - 1) - length tp0))%nat as Heq by lia.
        rewrite Heq /= in Hlk. rewrite -Hlk app_length /=. f_equal; lia.
      * rewrite app_length /=. apply Nat.le_succ_l in Hle. rewrite Nat.add_comm //.
Qed.

Lemma from_locale_lookup tp tid e :
  from_locale tp tid = Some e <-> tp !! tid = Some e.
Proof.
  assert (from_locale tp tid = Some e <-> (tp !! tid = Some e ∧ 0 ≤ tid)%nat) as H; last first.
  { split; intros ?; apply H; eauto. split; [done|lia]. }
  unfold from_locale. replace (tid) with (tid - length (A := expr) [])%nat at 2;
    first apply from_locale_from_lookup. simpl; lia.
Qed.

Definition indexes {A} (xs : list A) := imap (λ i _, i) xs.

Lemma locales_of_list_from_indexes (es' es : list expr) :
  locales_of_list_from es' es = imap (λ i _, length es' + i)%nat es.
Proof.
  revert es'. induction es; [done|]; intros es'.
  rewrite locales_of_list_from_cons=> /=. rewrite /locale_of.
  f_equiv; [lia|]. rewrite IHes. apply imap_ext.
  intros x ? Hin. rewrite app_length=> /=. lia.
Qed.

Lemma locales_of_list_indexes (es : list expr) :
  locales_of_list es = indexes es.
Proof. apply locales_of_list_from_indexes. Qed.

Theorem heap_lang_continued_simulation_fair_termination {FM : FairModel}
        `{FairTerminatingModel FM} {LM:LiveModel heap_lang FM} ξ a1 r1 extr :
  continued_simulation
    (sim_rel_with_user LM ξ)
    ({tr[trfirst extr]}) ({tr[initial_ls (LM := LM) a1 r1]}) →
  extrace_fairly_terminating extr.
Proof.
  apply continued_simulation_fair_termination.
  - intros ?? contra. inversion contra.
    simplify_eq. inversion H2.
  - by intros ex atr [[??]?].
  - by intros ex atr [[??]?].
Qed.

Definition rel_always_holds {Σ} `{LM:LiveModel heap_lang M} `{!heapGS Σ LM}
           (s:stuckness) (ξ : execution_trace heap_lang → finite_trace M
                  (option $ fmrole M) → Prop) (c1:cfg heap_lang)
           (c2:live_model_to_model LM) : iProp Σ :=
  ∀ ex atr c,
    ⌜valid_system_trace ex atr⌝ -∗
    ⌜trace_starts_in ex c1⌝ -∗
    ⌜trace_starts_in atr c2⌝ -∗
    ⌜trace_ends_in ex c⌝ -∗
    ⌜∀ ex' atr' oζ ℓ, trace_contract ex oζ ex' →
                      trace_contract atr ℓ atr' →
                      ξ ex' (map_underlying_trace atr')⌝ -∗
    ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗
    state_interp ex atr -∗
    posts_of c.1 ((λ _, 0%nat ↦M ∅) :: ((λ '(tnew, e), fork_post (locale_of tnew e)) <$> (prefixes_from c1.1 (drop (length c1.1) c.1)))) -∗
    |={⊤, ∅}=> ⌜ξ ex (map_underlying_trace atr)⌝.


Theorem strong_simulation_adequacy Σ `(LM:LiveModel heap_lang M)
    `{!heapGpreS Σ LM} (s: stuckness) (e1 : expr) σ1 (s1: M) (FR: gset _)
    (ξ : execution_trace heap_lang → finite_trace M (option $ fmrole M) →
         Prop) :
  rel_finitary (sim_rel_with_user LM ξ) →
  live_roles M s1 ≠ ∅ ->
  (∀ `{Hinv : !heapGS Σ LM},
    ⊢ |={⊤}=>
       (* state_interp (trace_singleton ([e1], σ1)) (trace_singleton (initial_ls (LM := LM) s1 0%nat)) ∗ *)
       ([∗ map] l ↦ v ∈ heap σ1, mapsto l (DfracOwn 1) v) -∗
       frag_model_is s1 -∗
       frag_free_roles_are (FR ∖ live_roles _ s1) -∗
       has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (M.(live_roles) s1)) ={⊤}=∗
       WP e1 @ s; locale_of [] e1; ⊤ {{ v, 0%nat ↦M ∅ }} ∗
       rel_always_holds s ξ ([e1], σ1) (initial_ls (LM := LM) s1 0%nat)) ->
  continued_simulation (sim_rel_with_user LM ξ) (trace_singleton ([e1], σ1)) (trace_singleton (initial_ls (LM := LM) s1 0%nat)).
Proof.
  intros Hfin Hfevol H.
  apply (wp_strong_adequacy heap_lang LM Σ s); first by eauto.
  iIntros (?) "".
  iMod (gen_heap_init (heap σ1)) as (genheap)" [Hgen [Hσ _]]".
  iMod (model_state_init s1) as (γmod) "[Hmoda Hmodf]".
  iMod (model_fuel_mapping_init s1) as (γmap) "[Hmapa Hmapf]".
  iMod (model_free_roles_init s1 (FR ∖ live_roles _ s1)) as (γfr) "[HFR Hfr]".
  set (distG :=
         {|
          heap_fairnessGS := {|
                              fairness_model_name := γmod;
                              fairness_model_fuel_mapping_name := γmap;
                              fairness_model_free_roles_name := γfr;
                              |}
         |}).
  iMod (H distG) as "Hwp". clear H.
  iExists state_interp, (λ _, 0%nat ↦M ∅)%I, fork_post.
  iSplitR.
  { unfold config_wp. iIntros "!>!>" (???????) "?". done. }
  iSpecialize ("Hwp" with "Hσ Hmodf Hfr [Hmapf]").
  { rewrite /init_fuel_map.
    rewrite /has_fuels /frag_fuel_mapping_is.
    rewrite fmap_insert fmap_empty. iFrame. }
  iDestruct "Hwp" as ">[Hwp H]".
  iModIntro. iFrame "Hwp".
  iSplitL "Hgen Hmoda Hmapa HFR".
  { unfold state_interp. simpl. iFrame.
    iExists (ls_map (initial_ls s1 0%nat)).
    iSplit; [done|].
    iSplit.
    { iPureIntro. simpl. rewrite /fuel_map_preserve_dead.
      intros ρ Hline. eexists 0%nat, _. rewrite lookup_insert. split; [done|].
      by rewrite dom_gset_to_gmap. }
    iSplit.
    { iPureIntro. intros tid Hlocs. rewrite lookup_singleton_ne //.
      compute in Hlocs. set_solver. }
    iFrame. }
  iIntros (ex atr c Hvalex Hstartex Hstartatr Hendex Hcontr Hstuck Hequiv) "Hsi Hposts".
  assert ( ∀ (ex' : finite_trace (cfg heap_lang) (olocale heap_lang)) (atr' : auxiliary_trace LM) (oζ : olocale heap_lang) (ℓ : mlabel LM),
   trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' (map_underlying_trace atr')) as Hcontr'.
  { intros ex' atr' oζ ℓ H1 H2. cut (sim_rel_with_user LM ξ ex' atr'); eauto. rewrite /sim_rel_with_user. intros [??]. done. }
  iSpecialize ("H" $! ex atr c Hvalex Hstartex Hstartatr Hendex Hcontr' Hstuck).
  unfold sim_rel_with_user.
  iAssert (|={⊤}=> ⌜ξ ex (map_underlying_trace atr)⌝ ∗ state_interp ex atr ∗ posts_of c.1
               ((λ _ : language.val heap_lang, 0%nat ↦M ∅)
                :: ((λ '(tnew, e), fork_post (language.locale_of tnew e)) <$>
                    prefixes_from [e1] (drop (length [e1]) c.1))))%I with "[Hsi H Hposts]" as "H".
  { iApply fupd_plain_keep_l. iFrame. iIntros "[Hsi Hposts]".
    iSpecialize ("H" with "Hsi Hposts").
    by iApply fupd_plain_mask_empty. }
  iMod "H" as "[H1 [Hsi Hposts]]".
  destruct ex as [c'|ex' tid (e, σ)].
  - (* We need to prove that the initial state satisfies the property *)
    destruct atr as [δ|???]; last by inversion Hvalex. simpl.
    have Heq1 := trace_singleton_ends_in_inv _ _ Hendex.
    have Heq3 := trace_singleton_starts_in_inv _ _ Hstartex.
    have Heq4 := trace_singleton_starts_in_inv _ _ Hstartex.
    pose proof (trace_singleton_starts_in_inv _ _ Hstartatr). simpl.
    simplify_eq.
    iApply (fupd_mask_weaken ∅); first set_solver. iIntros "_ !>".
    iSplit; last done. iClear "H1".
    iSplit; first done.
    destruct (to_val e1) as [v1|] eqn:Heq.
    + iSplit.
      { iPureIntro. intros ρ tid Hinit.
        apply ls_mapping_data_inv in Hinit.
        destruct Hinit as [fs [HSome Hfs]].
        assert (tid = 0%nat).
        { simpl in *. rewrite lookup_insert_Some in HSome. by set_solver. }
        rewrite /from_locale //. simpl in *. set_solver. }
      iIntros (tid e Hsome Hnoval ρ). destruct tid; last done.
      simpl in Hsome. compute in Hsome. simplify_eq.
      iAssert (0%nat ↦M ∅)%I with "[Hposts]" as "Hem".
      { rewrite /= Heq /fmap /=. by iDestruct "Hposts" as "[??]". }
      iDestruct "Hsi" as "(_&_&Hsi)".
      iDestruct "Hsi" as (fm Hfmle Hfmdead Hmapinv) "(Hm & Hfm)".
      iDestruct (has_fuels_agree with "Hfm Hem") as "%Hagree".
      iPureIntro.
      intros HSome. apply ls_mapping_data_inv in HSome.
      destruct HSome as [fs [HSome Hfs]].
      destruct Hfmle as [Hfmle1 Hfmle2].
      rewrite /fuel_map_le_inner map_included_spec in Hfmle1.
      pose proof Hagree as HSome'.
      apply Hfmle1 in Hagree as (fs''&HSome''&Hfs''). simpl in *. clear Hfmle1.
      simplify_eq. rewrite lookup_insert in HSome''. simplify_eq.
      rewrite dom_gset_to_gmap in Hfs.
      apply Hfmdead in Hfs as (tid''&fs'''&HSome'''&Hfs''').
      rewrite dom_singleton_L in Hfmle2.
      assert (tid'' = 0%nat).
      { apply elem_of_dom_2 in HSome'''. rewrite Hfmle2 in HSome'''. set_solver. }
      simplify_eq. by set_solver.
    + iSplit; iPureIntro.
      { intros ρ tid Hinit.
        apply ls_mapping_data_inv in Hinit.
        destruct Hinit as [fs [HSome Hfs]].
        assert (tid = 0%nat).
        { simpl in *. rewrite lookup_insert_Some in HSome. by set_solver. }
        rewrite /from_locale //. simpl in *. set_solver. }
      intros tid e Hsome Hval' ρ.
      destruct tid as [|tid]; rewrite /from_locale /= in Hsome; by simplify_eq.
  - (* We need to prove that that the property is preserved *)
    destruct atr as [|atr' ℓ δ]; first by inversion Hvalex.
    specialize (Hcontr ex' atr' tid ℓ).
    have H: trace_contract (trace_extend ex' tid (e, σ)) tid ex' by eexists.
    have H': trace_contract (trace_extend atr' ℓ δ) ℓ atr' by eexists.
    specialize (Hcontr H H') as Hvs. clear H H' Hcontr.
    have H: trace_ends_in ex' (trace_last ex') by eexists.
    have H': trace_ends_in atr' (trace_last atr') by eexists.
    iApply (fupd_mask_weaken ∅); first set_solver. iIntros "_ !>".
    apply (trace_singleton_ends_in_inv (L := unit)) in Hendex.
    simpl in *. simplify_eq.
    iDestruct "Hsi" as "((%&%&%Htids)&_&Hsi)".
      iDestruct "Hsi" as (fm Hfmle Hfmdead Hmapinv) "(Hm & Hfm)".
    iSplit; [|done].
    iSplit; [done|].
    iSplit.
    + iPureIntro. intros ρ tid' Hsome. simpl. unfold tids_smaller in Htids.
      eapply Htids.
      apply ls_mapping_data_inv in Hsome.
      destruct Hsome as [fs [HSome Hfs]].
      simpl in *. apply elem_of_dom. set_solver.
    + iIntros (tid' e' Hsome Hnoval ρ HSome). simpl.
      iAssert (tid' ↦M ∅)%I with "[Hposts]" as "H".
      { destruct (to_val e') as [?|] eqn:Heq; last done.
        iApply posts_of_empty_mapping => //.
        apply from_locale_lookup =>//. }
      iDestruct (has_fuels_agree with "Hfm H") as "%Hlk".
      iPureIntro.
      intros Hlive.
      apply ls_mapping_data_inv in HSome.
      destruct HSome as [fs [HSome Hfs]].
      destruct Hfmle as [Hfmle1 Hfmle2].
      rewrite /fuel_map_le_inner map_included_spec in Hfmle1.
      pose proof Hlk as HSome'.
      apply Hfmle1 in Hlk as (fs'&HSomefs&Hfs'). simpl in *.
      simplify_eq.
      apply Hfmdead in Hlive as (tid''&fs''&HSome''&Hfs'').
      assert (tid'' = tid').
      { apply Hfmle1 in HSome'' as (fs'''&HSome'''&Hfs''').
        pose proof (δ.(ls_map_disj)) as Hdisj.
        destruct (decide (tid' = tid'')) as [->|Hneq]; [done|].
        specialize (Hdisj tid' tid'' fs fs''' Hneq HSome HSome''').
        apply map_disjoint_dom in Hdisj.
        apply map_included_subseteq_inv in Hfs'''.
        set_solver. }
      simplify_eq.
      by set_solver.
Qed.

Theorem simulation_adequacy Σ `(LM:LiveModel heap_lang M) `{!heapGpreS Σ LM} (s: stuckness) (e1 : expr) σ1 (s1: M) (FR: gset _):
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  live_roles M s1 ≠ ∅ ->
  (* The initial configuration satisfies certain properties *)
  (* A big implication, and we get back a Coq proposition *)
  (* For any proper Aneris resources *)
  (∀ `{!heapGS Σ LM},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
        frag_free_roles_are (FR ∖ live_roles _ s1) -∗
        has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (M.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  @continued_simulation
    heap_lang
    LM
    (sim_rel LM)
    (trace_singleton ([e1], σ1))
    (trace_singleton (initial_ls (LM := LM) s1 0%nat)).
Proof.
  intros Hfevol Hne H.
  assert (sim_rel LM = sim_rel_with_user LM (λ _ _, True)) as Heq.
  { do 2 (apply FunExt; intros?). apply PropExt. 
    unfold sim_rel_with_user. intuition. }
  rewrite Heq.
  apply (strong_simulation_adequacy Σ LM s _ _ _ FR) =>//.
  { rewrite -Heq. done. }
  iIntros (Hinv) "".
  iPoseProof (H Hinv) as ">H". iModIntro. iIntros "Hσ Hm Hfr Hf". iSplitR "".
  - iApply ("H" with "Hm Hfr Hf").
  - iIntros "!>%%%????????". iApply (fupd_mask_weaken ∅); first set_solver. by iIntros "_ !>".
Qed.

Theorem simulation_adequacy_inftraces Σ `(LM: LiveModel heap_lang M)
        `{!heapGpreS Σ LM} (s: stuckness) FR
        e1 σ1 (s1: M)
        (iex : inf_execution_trace heap_lang)
        (Hvex : valid_inf_exec (trace_singleton ([e1], σ1)) iex)
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM)  →
  live_roles M s1 ≠ ∅ ->
  (∀ `{!heapGS Σ LM},
      ⊢ |={⊤}=>
     frag_model_is s1 -∗
         frag_free_roles_are (FR ∖ live_roles _ s1) -∗
         has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (M.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  exists iatr,
  @valid_inf_system_trace _ LM
    (@continued_simulation
       heap_lang
       LM
       (sim_rel LM))
    (trace_singleton ([e1], σ1))
    (trace_singleton (initial_ls (LM := LM) s1 0%nat))
    iex
    iatr.
Proof.
  intros Hfin Hlr Hwp. eexists. eapply produced_inf_aux_trace_valid_inf.
  Unshelve.
  - econstructor.
  - apply (simulation_adequacy Σ LM s _ _ _ FR) => //.
  - done.
Qed.

Definition heap_lang_extrace : Type := extrace heap_lang.

Theorem simulation_adequacy_traces Σ `(LM : LiveModel heap_lang M) `{!heapGpreS Σ LM} (s: stuckness) FR
        e1 (s1: M)
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  live_roles M s1 ≠ ∅ ->
  (∀ `{!heapGS Σ LM},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
         frag_free_roles_are (FR ∖ live_roles _ s1) -∗
         has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (M.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  ∃ (auxtr : auxtrace LM), exaux_traces_match extr auxtr.
Proof.
  intros Hfin Hlr Hwp.
  have [iatr Hbig] : exists iatr,
      @valid_inf_system_trace
        heap_lang LM
        (@continued_simulation
           heap_lang
           LM
           (sim_rel LM))
        (trace_singleton ([e1], (trfirst extr).2))
        (trace_singleton (initial_ls (LM := LM) s1 0%nat))
        (from_trace extr)
        iatr.
  { apply (simulation_adequacy_inftraces _ _ s FR); eauto.
    eapply from_trace_preserves_validity; eauto; first econstructor.
    simpl. destruct (trfirst extr) eqn:Heq.
    simpl in Hexfirst. rewrite -Hexfirst Heq //. }
  exists (to_trace (initial_ls (LM := LM) s1 0%nat) iatr).
  eapply (valid_inf_system_trace_implies_traces_match (continued_simulation (sim_rel LM))); eauto.
  - by intros ? ? [? ?]%continued_simulation_rel.
  - by intros ? ? [? ?]%continued_simulation_rel.
  - apply from_trace_spec. simpl. destruct (trfirst extr) eqn:Heq. simplify_eq. f_equal.
    simpl in Hexfirst. rewrite -Hexfirst Heq //.
  - apply to_trace_spec.
Qed.

Theorem simulation_adequacy_model_trace Σ `(LM : LiveModel heap_lang M)
        `{!heapGpreS Σ LM} (s: stuckness) FR
        e1 (s1: M)
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  live_roles M s1 ≠ ∅ ->
  (∀ `{!heapGS Σ LM},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
         frag_free_roles_are (FR ∖ live_roles _ s1) -∗
         has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (M.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  ∃ (auxtr : auxtrace LM) mtr, exaux_traces_match extr auxtr ∧
                               upto_stutter (λ x, ls_under (ls_data x)) Ul auxtr mtr.
Proof.
  intros Hfb Hlr Hwp.
  destruct (simulation_adequacy_traces
              Σ _ _ FR e1 s1 extr Hvex Hexfirst Hfb Hlr Hwp) as [auxtr Hmatch].
  assert (auxtrace_valid auxtr) as Hstutter.
  { by eapply exaux_preserves_validity in Hmatch. }
  destruct (can_destutter_auxtr auxtr) as [mtr Hupto] =>//.
  eauto.
Qed.

Theorem simulation_adequacy_terminate Σ `{LM:LiveModel heap_lang Mdl}
        `{!heapGpreS Σ LM} (s: stuckness)
        e1 (s1: Mdl) FR
        (extr : heap_lang_extrace)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (∀ mtr : @mtrace Mdl, mtrace_fairly_terminating mtr) ->
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  live_roles Mdl s1 ≠ ∅ ->
  (∀ `{!heapGS Σ LM},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
         frag_free_roles_are (FR ∖ live_roles _ s1) -∗
         has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (Mdl.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  extrace_fairly_terminating extr.
Proof.
  intros Hterm Hfb Hlr Hwp Hvex Hfair.
  destruct (simulation_adequacy_model_trace
              Σ _ _ FR e1 s1 extr Hvex Hexfirst Hfb Hlr Hwp) as (auxtr&mtr&Hmatch&Hupto).
  destruct (infinite_or_finite extr) as [Hinf|] =>//.
  have Hfairaux := fairness_preserved extr auxtr Hinf Hmatch Hfair.
  have Hvalaux := exaux_preserves_validity extr auxtr Hmatch.
  have Hfairm := upto_stutter_fairness auxtr mtr Hupto Hfairaux.
  have Hmtrvalid := upto_preserves_validity auxtr mtr Hupto Hvalaux.
  have Htermtr := Hterm mtr Hmtrvalid Hfairm.
  eapply exaux_preserves_termination =>//.
  eapply upto_stutter_finiteness =>//.
Qed.

Theorem simulation_adequacy_terminate_ftm Σ `{FairTerminatingModel M}
        `(LM : LiveModel heap_lang M)
        `{!heapGpreS Σ LM} (s: stuckness)
        e1 (s1: M) FR
        (extr : heap_lang_extrace)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  live_roles M s1 ≠ ∅ ->
  (∀ `{!heapGS Σ LM},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
        frag_free_roles_are (FR ∖ live_roles _ s1) -∗
        has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (M.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  extrace_fairly_terminating extr.
Proof.
  eapply simulation_adequacy_terminate =>//.
  apply fair_terminating_traces_terminate.
Qed.

End adequacy.
