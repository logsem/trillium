From stdpp Require Import finite.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.bi.lib Require Import fixpoint.
From iris.base_logic.lib Require Import wsat later_credits.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Import quantifiers iris_extraction finitary classical_instances.
From trillium.program_logic Require Export weakestpre traces.
From trillium.program_logic Require Export adequacy_utils.

Set Default Proof Using "Type".
Import uPred.


(* the guarded definition of simulation. *)
Definition Gsim_cond_pre Σ {Λ} (M : Model) (s : stuckness)
           (ξ : execution_trace Λ → auxiliary_trace M → Prop)
           (C: execution_trace Λ → Prop)
           (gsim : execution_trace Λ -d> auxiliary_trace M -d> iPropO Σ) :
  execution_trace Λ -d> auxiliary_trace M -d> iPropO Σ :=
  (λ ex atr,
   ▷ (⌜ C ex ⌝ →
      ⌜ξ ex atr⌝ ∧
      ∀ c oζ c',
        ⌜trace_ends_in ex c⌝ →
        ⌜locale_step c oζ c'⌝ →
        ▷ ▷^(S $ trace_length ex) (∃ δ' ℓ, gsim (trace_extend ex oζ c') (trace_extend atr ℓ δ'))))%I.

#[local] Instance Gsim_cond_pre_contractive Σ M Λ s ξ C :
  Contractive (@Gsim_cond_pre Σ M Λ s ξ C).
Proof.
  rewrite /Gsim_cond_pre=> n wp wp' HGsm ex sm.
  repeat (f_contractive || f_equiv).
  repeat (eapply dist_lt; try apply HGsm). auto. 
Qed.

Definition Gsim_cond Σ {Λ} (M : Model) (s : stuckness)
           (ξ : execution_trace Λ → auxiliary_trace M → Prop)
           (C: execution_trace Λ → Prop)
  :
  execution_trace Λ → auxiliary_trace M → iProp Σ :=
  fixpoint (Gsim_cond_pre Σ M s ξ C).

#[global] Instance is_except_0_Gsim_cond {Σ} Λ M s ξ C ex sm:
  IsExcept0 (@Gsim_cond Σ Λ M s ξ C ex sm).
Proof.
  rewrite /IsExcept0; iIntros "H".
  rewrite /Gsim_cond (fixpoint_unfold (Gsim_cond_pre _ _ _ _ _) _ _).
  iMod "H".
  iApply "H"; done.
Qed.

#[global] Instance Gsim_cond_plain Σ M {Λ} s ξ C ex sm
  `{forall ex, Decision (C ex)}: 
  Plain (@Gsim_cond Σ M Λ s ξ C ex sm).
Proof.
  rewrite /Plain.
  iIntros "H".
  iLöb as "IH" forall (ex sm).
  rewrite /Gsim_cond (fixpoint_unfold (Gsim_cond_pre _ _ _ _ _) _ _).
  rewrite {3 5}/Gsim_cond_pre.
  iApply later_plainly_1; iNext.
  destruct (decide (C ex)) as [PASS | FAIL].
  2: { iClear "IH H". iModIntro. by iIntros "%". } 
  iSpecialize ("H" with "[//]"). 
  iDestruct "H" as "(#H1 & H)".

  iApply plainly_mono.
  { iIntros "X Y". iApply "X". }

  iSplit; first (iClear "IH H"; iModIntro; done).
  iIntros (c ? ? ? ?).
  iDestruct ("H" with "[] []") as "H"; [done|done|].
  do 2 (iApply later_plainly_1; iNext).
  iApply laterN_plainly.
  iModIntro.
  iDestruct "H" as (δ' ℓ) "H".
  iExists _, _. iApply "IH"; done.
Qed.


Definition all_posts `{irisG Λ M Σ} (tp: list (expr Λ)) es
  (Φs: list (val Λ → iProp Σ)): list (val Λ → iProp Σ) :=
  Φs ++ ((λ '(tnew, e), fork_post (locale_of tnew e)) <$>
                        prefixes_from es (drop (length es) tp)).

(* TODO: can tp and es actually be different? *)
Definition cur_posts_multiple `{irisG Λ M Σ} (tp: list (expr Λ)) es
  (Φs: list (val Λ → iProp Σ)): iProp Σ :=
  posts_of tp (all_posts tp es Φs).

  Definition steps_from_ref {Λ: language} {M: Model}
    (ξ : execution_trace Λ → auxiliary_trace M → Prop)
    ex atr := 
    ∀ (ex' : finite_trace (list (expr Λ) * state Λ) (olocale Λ)) (atr' : auxiliary_trace M) 
      (oζ : olocale Λ) (ℓ : mlabel M),
      trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' atr'.

  Definition steps_from_inv `{!irisG Λ M Σ}
    (trace_inv: execution_trace Λ → auxiliary_trace M → iProp Σ)
    ex atr: iProp Σ := 
    ∀ (ex' : finite_trace (list (expr Λ) * state Λ) (olocale Λ)) (atr' : auxiliary_trace M) 
       (oζ : olocale Λ) (ℓ : mlabel M),
      ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr'. 


Definition tr_extras {Λ: language} {M: Model} (ξ : execution_trace Λ → auxiliary_trace M → Prop)
  c δ ex atr
  (c1 := trace_last ex) :=
  valid_system_trace ex atr ∧ trace_starts_in ex c ∧
  trace_starts_in atr δ ∧ steps_from_ref ξ ex atr.

Lemma tr_extras_locales_equiv {Λ M} (ξ : execution_trace Λ → auxiliary_trace M → Prop) c δ ex atr
  (EXTRAS: tr_extras ξ c δ ex atr):
  locales_equiv c.1 (take (length c.1) (trace_last ex).1).
Proof using.
  destruct EXTRAS as (VALID&START&?&?).
  apply valid_system_trace_valid_exec_trace in VALID.
  clear dependent atr. 
  red in START.
  induction ex; simpl in START.
  { subst. simpl.
    rewrite firstn_all. apply locales_equiv_refl. }
  inversion VALID. subst.  
  ospecialize (IHex _ _); try done. 
  simpl. eapply locales_equiv_prefix_from_trans; eauto.
  erewrite last_eq_trace_ends_in; eauto.
  red. eapply locale_step_equiv; eauto.
Qed.

Lemma tr_extras_length_le {Λ M} (ξ : execution_trace Λ → auxiliary_trace M → Prop) c δ ex atr
  (EXTRAS: tr_extras ξ c δ ex atr):
  length c.1 ≤ length (trace_last ex).1.
Proof using.
  destruct EXTRAS as (VALID&START&?&?).
  apply valid_system_trace_valid_exec_trace in VALID.
  clear dependent atr. 
  red in START.
  induction ex; simpl in START. 
  { subst. simpl. done. }
  inversion VALID. subst.
  ospecialize (IHex _ _); try done.
  etrans; [apply IHex| ]. 
  erewrite last_eq_trace_ends_in; [| apply H2].
  simpl. eapply step_tp_length; eauto.
Qed.    


Definition rel_always_holds `{!irisG Λ M Σ}
           (s:stuckness) Φs
           (ξ : execution_trace Λ → auxiliary_trace M → Prop) (c1:cfg Λ)
           (c2:M) : iProp Σ :=
  (∀ (ex : execution_trace Λ) (atr : auxiliary_trace M) (c : cfg Λ),
         ⌜ tr_extras ξ c1 c2 ex atr ⌝ -∗
         ⌜trace_ends_in ex c⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗
         state_interp ex atr -∗
         cur_posts_multiple c.1 c1.1 Φs
         -∗
         |={⊤, ∅}=> ⌜ξ ex atr⌝).

Definition rel_always_holds_with_trace_inv `{!irisG Λ M Σ}
           (s:stuckness) trace_inv Φs
           (ξ : execution_trace Λ → auxiliary_trace M → Prop)
           (c1:cfg Λ) (c2:M) : iProp Σ :=
  (∀ (ex : execution_trace Λ) (atr : auxiliary_trace M) (c : cfg Λ),
         ⌜ tr_extras ξ c1 c2 ex atr ⌝ -∗
         ⌜trace_ends_in ex c⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗
         state_interp ex atr -∗
         cur_posts_multiple c.1 c1.1 Φs -∗
         □ (state_interp ex atr ∗ steps_from_inv trace_inv ex atr
            ={⊤}=∗ state_interp ex atr ∗ trace_inv ex atr) ∗
         (steps_from_inv trace_inv ex atr ={⊤, ∅}=∗ ⌜ξ ex atr⌝)).


Section StrongAdequacyHelpers.
  Context {Λ: language} {M: Model}. 
  Context (ξ : execution_trace Λ → auxiliary_trace M → Prop).

  Context `{invGpreS Σ}. 
  Context (stateI trace_inv: execution_trace Λ → auxiliary_trace M → iProp Σ). 
  Context (post : locale Λ → val Λ → iProp Σ).

  Context (C: execution_trace Λ → Prop).
  Hypothesis C_DEC: forall ex, Decision (C ex).

  (* (** "Progress Resource" - generalization of wptp *) *)
  (* (* TODO: do we need to expose stuckness, or it is local to wptp? *) *)
  (* Context (PR: stuckness -> execution_trace Λ -> list (val Λ → iProp Σ) -> iProp Σ).  *)

  Definition cur_tr_repr_impl
    (Hinv : invGS_gen HasNoLc Σ)    
(i := {| iris_invGS := Hinv; state_interp := stateI; fork_post := post |} : irisG Λ M Σ)
    s Φs ex atr: iProp Σ :=
    (
    let c0 := trace_first ex in 
    let c1 := trace_last ex in 
    stateI ex atr ∗
    steps_from_inv trace_inv ex atr ∗
    (let i := {| iris_invGS := Hinv; state_interp := stateI; fork_post := post |} : irisG Λ M Σ in
     wptp s c1.1 (all_posts c1.1 c0.1 Φs)
    (* PR s ex Φs *)
    ) ).

  Definition cur_tr_repr
    (Hinv : invGS_gen HasNoLc Σ)    
(i := {| iris_invGS := Hinv; state_interp := stateI; fork_post := post |} : irisG Λ M Σ)
    s Φs ex atr: iProp Σ :=
    ⌜ C ex ⌝ → cur_tr_repr_impl _ s Φs ex atr.

  Lemma init_st_into_trace
    s es σ δ
    (Hes : length es ≥ 1)
    (Hinv : invGS_gen HasNoLc Σ)
    (Φs : list (val Λ → iProp Σ))
    (i :=
       {|
         iris_invGS := Hinv;
         state_interp := stateI;
         fork_post := post
       |} : irisG Λ M Σ):

    stateI {tr[ (es, σ) ]} {tr[ δ ]} -∗ wptp s es Φs -∗

    ∃ (ex : finite_trace (list (expr Λ) * state Λ) (olocale Λ)) (atr : auxiliary_trace M)
      (c1 : list (expr Λ) * state Λ) (δ1 : M),
      ⌜{tr[ (es, σ) ]} = ex⌝ ∗ ⌜{tr[ δ ]} = atr⌝ ∗
    ⌜(es, σ) = c1⌝ ∗ ⌜δ = δ1⌝ ∗ ⌜length c1.1 ≥ 1⌝ ∗
    cur_tr_repr _ s Φs ex atr
  .
  Proof using.
    iIntros "? ?". 
    iExists (trace_singleton (es, σ)), (trace_singleton δ), (es, σ), δ; simpl.
    rewrite /cur_tr_repr /cur_tr_repr_impl.
    rewrite /all_posts. 
    rewrite drop_ge.
    2: { simpl. lia. }
    rewrite right_id.
    iFrame.
    repeat (iSplit; first by auto).
    iIntros (????? ?%not_trace_contract_singleton); done.
  Qed.

  (* TODO: better name *)
  Local Lemma locales_rewrite
    (Hinv : invGS_gen HasNoLc Σ)
    (i := {| iris_invGS := Hinv; state_interp := stateI; fork_post := post |} : irisG Λ M Σ)
    (* (R: list (expr Λ) → expr Λ -> iProp Σ) *)
    es
    (tp : list (expr Λ))
    (σ1' : state Λ)
    (Htake : locales_equiv es (take (length es) tp))
    (Htakelen : length es ≤ length tp)
    (oζ : olocale Λ)
    (c' : cfg Λ)
    (Hstep : locale_step (tp, σ1') oζ c')
    :
  ((λ '(tnew, e), fork_post (locale_of tnew e)) <$>
   prefixes_from es (drop (length es) tp)) ++
  ((λ '(tnew, e), fork_post (locale_of tnew e)) <$>
   prefixes_from tp (drop (length tp) c'.1)) =
  (λ '(tnew, e), fork_post (locale_of tnew e)) <$>
  prefixes_from es (drop (length es) c'.1).
  Proof using.
    rewrite -fmap_app. apply locales_of_list_from_fork_post. rewrite fmap_app.
    apply locale_step_equiv in Hstep.
    rewrite (locales_equiv_prefix_drop_alt _ tp); [|done].
    rewrite -drop_app_le; last first.
    { rewrite length_fmap. rewrite prefixes_from_length. lia. }
    rewrite (locales_equiv_prefix_drop_alt es c'.1). 
      (* [|by eapply locales_equiv_prefix_trans]. *)
    2: { eapply locales_equiv_prefix_trans; eauto. }
    f_equiv.
    rewrite -fmap_app -prefixes_from_app -locales_of_list_equiv.
    apply locales_equiv_from_comm, locales_equiv_prefix_from_drop.
    eauto.
  Qed.

  Lemma ref_preserved'
    (s : stuckness) (es : list (expr Λ)) (σ : state Λ) (δ : M)
    (Hinv : invGS_gen HasNoLc Σ)
    (Φs : list (val Λ → iProp Σ))
    (i := {| iris_invGS := Hinv; state_interp := stateI;fork_post := post |} : irisG Λ M Σ)
    ex atr
  (Hv : valid_system_trace ex atr)
  (Hex : trace_starts_in ex (es, σ))
  (Hatr : trace_starts_in atr δ)
  (tp : list (expr Λ))
  (σ1' : state Λ)
  (Hξ' : ξ ex atr)
  (c : cfg Λ)
  (oζ : olocale Λ)
  (c' : cfg Λ)
  (Hc : trace_ends_in ex c)
  (Hstep : locale_step c oζ c')
  (H1 : ∀ e2 : expr Λ, s = NotStuck → e2 ∈ c'.1 → not_stuck e2 c'.2)
  (δ'' : M)
  (ℓ : mlabel M):
      rel_always_holds_with_trace_inv s trace_inv Φs ξ (es, σ) δ -∗
      cur_tr_repr_impl Hinv s Φs (ex :tr[ oζ ]: c') (atr :tr[ ℓ ]: δ'') -∗
      fupd_to_bupd ⊤ -∗
      ▷ ⌜ξ (ex :tr[ oζ ]: c') (atr :tr[ ℓ ]: δ'')⌝.
  Proof using.
    iIntros "Hstep (HSI & HTI & WPS) FB". simpl. 
    iPoseProof (wptp_of_val_post with "WPS") as "WPS".
    replace stateI with state_interp by done.
    iPoseProof (pre_step_elim with "HSI WPS") as "foo".
    rewrite /steps_from_inv. simpl.
    iSpecialize ("HTI" with "[] []").
    1, 2: by iPureIntro; red; eauto.

    iApply (f2b_helper with "[$]"). 
    iMod "foo" as "[HSI [POSTS WPS']]". iModIntro. iIntros "FB".     

    iDestruct ("Hstep" with "[] [] [] HSI") as "H"; [iPureIntro..|].
    - repeat split; eauto. 
      + eapply valid_system_trace_extend; eauto.
      + by intros ? ? ? ? [-> ->]%trace_contract_of_extend [-> ->]%trace_contract_of_extend.
    - done.
    - done.
    - iApply (f2b_helper with "[$]"). 
      iDestruct ("H" with "[POSTS]") as "[? Hξ]".
      { simpl. rewrite /cur_posts_multiple.
        erewrite first_eq_trace_starts_in; eauto. done. }
      iMod ("Hξ" with "[HTI]") as "%".
      + iIntros (? ? ? ? [-> ->]%trace_contract_of_extend
                 [-> ->]%trace_contract_of_extend); done.
      + iModIntro.
        iIntros "HFtB"; done.
  Qed.

  Lemma get_current_facts
    s es σ δ
    (Hinv : invGS_gen HasNoLc Σ)
    (Φs : list (val Λ → iProp Σ))
    (i := {| iris_invGS := Hinv; state_interp := stateI; fork_post := post |} : irisG Λ M Σ)
  (ex : finite_trace (list (expr Λ) * state Λ) (olocale Λ))
  (atr : auxiliary_trace M)
  (Hextras : tr_extras ξ (es, σ) δ ex atr):

  rel_always_holds_with_trace_inv s trace_inv Φs ξ (es, σ) δ -∗
  cur_tr_repr_impl Hinv s Φs ex atr ={⊤}=∗
  ⌜ξ ex atr⌝ ∗
  rel_always_holds_with_trace_inv s trace_inv Φs ξ (es, σ) δ ∗
  cur_tr_repr_impl Hinv s Φs ex atr ∗
  ⌜ ∀ e, e ∈ (trace_last ex).1 → s = NotStuck → not_stuck e (trace_last ex).2 ⌝.
  Proof using.
    iIntros "Hstep PRE". iDestruct "PRE" as "(HSI & HTI & Htp)".
    pose proof Hextras as (Hv & Hex & Hatr & Hξ).

    iPoseProof (wptp_not_stuck _ _ _ _ _ _ [] with "[$HSI] Htp") as "Htp";
      [apply locales_equiv_refl| | |].
    { by eapply valid_system_trace_valid_exec_trace. }
    { list_simplifier. rewrite <- surjective_pairing. apply trace_ends_in_last. }
    iMod ("Htp") as "(HSI & Htp & %Hnstk)".

    iApply fupd_plain_keep_l. iSplitR.
    2: { by iFrame. }
      
    iIntros "(Hstep & PRE & _)".
    iDestruct "PRE" as "(HSI & HTI & Htp)".
      
    iPoseProof (wptp_of_val_post with "Htp") as "Htp".
    replace stateI with state_interp by done.
    iMod (pre_step_elim with "HSI Htp") as "[HSI Htp]".
    iDestruct ("Htp") as "(Hpost & Hback)".
    
    iDestruct ("Hstep" with "[] [] [] HSI [Hpost]") as "[_ Hξ]"; eauto.
    { erewrite first_eq_trace_starts_in; eauto. }
    iApply fupd_plain_mask.
    iMod ("Hξ" with "HTI") as "%"; auto.
  Qed.

  Lemma get_trace_inv ex atr δ es σ s
    (Hinv : invGS_gen HasNoLc Σ)
    (Φs : list (val Λ → iProp Σ))
    (EXTRAS: tr_extras ξ (es, σ) δ ex atr)
    (NSTUCK: ∀ e, e ∈ (trace_last ex).1 → s = NotStuck → not_stuck e (trace_last ex).2)
    (i := {| iris_invGS := Hinv; state_interp := stateI; fork_post := post |} : irisG Λ M Σ):
  rel_always_holds_with_trace_inv s trace_inv Φs ξ (es, σ) δ -∗
  stateI ex atr -∗ steps_from_inv trace_inv ex atr -∗
  wptp s (trace_last ex).1 (all_posts (trace_last ex).1 es Φs)
  ={⊤}=∗
  trace_inv ex atr ∗   
  rel_always_holds_with_trace_inv s trace_inv Φs ξ (es, σ) δ ∗
  stateI ex atr ∗ 
  wptp s (trace_last ex).1 (all_posts (trace_last ex).1 es Φs).
  Proof using.
    iIntros "Hstep HSI HTI Htp".
    iPoseProof (wptp_of_val_post with "Htp") as "Htp".
    replace stateI with state_interp by done.
    iMod (pre_step_elim with "HSI Htp") as "[HSI Htp]".
    iDestruct ("Htp") as "(Hpost & Hback)".
    
    iAssert (□ (stateI ex atr -∗ steps_from_inv _ ex atr
                ={⊤}=∗ stateI ex atr ∗ trace_inv ex atr))%I
      as "#HTIextend".
    { iDestruct ("Hstep" with "[] [] [] HSI Hpost") as "[#Hext _]";
        auto.
      iModIntro.
      iIntros "HSI HTI".
      iApply ("Hext" with "[$HSI $HTI]"). }
    
    iMod ("HTIextend" with "HSI HTI") as "[HSI HTI]".
    iClear "HTIextend".
    iDestruct ("Hback" with "[$]") as "Htp".
    iModIntro. iFrame.
  Qed.

  Lemma reestablish_tr_extras ex atr (c: cfg Λ) (oζ: olocale Λ) (c': cfg Λ) (δ'' : M) (ℓ : mlabel M) c0 δ
    (Hξ' : ξ ex atr)
    (Hc : trace_ends_in ex c)
    (Hstep : locale_step c oζ c')
    (Hextras : tr_extras ξ c0 δ ex atr):
    tr_extras ξ c0 δ (ex :tr[ oζ ]: c') (atr :tr[ ℓ ]: δ'').
  Proof using.
    split_and!.
    + eapply valid_system_trace_extend; eauto; try apply Hextras. 
    + eapply trace_extend_starts_in. apply Hextras. 
    + eapply trace_extend_starts_in. apply Hextras. 
    + intros ???? [??]%trace_contract_of_extend [??]%trace_contract_of_extend.
      subst. eauto. 
  Qed.

  Lemma strong_adequacy_trace s es σ δ
    (Hes : length es ≥ 1)
    (Hinv : invGS_gen HasNoLc Σ)
    (Φs : list (val Λ → iProp Σ))
    (i := {| iris_invGS := Hinv; state_interp := stateI; fork_post := post |} : irisG Λ M Σ)
  (ex : finite_trace (list (expr Λ) * state Λ) (olocale Λ))
  (atr : auxiliary_trace M)
  (c1 := trace_last ex)
  (Hextras : tr_extras ξ (es, σ) δ ex atr):
    config_wp -∗ 
    rel_always_holds_with_trace_inv s trace_inv Φs ξ (es, σ) δ -∗
    cur_tr_repr _ s Φs ex atr
    -∗
    |={⊤}=> fupd_to_bupd ⊤ -∗ Gsim_cond Σ M s ξ C ex atr.
  Proof using C_DEC.
    iIntros "#config_wp Hstep PRE".
    
    subst c1. 
    iLöb as "IH" forall (ex atr Hextras) "PRE".

    destruct (decide (C ex)) as [PASS | FAIL].
    2: { iIntros "!> F2B".
         rewrite /Gsim_cond (fixpoint_unfold (Gsim_cond_pre _ _ _ _ _) _ _).
         rewrite /Gsim_cond_pre.
         by iIntros "!> %". }
    iSpecialize ("PRE" with "[//]"). 

    pose proof Hextras as (Hv & Hex & Hatr & Hξ).

    remember (trace_last ex) as c1 eqn:Hc1. 
    assert (valid_exec ex) as Hexv.
    { by eapply valid_system_trace_valid_exec_trace. }

    iMod (get_current_facts with "[$] [$]") as "(Hξ & Hstep & PRE & %NSTUCK)".
    { repeat split; auto. }

    iDestruct "PRE" as "(HSI & HTI & Htp)".
    replace stateI with state_interp by done.

    rewrite {2}/Gsim_cond (fixpoint_unfold (Gsim_cond_pre _ _ _ _ _) _ _).
    destruct c1 as [tp σ1'].

    erewrite first_eq_trace_starts_in; eauto.
    iMod (get_trace_inv with "[$] [$] [$] [$]") as "(HTI & Hstep & HSI & Htp)"; eauto.
    
    iModIntro. 
    iIntros "HFtB".
    iNext. iIntros "_". iSplit; first done.
    iDestruct "Hξ" as %Hξ'.
    iIntros (c oζ c' Hc Hstep).
  
  opose proof (trace_ends_in_inj ex c (tp, σ1') Hc _).
  { rewrite Hc1. apply trace_ends_in_last. }

  iPoseProof (take_step with "config_wp HSI [Htp]") as "Hstp"; [done|done| ..].
  { done. }
  { rewrite -Hc1.
    simpl. rewrite H0. simpl.
    subst. eauto. }

  assert (∃ n, n = trace_length ex) as [n Hn] by eauto.
  rewrite -Hn. clear Hn.

  iApply (f2b_helper with "[$]"). 
  iMod "Hstp"; simpl.
  iMod "Hstp". iModIntro. iIntros "HFtB".

  iNext.
  iApply (f2b_helper with "[$]"). 
  iMod "Hstp". iModIntro.  iIntros "HFtB".

  (* TODO: This should be generalisable in a lemma *)

  iInduction n as [|n] "IHlen"; simpl; last first.
  { iClear "config_wp IH".
    iSpecialize ("IHlen" with "HTI Hstep").
    
    iApply (f2b_helper with "[$]"). 
    iMod "Hstp".
    iModIntro. iIntros "HFtB".

    iNext. 

    iApply (f2b_helper with "[$]"). 
    iMod "Hstp".
    iModIntro. iIntros "HFtB".

    iApply ("IHlen" with "[$]"); done. }

  iApply (f2b_helper with "[$]"). 
  iMod "Hstp" as "(% & H)".
  iDestruct "H" as (δ'' ℓ) "(HSI & Hpost)"; simpl in *.

  replace stateI with state_interp by done.
  iPoseProof (wptp_of_val_post with "Hpost") as "Hpost".
  iMod (pre_step_elim with "HSI Hpost") as "[HSI Hback]".

  iModIntro. iIntros "HFtB".
 
  iAssert (cur_tr_repr Hinv s Φs (ex :tr[ oζ ]: c') (atr :tr[ ℓ ]: δ'') ∗ fupd_to_bupd ⊤ ∗ rel_always_holds_with_trace_inv s trace_inv Φs ξ (es, σ) δ)%I
    with "[Hstep HSI HTI Hback HFtB]" as "(PRE' & HFtB & Hstep)".
  { pose proof Hextras as Htake%tr_extras_locales_equiv.
    pose proof Hextras as Htakelen%tr_extras_length_le.
    iPoseProof (ref_preserved' with "[$] [HSI HTI Hback] [$]") as "#Hextend"; eauto.
    { iFrame. iSplitL "HTI".
      { rewrite /steps_from_inv. 
        by iIntros "*" ([->->]%trace_contract_of_extend [->->]%trace_contract_of_extend). }        
        
      iDestruct "Hback" as "[X Y]".
      iSpecialize ("Y" with "X").
      subst c. rewrite Hc1 in Hstep. 
      opose proof (locales_rewrite _ _ _ _ Htake Htakelen _ _ _) as Hlocales.
      { rewrite <- surjective_pairing. eauto. }
      
      simpl.
      rewrite -app_assoc.
      rewrite -Hc1 in Hlocales.
      erewrite first_eq_trace_starts_in; eauto. 
      by rewrite Hlocales. }
    
    iFrame "#∗". iIntros "%PASS'".
    iSplitL "HTI". 
    + iIntros (???? [-> ->]%trace_contract_of_extend
                  [-> ->]%trace_contract_of_extend); done.
    + unshelve opose proof (locales_rewrite _ _ _ _ Htake Htakelen _ _ _) as Hlocales.
      4: { rewrite <- surjective_pairing. rewrite -Hc1 -H0. eauto. }
      rewrite -Hc1 in Hlocales.
      subst c. 
      rewrite -app_assoc Hlocales //.
      iDestruct "Hback" as "(Hpost & Hwptp)".
      erewrite first_eq_trace_starts_in; eauto.
      by iApply "Hwptp". }
 
  iExists _, _.
  iApply (f2b_helper with "[$]"). 
  iMod ("IH" with "[] [$] PRE'") as "IH'".
  - iPureIntro.
    clear -Hextras Hc Hstep Hξ'.
    eapply reestablish_tr_extras; eauto.
  - iModIntro. iIntros "HFtB". iNext. iApply "IH'"; done.
  Qed.

End StrongAdequacyHelpers.


Theorem wp_strong_adequacy_multiple_helper Σ Λ M `{!invGpreS Σ}
        (s: stuckness) (ξ : execution_trace Λ → auxiliary_trace M → Prop)
        (C: execution_trace Λ → Prop)
        `{forall ex, Decision (C ex)}
        es σ δ:
  length es ≥ 1 →
  (∀ `{Hinv : !invGS_gen HasNoLc Σ},
    ⊢ |={⊤}=> ∃
         (stateI : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (trace_inv : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (Φs : list (val Λ → iProp Σ))
         (fork_post : locale Λ → val Λ → iProp Σ),
       let _ : irisG Λ M Σ := IrisG _ _ _ Hinv stateI fork_post in
       config_wp ∗
       stateI (trace_singleton (es, σ)) (trace_singleton δ) ∗
       wptp s es Φs ∗
       rel_always_holds_with_trace_inv s trace_inv Φs ξ (es, σ) δ
  ) →
  ⊢ Gsim_cond Σ M s ξ C (trace_singleton (es, σ)) (trace_singleton δ).
Proof.
  intros Hes Hwp.
  apply extract_except_0.
  iApply fupd_to_bupd_soundness_no_lc'.
  iIntros (Hinv) "HFtB".
  rewrite fupd_to_bupd_unfold /fupd_to_bupd_aux.
  iApply bupd_elim.
  iApply "HFtB".
  iPoseProof (Hwp Hinv) as "Hwp".
  iMod "Hwp" as (stateI trace_inv Φs fork_post)
                  "(#config_wp & HSI & Hwp & Hstep)".
  clear Hwp.
  set (IrisG Λ M Σ Hinv stateI fork_post).

  iDestruct (init_st_into_trace _ _ _ C with "HSI Hwp") as (ex atr c1 δ1 Hexsing Hatrsing Hc1 Hδ1 Hlen) "PRE"; [done| ].

  destruct (decide (C ex)) as [PASS0 | FAIL0].
  2: { iModIntro. 
       rewrite {1}/Gsim_cond (fixpoint_unfold (Gsim_cond_pre _ _ _ _ _) _ _).
       subst. by iIntros "_ %". }

  iDestruct ("PRE" with "[//]") as "(HSI & HTI & Htp)".

  assert (tr_extras ξ (es, σ) δ ex atr) as Hextras.
  { subst. 
    repeat (split; try done).
    - constructor.
    - intros ? ? ? ? ? ?%not_trace_contract_singleton; done. }

  assert (c1 = trace_last ex) as Hlast.
  { by subst. }

  clear Hc1 Hδ1.
  rewrite Hexsing Hatrsing; clear Hexsing Hatrsing.

  (* rewrite Hlast.  *)
  iApply (strong_adequacy_trace with "[$] [$]").
  3: { iFrame "#∗". done. }
  all: tauto. 
Qed.

Theorem wp_strong_adequacy_helper Σ Λ M `{!invGpreS Σ}
        (s: stuckness) (ξ : execution_trace Λ → auxiliary_trace M → Prop)
        (C: execution_trace Λ → Prop)
        `{forall ex, Decision (C ex)}
        e1 σ1 δ:
  (∀ `{Hinv : !invGS_gen HasNoLc Σ},
    ⊢ |={⊤}=> ∃
         (stateI : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (trace_inv : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (Φ : val Λ → iProp Σ)
         (fork_post : locale Λ → val Λ → iProp Σ),
       let _ : irisG Λ M Σ := IrisG _ _ _ Hinv stateI fork_post in
       config_wp ∗
       stateI (trace_singleton ([e1], σ1)) (trace_singleton δ) ∗
       WP e1 @ s; locale_of [] e1; ⊤ {{ Φ }} ∗
       (∀ (ex : execution_trace Λ) (atr : auxiliary_trace M) c,
         ⌜valid_system_trace ex atr⌝ -∗
         ⌜trace_starts_in ex ([e1], σ1)⌝ -∗
         ⌜trace_starts_in atr δ⌝ -∗
         ⌜trace_ends_in ex c⌝ -∗
         ⌜steps_from_ref ξ ex atr⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗
         ⌜locales_equiv [e1] (take (length [e1]) c.1)⌝ -∗
         stateI ex atr -∗
         posts_of c.1 (Φ :: ((λ '(tnew, e), fork_post (locale_of tnew e)) <$> (prefixes_from [e1] (drop (length [e1]) c.1)))) -∗
         □ (stateI ex atr ∗
             steps_from_inv trace_inv ex atr
            ={⊤}=∗ stateI ex atr ∗ trace_inv ex atr) ∗
         ((∀ ex' atr' oζ ℓ,
              ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
          ={⊤, ∅}=∗ ⌜ξ ex atr⌝))) →
  ⊢ Gsim_cond Σ M s ξ C (trace_singleton ([e1], σ1)) (trace_singleton δ).
Proof.
  intros Hwp. apply wp_strong_adequacy_multiple_helper; [done| ..].
  { done. }
  { simpl; lia. }
  iIntros (Hinv).
  iMod (Hwp Hinv) as (stateI trace_inv Φs fork_post)
                       "(#config_wp & HSI & Hwp & Hstep)".
  iIntros "!>". iExists stateI, trace_inv, [Φs], fork_post.
  iFrame "#∗". iSplitR.
  { done. }
  rewrite /rel_always_holds_with_trace_inv. iIntros "**".
  iApply ("Hstep" with "[][][][][][][] [$][$]").
  all: try by (iPureIntro; apply H0 || done).
  iPureIntro.
  apply last_eq_trace_ends_in in H1. rewrite -H1.
  replace [e1] with ([e1], σ1).1 by done. 
  eapply tr_extras_locales_equiv; eauto. 
Qed.

Definition rel_finitary {A B C D}
           (ξ : finite_trace A B → finite_trace C D → Prop) :=
  ∀ (ex : finite_trace A B) (atr : finite_trace C D) c' oζ,
    smaller_card (sig (λ '(δ', ℓ), ξ (ex :tr[oζ]: c') (atr :tr[ℓ]: δ'))) nat.

Section finitary_lemma.
  Lemma rel_finitary_impl {A B C D} `{EqDecision C, EqDecision D}
        (ξ ξ' : finite_trace A B -> finite_trace C D -> Prop):
    (∀ ex aux, ξ ex aux -> ξ' ex aux) ->
    rel_finitary ξ' ->
    rel_finitary ξ.
  Proof.
    intros Himpl Hξ' ex aux c' oζ.
    assert (
        ∀ ξ x, ProofIrrel
                 (match x return Prop with (δ', ℓ) =>
                    ξ (ex :tr[ oζ ]: c') (aux :tr[ ℓ ]: δ')
                  end)).
    { intros ?[??]. apply make_proof_irrel. }
    apply finite_smaller_card_nat.
    specialize (Hξ' ex aux c' oζ). apply smaller_card_nat_finite in Hξ'.
    eapply (in_list_finite (map proj1_sig (@enum _ _ Hξ'))).
    intros [δ' ℓ] ?. apply elem_of_list_fmap.
    assert ((λ '(δ', ℓ), ξ' (ex :tr[ oζ ]: c') (aux :tr[ ℓ ]: δ')) (δ', ℓ)) by eauto.
    exists ((δ', ℓ) ↾ ltac:(eauto)). split =>//.
    apply elem_of_enum.
  Qed.
End finitary_lemma.

(** We can extract the simulation correspondence in the meta-logic
    from a proof of the simulation correspondence in the object-logic. *)
Theorem simulation_correspondence_multiple Λ M Σ `{!invGpreS Σ}
        (s: stuckness)
        (ξ : execution_trace Λ → auxiliary_trace M → Prop)
        (C: execution_trace Λ → Prop)
        `{forall ex, Decision (C ex)}
        {ML_INH: Inhabited (mlabel M)}
        es σ δ :
  rel_finitary ξ →
  (⊢ Gsim_cond Σ M s ξ C {tr[ (es, σ) ]} {tr[ δ ]}) →
  continued_simulation_cond ξ C {tr[ (es, σ) ]} {tr[δ]}.
Proof.
  intros Hsc Hwptp.
  exists (λ exatr, ⊢ Gsim_cond Σ M s ξ C exatr.1 exatr.2); split; first done.
  clear Hwptp.
  intros [ex atr].
  rewrite {1}/Gsim_cond (fixpoint_unfold (Gsim_cond_pre _ _ _ _ _) _ _); simpl; intros Hgsim.
  revert Hgsim; rewrite extract_later; intros Hgsim.

  destruct (decide (C ex)) as [PASS | FAIL].
  2: { done. } 
  apply extract_impl with (P := ⌜C ex⌝%I) in Hgsim.
  2: { set_solver. }
  
  apply extract_and in Hgsim as [Hvlt Hgsim].
  revert Hvlt; rewrite extract_pure; intros Hvlt.
  split; first done.

  intros c c' oζ Hsmends Hstep.
  revert Hgsim; rewrite extract_forall; intros Hgsim.
  specialize (Hgsim c).
  revert Hgsim; rewrite extract_forall; intros Hgsim.
  specialize (Hgsim oζ).
  revert Hgsim; rewrite extract_forall; intros Hgsim.
  specialize (Hgsim c').
  apply (extract_impl ⌜_⌝) in Hgsim; last by apply extract_pure.
  apply (extract_impl ⌜_⌝) in Hgsim; last by apply extract_pure.
  induction (trace_length ex) as [|n IHlen]; last first.
  { simpl in *.
    revert Hgsim; do 3 rewrite extract_later; intros Hgsim.
    apply IHlen. do 2 rewrite extract_later. apply Hgsim. }
  revert Hgsim; rewrite !extract_later; intros Hgsim.
  simpl in *.

  destruct (decide (C (ex :tr[ oζ ]: c'))) as [PASS' | FAIL'].
  2: { inversion ML_INH as [ℓ].
       exists (trace_last atr), ℓ.
       rewrite {1}/Gsim_cond (fixpoint_unfold (Gsim_cond_pre _ _ _ _ _) _ _).
       rewrite /Gsim_cond_pre. iNext. by iIntros "%". }

  assert (⊢ ▷ ∃ (δ': M) ℓ,
               (⌜ξ (ex :tr[oζ]: c') (atr :tr[ℓ]: δ')⌝) ∧
               fixpoint (Gsim_cond_pre Σ M s ξ C) (ex :tr[oζ]: c') (atr :tr[ℓ]: δ')).
  {
    iStartProof. iDestruct Hgsim as (δ'' ℓ) "Hfix". iExists δ'', ℓ.
    iSplit; last done.
    rewrite (fixpoint_unfold (Gsim_cond_pre _ _ _ _ _) _ _) /Gsim_cond_pre.
    iNext. iSpecialize ("Hfix" with "[//]").
    by iDestruct "Hfix" as "[? _]". }
  rewrite -> extract_later in H1.
  apply extract_exists_alt2 in H1 as (δ'' & ℓ & YY); [| done]. 
  exists δ'', ℓ.
  revert YY.
  rewrite !extract_and.
  intros [_ ?]; done.
Qed.

(** We can extract the simulation correspondence in the meta-logic
    from a proof of the simulation correspondence in the object-logic. *)
Theorem simulation_correspondence Λ M Σ `{!invGpreS Σ}
        (s: stuckness)
        (ξ : execution_trace Λ → auxiliary_trace M → Prop)
        C
        `{forall ex, Decision (C ex)}
        {ML_INH: Inhabited (mlabel M)}
        e1 σ1 δ1 :
  rel_finitary ξ →
  (⊢ Gsim_cond Σ M s ξ C {tr[ ([e1], σ1) ]} {tr[ δ1 ]}) →
  continued_simulation_cond ξ C {tr[ ([e1], σ1) ]} {tr[δ1]}.
Proof. by apply simulation_correspondence_multiple. Qed.

Theorem wp_strong_adequacy_multiple_with_trace_inv Λ M Σ `{!invGpreS Σ}
        (s: stuckness)
        (ξ : execution_trace Λ → auxiliary_trace M → Prop)
        C
        `{forall ex, Decision (C ex)}
        {ML_INH: Inhabited (mlabel M)}
        es σ δ :
  length es ≥ 1 →
  rel_finitary ξ →
  (∀ `{Hinv : !invGS_gen HasNoLc Σ},
    ⊢ |={⊤}=> ∃
         (stateI : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (trace_inv : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (Φs : list (val Λ → iProp Σ))
         (fork_post : locale Λ → val Λ → iProp Σ),
       let _ : irisG Λ M Σ := IrisG _ _ _ Hinv stateI fork_post in
       config_wp ∗
       stateI (trace_singleton (es, σ)) (trace_singleton δ) ∗
       wptp s es Φs ∗
       rel_always_holds_with_trace_inv s trace_inv Φs ξ (es,σ) δ) →
  continued_simulation_cond ξ C (trace_singleton (es, σ)) (trace_singleton δ).
Proof.
  intros Hlen Hsc Hwptp.
  eapply wp_strong_adequacy_multiple_helper in Hwptp; eauto. 
  by eapply simulation_correspondence_multiple.
Qed.

(* Theorem wp_strong_adequacy_with_trace_inv Λ M Σ `{!invGpreS Σ} *)
(* (same but for one initial thread)  *)

Theorem wp_strong_adequacy_multiple Λ M Σ `{!invGpreS Σ}
        (s: stuckness)
        (ξ : execution_trace Λ → auxiliary_trace M → Prop)
        C
        `{forall ex, Decision (C ex)}
        {ML_INH: Inhabited (mlabel M)}
        es σ δ :
  length es ≥ 1 →
  rel_finitary ξ →
  (∀ `{Hinv : !invGS_gen HasNoLc Σ},
    ⊢ |={⊤}=> ∃
         (stateI : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (Φs : list (val Λ → iProp Σ))
         (fork_post : locale Λ → val Λ → iProp Σ),
       let _ : irisG Λ M Σ := IrisG _ _ _ Hinv stateI fork_post in
       config_wp ∗
       stateI (trace_singleton (es, σ)) (trace_singleton δ) ∗
       wptp s es Φs ∗
       rel_always_holds s Φs ξ (es, σ) δ) →
  continued_simulation_cond ξ C (trace_singleton (es, σ)) (trace_singleton δ).
Proof.
  intros Hlen Hsc Hwptp.
  eapply wp_strong_adequacy_multiple_with_trace_inv; try done. 
  iIntros (Hinv) "".
  iMod (Hwptp Hinv) as (stateI Φ fork_post) "(Hwpcfg & HSI & Hwp & Hstep)".
  iModIntro.
  iExists stateI, (λ _ _, True)%I, Φ, fork_post; iFrame "Hwpcfg HSI Hwp".
  iIntros (ex atr c ? ? ?) "HSI Hposts".
  iSplit; last first.
  { iIntros "?". iApply ("Hstep" with "[] [] [] HSI"); eauto. }
  iModIntro; iIntros "[$ ?]"; done.
Qed.

Definition cur_posts `{irisG Λ M Σ} (tp: list (expr Λ)) e0 (Φ0: val Λ → iProp Σ): iProp Σ :=
  posts_of tp (Φ0 :: ((λ '(tnew, e), fork_post (locale_of tnew e)) <$>
                        prefixes_from [e0] (drop 1 tp))).
