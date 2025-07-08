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

Notation wptp_from t0 s t Φs := ([∗ list] tp1_e;Φ ∈ (prefixes_from t0 t);Φs, WP tp1_e.2 @ s; locale_of tp1_e.1 tp1_e.2; ⊤ {{ Φ }})%I.
Notation wptp s t Φs := (wptp_from [] s t Φs).

Definition config_wp `{!irisG Λ M Σ} : iProp Σ :=
  □ ∀ ex atr c1 σ2 ,
      ⌜valid_exec ex⌝ →
      ⌜trace_ends_in ex c1⌝ →
      ⌜config_step c1.2 σ2⌝ →
      state_interp ex atr ={⊤,∅}=∗ |={∅}▷=>^(S $ trace_length ex) |={∅,⊤}=>
         ∃ δ2 ℓ, state_interp (trace_extend ex None (c1.1, σ2))
                              (trace_extend atr ℓ δ2).

#[global] Instance config_wp_persistent `{!irisG Λ M Σ} : Persistent config_wp.
Proof. apply _. Qed.

#[global] Typeclasses Opaque config_wp.

(* (* condition that filters the executions to be considered *) *)
(* Context (C: execution_trace Λ → Prop). *)

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

#[global] Instance is_except_0_wptp {Σ} Λ M s ξ C ex sm:
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

Section adequacy_helper_lemmas.
  Context `{!irisG Λ M Σ}.

  Lemma wptp_from_same_locales t0' t0 s tp Φs:
    locales_equiv t0 t0' ->
    wptp_from t0' s tp Φs -∗ wptp_from t0 s tp Φs.
  Proof.
    revert Φs t0 t0'. induction tp; intros Φs t0 t0'; iIntros (Hequiv) "H" =>//.
    simpl.
    iDestruct (big_sepL2_cons_inv_l with "H") as (Φ Φs' ->) "[??]".
    rewrite big_sepL2_cons. simpl. erewrite <-locale_equiv =>//. iFrame.
    iApply IHtp =>//. apply locales_equiv_snoc =>//.
    apply locale_equiv =>//.
  Qed.

  Lemma wptp_not_stuck ex atr σ tp t0 t0' trest s Φs :
    Forall2 (λ '(t, e) '(t', e'), locale_of t e = locale_of t' e') (prefixes t0) (prefixes t0') ->
    valid_exec ex →
    trace_ends_in ex (t0 ++ tp ++ trest, σ) →
    state_interp ex atr -∗ wptp_from t0' s tp Φs ={⊤}=∗
    state_interp ex atr ∗ wptp_from t0 s tp Φs ∗
    ⌜∀ e, e ∈ tp → s = NotStuck → not_stuck e (trace_last ex).2⌝.
  Proof.
    iIntros (Hsame Hexvalid Hex) "HSI Ht".
    rewrite assoc.
    iDestruct (wptp_from_same_locales t0' with "Ht") as "Ht"; first done.
    iApply fupd_plain_keep_r; iFrame.
    iIntros "[HSI Ht]".
    iIntros (e He).
    apply elem_of_list_split in He as (t1 & t2 & ->).
    rewrite prefixes_from_app.
    iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2') "[-> [Ht1 Het2]]".
    iDestruct (big_sepL2_cons_inv_l with "Het2") as (Φ Φs2) "[-> [He Ht2]]".
    iMod (wp_not_stuck _ _ ectx_emp with "HSI He") as "(_ & _ & ?)";
      [done| rewrite ectx_fill_emp // | |done].
    - replace (t0 ++ (t1 ++ e :: t2) ++ trest) with ((t0 ++ t1) ++ e :: (t2 ++ trest)) in Hex.
      + simpl. done.
      + list_simplifier. done.
    - done.
  Qed.

  Lemma wptp_not_stuck_same ex atr σ tp t0 trest s Φs :
    valid_exec ex →
    trace_ends_in ex (t0 ++ tp ++ trest, σ) →
    state_interp ex atr -∗ wptp_from t0 s tp Φs ={⊤}=∗
    state_interp ex atr ∗ wptp_from t0 s tp Φs ∗
    ⌜∀ e, e ∈ tp → s = NotStuck → not_stuck e (trace_last ex).2⌝.
  Proof.
    iIntros (??) "??". iApply (wptp_not_stuck with "[$] [$]") =>//.
    eapply Forall2_lookup. intros i. destruct (prefixes t0 !! i) as [[??]|]; by constructor.
  Qed.

  Lemma wptp_app s t0 t1 t0t1 Φs1 t2 Φs2 :
    t0t1 = t0 ++ t1 ->
    wptp_from t0 s t1 Φs1 -∗ wptp_from t0t1 s t2 Φs2 -∗ wptp_from t0 s (t1 ++ t2) (Φs1 ++ Φs2).
  Proof.
    iIntros (->) "H1 H2". rewrite prefixes_from_app.
    iApply (big_sepL2_app with "[H1] [H2]"); eauto.
  Qed.

  Lemma wptp_cons_r s e Φ Φs t0 t1:
    WP e @ s; locale_of (t0 ++ t1) e; ⊤ {{v, Φ v}} -∗ wptp_from t0 s t1 Φs
                              -∗ wptp_from t0 s (t1 ++ [e]) (Φs ++ [Φ]).
  Proof.
    iIntros "H1 H2". rewrite !prefixes_from_app.
    iApply (big_sepL2_app with "[H2] [H1]"); eauto.
    rewrite big_sepL2_singleton. done.
  Qed.

  Lemma wptp_cons_l s e Φ t Φs t0:
    WP e @ s; locale_of t0 e; ⊤ {{v, Φ v}} -∗
    wptp_from (t0 ++[e]) s t Φs -∗
    wptp_from t0 s (e :: t) (Φ :: Φs).
  Proof. iIntros "? ?"; rewrite big_sepL2_cons; iFrame. Qed.

  Lemma wptp_of_val_post t s Φs t0:
    wptp_from t0 s t Φs -∗ |~{⊤}~|
    posts_of t Φs ∗
    (posts_of t Φs -∗ wptp_from t0 s t Φs).
  Proof.
    iIntros "Ht"; simpl.
    iInduction t as [|e t IHt] "IH" forall (Φs t0); simpl.
    { iDestruct (big_sepL2_nil_inv_l with "Ht") as %->; eauto.
      iIntros "!>". eauto. }
    iDestruct (big_sepL2_cons_inv_l with "Ht") as (Φ Φs') "[-> [He Ht]] /=".
    iMod (wp_of_val_post with "He") as "[Hpost Hback]".
    iMod ("IH" with "Ht") as "[Ht Htback]".
    destruct (to_val e); simpl.
    - iFrame.
      iIntros "!>". iFrame.
      iIntros "[Hpost Htpost]".
      iSplitL "Hpost Hback"; [iApply "Hback"|iApply "Htback"]; iFrame.
      by iIntros "!>".
    - iIntros "!>".
      iFrame.
      iIntros "Hefspost".
      iSplitL "Hback"; [iApply "Hback"|iApply "Htback"]; iFrame; done.
  Qed.

  Lemma new_threads_wptp_from s t efs:
    (([∗ list] i ↦ ef ∈ efs,
      WP ef @ s; locale_of (t ++ take i efs) ef ; ⊤
      {{ v, fork_post (locale_of (t ++ take i efs) ef) v }})
    ⊣⊢ wptp_from t s efs (newposts t (t ++ efs))).
  Proof.
    (* TODO: factorize the two halves *)
    rewrite big_sepL2_alt; iSplit.
    - iIntros "H". iSplit.
      { rewrite /newposts /newelems. 
        rewrite drop_app_length // map_length !prefixes_from_length //. }
      iInduction efs as [|ef efs] "IH" forall (t); first done.
      rewrite /newposts /newelems. rewrite /= !drop_app_length //=.
      iDestruct "H" as "[H1 H]". rewrite (right_id [] (++)). iFrame.
      replace (map (λ '(tnew, e), fork_post (locale_of tnew e))
                   (prefixes_from (t ++ [ef]) efs))
        with
          (newposts (t ++[ef]) ((t ++ [ef]) ++ efs)).
      + iApply "IH". iApply (big_sepL_impl with "H").
        iIntros "!>" (k e Hin) "H". by list_simplifier.
      + list_simplifier.
        replace (t ++ ef :: efs) with ((t ++ [ef]) ++ efs); last by list_simplifier.
        rewrite /newposts /newelems. rewrite drop_app_length //.
    - iIntros "[_ H]".
      iInduction efs as [|ef efs] "IH" forall (t); first done.
      rewrite /newposts /newelems. rewrite /= !drop_app_length //=.
      iDestruct "H" as "[H1 H]". rewrite (right_id [] (++)). iFrame.
      replace (map (λ '(tnew, e), fork_post (locale_of tnew e))
                   (prefixes_from (t ++ [ef]) efs))
        with
          (newposts (t ++[ef]) ((t ++ [ef]) ++ efs)).
      + iSpecialize ("IH" with "H"). iApply (big_sepL_impl with "IH").
        iIntros "!>" (k e Hin) "H". by list_simplifier.
      + list_simplifier.
        replace (t ++ ef :: efs) with ((t ++ [ef]) ++ efs); last by list_simplifier.
        rewrite /newposts /newelems. rewrite drop_app_length //.
  Qed.

  Lemma take_step s Φs ex atr c c' oζ:
    valid_exec ex →
    trace_ends_in ex c →
    locale_step c oζ c' →
    config_wp -∗
    state_interp ex atr -∗
    wptp s c.1 Φs ={⊤,∅}=∗ |={∅}▷=>^(S (trace_length ex))
                                             |={∅,⊤}=>
    ⌜∀ e2, s = NotStuck → e2 ∈ c'.1 → not_stuck e2 c'.2⌝ ∗
    ∃ δ' ℓ,
      state_interp (trace_extend ex oζ c') (trace_extend atr ℓ δ') ∗
      wptp s  c'.1 (Φs ++ newposts c.1 c'.1). 
  Proof.
    iIntros (Hexvalid Hexe Hstep) "config_wp HSI Hc1".
    inversion Hstep as
        [ρ1 ρ2 e1 σ1 e2 σ2 efs t1 t2 -> -> Hpstep | ρ1 ρ2 σ1 σ2 t -> -> Hcfgstep].
    - rewrite /= !prefixes_from_app.
      iDestruct (big_sepL2_app_inv_l with "Hc1") as
          (Φs1 Φs2') "[-> [Ht1 Het2]]".
      iDestruct (big_sepL2_cons_inv_l with "Het2") as (Φ Φs2) "[-> [He Ht2]]".
      iDestruct (wp_take_step with "HSI He") as "He"; [done|done|done|done|].
      iMod "He" as "He". iModIntro. iMod "He" as "He". iModIntro. iNext.
      iMod "He" as "He". iModIntro.
      iApply (step_fupdN_wand with "[He]"); first by iApply "He".
      iIntros "He".
      iMod "He" as (δ' ℓ) "(HSI & He2 & Hefs) /=".
      have Heq: forall a b c d, a ++ e1 :: c ++ d = (a ++ e1 :: c) ++ d.
      { intros **. by list_simplifier. }
      iAssert (wptp_from (t1 ++ e2 :: t2) s efs (newposts (t1 ++ e2 :: t2) ((t1 ++ e2 :: t2) ++ efs)))
        with "[Hefs]" as "Hefs".
      { rewrite -new_threads_wptp_from. iApply (big_sepL_impl with "Hefs").
        iIntros "!#" (i e Hin) "Hwp". list_simplifier.
        erewrite locale_equiv; first by iFrame.
        apply locales_equiv_middle. erewrite locale_step_preserve =>//. }
      assert (valid_exec (ex :tr[Some (locale_of t1 e1)]: (t1 ++ e2 :: t2 ++ efs, σ2))).
      { econstructor; eauto. }
      iMod (wptp_not_stuck_same _ _ σ2 _ _ [] with "HSI Hefs") as "[HSI [Hefs %]]"; [done| | ].
      { list_simplifier. done. }
      iMod (wptp_not_stuck_same _ _ σ2 _ _ (e2 :: (t2 ++ efs)) with "HSI Ht1") as "[HSI [Ht1 %]]"; [done|  |].
      {  list_simplifier. done. }
      iMod (wptp_not_stuck _ _ σ2 _ (t1 ++ [e2]) _ efs with "HSI Ht2") as "[HSI [Ht2 %]]"; [| done | |].
      { rewrite !prefixes_from_app. apply Forall2_app.
        - apply locales_equiv_refl.
        - constructor; last constructor. list_simplifier. erewrite <-locale_step_preserve =>//. }
      { list_simplifier. done. }
      iMod (wp_not_stuck _ _ ectx_emp with "HSI He2") as "[HSI [He2 %]]";
        [done|by rewrite ectx_fill_emp|by erewrite <-locale_step_preserve|].

      iDestruct (wptp_app with "Ht2 Hefs") as "Ht2efs".
      { by list_simplifier. }
      erewrite (locale_step_preserve e1 e2) =>//.
      iDestruct (wptp_cons_l with "He2 Ht2efs") as "He2t2efs".
      iDestruct (wptp_app with "Ht1 He2t2efs") as "Hc2"; [by list_simplifier|].
      iDestruct (wptp_of_val_post with "Hc2") as "Hc2".
      iMod (pre_step_elim with "HSI Hc2") as "[HSI [Hc2posts Hc2back]]".
      iModIntro; simpl in *.
      iSplit.
      { iPureIntro; set_solver. }
      iExists δ', ℓ.
      rewrite -!app_assoc.
      iFrame.
      list_simplifier.
      erewrite newposts_locales_equiv;
        [iFrame | apply locales_equiv_middle; erewrite <-locale_step_preserve =>//].
      iDestruct ("Hc2back" with "[$]") as "X". iFrame. 
      rewrite prefixes_from_app //.
    - rewrite /= /config_wp.
      iDestruct ("config_wp" with "[] [] [] HSI") as "Hcfg"; [done|done|done|].
      iMod "Hcfg". iModIntro. iMod "Hcfg". iModIntro.
      iNext. iMod "Hcfg". iModIntro.
      iApply (step_fupdN_wand with "[Hcfg]"); first by iApply "Hcfg".
      iIntros "Hcfg".
      iMod "Hcfg" as (δ2 ℓ) "HSI".
      assert (valid_exec (ex :tr[None]: ((t, σ1).1, σ2))).
      { econstructor; eauto. }
      iMod (wptp_not_stuck _ _ σ2 _ _ _ [] with "HSI Hc1") as "[HSI [Hc1 %]]";
        [apply locales_equiv_refl|done|by list_simplifier|].
      iDestruct (wptp_of_val_post with "Hc1") as "Hc1".
      iMod (pre_step_elim with "HSI Hc1") as "[HSI [Hc1posts Hc1back]]".
      iModIntro.
      iSplit; first by auto.
      iExists δ2, ℓ.
      rewrite newposts_same_empty. list_simplifier.
      iFrame.
      by iApply "Hc1back". 
  Qed.

End adequacy_helper_lemmas.


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

Definition rel_always_holds `{!irisG Λ M Σ}
           (s:stuckness) Φs
           (ξ : execution_trace Λ → auxiliary_trace M → Prop) (c1:cfg Λ)
           (c2:M) : iProp Σ :=
  (∀ (ex : execution_trace Λ) (atr : auxiliary_trace M) (c : cfg Λ),
         ⌜valid_system_trace ex atr⌝ -∗
         ⌜trace_starts_in ex c1⌝ -∗
         ⌜trace_starts_in atr c2⌝ -∗
         ⌜trace_ends_in ex c⌝ -∗
         ⌜steps_from_ref ξ ex atr⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗
         ⌜locales_equiv c1.1 (take (length c1.1) c.1)⌝ -∗
         state_interp ex atr -∗
         cur_posts_multiple c.1 c1.1 Φs
         -∗
         |={⊤, ∅}=> ⌜ξ ex atr⌝).

Definition rel_always_holds_with_trace_inv `{!irisG Λ M Σ}
           (s:stuckness) trace_inv Φs
           (ξ : execution_trace Λ → auxiliary_trace M → Prop)
           (c1:cfg Λ) (c2:M) : iProp Σ :=
  (∀ (ex : execution_trace Λ) (atr : auxiliary_trace M) (c : cfg Λ),
         ⌜valid_system_trace ex atr⌝ -∗
         ⌜trace_starts_in ex c1⌝ -∗
         ⌜trace_starts_in atr c2⌝ -∗
         ⌜trace_ends_in ex c⌝ -∗
         ⌜steps_from_ref ξ ex atr ⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗
         ⌜locales_equiv c1.1 (take (length c1.1) c.1)⌝ -∗
         state_interp ex atr -∗
         cur_posts_multiple c.1 c1.1 Φs -∗
         □ (state_interp ex atr ∗
             steps_from_inv trace_inv ex atr
            ={⊤}=∗ state_interp ex atr ∗ trace_inv ex atr) ∗
         ((∀ ex' atr' oζ ℓ,
              ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
          ={⊤, ∅}=∗ ⌜ξ ex atr⌝)).


Section StrongAdequacyHelpers.
  Context {Λ: language} {M: Model}. 
  Context (ξ : execution_trace Λ → auxiliary_trace M → Prop).

  Context `{invGpreS Σ}. 
  Context (stateI trace_inv: execution_trace Λ → auxiliary_trace M → iProp Σ). 
  Context (post : locale Λ → val Λ → iProp Σ).

  Context (C: execution_trace Λ → Prop).
  Hypothesis C_DEC: forall ex, Decision (C ex). 

  Definition cur_tr_repr_impl
    (Hinv : invGS_gen HasNoLc Σ)    
(i :=
    {|
      iris_invGS := Hinv;
      state_interp := stateI;
      fork_post := post
    |} : irisG Λ M Σ)
    s es Φs ex atr: iProp Σ :=
    (
    let c1 := trace_last ex in 
    stateI ex atr ∗
    steps_from_inv trace_inv ex atr ∗
    (let i := {| iris_invGS := Hinv; state_interp := stateI; fork_post := post |} : irisG Λ M Σ in
     wptp s c1.1 (all_posts c1.1 es Φs))). 

  Definition cur_tr_repr
    (Hinv : invGS_gen HasNoLc Σ)    
(i :=
    {|
      iris_invGS := Hinv;
      state_interp := stateI;
      fork_post := post
    |} : irisG Λ M Σ)
    s es Φs ex atr: iProp Σ :=
    ⌜ C ex ⌝ → cur_tr_repr_impl _ s es Φs ex atr.

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
    cur_tr_repr _ s es Φs ex atr
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
    (i :=
    {|
      iris_invGS := Hinv;
      state_interp := stateI;
      fork_post := post
    |} : irisG Λ M Σ)
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
  (Hc1 : (tp, σ1') = trace_last ex)
  (Htake : locales_equiv es (take (length es) tp))
  (Htakelen : length es ≤ length tp)
  (Hξ' : ξ ex atr)
  (c : cfg Λ)
  (oζ : olocale Λ)
  (c' : cfg Λ)
  (Hc : trace_ends_in ex c)
  (Hstep : locale_step c oζ c')
  (H0 : c = (tp, σ1'))
  (H1 : ∀ e2 : expr Λ, s = NotStuck → e2 ∈ c'.1 → not_stuck e2 c'.2)
  (δ'' : M)
  (ℓ : mlabel M):
      rel_always_holds_with_trace_inv s trace_inv Φs ξ (es, σ) δ -∗
      cur_tr_repr_impl Hinv s es Φs (ex :tr[ oζ ]: c') (atr :tr[ ℓ ]: δ'') -∗
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

    iDestruct ("Hstep" with "[] [] [] [] [] [] [] HSI") as "H"; [iPureIntro..|].
    - eapply valid_system_trace_extend; eauto.
    - eapply trace_extend_starts_in; eauto.
    - eapply trace_extend_starts_in; eauto.
    - eapply trace_extend_ends_in; eauto.
    - by intros ? ? ? ? [-> ->]%trace_contract_of_extend [-> ->]%trace_contract_of_extend.
    - done.
    - eapply locales_equiv_from_transitive;
        [by apply locales_equiv_refl|by apply locales_equiv_refl|done|].
      apply locale_step_equiv in Hstep.
      eapply (locales_equiv_from_take _ _ _ _ (length es)) in Hstep.
      rewrite !firstn_firstn in Hstep.
      subst c.
      rewrite !min_l in Hstep; [done|simpl; lia].
    - subst c.
      iApply (f2b_helper with "[$]"). 
      iDestruct ("H" with "POSTS") as "[? Hξ]".
      iMod ("Hξ" with "[HTI]") as "%".
      + iIntros (? ? ? ? [-> ->]%trace_contract_of_extend
                 [-> ->]%trace_contract_of_extend); done.
      + iModIntro.
        iIntros "HFtB"; done.
  Qed.

  Definition tr_extras es σ δ ex atr
    (c1 := trace_last ex) :=
    valid_system_trace ex atr
    ∧ trace_starts_in ex (es, σ)
        ∧ trace_starts_in atr δ
          ∧ steps_from_ref ξ ex atr
            ∧ locales_equiv es (take (length es) c1.1)
              ∧ length es ≤ length c1.1.

  Lemma get_current_facts
    s es σ δ
    (* (Hes : length es ≥ 1) *)
    (Hinv : invGS_gen HasNoLc Σ)
    (Φs : list (val Λ → iProp Σ))
  (i :=
    {|
      iris_invGS := Hinv;
      state_interp := stateI;
      fork_post := post
    |} : irisG Λ M Σ)
  (ex : finite_trace (list (expr Λ) * state Λ) (olocale Λ))
  (atr : auxiliary_trace M)
  (Hextras : tr_extras es σ δ ex atr):

  rel_always_holds_with_trace_inv s trace_inv Φs ξ (es, σ) δ -∗
  cur_tr_repr_impl Hinv s es Φs ex atr ={⊤}=∗
  ⌜ξ ex atr⌝ ∗
  rel_always_holds_with_trace_inv s trace_inv Φs ξ (es, σ) δ ∗
  cur_tr_repr_impl Hinv s es Φs ex atr ∗
  ⌜ ∀ e, e ∈ (trace_last ex).1 → s = NotStuck → not_stuck e (trace_last ex).2 ⌝.
  Proof using.
    iIntros "Hstep PRE". iDestruct "PRE" as "(HSI & HTI & Htp)".
    destruct Hextras as (Hv & Hex & Hatr & Hξ & Htake & Htakelen).

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
    
    iDestruct ("Hstep" with "[] [] [] [] [] [] [] HSI Hpost") as "[_ Hξ]"; eauto.
    iApply fupd_plain_mask.
    iMod ("Hξ" with "HTI") as "%"; auto.
  Qed.

  Lemma get_trace_inv ex atr δ es σ s
    (Hinv : invGS_gen HasNoLc Σ)
    (Φs : list (val Λ → iProp Σ))
    (EXTRAS: tr_extras es σ δ ex atr)
    (NSTUCK: ∀ e, e ∈ (trace_last ex).1 → s = NotStuck → not_stuck e (trace_last ex).2)
  (i :=
    {|
      iris_invGS := Hinv;
      state_interp := stateI;
      fork_post := post
    |} : irisG Λ M Σ):
  rel_always_holds_with_trace_inv s trace_inv Φs ξ (es, σ) δ -∗
  stateI ex atr -∗ steps_from_inv trace_inv ex atr -∗
  wptp s (trace_last ex).1 (all_posts (trace_last ex).1 es Φs)
    (* cur_tr_repr _ s es Φs ex atr *)
  ={⊤}=∗
  trace_inv ex atr ∗   
  rel_always_holds_with_trace_inv s trace_inv Φs ξ (es, σ) δ ∗
  (* cur_tr_repr _ s es Φs ex atr. *)
  stateI ex atr ∗ (* steps_from_inv ex atr ∗ *)
  wptp s (trace_last ex).1 (all_posts (trace_last ex).1 es Φs).
  Proof using.
    (* iIntros "Hstep (HSI & HTI & Htp)". *)
    iIntros "Hstep HSI HTI Htp".
    iPoseProof (wptp_of_val_post with "Htp") as "Htp".
    replace stateI with state_interp by done.
    iMod (pre_step_elim with "HSI Htp") as "[HSI Htp]".
    iDestruct ("Htp") as "(Hpost & Hback)".
    
    iAssert (□ (stateI ex atr -∗ steps_from_inv _ ex atr
                ={⊤}=∗ stateI ex atr ∗ trace_inv ex atr))%I
      as "#HTIextend".
    { 
      iDestruct ("Hstep" with "[] [] [] [] [] [] [] HSI Hpost") as "[#Hext _]";
        auto.
      { iPureIntro. apply EXTRAS. }
      { iPureIntro. apply EXTRAS. }
      { iPureIntro. apply EXTRAS. }
      { iPureIntro. apply EXTRAS. }
      { iPureIntro. apply EXTRAS. }
      iModIntro.
      iIntros "HSI HTI".
      iApply ("Hext" with "[$HSI $HTI]"). }
    
    iMod ("HTIextend" with "HSI HTI") as "[HSI HTI]".
    iClear "HTIextend".
    iDestruct ("Hback" with "[$]") as "Htp".
    iModIntro. iFrame.
  Qed.

  Lemma reestablish_tr_extras ex atr (c: cfg Λ) (oζ: olocale Λ) (c': cfg Λ) (δ'' : M) (ℓ : mlabel M) es σ δ
    (Hξ' : ξ ex atr)
    (Hc : trace_ends_in ex c)
    (Hstep : locale_step c oζ c')
    (Hextras : tr_extras es σ δ ex atr):
    tr_extras es σ δ (ex :tr[ oζ ]: c') (atr :tr[ ℓ ]: δ'').
  Proof using.
    split_and!.
    + eapply valid_system_trace_extend; eauto; try apply Hextras. 
    + eapply trace_extend_starts_in. apply Hextras. 
    + eapply trace_extend_starts_in. apply Hextras. 
    + intros ???? [??]%trace_contract_of_extend [??]%trace_contract_of_extend.
      subst. eauto. 
    + eapply locales_equiv_from_transitive;
        [by apply locales_equiv_refl|by apply locales_equiv_refl|by apply Hextras |].
      apply locale_step_equiv in Hstep.
      eapply (locales_equiv_from_take _ _ _ _ (length es)) in Hstep.
      rewrite !firstn_firstn in Hstep.
      pose proof Hc as <-%last_eq_trace_ends_in. 
      rewrite !min_l in Hstep.
      2: { red in Hextras. apply Hextras. }
      simpl in *. done. 
    + eapply step_tp_length in Hstep.
      simpl in *. etrans; [| apply Hstep].
      pose proof Hc as <-%last_eq_trace_ends_in. apply Hextras. 
  Qed.

  Lemma strong_adequacy_trace
    s
    es σ δ
    (Hes : length es ≥ 1)
    (Hinv : invGS_gen HasNoLc Σ)
    (Φs : list (val Λ → iProp Σ))
  (i :=
    {|
      iris_invGS := Hinv;
      state_interp := stateI;
      fork_post := post
    |} : irisG Λ M Σ)
  (ex : finite_trace (list (expr Λ) * state Λ) (olocale Λ))
  (atr : auxiliary_trace M)
  (c1 := trace_last ex)
  (Hextras : tr_extras es σ δ ex atr):
    config_wp -∗ 
    rel_always_holds_with_trace_inv s trace_inv Φs ξ (es, σ) δ -∗
    cur_tr_repr _ s es Φs ex atr
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

    destruct Hextras as (Hv & Hex & Hatr & Hξ & Htake & Htakelen).

    remember (trace_last ex) as c1 eqn:Hc1. 
    assert (valid_exec ex) as Hexv.
    { by eapply valid_system_trace_valid_exec_trace. }

    iMod (get_current_facts with "[$] [$]") as "(Hξ & Hstep & PRE & %NSTUCK)".
    { repeat split; auto. }

    iDestruct "PRE" as "(HSI & HTI & Htp)".
    replace stateI with state_interp by done.

    rewrite {2}/Gsim_cond (fixpoint_unfold (Gsim_cond_pre _ _ _ _ _) _ _).
    destruct c1 as [tp σ1'].

    iMod (get_trace_inv with "[$] [$] [$] [$]") as "(HTI & Hstep & HSI & Htp)"; eauto.
    { repeat split; auto. }
    
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
 
  iAssert (cur_tr_repr Hinv s es Φs (ex :tr[ oζ ]: c') (atr :tr[ ℓ ]: δ'') ∗ fupd_to_bupd ⊤ ∗ rel_always_holds_with_trace_inv s trace_inv Φs ξ (es, σ) δ)%I
    with "[Hstep HSI HTI Hback HFtB]" as "(PRE' & HFtB & Hstep)".
  {

    (* destruct (decide (C (ex :tr[ oζ ]: c'))) as [PASS' | FAIL']. *)
    (* 2: { iFrame. by iIntros "%". } *)

    iPoseProof (ref_preserved' with "[$] [HSI HTI Hback] [$]") as "#Hextend"; eauto.
    { by rewrite -Hc1 in Htake. } 
    (* { by rewrite -Hc1 in Htakelen. } *)
    { rewrite -Hc1 in Htakelen. simpl in *. lia. }
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
      iDestruct "Hback" as "(Hpost & Hwptp)". by iApply "Hwptp". }
 
  iExists _, _.
  iApply (f2b_helper with "[$]"). 
  iMod ("IH" with "[] [$] PRE'") as "IH'".
  - iPureIntro.
    assert (Hextras : tr_extras es σ δ ex atr) by (repeat split; auto). 
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

  assert
    (valid_system_trace ex atr ∧
     trace_starts_in ex (es, σ) ∧
     trace_ends_in ex c1 ∧
     trace_starts_in atr δ ∧
     (∀ ex' atr' oζ ℓ,
         trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' atr') ∧
    locales_equiv es (take (length es) c1.1) ∧
    length es ≤ length c1.1)
    as Hextras.
  { rewrite -Hexsing -Hatrsing -Hc1.
    split; first apply valid_system_trace_singletons.
    repeat (split; first done).
    split; [intros ? ? ? ? ? ?%not_trace_contract_singleton; done|].
    split; [|done].
    rewrite take_ge; [apply locales_equiv_refl|done].
  }
  clear Hc1 Hδ1.
  rewrite Hexsing Hatrsing; clear Hexsing Hatrsing.

  assert (c1 = trace_last ex) as Hlast.
  { symmetry. eapply last_eq_trace_ends_in. apply Hextras. }
  (* rewrite Hlast.  *)
  iApply (strong_adequacy_trace with "[$] [$]").
  3: { iFrame "#∗". done. }
  { tauto. }
  destruct Hextras as (?&?&?&?&?&?&?).
  split_and !; try by eauto.
  all: set_solver.
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
  iIntros "!>". iExists stateI, trace_inv, [Φs], fork_post. by iFrame "#∗".
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

Theorem wp_strong_adequacy_with_trace_inv Λ M Σ `{!invGpreS Σ}
        (s: stuckness)
        (ξ : execution_trace Λ → auxiliary_trace M → Prop)
        C
        `{forall ex, Decision (C ex)}
        {ML_INH: Inhabited (mlabel M)}
        e1 σ1 δ1 :
  rel_finitary ξ →
  (∀ `{Hinv : !invGS_gen HasNoLc Σ},
    ⊢ |={⊤}=> ∃
         (stateI : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (trace_inv : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (Φ : val Λ → iProp Σ)
         (fork_post : locale Λ → val Λ → iProp Σ),
       let _ : irisG Λ M Σ := IrisG _ _ _ Hinv stateI fork_post in
       config_wp ∗
       stateI (trace_singleton ([e1], σ1)) (trace_singleton δ1) ∗
       WP e1 @ s; locale_of [] e1; ⊤ {{ Φ }} ∗
       rel_always_holds_with_trace_inv s trace_inv [Φ] ξ ([e1], σ1) δ1) →
  continued_simulation_cond ξ C (trace_singleton ([e1], σ1)) (trace_singleton δ1).
Proof.
  intros Hsc Hwptp. 
  eapply wp_strong_adequacy_helper in Hwptp; eauto. 
  by eapply simulation_correspondence.
Qed.

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
  iIntros (ex atr c ? ? ? ? ? ? ?) "HSI Hposts".
  iSplit; last first.
  { iIntros "?". iApply ("Hstep" with "[] [] [] [] [] [] [] HSI"); eauto. }
  iModIntro; iIntros "[$ ?]"; done.
Qed.

Definition cur_posts `{irisG Λ M Σ} (tp: list (expr Λ)) e0 (Φ0: val Λ → iProp Σ): iProp Σ :=
  posts_of tp (Φ0 :: ((λ '(tnew, e), fork_post (locale_of tnew e)) <$>
                        prefixes_from [e0] (drop 1 tp))).


(* Definition rel_always_holds0 `{irisG Λ M Σ} *)
(*   (ξ: execution_trace Λ → auxiliary_trace M → Prop) *)
(*   C *)
(*   `{forall ex, Decision (C ex)} *)
(*   {ML_INH: Inhabited (mlabel M)} *)
(*   (s: stuckness) *)
(*   (stateI: execution_trace Λ → auxiliary_trace M → iProp Σ) *)
(*   (Φ0: val Λ → iProp Σ)  *)
(*   e1 σ1 δ1: iProp Σ *)
(*   := *)
(*   ∀ (ex : execution_trace Λ) (atr : auxiliary_trace M) *)
(*     (c : cfg Λ), *)
(*     ⌜valid_system_trace ex atr⌝ -∗ *)
(*     ⌜trace_starts_in ex ([e1], σ1)⌝ -∗ *)
(*     ⌜trace_starts_in atr δ1⌝ -∗ *)
(*     ⌜trace_ends_in ex c⌝ -∗ *)
(*     ⌜∀ (ex' : finite_trace (cfg Λ) (olocale Λ)) *)
(*        (atr' : auxiliary_trace M) (oζ : olocale Λ) *)
(*        (ℓ: mlabel M), *)
(*     trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' atr'⌝ -∗ *)
(*     ⌜∀ e2 : expr Λ, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗ *)
(*     ⌜locales_equiv [e1] (take (length [e1]) c.1)⌝ -∗ *)
(*     stateI ex atr -∗ *)
(*     (* posts_of c.1 (Φ0 :: ((λ '(tnew, e), fork_post (locale_of tnew e)) <$> *) *)
(*     (*                         prefixes_from [e1] (drop (length [e1]) c.1))) *) *)
(*     cur_posts c.1 e1 Φ0 *)
(*     ={⊤,∅}=∗ ⌜ξ ex atr⌝. *)

(* Theorem wp_strong_adequacy Λ M Σ `{!invGpreS Σ} *)
(*         (s: stuckness) *)
(*         (ξ : execution_trace Λ → auxiliary_trace M → Prop) *)
(*         e1 σ1 δ1 : *)
(*   rel_finitary ξ → *)
(*   (∀ `{Hinv : !invGS_gen HasNoLc Σ}, *)
(*     ⊢ |={⊤}=> ∃ *)
(*          (stateI : execution_trace Λ → auxiliary_trace M → iProp Σ) *)
(*          (Φ : val Λ → iProp Σ) *)
(*          (fork_post : locale Λ → val Λ → iProp Σ), *)
(*        let _ : irisG Λ M Σ := IrisG _ _ _ Hinv stateI fork_post in *)
(*        config_wp ∗ *)
(*        stateI (trace_singleton ([e1], σ1)) (trace_singleton δ1) ∗ *)
(*        WP e1 @ s; locale_of [] e1; ⊤ {{ Φ }} ∗ *)
(*        (* rel_always_holds s [Φ] ξ ([e1], σ1) δ1) → *) *)
(*        rel_always_holds0 ξ s stateI Φ e1 σ1 δ1) -> *)
(*   continued_simulation ξ (trace_singleton ([e1], σ1)) (trace_singleton δ1). *)
(* Proof. *)
(*   intros Hsc Hwptp. *)
(*   eapply wp_strong_adequacy_with_trace_inv; [done|done|]. *)
(*   iIntros (Hinv) "". *)
(*   iMod (Hwptp Hinv) as (stateI Φ fork_post) "(Hwpcfg & HSI & Hwp & Hstep)". *)
(*   iModIntro. *)
(*   iExists stateI, (λ _ _, True)%I, Φ, fork_post; iFrame "Hwpcfg HSI Hwp". *)
(*   iIntros (ex atr c ? ? ? ? ? ? ?) "HSI Hposts". *)
(*   iSplit; last first. *)
(*   { iIntros "?". iApply ("Hstep" with "[] [] [] [] [] [] [] HSI"); eauto. } *)
(*   iModIntro; iIntros "[$ ?]"; done. *)
(* Qed. *)
