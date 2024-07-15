From Paco Require Import paco1 paco2 pacotac.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import excl_auth.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination fairness_finiteness trace_utils.
From trillium.fairness.heap_lang Require Export lang lifting tactics notation adequacy.
From trillium.fairness.heap_lang.examples.even_odd Require Import eo_vs_mod2 interface utils action_model.
From stdpp Require Import finite.

(** Helper lemmas for working with even and odd *)

Lemma even_odd_False n : Nat.even n → Nat.odd n → False.
Proof.
  intros Heven Hodd. rewrite -Nat.negb_odd in Heven.
  apply Is_true_true_1 in Heven.
  apply Is_true_true_1 in Hodd.
  by rewrite Hodd in Heven.
Qed.

Lemma even_not_odd n : Nat.even n → ¬ Nat.odd n.
Proof. intros Heven Hodd. by eapply even_odd_False. Qed.

Lemma odd_not_even n : Nat.odd n → ¬ Nat.even n.
Proof. intros Heven Hodd. by eapply even_odd_False. Qed.

Section ModelMono.
(** Proof that any fair execution of model visits all natural numbers *)
  Context {even_impl: EvenModel} {odd_impl: OddModel}.
  Let M := @the_fair_model even_impl odd_impl.
  Let even_AM := @even_AM even_impl. 

  Definition evenodd_mtrace : Type := mtrace M.
  
  Definition evenodd_mdl_progress (tr : evenodd_mtrace) :=
    ∀ (i: nat), ∃ n, pred_at tr n (λ s _, st2nat s i).

  Definition evenodd_mdl_mono (tr : evenodd_mtrace) :=
    ∀ n, ∃ i, pred_at tr n (λ s _, st2nat s i) ∧
              pred_at tr (S n) (λ s _, ∃ j, st2nat s j ∧ i ≤ j).
  
  (* Lemma evenodd_mdl_always_live ρ n (mtr : evenodd_mtrace) : *)
  (*   infinite_trace mtr → *)
  (*   pred_at mtr n *)
  (*     (λ (δ : M) (_ : option (option (fmrole M))), *)
  (*       role_enabled_model ρ δ). *)
  (* Proof. *)
  (*   intros Hinf. specialize (Hinf n) as [mtr' Hafter]. *)
  (*   rewrite /pred_at Hafter /role_enabled_model. *)
  (*   destruct mtr'; destruct ρ; set_solver. *)
  (* Qed. *)
  
  (* Lemma evenodd_mdl_always_eventually_scheduled ρ (mtr : evenodd_mtrace) : *)
  (*   infinite_trace mtr → fair_model_trace ρ mtr → *)
  (*   ∀ n, ∃ m, pred_at mtr (n+m) (λ _ ℓ, ℓ = Some (Some ρ)). *)
  (* Proof. *)
  (*   intros. *)
    
  (*   intros Hinf Hfair n. *)
  (*   apply (evenodd_mdl_always_live ρ n mtr) in Hinf. *)
  (*   specialize (Hfair n Hinf) as [m [Hfair | Hfair]]. *)
  (*   - rewrite /pred_at in Hfair. destruct (after (n + m) mtr); [|done]. *)
  (*     rewrite /role_enabled_model in Hfair. destruct t; destruct ρ; set_solver. *)
  (*   - by exists m. *)
  (* Qed. *)
  
  (* Lemma evenodd_mdl_noprogress_Even i n (mtr : evenodd_mtrace) : *)
  (*   infinite_trace mtr → mtrace_valid mtr → (trfirst mtr) = i → Nat.even i → *)
  (*   (∀ m, m < n → pred_at mtr m (λ _ l, l ≠ Some (Some ρEven))) → *)
  (*   pred_at mtr n (λ s _, s = i). *)
  (* Proof. *)
  (*   intros Hinf Hvalid Hfirst Heven Hne. *)
  (*   induction n as [|n IHn]. *)
  (*   { rewrite /pred_at. destruct mtr; done. } *)
  (*   simpl in *. *)
  (*   assert (∀ m : nat, m < n → pred_at mtr m (λ _ l, l ≠ Some (Some ρEven))) as Hne'. *)
  (*   { intros. apply Hne. lia. } *)
  (*   specialize (IHn Hne'). rewrite /pred_at in IHn. *)
  (*   destruct (after n mtr) as [mtr'|] eqn:Hafter; rewrite Hafter in IHn; [|done]. *)
  (*   rewrite /pred_at. replace (S n) with (n + 1) by lia. *)
  (*   rewrite after_sum'. rewrite Hafter. specialize (Hinf (n+1)). *)
  (*   rewrite after_sum' in Hinf. rewrite Hafter in Hinf. *)
  (*   destruct mtr'; [by apply is_Some_None in Hinf|]. *)
  (*   eapply mtrace_valid_after in Hvalid; [|done]. *)
  (*   assert (ℓ ≠ Some ρEven) as Hneq. *)
  (*   { assert (n < S n) by lia. specialize (Hne n H). rewrite /pred_at in Hne. *)
  (*     rewrite Hafter in Hne. intros ->. apply Hne. done. } *)
  (*   pinversion Hvalid. simplify_eq. inversion H1; simplify_eq. *)
  (*   - by rewrite Nat.negb_odd in Heven. *)
  (*   - by destruct mtr'. *)
  (* Qed. *)
  
  (* Lemma evenodd_mdl_noprogress_Odd i n (mtr : evenodd_mtrace) : *)
  (*   infinite_trace mtr → mtrace_valid mtr → (trfirst mtr) = i → Nat.odd i → *)
  (*   (∀ m, m < n → pred_at mtr m (λ _ l, l ≠ Some (Some ρOdd))) → *)
  (*   pred_at mtr n (λ s _, s = i). *)
  (* Proof. *)
  (*   intros Hinf Hvalid Hfirst Hodd Hne. *)
  (*   induction n as [|n IHn]. *)
  (*   { rewrite /pred_at. destruct mtr; done. } *)
  (*   simpl in *. *)
  (*   assert (∀ m : nat, m < n → pred_at mtr m (λ _ l, l ≠ Some (Some ρOdd))) as Hne'. *)
  (*   { intros. apply Hne. lia. } *)
  (*   specialize (IHn Hne'). rewrite /pred_at in IHn. *)
  (*   destruct (after n mtr) as [mtr'|] eqn:Hafter; rewrite Hafter in IHn; [|done]. *)
  (*   rewrite /pred_at. replace (S n) with (n + 1) by lia. *)
  (*   rewrite after_sum'. rewrite Hafter. specialize (Hinf (n+1)). *)
  (*   rewrite after_sum' in Hinf. rewrite Hafter in Hinf. *)
  (*   destruct mtr'; [by apply is_Some_None in Hinf|]. *)
  (*   eapply mtrace_valid_after in Hvalid; [|done]. *)
  (*   assert (ℓ ≠ Some ρOdd) as Hneq. *)
  (*   { assert (n < S n) by lia. specialize (Hne n H). rewrite /pred_at in Hne. *)
  (*     rewrite Hafter in Hne. intros ->. apply Hne. done. } *)
  (*   pinversion Hvalid. simplify_eq. inversion H1; simplify_eq. *)
  (*   - by apply odd_not_even in Hodd. *)
  (*   - by destruct mtr'. *)
  (* Qed. *)

  Lemma even_steppable (n: nat) st (EVEN: Nat.even n) (CUR: cur_even _ st n):
    exists st' ρ, amTrans even_AM st (inl (step_sync n), Some ρ) st' /\ cur_even _ st' (n + 1).
  Proof. Admitted.

  Lemma even_sync_inner_pres st ρ st' ρ' (pa: ePriv even_impl):
    let syncs := fun s ρ => exists n s', amTrans even_AM s (inl $ step_sync n, Some ρ) s' in
    syncs st ρ -> amTrans even_AM st (inr pa, ρ') st' -> syncs st' ρ.
  Proof. Admitted. 

  (* TODO: proof in another branch *)
  Lemma pred_at_state_trfirst:
  ∀ {St L : Type} (tr : trace St L) (P : St → Prop),
    pred_at tr 0 (λ (st : St) (_ : option L), P st) ↔ P (trfirst tr).
  Proof. Admitted.

  (* TODO: look for general version regarding trace length *)
  Lemma pred_at_S_singl:
  ∀ {St L : Type} s P m,
    pred_at (⟨ s ⟩: trace St L) (S m) P <-> False.
  Proof. done. Qed. 

  (* TODO: reuse trace_lookup definitions here *)
  Theorem evenodd_mdl_progresses_Even i (mtr : evenodd_mtrace) :
    infinite_trace mtr → mtrace_valid mtr → (∀ ρ, fair_model_trace ρ mtr) →
    st2nat (trfirst mtr) i → Nat.even i →
    ∃ m, pred_at mtr m (λ s _, st2nat s (S i)).
  Proof.
    intros Hinf Hvalid Hfair Hfirst Heven.
    destruct (trfirst mtr) as [st__e st__o] eqn:TR0.
    destruct Hfirst as [CUR__e CUR__o]. simpl in CUR__e, CUR__o.
    edestruct even_steppable as (st__e' & ρ__e & STEP__e & CUR__e'); eauto. 
    specialize (Hfair (inl ρ__e)).

    assert (@role_enabled_model M (inl ρ__e) (trfirst mtr)) as EN__e0. 
    { apply (AM_live_roles_spec (@prod_AM_strong_lr even_impl odd_impl)).
      forward eapply odd_syncable as (st__o' & STEP__O & CUR__o'); eauto.
      eexists _, (_, _). rewrite TR0. simpl. eapply @pt_sync1; eauto.
      Unshelve. 2: exact (inl $ step_sync i). done. }

    red in Hfair. ospecialize (Hfair 0 _).
    { by apply pred_at_state_trfirst. }
    
    destruct Hfair as [m FAIR]. rewrite plus_O_n in FAIR.

    clear dependent st__e st__o st__e'.
    generalize dependent ρ__e. generalize dependent mtr.
    induction m.

    { intros. destruct FAIR as [DIS | STEP].
      { by apply pred_at_state_trfirst in DIS. }
      exists 1. punfold Hvalid. inversion Hvalid; subst. 
      { done. }
      rewrite pred_at_S.
      rewrite /pred_at in STEP. simpl in STEP. inversion STEP. subst.
      apply pred_at_state_trfirst. remember (trfirst tr) as st'. 

  (*   intros. *)
  (*   destruct mtr. *)
  (*   { rewrite !pred_at_S_singl in FAIR. tauto. } *)
  (*   specialize (IHm mtr). specialize_full IHm. *)
  (*   { eapply infinite_cons; eauto. } *)
  (*   { admit. } *)
  (*   {  *)
  (*     (* TODO: show that non-incrementing step keeps _the same_ role enabled. *)
  (*        Is it possible? *) *)
  (*     admit. } *)
  (*   { by rewrite !pred_at_S in FAIR. } *)
  (*   destruct IHm as [? ?]. eexists. apply pred_at_S. eauto.   *)
  (* Qed. *)
  Admitted. 
  
  (* Theorem evenodd_mdl_progresses_Odd i (mtr : evenodd_mtrace) : *)
  (*   infinite_trace mtr → mtrace_valid mtr → (∀ ρ, fair_model_trace ρ mtr) → *)
  (*   (trfirst mtr) = i → Nat.odd i → *)
  (*   ∃ m, pred_at mtr m (λ s _, s = S i). *)
  (* Proof. *)
  (*   intros Hinf Hvalid Hfair Hfirst Hodd. *)
  (*   specialize (Hfair ρOdd). *)
  (*   pose proof (evenodd_mdl_always_eventually_scheduled ρOdd mtr Hinf Hfair 0) as Hsched. *)
  (*   simpl in *. apply trace_eventually_until in Hsched as [m [Hsched Hschedne]]. *)
  (*   rewrite /pred_at in Hsched. *)
  (*   destruct (after m mtr) as [mtr'|] eqn:Hafter; last first. *)
  (*   { rewrite Hafter in Hsched. done. } *)
  (*   rewrite Hafter in Hsched. *)
  (*   destruct mtr'; [done|]. *)
  (*   simplify_eq. *)
  (*   assert (s = trfirst mtr) as ->. *)
  (*   { eapply evenodd_mdl_noprogress_Odd in Hschedne; [|done..]. *)
  (*     rewrite /pred_at in Hschedne. rewrite Hafter in Hschedne. done. } *)
  (*   eapply mtrace_valid_after in Hvalid; [|done]. *)
  (*   pinversion Hvalid; simplify_eq. inversion H1; simplify_eq. *)
  (*   - exists (m + 1). *)
  (*     rewrite /pred_at. rewrite !after_sum'. rewrite Hafter. simpl. *)
  (*     destruct mtr'; simpl in *; simplify_eq; done. *)
  (*   - by apply odd_not_even in Hodd. *)
  (* Qed. *)
  
  Theorem evenodd_mdl_progresses (mtr : evenodd_mtrace) :
    infinite_trace mtr → mtrace_valid mtr → (∀ ρ, fair_model_trace ρ mtr) →
    st2nat (trfirst mtr) 0 →
    evenodd_mdl_progress mtr.
  Proof.
    intros Hinf Hvalid Hfair Hfirst i.
    induction i as [|i IHi].
    { exists 0. rewrite /pred_at. rewrite /trfirst in Hfirst. simpl.
      destruct mtr; done. }
    destruct IHi as [n Hpred].
    rewrite /pred_at in Hpred.
    destruct (after n mtr) as [mtr'|] eqn:Hafter; [|done].
    eapply infinite_trace_after'' in Hinf; [|done].
    eapply mtrace_valid_after in Hvalid; [|done].
    destruct (Nat.even i) eqn:Heqn.
    - assert (∀ ρ : fmrole M, fair_model_trace ρ mtr') as Hfair'.
      { intros. by eapply fair_model_trace_after. }
      assert (st2nat (trfirst mtr') i) as Hfirst'.
      { rewrite /trfirst. destruct mtr'; done. }
      pose proof (evenodd_mdl_progresses_Even i mtr' Hinf Hvalid Hfair' Hfirst')
        as [m Hpred']; [by eauto|].
      exists (n + m).
      rewrite pred_at_sum. rewrite Hafter. done.
  (*   - assert (∀ ρ : fmrole M, fair_model_trace ρ mtr') as Hfair'. *)
  (*     { intros. by eapply fair_model_trace_after. } *)
  (*     assert (trfirst mtr' = i) as Hfirst'. *)
  (*     { rewrite /trfirst. destruct mtr'; done. } *)
  (*     pose proof (evenodd_mdl_progresses_Odd i mtr' Hinf Hvalid Hfair' Hfirst') *)
  (*       as [m Hpred']; [by rewrite -Nat.negb_even Heqn|]. *)
  (*     exists (n + m). *)
  (*     rewrite pred_at_sum. rewrite Hafter. done. *)
  (* Qed. *)
  Admitted. 
  
  Theorem evenodd_mdl_is_mono (mtr : evenodd_mtrace) :
    infinite_trace mtr → mtrace_valid mtr → (∀ ρ, fair_model_trace ρ mtr) →
    (* (trfirst mtr) = 0 → *)
    st2nat (trfirst mtr) 0 ->
    evenodd_mdl_mono mtr.
  Proof.
    (* intros Hinf Hvalid Hfair Hfirst n. *)
    (* pose proof (Hinf n) as [mtr' Hafter]. *)
    (* destruct mtr' as [|s l mtr']. *)
    (* { pose proof (Hinf (S n)) as [mtr'' Hafter']. *)
    (*   replace (S n) with (n + 1) in Hafter' by lia. *)
    (*   rewrite after_sum' in Hafter'. rewrite Hafter in Hafter'. done. } *)
    (* exists s. *)
    (* rewrite /pred_at. rewrite Hafter. *)
    (* split; [done|]. *)
    (* replace (S n) with (n + 1) by lia. *)
    (* rewrite after_sum'. rewrite Hafter. simpl. *)
    (* eapply mtrace_valid_after in Hvalid; [|done]. *)
    (* punfold Hvalid. inversion Hvalid as [|??? Htrans]. simplify_eq. *)
    (* inversion Htrans; simplify_eq. *)
    (* - destruct mtr'. *)
    (*   + exists (S s); split; [done|lia]. *)
    (*   + exists (S s); split; [done|lia]. *)
    (* - destruct mtr'. *)
    (*   + exists s; done. *)
    (*   + exists s; done. *)
    (* - destruct mtr'. *)
    (*   + exists (S s); split; [done|lia]. *)
    (*   + exists (S s); split; [done|lia]. *)
    (* - destruct mtr'. *)
    (*   + exists s; done. *)
    (*   + exists s; done. *)
  (* Qed. *)
  Admitted. 
  
End ModelMono.


Section MonoLMPreserved.
  (** Proof that fair progress is preserved through auxiliary trace *)

  Context {even_impl: EvenModel} {odd_impl: OddModel}.
  Let M := @the_fair_model even_impl odd_impl.
  Let LM := @the_model even_impl odd_impl.
  (* Let st2nat := st2nat even_impl odd_impl.  *)

  Definition evenodd_aux_progress (auxtr : auxtrace LM) :=
    ∀ (i: nat), ∃ n, pred_at auxtr n (λ s l, (λ s' _, st2nat s' i)
                                        (ls_under s) (l ≫= Ul)).
  
  Lemma evenodd_mtr_aux_progress_preserved
    (mtr : mtrace M)
    (auxtr : auxtrace LM) :
    upto_stutter (ls_under ∘ ls_data) Ul auxtr mtr →
    evenodd_mdl_progress mtr → evenodd_aux_progress auxtr.
  Proof.
    intros Hstutter Hmtr n. specialize (Hmtr n).
    by apply (trace_eventually_stutter_preserves
                (ls_under ∘ ls_data) Ul auxtr mtr (λ s' _, st2nat s' n)).
  Qed.
  
  Definition evenodd_aux_mono (auxtr : auxtrace LM) :=
    ∀ n, ∃ (i: nat), pred_at auxtr n (λ s l, (λ s' _, st2nat s' i) (ls_under s) (l ≫= Ul)) ∧
                pred_at auxtr (S n) (λ s l, (λ s' _, ∃ j, st2nat s' j ∧ i ≤ j) (ls_under $ ls_data s) (l ≫= Ul)).
  
  Lemma evenodd_mtr_aux_mono_preserved (mtr : mtrace M)
    (auxtr : auxtrace LM) :
    upto_stutter (ls_under ∘ ls_data) Ul auxtr mtr →
    evenodd_mdl_mono mtr → evenodd_aux_mono auxtr.
  Proof.
    Set Printing Coercions.
    intros Hstutter Hmtr n.
    revert auxtr mtr Hstutter Hmtr.
    induction n as [|n IHn]; intros auxtr mtr Hstutter Hmtr.
    { 
      punfold Hstutter; [|apply upto_stutter_mono].
      induction Hstutter as
        [|auxtr mtr s ℓ Hℓ Hauxtr_first Hmtr_first CIHstutter IHstutter|
          auxtr mtr s ℓ δ ρ Hs Hℓ CIHstutter].
      - by destruct (Hmtr 0) as [? [? Hmtr']].
      - simplify_eq.
        destruct (IHstutter Hmtr) as [i [Hpred ?]].
        rewrite /pred_at in Hpred. simpl in *.
        exists i. rewrite /pred_at. simpl.
        destruct auxtr as [|s' ℓ' auxtr']; [done|].
        rewrite /trfirst in Hauxtr_first. split.
        { congruence. }
        exists i. simplify_eq. split; [|lia]. congruence. 
      - simplify_eq.
        destruct (Hmtr 0) as [i [Hpred1 Hpred2]].
        rewrite /pred_at in Hpred1. simpl in *.
        exists i.
        rewrite /pred_at. split; [done|].
        rewrite /pred_at in Hpred2. simpl in *.
        destruct CIHstutter as [CIHstutter|?]; [|done].
        punfold CIHstutter; [|apply upto_stutter_mono].
        induction CIHstutter as
          [|mtr auxtr ??? Hauxtr_first Hmtr_first ? IHstutter|];
          [done| |by simplify_eq].
        specialize (IHstutter Hmtr Hpred2).        
        destruct mtr.
        * destruct IHstutter as [j [Hj1 Hj2]]. exists j.
          split; try by simplify_eq.
          simpl in Hauxtr_first. congruence. 
        * destruct IHstutter as [j [Hj1 Hj2]]. exists j.
          split; try by simplify_eq.
          simpl in Hauxtr_first. congruence. }
    punfold Hstutter; [|apply upto_stutter_mono].
    induction Hstutter as
      [|auxtr mtr s ℓ Hℓ Hauxtr_first Hmtr_first CIHstutter IHstutter|
        auxtr mtr s ℓ δ ρ Hs Hℓ CIHstutter].
    + by destruct (Hmtr 0) as [? [? Hmtr']].
    + simplify_eq. setoid_rewrite pred_at_S. eapply IHn; [by apply paco2_fold|done].
    + simplify_eq. destruct CIHstutter as [CIHstutter|?]; [|done].
      assert (evenodd_mdl_mono mtr) as Hmtr'.
      { intros m. specialize (Hmtr (S m)). by setoid_rewrite pred_at_S in Hmtr. }
      destruct (IHn auxtr mtr CIHstutter Hmtr') as [i [Hpred1 Hpred2]].
      exists i. by rewrite !pred_at_S.
Qed.

End MonoLMPreserved.

Section ExAuxPropsPreserved.
  (** Proof that progress is preserved between auxilary and execution trace,
      for a specific ξ *)
  
  Context {even_impl: EvenModel} {odd_impl: OddModel}.
  Let M := @the_fair_model even_impl odd_impl.
  Let LM := @the_model even_impl odd_impl.

  Definition evenodd_ex_progress (l:loc) (extr : heap_lang_extrace) :=
    ∀ (i: nat), ∃ n, pred_at extr n (λ s _, heap s.2 !! l = Some #i).
  
  Definition evenodd_ex_mono (l:loc) (extr : heap_lang_extrace) :=
    ∀ n, ∃ (i: nat),
      pred_at extr n (λ s _, heap s.2 !! l = Some #i) ∧
      pred_at extr (S n) (λ s _, ∃ (j:nat), heap s.2 !! l = Some #j ∧ i ≤ j).  
  
  Definition ξ_evenodd_model_match (l : loc) (c : cfg heap_lang) (δ: M) :=
    ∃ (N:nat), heap c.2 !! l = Some #N ∧ st2nat δ N.
  
  Definition ξ_evenodd_no_val_steps (c : cfg heap_lang) :=
    (Forall (λ e, is_Some $ to_val e) c.1 → False) ∧
      Forall (λ e, not_stuck e c.2) c.1.
  
  Definition ξ_evenodd (l : loc) (c : cfg heap_lang) (δ : M) :=
    ξ_evenodd_no_val_steps c ∧ ξ_evenodd_model_match l c δ.

  Set Printing Coercions.
  Definition ξ_evenodd_trace (l : loc) (extr : execution_trace heap_lang)
    (mtr : finite_trace M (option (fmrole M))) :=
    ξ_evenodd l (trace_last extr) (trace_last mtr).
  
  Lemma evenodd_aux_ex_progress_preserved l (extr: heap_lang_extrace) (auxtr : auxtrace LM):
    traces_match labels_match (λ c (δ: LM), ξ_evenodd l c δ) locale_step
      (lm_ls_trans LM) extr auxtr →
    evenodd_aux_progress auxtr → evenodd_ex_progress l extr.
  Proof.
    intros Hξ Hauxtr n. specialize (Hauxtr n).
    rewrite /pred_at in Hauxtr. destruct Hauxtr as [m Hauxtr].
    destruct (after m auxtr) as [auxtr'|] eqn:Heqn.
    2: { by rewrite Heqn in Hauxtr. }
    eapply traces_match_after in Hξ as [extr' [Hafter' Hextr']]; [|done].
    exists m. rewrite /pred_at. rewrite Hafter'.
    inversion Hextr' as [?? Hξ|??????? Hξ]; simplify_eq.
    - destruct Hξ as (?&k&?&?).
      rewrite Heqn in Hauxtr.
      assert (k = n) as -> by (eapply st2nat_inj; eauto). 
      by simplify_eq.
    - destruct Hξ as (?&k&?&?).
      rewrite Heqn in Hauxtr.
      assert (k = n) as -> by (eapply st2nat_inj; eauto). 
      by simplify_eq.
  Qed.
  
  Lemma evenodd_aux_ex_mono_preserved l (extr : heap_lang_extrace) (auxtr : auxtrace LM) :
    traces_match labels_match (λ c (δ: LM), ξ_evenodd l c δ) locale_step
      (lm_ls_trans LM) extr auxtr →
    evenodd_aux_mono auxtr → evenodd_ex_mono l extr.
  Proof.
    intros Hξ Hauxtr n. specialize (Hauxtr n).
    destruct Hauxtr as [i Hauxtr].
    exists i.
    split.
    - destruct Hauxtr as [Hauxtr _].
      rewrite /pred_at in Hauxtr.
      destruct (after n auxtr) as [auxtr'|] eqn:Heqn.
      2: { by rewrite Heqn in Hauxtr. }
      eapply traces_match_after in Hξ as [extr' [Hafter' Hextr']]; [|done].
      rewrite /pred_at. rewrite Hafter'.
      inversion Hextr' as [?? Hξ|??????? Hξ]; simplify_eq.
      + destruct Hξ as (?&k&?&?).
        rewrite Heqn in Hauxtr.
        assert (k = i) as -> by (eapply st2nat_inj; eauto).
        by simplify_eq.
      + destruct Hξ as (?&k&?&?).
        rewrite Heqn in Hauxtr.
        assert (k = i) as -> by (eapply st2nat_inj; eauto).
        by simplify_eq.
    - destruct Hauxtr as [_ Hauxtr].
      rewrite /pred_at in Hauxtr.
      destruct (after (S n) auxtr) as [auxtr'|] eqn:Heqn.
      2: { by rewrite Heqn in Hauxtr. } 
      eapply traces_match_after in Hξ as [extr' [Hafter' Hextr']]; [|done].
      rewrite /pred_at. rewrite Hafter'.
      rewrite Heqn in Hauxtr. 
      inversion Hextr' as [?? Hξ|??????? Hξ]; simplify_eq.
      + destruct Hauxtr as [j [ST2 Hle]].
        destruct Hξ as (?&k&?&?). 
        exists j. split; auto.
        assert (k = j) as -> by (eapply st2nat_inj; eauto).
        by simplify_eq.
      + destruct Hauxtr as [j [ST2 Hle]].
        destruct Hξ as (?&k&?&?).
        exists j. split; auto.
        assert (k = j) as -> by (eapply st2nat_inj; eauto).
        by simplify_eq.
  Qed.

End ExAuxPropsPreserved.

(** Proof that program refines model up to ξ_evenodd *)

Section Adequacy.
  Context (even_impl: EvenModel) (odd_impl: OddModel).
  Let M := @the_fair_model even_impl odd_impl.
  Let LM := @the_model even_impl odd_impl.

  Let init_roles: gset (fmrole M) := {[ inl (ρ__e even_impl); inr (ρ__o odd_impl) ]}.

  Lemma init_roles_live0 st (CUR__0: st2nat st 0):
    AM_live_roles prod_AM_strong_lr st = init_roles.
  Proof. Admitted. 

  (* TODO: move *)
  Lemma gset_to_gmap_singleton `{Countable A} {B : Type} (v: B) (a: A):
    gset_to_gmap v {[ a ]} = {[ a := v ]}.
  Proof using.
    rewrite /gset_to_gmap. simpl. by rewrite map_fmap_singleton.
  Qed. 

  Lemma start_spec_use Σ
    (l : loc)
    (Hinv : heapGS Σ LM)
    (eoΣ: evenoddG Σ)
    (th_preG: threadPreG Σ)
    :
    {{{ inv (nroot.@"even_odd") (evenodd_inv_inner l) ∗
        0 ↦M gset_to_gmap 61 init_roles ∗
        own even_name (◯E 0) ∗
        own odd_name (◯E 1) ∗
        frag_free_roles_are ∅ }}}
      (@start even_impl odd_impl) #l @0
      {{{ x, RET x; 0 ↦M ∅ }}}.
  Proof.  
    simpl. rewrite /init_roles.
    rewrite !gset_to_gmap_union_singleton. rewrite gset_to_gmap_singleton. 
    iIntros (Φ) "(#Hinv & Hf & Heven_at & Hodd_at) HΦ".
    iApply (start_spec with "[$Hf Heven_at Hodd_at $Hinv]"); [lia| ..].
    2: { by iFrame. }
    { lia. }
    iIntros "!>?". by iApply "HΦ".
  Qed.
  
  Lemma dom_locales
    (c: cfg heap_lang)
    (fm : gmap (locale heap_lang) (gmap (fmrole M) nat))
    (Htp : fuel_map_preserve_threadpool c.1 fm)
    (HMζ : ∀ i : nat, i < length c.1 → fm !! i = Some ∅):
    dom fm = list_to_set (locales_of_list c.1).
  Proof.
    apply set_eq.
    intros x. rewrite elem_of_dom.
    rewrite elem_of_list_to_set.
    split.
    - intros HSome.
      destruct (decide (x ∈ locales_of_list c.1)) as [|Hnin]; [done|].
      apply Htp in Hnin.
      destruct HSome as [??]. set_solver. 
    - intros Hin. exists ∅. apply HMζ.
      rewrite locales_of_list_indexes in Hin.
      rewrite /indexes in Hin.
      apply elem_of_lookup_imap_1 in Hin as (i&?&->&HSome).
      by apply lookup_lt_is_Some_1.
  Qed.

  Lemma AM_lr_M_nonempty (st: fmstate M):
    AM_live_roles prod_AM_strong_lr st ≠ ∅.
  Proof. Admitted. 

  Lemma not_all_val `{!heapGS Σ LM} 
    (c : cfg heap_lang) δ e
    (Hsmaller : tids_smaller c.1 δ)
    (fm : gmap (locale heap_lang) (gmap (fmrole M) nat))
    (Hfmle : fuel_map_le fm (ls_map δ))
    (Hfmdead : fuel_map_preserve_dead fm (live_roles M δ))
    (Htp : fuel_map_preserve_threadpool c.1 fm)
    (Hall : Forall (λ e : expr, is_Some (to_val e)) c.1):
    auth_fuel_mapping_is fm -∗
      posts_of c.1  ([λ _ : language.val heap_lang, 0 ↦M ∅] ++
                       ((λ '(tnew, e), fork_post (language.locale_of tnew e)) <$>
                          prefixes_from
                          [e]
                          (drop 1 c.1)))
      -∗
      False.
  Proof.
    iIntros "Hfm Hposts".
    simpl. 
    rewrite !big_sepL_omap !big_sepL_zip_with=> /=.
    iAssert ([∗ list] k↦x ∈ c.1, k ↦M ∅)%I with "[Hposts]" as "Hposts".
    { destruct c as [es σ]=> /=.
      iApply (big_sepL_impl with "Hposts").
      iIntros "!>" (k x HSome) "Hk".
      assert (is_Some (to_val x)) as [v Hv].
      { by eapply (Forall_lookup_1 (λ e : expr, is_Some (to_val e))). }
      rewrite Hv. destruct k; [done|]. destruct es; [done|].
      simpl in *. rewrite drop_0. rewrite list_lookup_fmap.
      erewrite prefixes_from_lookup; [|done].
      simpl. rewrite /locale_of. rewrite take_length.
      assert (k < length es).
      { apply lookup_lt_is_Some_1. by eauto. }
      by replace (k `min` length es) with k by lia. }
    iAssert (⌜∀ i, i < length c.1 → fm !! i = Some ∅⌝)%I as "%HMζ".
    { iIntros (i Hlen).
      assert (is_Some $ c.1 !! i) as [e' HSome].
      { by apply lookup_lt_is_Some_2. }
      iDestruct (big_sepL_delete with "Hposts") as "[Hpost _]"; [done|].
      by iDestruct (has_fuels_agree with "Hfm Hpost") as "?". }
    assert (dom fm = list_to_set $ locales_of_list c.1).
    { subst. apply dom_locales; auto. }
    
    assert (live_roles _ δ = ∅) as Hlive.
    { clear -Hfmdead HMζ Hfmle Hsmaller.
      apply set_eq. intros i. split; [|done].
      intros (ζ&fs&HSome&Hfs)%Hfmdead.
      assert (fm !! ζ = Some ∅).
      { apply HMζ.
        assert (ζ ∈ dom (ls_map δ)) as Hin.
        { destruct Hfmle as [Hfmle1 Hfmle2].
          rewrite /fuel_map_le_inner map_included_spec in Hfmle1.
          apply Hfmle1 in HSome as (?&?&?).
          by apply elem_of_dom. }
        apply Hsmaller in Hin as [? Hin].
        apply lookup_lt_is_Some_1.
        by apply from_locale_lookup in Hin. }
      set_solver. }

    simpl in Hlive. by apply AM_lr_M_nonempty in Hlive.  
  Qed. 
    
  Existing Instance even_AME. 
  Existing Instance odd_AME.

  (* TODO: move *)
  Lemma trace_last_underlying (auxtr: auxiliary_trace LM):
    trace_last (map_underlying_trace auxtr) = ls_under $ ls_data $ trace_last auxtr.
  Proof. by destruct auxtr. Qed. 

  Lemma eo_rah l `(!heapGS Σ LM) (eoΣ: evenoddG Σ) `(threadPreG Σ)
    st e h
    (CUR__0: st2nat st 0)
    :
    inv (nroot.@"even_odd") (evenodd_inv_inner l) -∗
      rel_always_holds NotStuck [λ _ : language.val heap_lang, 0 ↦M ∅]
      (λ (extr : execution_trace heap_lang) (atr : auxiliary_trace LM),
        ξ_evenodd_trace l extr (map_underlying_trace atr))
      (* ([e], {| heap := {[l := #0]}; used_proph_id := ∅ |})  *)
      ([e], h)
      (initial_ls st 0).
  Proof.
    iIntros "#Hinv".
    iIntros (extr auxtr c) "_ _ _ %Hends _ %Hnstuck %Hequiv [_ [Hσ Hδ]] Hposts".
    
    iInv "Hinv" as (st__e st__o N) "(>Hmod & >%CUR__E & >%CUR__O & >Hn & Hauths)" "Hclose".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose'".
    iDestruct (gen_heap_valid with "Hσ Hn") as %Hn.
    iDestruct (model_state_interp_tids_smaller with "Hδ") as %Hsmaller.
    iDestruct "Hδ" as (fm Hfmle Hfmdead Htp) "[Hδ Hfm]".
    iDestruct (model_agree with "Hδ Hmod") as %Hn'.
    iSplitL; last first.
    { iPureIntro. exists N. split; [done|].
      rewrite trace_last_underlying Hn'. done. }
    rewrite /trace_ends_in in Hends.
    rewrite Hends.
    iSplit.
    - iIntros "%Hall". subst c. iApply (not_all_val with "[$]"); eauto. 
    - iPureIntro.
      apply Forall_forall.
      intros e' He. by apply Hnstuck.
  Qed.

  (* TODO: move *)
  Definition threadΣ: gFunctors :=
    #[GFunctor (excl_authR natO)].
  Global Instance subG_threadΣ {Σ}: subG threadΣ Σ -> threadPreG Σ.
  Proof. solve_inG. Qed. 
  
  Definition evenoddΣ : gFunctors :=
    #[ heapΣ M; GFunctor (excl_authR boolO) ].

  Global Instance subG_evenoddΣ {Σ} : subG evenoddΣ Σ → evenoddPreG Σ.
  Proof. Qed. 
  (* Proof. solve_inG. Qed. *)

  Definition wholeΣ := #[evenoddΣ; threadΣ]. 

  #[local] Instance proof_irrel_trans s1 x:
    ProofIrrel ((let '(s2, ℓ) := x in fmtrans M s1 ℓ s2): Prop).
  Proof. apply make_proof_irrel. Qed.

  Lemma prod_model_finitary s1:
    Finite
      {'(s2, ℓ) | fmtrans M s1 ℓ s2}. 
  Proof.
    pose proof (@eo_vs_mod2.prod_AM_fin_branch' even_impl odd_impl) as [ns NEXTS].
    apply (in_list_finite ((fun '(x, y, z) => (x, z)) <$> ns s1)).
    intros [st oρ] STEP. apply am_fmtrans_action in STEP as [? STEP].
    eapply elem_of_list_fmap. eexists. split; eauto. done.
  Qed. 

  (* TODO: find more general versions *)
  Instance the_model_mstate_countable : EqDecision (mstate LM).
  Proof. intros x y. apply make_decision. Qed.
  Instance the_model_mlabel_countable : EqDecision (mlabel LM).
  Proof. solve_decision. Qed.

  Lemma evenodd_sim l
    st (CUR__0: st2nat st 0):
    continued_simulation
      (sim_rel_with_user LM (ξ_evenodd_trace l))
      (trace_singleton ([(@start even_impl odd_impl) #l], {| heap := {[l:=#0]};  used_proph_id := ∅ |}))
      (trace_singleton (initial_ls (LM := LM) st 0)).
  Proof.
    assert (evenoddPreG wholeΣ) as HPreG'.
    { apply _. }
    assert (heapGpreS evenoddΣ LM) as HPreG.
    { apply _. }
    assert (threadPreG wholeΣ) as thPreG.
    { apply _. }
    eapply (strong_simulation_adequacy
              wholeΣ _ NotStuck _ _ _ ∅).
    2: { simpl. apply AM_lr_M_nonempty. } 
    { eapply rel_finitary_sim_rel_with_user_sim_rel.
      eapply valid_state_evolution_finitary_fairness_simple.
      intros ?. simpl. apply prod_model_finitary. }
    iIntros (?) "!> Hσ Hs Hr Hf".
    iMod (own_alloc (●E 0  ⋅ ◯E 0))%nat as (γ_even_at) "[Heven_at_auth Heven_at]".
    { apply auth_both_valid_2; eauto. by compute. }
    iMod (own_alloc (●E 1  ⋅ ◯E 1))%nat as (γ_odd_at) "[Hodd_at_auth Hodd_at]".
    { apply auth_both_valid_2; eauto. by compute. }
    pose (the_names := {|
                        even_name := γ_even_at;
                        odd_name := γ_odd_at;
                      |}).
    iMod (inv_alloc (nroot .@ "even_odd") _ (evenodd_inv_inner l) with "[Hσ Hs Heven_at_auth Hodd_at_auth]") as "#Hinv".
    { iNext. unfold evenodd_inv_inner.
      destruct st as [st__e st__o]. 
      do 2 iExists _. iExists 0.
      simpl. rewrite big_sepM_singleton. iFrame.
      iPureIntro. apply CUR__0. }
    iModIntro.
    iSplitL.
    2: by iApply eo_rah. 
    iApply (start_spec_use with "[-]").
    Unshelve.
    3, 4: by apply _.
    2: { iNext. by iIntros "**". }
    rewrite subseteq_empty_difference_L; [| done]. 
    iFrame "#∗".
    simpl. rewrite init_roles_live0; auto.  
  Qed.
  
  CoInductive extrace_maximal {Λ} : extrace Λ → Prop :=
  | extrace_maximal_singleton c :
    (∀ oζ c', ¬ locale_step c oζ c') → extrace_maximal ⟨c⟩
  | extrace_maximal_cons c oζ tr :
    locale_step c oζ (trfirst tr) ->
    extrace_maximal tr →
    extrace_maximal (c -[oζ]-> tr).
  
  Lemma extrace_maximal_valid {Λ} (extr : extrace Λ) :
    extrace_maximal extr → extrace_valid extr.
  Proof.
    revert extr. cofix IH. intros extr Hmaximal. inversion Hmaximal.
    - constructor 1.
    - constructor 2; [done|by apply IH].
  Qed.
  
  Lemma extrace_maximal_after {Λ} n (extr extr' : extrace Λ) :
    extrace_maximal extr → after n extr = Some extr' → extrace_maximal extr'.
  Proof.
    revert extr extr'. induction n; intros extr extr' Hafter Hvalid.
    { destruct extr'; simpl in *; by simplify_eq. }
    simpl in *. destruct extr; [done|]. eapply IHn; [|done]. by inversion Hafter.
  Qed.
  
  Lemma infinite_trace_no_val_steps extr auxtr :
    extrace_maximal extr →
    traces_match
      (labels_match (LM:=LM))
      (λ c _ , ξ_evenodd_no_val_steps c) locale_step
      (lm_ls_trans LM) extr auxtr →
    infinite_trace extr.
  Proof.
    intros Hmaximal Hmatch.
    intros n. induction n as [|n IHn]; [done|].
    destruct IHn as [extr' Hafter].
    apply traces_match_flip in Hmatch.
    eapply traces_match_after in Hmatch; [|done].
    destruct Hmatch as [auxtr' [Hafter' Hmatch]].
    replace (S n) with (n + 1) by lia.
    rewrite after_sum'.
    rewrite Hafter.
    apply traces_match_first in Hmatch.
    destruct Hmatch as [Hξ1 Hξ2].
    eapply extrace_maximal_after in Hmaximal; [|done].
    inversion Hmaximal as [? Hnstep|]; simplify_eq; [|done].
    assert (∃ oζ c', locale_step c oζ c') as Hstep; last first.
    { exfalso. destruct Hstep as (?&?&Hstep). by eapply Hnstep. }
    apply not_Forall_Exists in Hξ1; [|apply _].
    apply Exists_exists in Hξ1 as [e [Hξ11 Hξ12]].
    rewrite Forall_forall in Hξ2.
    specialize (Hξ2 e Hξ11) as [|Hred]; [done|].
    destruct Hred as (e' & σ' & es' & Hred).
    apply elem_of_list_split in Hξ11 as (es1&es2&Hes).
    destruct c; simpl in *.
    eexists (Some _), _.
    econstructor; eauto. simpl in *.
    by f_equiv.
  Qed.
  
  Lemma extr_props (l: loc) e
    (extr : heap_lang_extrace)
    (Hmaximal : extrace_maximal extr)
    (Hfair : ∀ tid : locale heap_lang, fair_ex tid extr)
    (Hfirst : trfirst extr = ([e], {| heap := {[l := #0]}; used_proph_id := ∅ |}))
    (auxtr : auxtrace LM)
    (Hmatch_strong : traces_match labels_match
                       (λ (x0 : cfg heap_lang) (x1 : lm_ls LM),
                         live_tids x0 x1 ∧ ξ_evenodd l x0 x1) locale_step
                       (λ (δ : lm_ls LM) (ℓ : lm_lbl LM) 
                          (b : lm_ls LM), lm_ls_trans LM δ ℓ b) extr
                       auxtr):
    evenodd_ex_progress l extr ∧ evenodd_ex_mono l extr.
  Proof. 
    assert (exaux_traces_match extr auxtr) as Hmatch.
    { eapply traces_match_impl; [done| |done]. by intros ??[??]. }
    assert (auxtrace_valid auxtr) as Hstutter.
    { by eapply exaux_preserves_validity. }
    apply can_destutter_auxtr in Hstutter.
    destruct Hstutter as [mtr Hupto].
    assert (infinite_trace extr) as Hinf.
    { eapply infinite_trace_no_val_steps; [done|].
      eapply traces_match_impl; [done| |apply Hmatch_strong].
      by intros s1 s2 [_ [? _]]. }
    pose proof (fairness_preserved extr auxtr Hinf Hmatch Hfair) as Hfairaux.
    have Hvalaux := exaux_preserves_validity extr auxtr Hmatch.
    have Hfairm := upto_stutter_fairness auxtr mtr Hupto Hfairaux.
    have Hmtrvalid := upto_preserves_validity auxtr mtr Hupto Hvalaux.
    pose proof (fairness_preserved extr auxtr Hinf Hmatch Hfair) as Hfair'.
    pose proof (upto_stutter_fairness auxtr mtr Hupto Hfair') as Hfair''.
    assert (infinite_trace mtr) as Hinf''.
    { eapply upto_stutter_infinite_trace; [done|].
      by eapply traces_match_infinite_trace. }
    assert (mtrace_valid mtr) as Hvalid''.
    { eapply upto_preserves_validity; [done|].
      by eapply exaux_preserves_validity. }
    (* assert (trfirst mtr = 0) as Hfirst''. *)
    assert (st2nat (trfirst mtr) 0) as Hfirst''.
    { apply traces_match_first in Hmatch_strong.
      destruct Hmatch_strong as [_ [_ [n [Hσ Hmdl]]]].
      rewrite Hfirst in Hσ. simpl in *. rewrite lookup_insert in Hσ.
      simplify_eq. punfold Hupto; [|by apply upto_stutter_mono'].
      (* assert (0 = ls_under (trfirst auxtr)) as Hσ' by lia. *)
      destruct n; [| lia]. clear Hσ.
      inversion Hupto; simplify_eq; simpl in *; congruence. }
    split.
    - pose proof (evenodd_mdl_progresses mtr Hinf'' Hvalid'' Hfair'' Hfirst'')
        as Hprogress.
      eapply (evenodd_aux_ex_progress_preserved l _ auxtr).
      { eapply traces_match_impl; [done| |apply Hmatch_strong]. by intros ??[??]. }
      by eapply evenodd_mtr_aux_progress_preserved.
    - pose proof (evenodd_mdl_is_mono mtr Hinf'' Hvalid'' Hfair'' Hfirst'')
        as Hmono.
      eapply (evenodd_aux_ex_mono_preserved l _ auxtr).
      { eapply traces_match_impl; [done| |apply Hmatch_strong]. by intros ??[??]. }
      by eapply evenodd_mtr_aux_mono_preserved.
  Qed. 
  
  
  (** Proof that the execution trace satisfies the liveness properties *)
  Theorem evenodd_ex_liveness (l:loc) (extr : heap_lang_extrace) (st: fmstate M):
    extrace_maximal extr →
    (∀ tid, fair_ex tid extr) →
    trfirst extr = ([(@start even_impl odd_impl) #l], {| heap := {[l:=#0]}; used_proph_id := ∅ |}) →
    st2nat st 0 ->
    evenodd_ex_progress l extr ∧ evenodd_ex_mono l extr.
  Proof.
    intros Hmaximal Hfair Hfirst CUR__0.
    pose proof Hmaximal as Hvalid%extrace_maximal_valid.
    pose proof (evenodd_sim l _ CUR__0) as Hsim.
    
    assert (∃ iatr,
               valid_inf_system_trace
                 (continued_simulation (sim_rel_with_user LM (ξ_evenodd_trace l)))
                 (trace_singleton (trfirst extr))
                 (trace_singleton (initial_ls (LM:=LM) st 0))
                 (from_trace extr)
                 iatr) as [iatr Hiatr].
    { eexists _. eapply produced_inf_aux_trace_valid_inf. econstructor.
      Unshelve.
      - rewrite Hfirst. apply Hsim.
      - eapply from_trace_preserves_validity; eauto; first econstructor. }
    
    assert (∃ (auxtr : auxtrace LM),
               traces_match labels_match
                 (live_tids /2\ (ξ_evenodd l))
                 locale_step
                 LM.(lm_ls_trans) extr auxtr) as [auxtr Hmatch_strong].
    { exists (to_trace (initial_ls (LM := LM) st 0 ) iatr).
      eapply (valid_inf_system_trace_implies_traces_match_strong
                (continued_simulation (sim_rel_with_user LM (ξ_evenodd_trace l)))); eauto.
      - intros ? ? Hξ%continued_simulation_rel. by destruct Hξ as [[_ Hξ] _].
      - intros ? ? Hξ%continued_simulation_rel. by destruct Hξ as [[Hξ _] _].
      - intros extr' auxtr' Hξ%continued_simulation_rel.
        destruct Hξ as [_ [Hξ1 Hξ2]].
        split; [done|].
        destruct Hξ2 as [n [Hξ21 Hξ22]].
        exists n. split; [done|]. by destruct auxtr'.
      - by apply from_trace_spec.
      - by apply to_trace_spec. }
    
    eapply extr_props; eauto. 
  Qed.

  Lemma ensure_init_st_exists: False.
  Proof. Admitted. 
  
End Adequacy.
