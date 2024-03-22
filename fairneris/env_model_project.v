From stdpp Require Import option countable.
From fairneris Require Export inftraces trace_utils fairness env_model ltl_lite.
From trillium.prelude Require Import classical classical_instances.

Section measure.
  Context {Λ: language}.
  Context `{GoodLang Λ}.
  Context (M: UserModel Λ).
  Context (N: EnvModel Λ).

  Notation JM := (joint_model M N).

  Notation jmtrace := (trace JM (fmlabel JM)).

  Definition trans_valid (mtr : jmtrace) :=
     match mtr with
     | ⟨s⟩ => True
     | (s -[l]-> tr) => fmtrans _ s l (trfirst tr)
     end.

  Definition jmtrace_valid (mtr : jmtrace) :=
    trace_always trans_valid mtr.

  Definition fair_scheduling_mtr (ρ : M.(usr_role)) : jmtrace → Prop :=
    trace_always_eventually_implies_now
      (λ (δ: JM) _, ρ ∈ live_roles _ δ)
      (λ δ (ℓ: option $ fmlabel JM), ρ ∉ live_roles _ δ ∨ ∃ α, ℓ = Some (inl (ρ, α))).

  Definition fair_scheduling (mtr : jmtrace) : Prop :=
    ∀ ρ, fair_scheduling_mtr ρ mtr.

  Fixpoint env_steps_count (tr: jmtrace) (bound: nat) : option nat :=
    match bound with
    | 0 => None
    | S bound =>
        match tr with
        | ⟨ s ⟩ => Some 0
        | s -[ inl _ ]->  r => Some 0
        | s -[ inr _ ]->  r => option_map (λ x, 1 + x) (env_steps_count r bound)
        end
    end.

  Lemma env_steps_count_deterministic tr n1 n2 x y :
    env_steps_count tr n1 = Some x →
    env_steps_count tr n2 = Some y →
    x = y.
  Proof.
    revert tr n2 x y. induction n1 as [|n1 IH]; first naive_solver.
    intros tr n2 x y He1 He2.
    destruct n2 as [|n2]=>//.
    destruct tr as [|s ℓ tr] =>//; first naive_solver.
    simpl in *. destruct ℓ; first naive_solver.
    destruct (env_steps_count tr n1) eqn:Heq1; last naive_solver.
    destruct (env_steps_count tr n2) eqn:Heq2; last naive_solver.
    simpl in *. simplify_eq. f_equal. by eapply IH.
  Qed.

  Lemma env_steps_count_step n s ℓ tr :
    env_steps_count (s -[ ℓ ]-> tr) (1+n) = Some (1+n) →
    env_steps_count tr n = Some n.
  Proof.
    simpl. destruct ℓ. naive_solver. destruct (env_steps_count _ _) eqn:Heq=>//. naive_solver.
  Qed.

  Lemma env_steps_count_step_gt' bound n m s ℓ tr :
    env_steps_count (s -[ inr ℓ ]-> tr) (S bound) = Some n →
    env_steps_count tr bound = Some m →
    n > m.
  Proof.
    simpl. destruct (env_steps_count _ _); naive_solver.
  Qed.

  Lemma env_steps_count_step_gt n1 n2 n m s ℓ tr :
    env_steps_count (s -[ inr ℓ ]-> tr) n1 = Some n →
    env_steps_count tr n2 = Some m →
    n > m.
  Proof.
    destruct n1 as [|n1]; first naive_solver. simpl.
    simpl. destruct (env_steps_count _ _) as [n0|] eqn:Heq; last naive_solver.
    simpl. intros; simplify_eq.
    have -> //: n0 = m; last lia.
    by eapply env_steps_count_deterministic.
  Qed.

  Definition is_usr_step (_ : JM) (ℓ : option $ fmlabel JM) : Prop :=
    match ℓ with
    | Some (inl _) => True
    | _ => False
    end.

  Definition is_usr_step_or_disabled ρ (s : JM) (ℓ : option $ fmlabel JM) : Prop :=
    ρ ∉ live_roles _ s ∨ ∃ ℓ', ℓ = Some $ inl ℓ'.

  Lemma env_steps_count_is_Some' n tr ρ:
    jmtrace_valid tr →
    ρ ∈ live_roles _ (trfirst tr) →
    pred_at tr n (is_usr_step_or_disabled ρ) →
    ∃ m, env_steps_count tr (S n) = Some m ∧ pred_at tr m is_usr_step.
  Proof.
    revert tr. induction n as [|n IH]; intros tr Hval Hρ Henv.
    { destruct tr; rewrite /pred_at /is_usr_step_or_disabled //= in Henv; naive_solver. }
    destruct tr as [|s ℓ tr]=>//.
    simpl. destruct ℓ.
    { exists 0. split=>//. }
    odestruct (IH tr _ _) as [m [HS Hpa]] =>//.
    { unshelve eapply (trace_always_suffix_of _ _ _ _ Hval). by exists 1. }
    { simpl in Hρ, Hval. rewrite /jmtrace_valid in Hval.
      apply trace_always_elim in Hval.
      destruct (trfirst tr) eqn:Heq.
      inversion Hval; simplify_eq. simpl in *. congruence. }
    exists (1+m). simpl. split=>//. destruct tr as [| ? ℓ ?]; first naive_solver.
    destruct ℓ; first naive_solver. simpl in HS. rewrite HS //.
  Qed.

  Lemma env_steps_bound_exists ρ tr :
    fair_scheduling tr →
    ρ ∈ live_roles _ (trfirst tr) →
    exists n, pred_at tr n (is_usr_step_or_disabled ρ).
  Proof.
    unfold fair_scheduling, fair_scheduling_mtr, trace_always_eventually_implies_now,
      trace_always_eventually_implies.
    intros Hf Hl. specialize (Hf ρ).
    apply trace_always_elim in Hf.
    rewrite trace_impliesI in Hf.
    ospecialize (Hf _).
    { rewrite /trace_now. destruct tr=>//. }
    rewrite trace_eventuallyI in Hf. destruct Hf as [tr' [Hsuff Hlive]].
    rewrite /trace_now in Hlive.
    destruct Hsuff as [n Hafter].
    exists n. rewrite /pred_at /is_usr_step_or_disabled Hafter. rewrite /pred_at in Hlive.
    destruct tr'; simpl in Hlive; naive_solver.
  Qed.

  Definition env_steps_bound_get_bound ρ tr
    (Hf: fair_scheduling tr)
    (Hlive: ρ ∈ live_roles _ (trfirst tr)):
    nat := epsilon (env_steps_bound_exists _ _ Hf Hlive).

  Lemma env_steps_bound_get_bound_correct ρ tr
    (Hf: fair_scheduling tr)
    (Hlive: ρ ∈ live_roles _ (trfirst tr)):
    pred_at tr (env_steps_bound_get_bound _ _ Hf Hlive) (is_usr_step_or_disabled ρ).
  Proof. rewrite /env_steps_bound_get_bound. apply epsilon_correct. Qed.

  Lemma env_steps_count_is_Some tr ρ
    (Hval: jmtrace_valid tr)
    (Hf: fair_scheduling tr)
    (Hlive: ρ ∈ live_roles _ (trfirst tr)):
    ∃ m, env_steps_count tr (S $ env_steps_bound_get_bound _ _ Hf Hlive) = Some m ∧ pred_at tr m is_usr_step.
  Proof.
    eapply env_steps_count_is_Some' =>//.
    apply env_steps_bound_get_bound_correct.
  Qed.

  Definition env_steps_count_good tr ρ
    (Hval: jmtrace_valid tr)
    (Hf: fair_scheduling tr)
    (Hlive: ρ ∈ live_roles _ (trfirst tr)):
    nat
    := epsilon (env_steps_count_is_Some _ _ Hval Hf Hlive).

  Lemma env_steps_count_good_correct tr ρ
    (Hval: jmtrace_valid tr)
    (Hf: fair_scheduling tr)
    (Hlive: ρ ∈ live_roles _ (trfirst tr)):
    env_steps_count tr (S $ env_steps_bound_get_bound _ _ Hf Hlive) = Some (env_steps_count_good _ _ Hval Hf Hlive)
      ∧ pred_at tr (env_steps_count_good _ _ Hval Hf Hlive) is_usr_step.
  Proof. rewrite /env_steps_count_good. apply epsilon_correct. Qed.

  #[local] Instance live_dec (tr : jmtrace): Decision (∃ ρ : fmrole JM, ρ ∈ live_roles JM (trfirst tr)).
  Proof. apply make_decision. Qed.
  #[local] Instance valid_dec (tr: jmtrace) : Decision (jmtrace_valid tr ∧ fair_scheduling tr).
  Proof. apply make_decision. Qed.

  Definition env_steps_count_total tr : nat :=
    match decide (∃ ρ, ρ ∈ live_roles _ (trfirst tr)) with
    | left Hin =>
        let ρ := choose _ Hin in
        match decide (jmtrace_valid tr ∧ fair_scheduling tr) with
        | left (conj Hval Hf) =>
            env_steps_count_good tr ρ Hval Hf (choose_correct (λ ρ, ρ ∈ live_roles _ (trfirst tr)) _)
        | right _ => 0
        end
    | right _ =>
        0
    end.

  Definition trace_is_trimmed (tr: jmtrace) :=
    ∀ n, match after n tr with
         | Some (s -[ℓ]-> tr') =>
             ∃ m, pred_at tr' m is_usr_step
         | _ => True
        end.

  Definition trace_is_trimmed_alt (tr: jmtrace) :=
    ∀ n, match after n tr with
         | Some (s -[ℓ]-> tr') =>
             ∃ ρ, ρ ∈ live_roles _ (trfirst tr')
         | _ => True
        end.

  Lemma trace_no_roles_no_usr tr:
    jmtrace_valid tr →
    live_roles _ (trfirst tr) = ∅ →
    ∀ n, ¬ pred_at tr n is_usr_step.
  Proof.
    intros Hval Hnl n; revert tr Hval Hnl.
    induction n as [|n IH]; intros tr Hval Hnl.
    { destruct tr; first naive_solver.
      rewrite pred_at_0. apply trace_always_elim in Hval.
      destruct ℓ as [ℓ|]; last naive_solver.
      destruct ℓ as [ρ α].
      have : ρ ∈ live_roles _ s; last set_solver.
      by eapply (fm_live_spec _ _ _ α (trfirst tr)). }
    destruct tr; first naive_solver.
    rewrite pred_at_S. apply IH.
    { apply (trace_always_suffix_of _ _ tr) in Hval =>//. by exists 1. }

    apply trace_always_elim in Hval.
    destruct ℓ as [ℓ|].
    - destruct ℓ as [ρ α].
      have : ρ ∈ live_roles _ s; last set_solver.
      by eapply (fm_live_spec _ _ _ α (trfirst tr)).
    - rewrite /trans_valid in Hval. destruct (trfirst tr).
      inversion Hval; simplify_eq. naive_solver.
  Qed.

  Lemma trace_is_trimmed_equiv tr :
    jmtrace_valid tr →
    trace_is_trimmed tr →
    trace_is_trimmed_alt tr.
  Proof.
    intros Hval Htr n.
    specialize (Htr n).
    destruct (after n tr) as [[|s ℓ tr']|] eqn:Heq=>//.
    apply NNP_P. intros Hc.
    have Hemp: live_roles _ (trfirst tr') = ∅.
    { set_solver. }
    apply (trace_always_suffix_of _ _ tr') in Hval; last first.
    { have ?: trace_suffix_of (s -[ℓ]-> tr') tr by eexists.
      by eapply trace_suffix_of_cons_l. }
    have ?:= trace_no_roles_no_usr tr' Hval Hemp.
    naive_solver.
  Qed.

  Definition env_proj_st (s: JM) : M := fst s.
  Definition env_proj_lab (ℓ: fmlabel JM) : option _ :=
    match ℓ with
    | inl x => Some x
    | _ => None
    end.

  Notation env_dec_unless := (dec_unless env_proj_st env_proj_lab env_steps_count_total).

  Lemma env_steps_dec_unless tr
    (Hval: jmtrace_valid tr)
    (Hf: fair_scheduling tr)
    (Htrim: trace_is_trimmed tr):
    env_dec_unless tr.
  Proof.
    intros n.
    destruct (after n tr) as [[|s ℓ tr']|] eqn:Heq =>//.
    destruct ℓ as [|f].
    { left. simpl. by eexists. }
    have Hsuff1: trace_suffix_of (s -[ inr f]-> tr') tr by exists n.
    have Hsuff2: trace_suffix_of tr' tr.
    { by eapply trace_suffix_of_cons_l. }
    right. split; last first.
    { apply (trace_always_suffix_of _ _ _ Hsuff1), trace_always_elim in Hval.
      destruct s as [us ns]. unfold trans_valid in Hval. destruct (trfirst tr').
      by inversion Hval; simplify_eq. }
    rewrite /env_steps_count_total.

    have Hlive1: ∃ ρ : fmrole JM, ρ ∈ live_roles JM (trfirst tr').
    { apply trace_is_trimmed_equiv in Htrim=>//.
      specialize (Htrim n). rewrite Heq // in Htrim. }
    have Hlive2: ∃ ρ : fmrole JM, ρ ∈ live_roles JM s.
    { apply (trace_always_suffix_of _ _ _ Hsuff1), trace_always_elim in Hval.
      destruct s as [us ns]. unfold trans_valid in Hval. destruct (trfirst tr').
      by inversion Hval; simplify_eq. }
    destruct (decide _) as [Hin1|]; last naive_solver.
    destruct (decide _) as [[Hval1 Hfair1]|]; last first.
    { exfalso.
      have ?: jmtrace_valid tr' by apply (trace_always_suffix_of _ _ _ Hsuff2) in Hval.
      have ?: fair_scheduling tr'.
      { intros ρ. eapply (trace_always_suffix_of _ _ _ Hsuff2) in Hf. apply Hf. }
      naive_solver. }
    destruct (decide _) as [Hin2|]; last naive_solver.
    destruct (decide _) as [[Hval2 Hfair2]|]; last first.
    { exfalso.
      have ?: jmtrace_valid (s -[ inr f ]-> tr') by apply (trace_always_suffix_of _ _ _ Hsuff1) in Hval.
      have ?: fair_scheduling (s -[ inr f ]-> tr').
      { intros ρ. eapply (trace_always_suffix_of _ _ _ Hsuff1) in Hf. apply Hf. }
      naive_solver. }

    generalize (choose_correct (λ ρ : fmrole JM, ρ ∈ live_roles JM (trfirst tr')) Hin1) as Hin1'.
    intros Hin1'.
    set (Hcc := choose_correct _).
    generalize (Hcc Hin2).
    intros Hin2'.

    set (ρ1 := choose _ _).
    set (ρ2 := choose _ _).

    Notation esb := env_steps_bound_get_bound.
    Notation esbg := env_steps_count_good.

    have [? _] := env_steps_count_good_correct _ _ Hval1 Hfair1 Hin1'.
    have [? _] := env_steps_count_good_correct _ _ Hval2 Hfair2 Hin2'.

    eapply env_steps_count_step_gt=>//.
  Qed.
End measure.
