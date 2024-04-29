From stdpp Require Import option countable.
From fairneris Require Export inftraces trace_utils fairness env_model ltl_lite.
From trillium.prelude Require Import classical classical_instances finitary.
From Paco Require Import paco2 pacotac.
From Coq.Logic Require Import Classical.

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
            S $ env_steps_count_good tr ρ Hval Hf (choose_correct (λ ρ, ρ ∈ live_roles _ (trfirst tr)) _)
        | right _ => 0
        end
    | right _ =>
        0
    end.

  Definition trace_is_trimmed (tr: jmtrace) :=
    ∀ n, match after n tr with
         | Some (s -[ℓ]-> tr') =>
             ∃ m, pred_at (s -[ℓ]-> tr') m is_usr_step
         | _ => True
        end.

  #[local] Instance decide_for_trimming tr:
    Decision (∃ m : nat, pred_at tr m is_usr_step).
  Proof. apply make_decision. Qed.

  CoFixpoint trim_trace (tr: jmtrace) : jmtrace :=
    match tr with
    | ⟨ s ⟩ => ⟨ s ⟩
    | s -[ℓ]-> tr' =>
        if decide (∃ m, pred_at (s -[ℓ]-> tr') m is_usr_step) then
          s -[ℓ]-> (trim_trace tr')
        else
          ⟨ s ⟩
    end.

  Inductive trimmed_of_ind (trimmed_of: jmtrace → jmtrace → Prop) : jmtrace → jmtrace → Prop :=
  | TrimmedEnd s : trimmed_of_ind trimmed_of ⟨s⟩ ⟨s⟩
  | TrimmedKeep s ℓ tr1 tr2 :
    trimmed_of tr1 tr2 →
    (∃ m, pred_at (s -[ℓ]-> tr1) m is_usr_step) →
    trimmed_of_ind trimmed_of (s -[ℓ]-> tr1) (s -[ℓ]-> tr2)
  | TrimmedStop s ℓ tr1 tr2 :
    trimmed_of tr1 tr2 →
    (¬ ∃ m, pred_at (s -[ℓ]-> tr1) m is_usr_step) →
    trimmed_of_ind trimmed_of (s -[ℓ]-> tr1) ⟨s⟩.

  Definition trimmed_of := paco2 trimmed_of_ind bot2.

  Lemma trimmed_of_mono :
    monotone2 (trimmed_of_ind).
  Proof.
    unfold monotone2. intros x0 x1 r r' IN LE.
    induction IN; try (econstructor; eauto; done).
  Qed.
  Hint Resolve trimmed_of_mono : paco.

  Lemma trim_trace_trimmed_of tr:
    trimmed_of tr (trim_trace tr).
  Proof.
    revert tr. pcofix CH=> tr. pfold.
    destruct tr as [s|s ℓ tr]; rewrite (trace_unfold_fold (trim_trace _)) /=.
    { constructor. }
    destruct (decide _).
    - constructor 2=>//. by right.
    - econstructor 3=>//. by right.
  Qed.

  Lemma trimmed_of_after m tr1 tr2 tr2':
    trimmed_of tr1 tr2 →
    after m tr2 = Some tr2' →
    ∃ tr1', after m tr1 = Some tr1' ∧ trimmed_of tr1' tr2'.
  Proof.
    revert tr1 tr2 tr2'. induction m as [|m IH]; intros tr1 tr2 tr2' Hto.
    - destruct tr1; simpl; intros ?; simplify_eq; naive_solver.
    - destruct tr1=>//; punfold Hto.
      + inversion Hto; simplify_eq; naive_solver.
      + inversion Hto; simplify_eq; last naive_solver. simpl.
        eintros ?%IH=>//. by pclearbot.
  Qed.

  Lemma trimmed_of_suffix_of tr1 tr2 tr2':
    trimmed_of tr1 tr2 →
    trace_suffix_of tr2' tr2 →
    ∃ tr1', trace_suffix_of tr1' tr1 ∧ trimmed_of tr1' tr2'.
  Proof.
    intros ? [? Ha]. eapply trimmed_of_after in Ha as [tr1' ?]=>//.
    exists tr1'. rewrite /trace_suffix_of. naive_solver.
  Qed.

  (* Lemma trimmed_of_finite_last *)


  Lemma trimmed_of_pred_at_usr m tr1 tr2:
    trimmed_of tr1 tr2 →
    pred_at tr1 m is_usr_step →
    pred_at tr2 m is_usr_step.
  Proof.
    revert tr1 tr2. induction m as [|m IH]; intros tr1 tr2 Hto.
    - destruct tr1=>//. punfold Hto. inversion Hto; simplify_eq; naive_solver.
    - destruct tr1=>//. punfold Hto. inversion Hto; simplify_eq; last naive_solver.
      rewrite !pred_at_S. intros ?. eapply IH=>//. by pclearbot.
  Qed.

  Lemma trimmed_of_pred_at_usr_ex tr1 tr2:
    trimmed_of tr1 tr2 →
    (∃ m, pred_at tr1 m is_usr_step) →
    ∃ m, pred_at tr2 m is_usr_step.
  Proof. have ?:= trimmed_of_pred_at_usr. naive_solver. Qed.

  Lemma trimmed_of_is_trimmed tr1 tr2:
    trimmed_of tr1 tr2 →
    trace_is_trimmed tr2.
  Proof.
    intros Hto n. revert tr1 tr2 Hto. induction n as [|n IH]; intros tr1 tr2 Hto.
    - destruct tr1 as [s1 | s1 ℓ1 tr1].
      + punfold Hto. by inversion Hto; simplify_eq.
      + punfold Hto. inversion Hto; simplify_eq; simpl=>//.
        eapply trimmed_of_pred_at_usr_ex=>//. pfold. done.
    - destruct tr1 as [s1 | s1 ℓ1 tr1].
      + punfold Hto. by inversion Hto; simplify_eq.
      + punfold Hto. inversion Hto; simplify_eq; simpl=>//.
        eapply IH. pclearbot. done.
  Qed.

  Lemma trim_trace_is_trimmed tr:
    trace_is_trimmed (trim_trace tr).
  Proof. eapply trimmed_of_is_trimmed, trim_trace_trimmed_of. Qed.

  Lemma trimmed_of_infinite tr1 tr2:
    trimmed_of tr1 tr2 →
    infinite_trace tr2 →
    trace_equiv tr1 tr2.
  Proof.
    revert tr1 tr2. cofix CH; intros tr1 tr2 Hto Hinf.
    destruct tr1 as [s|s ℓ tr1].
    - punfold Hto. inversion Hto; simplify_eq. done.
    - punfold Hto. inversion Hto; simplify_eq.
      + constructor=>//. apply CH=>//.
        * pclearbot. done.
        * eapply infinite_cons. done.
      + exfalso. clear CH. specialize (Hinf 1). simpl in Hinf.
        inversion Hinf. naive_solver.
  Qed.

  Lemma trim_trace_infinite tr:
    infinite_trace (trim_trace tr) →
    trace_equiv tr (trim_trace tr).
  Proof.
    intros Hinf.
    eapply trimmed_of_infinite=>//.
    apply trim_trace_trimmed_of.
  Qed.

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

  Lemma trace_no_usr_cst_live_roles n tr tr':
    jmtrace_valid tr →
    (∀ n, ¬ pred_at tr n is_usr_step) →
    after n tr = Some tr' →
    live_roles _ (trfirst tr) = live_roles _ (trfirst tr').
  Proof.
    revert tr tr'. induction n as [|n IH]; intros tr tr' Hval Hdead Hafter; first naive_solver.
    destruct tr as [s|s ℓ tr]; first naive_solver.
    rewrite /= in Hafter.
    transitivity (live_roles _ (trfirst tr)).
    - apply trace_always_elim in Hval.
      destruct ℓ.
      { exfalso. by apply (Hdead 0). }
      unfold trans_valid in Hval.
      destruct (trfirst tr) eqn:Heq; inversion Hval; simplify_eq=>//.
    - apply IH=>//.
      + eapply trace_always_suffix_of=>//. apply trace_suffix_of_cons_r, trace_suffix_of_refl.
      + intros m. specialize (Hdead (1+m)). naive_solver.
  Qed.

  Lemma trace_no_roles_no_usr_inv tr:
    jmtrace_valid tr →
    fair_scheduling tr →
    (∀ n, ¬ pred_at tr n is_usr_step) →
    live_roles _ (trfirst tr) = ∅.
  Proof.
    intros Hval Hfair Hdead.
    apply NNP_P. intros Hne.
    apply finitary.set_choose_L' in Hne as [ρ Hin].
    specialize (Hfair ρ). apply trace_always_elim in Hfair.
    rewrite trace_impliesI in Hfair.
    ospecialize (Hfair _).
    { destruct tr=>//. }
    rewrite trace_eventuallyI in Hfair.
    destruct Hfair as (tr'&[n Hafter]&Hx).
    have Hafter' := Hafter.
    apply trace_no_usr_cst_live_roles in Hafter=>//.
    destruct tr' eqn:Heq.
    - destruct Hx as [Hx|Hx]. set_solver. naive_solver.
    - destruct Hx as [Hx|[? Hx]]. set_solver.
      apply (Hdead n). rewrite /pred_at Hafter'. naive_solver.
  Qed.

  Lemma trimmed_of_None_fair n (tr tr' : jmtrace) tr1:
    jmtrace_valid tr →
    fair_scheduling tr →
    trimmed_of tr tr' →
    after n tr = Some tr1 →
    after n tr' = None →
    ∃ s n', n' < n ∧ after n' tr' = Some ⟨s⟩ ∧ live_roles _ s = ∅.
  Proof.
    revert tr tr' tr1. induction n as [|n IH]; intros tr tr' tr1 Hval Hfair Htrim HafterS HafterN.
    { punfold Htrim. inversion Htrim; simplify_eq. }
    destruct tr as [s | s ℓ tr]; punfold Htrim; inversion Htrim; simplify_eq;
      simpl in HafterS, HafterN.
    - odestruct (IH _ _ _ _ _ _ HafterS HafterN) as (s'&n'&CC&DD&EE)=>//.
      { eapply trace_always_suffix_of=>//. apply trace_suffix_of_cons_r, trace_suffix_of_refl. }
      { intros ρ. specialize (Hfair ρ).
        eapply trace_always_suffix_of=>//. apply trace_suffix_of_cons_r, trace_suffix_of_refl. }
      { by pclearbot. }
      exists s', (1 + n'). split; first lia. simpl. split=>//.
    - exists s, 0. split; first lia. split=>//.
      change s with (trfirst (s -[ ℓ ]-> tr)).
      eapply trace_no_roles_no_usr_inv=>//. by apply not_ex_all_not.
  Qed.

  Definition trace_is_trimmed_alt (tr: jmtrace) :=
    ∀ n, match after n tr with
         | Some (s -[ℓ]-> tr') =>
             ∃ ρ, ρ ∈ live_roles _ s
         | _ => True
        end.

  Lemma trace_is_trimmed_equiv tr :
    jmtrace_valid tr →
    trace_is_trimmed tr →
    trace_is_trimmed_alt tr.
  Proof.
    intros Hval Htr n.
    specialize (Htr n).
    destruct (after n tr) as [[|s ℓ tr']|] eqn:Heq=>//.
    apply NNP_P. intros Hc.
    have Hemp: live_roles _ s = ∅.
    { set_solver. }
    apply (trace_always_suffix_of _ _ (s -[ℓ]-> tr')) in Hval; last first.
    { by eexists. }
    have ?:= trace_no_roles_no_usr (s -[ℓ]-> tr') Hval Hemp.
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

    have Hlive1: ∃ ρ : fmrole JM, ρ ∈ live_roles JM s.
    { apply trace_is_trimmed_equiv in Htrim=>//.
      specialize (Htrim n). rewrite Heq // in Htrim. }

    have ? : jmtrace_valid tr' ∧ fair_scheduling tr'.
    { apply NNP_P. intros ?.
      have ?: jmtrace_valid tr' by apply (trace_always_suffix_of _ _ _ Hsuff2) in Hval.
      have ?: fair_scheduling tr'.
      { intros ρ. eapply (trace_always_suffix_of _ _ _ Hsuff2) in Hf. apply Hf. }
      naive_solver. }

    have ? : jmtrace_valid (s -[ inr f ]-> tr') ∧ fair_scheduling (s -[ inr f ]-> tr').
    { apply NNP_P. intros ?.
      have ?: jmtrace_valid (s -[ inr f ]-> tr') by apply (trace_always_suffix_of _ _ _ Hsuff1) in Hval.
      have ?: fair_scheduling (s -[ inr f ]-> tr').
      { intros ρ. eapply (trace_always_suffix_of _ _ _ Hsuff1) in Hf. apply Hf. }
      naive_solver. }

    destruct (decide _) as [Hin1|]; last first.
    { destruct (decide _) as [|]; last done.
      destruct (decide _) as [[??]|]; last done. lia. }

    destruct (decide _) as [[Hval1 Hfair1]|]; last done.
    destruct (decide _) as [Hin2|]; last done.
    destruct (decide _) as [[Hval2 Hfair2]|]; last done.

    rewrite -Nat.succ_lt_mono.

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

Arguments fair_scheduling {_ _ _ _ _ _ _ _}.
Arguments fair_scheduling_mtr {_ _ _ _ _ _ _ _}.
Arguments trim_trace {_ _ _ _ _ _ _ _}.
Arguments trimmed_of {_ _ _ _ _ _ _ _}.
Arguments jmtrace_valid {_ _ _ _ _ _ _ _}.

Section trim_scheduling_fairness.
  Context `{GoodLang Λ}.
  Context {M: UserModel Λ}.
  Context {N: EnvModel Λ}.

  Notation JM := (joint_model M N).
  Notation jmlabel := (fmlabel JM).
  Notation jmtrace := (trace JM jmlabel).

  Notation ltl_equiv P := (ltl_tme (S1 := JM) (L1 := jmlabel)
                             eq eq (λ _ _ _, True) (λ _ _ _, True) P P).

  Lemma trimming_preserves_fair_scheduling (tr : jmtrace):
    jmtrace_valid tr →
    fair_scheduling tr →
    fair_scheduling (trim_trace tr).
  Proof.
    have: trimmed_of tr (trim_trace tr).
    { apply trim_trace_trimmed_of. }
    generalize (trim_trace tr). intros ttr Htrim.

    rewrite /fair_scheduling /fair_scheduling_mtr /trace_always_eventually_implies_now.
    rewrite /trace_always_eventually_implies. intros Hval Hf ρ.
    have Hfair := Hf.
    specialize (Hf ρ).
    rewrite trace_alwaysI. intros ttr' Hsuff. rewrite trace_impliesI. intros Hlive.

    have {}Hlive: ρ ∈ live_roles _ (trfirst ttr').
    { destruct ttr'=>//. }

    destruct (trimmed_of_suffix_of _ _ _ _ _ Htrim Hsuff) as [tr' [Hsuff' Htrim']].

    have Hfeq: trfirst tr' = trfirst ttr'.
    { punfold Htrim'. inversion Htrim'=>//. apply trimmed_of_mono. }

    rewrite trace_alwaysI in Hf. specialize (Hf _ Hsuff').
    rewrite trace_impliesI in Hf. ospecialize (Hf _).
    { rewrite /trace_now /pred_at. destruct tr'; simpl; naive_solver. }
    rewrite trace_eventuallyI in Hf. destruct Hf as [tr'' [Hsuff'' Hf]].

    destruct Hsuff'' as [n Hn].
    destruct (after n ttr') as [ttr''|] eqn:Heq.
    - rewrite trace_eventuallyI. exists ttr''. split; [by exists n|].
      eapply trimmed_of_after in Heq as [tr''' [Hafter Htrim'']]=>//.
      have ?: tr''' = tr'' by congruence. simplify_eq.
      revert Hf. rewrite /trace_now /pred_at //=.
      destruct tr'', ttr'';
      (punfold Htrim''; last apply trimmed_of_mono); inversion Htrim''; simplify_eq=>//.
      intros _. left.
      have Hsuff0: trace_suffix_of (s0 -[ ℓ ]-> tr'') tr.
      { eapply trace_suffix_of_trans=>//. by exists n. }
      opose proof (trace_no_roles_no_usr_inv _ _ (s0 -[ ℓ ]-> tr'') _ _ _) as Hnr.
      + eapply trace_always_suffix_of=>//.
      + intros ρ0. specialize (Hfair ρ0).
        eapply trace_always_suffix_of=>//.
      + by apply not_ex_all_not.
      + simpl in Hnr. rewrite Hnr. set_solver.
    - unshelve eapply (trimmed_of_None_fair _ _ _ _ _ _ _ _ Htrim') in Heq=>//.
      { eapply trace_always_suffix_of=>//. }
      { intros ρ0. specialize (Hfair ρ0). eapply trace_always_suffix_of=>//. }
      destruct Heq as (s&n'&Hleq&Hafter&Hnl).
      rewrite trace_eventuallyI. exists ⟨s⟩. split; [by exists n'|].
      rewrite /trace_now /pred_at //=. simpl in Hnl. rewrite Hnl. left. set_solver.
  Qed.
End trim_scheduling_fairness.