From trillium.traces Require Export trace infinite_trace.
From trillium.program_logic Require Import language.

Import InfListNotations.

Definition execution_trace Λ := finite_trace (cfg Λ) (option (locale Λ)).

Record Model : Type := MkModel {
  mstate:> Type;
  mlabel: Type;
  mtrans: mstate -> mlabel -> mstate -> Prop;
}.

Arguments mtrans {_} _ _ _.

Notation olocale Λ := (option (locale Λ)).

Notation auxiliary_trace m := (finite_trace m.(mstate) m.(mlabel)).

Section execution_trace.
  Context {Λ : language}.

  Implicit Types c : cfg Λ.

  Definition valid_exec (ex : execution_trace Λ) : Prop := trace_steps locale_step ex.

  Lemma valid_singleton_exec c : valid_exec (trace_singleton c).
  Proof. constructor. Qed.

  Lemma extend_valid_exec ex c ζ c':
    valid_exec ex →
    trace_ends_in ex c →
    locale_step c ζ c' →
    valid_exec (ex :tr[ζ]: c').
  Proof. econstructor; done. Qed.

  Lemma valid_exec_exec_extend_inv ex ζ c':
    valid_exec (trace_extend ex ζ c') →
    valid_exec ex ∧
    ∃ c, trace_ends_in ex c ∧ locale_step c ζ c'.
  Proof. apply trace_steps_step_inv. Qed.

End execution_trace.

Section system_trace.
  Context {Λ : language} {M : Model}.

  Implicit Types ex : execution_trace Λ.
  Implicit Types atr : auxiliary_trace M.
  Implicit Types ζ : olocale Λ.
  Implicit Types ℓ : mlabel M.

  Inductive valid_system_trace : execution_trace Λ → auxiliary_trace M → Prop :=
  | valid_system_trace_singleton c δ :
      valid_system_trace (trace_singleton c) (trace_singleton δ)
  | valid_system_trace_step ex atr c c' δ' ζ ℓ:
      trace_ends_in ex c →
      locale_step c ζ c' →
      valid_system_trace ex atr →
      valid_system_trace (trace_extend ex ζ c') (trace_extend atr ℓ δ').

  Lemma valid_system_trace_valid_exec_trace ex atr :
    valid_system_trace ex atr → valid_exec ex.
  Proof. induction 1; econstructor; eauto. Qed.

  Lemma valid_system_trace_singletons c δ :
    valid_system_trace (trace_singleton c) (trace_singleton δ).
  Proof. constructor. Qed.

  Lemma valid_system_trace_extend ex atr c c' δ' ζ ℓ:
    valid_system_trace ex atr →
    trace_ends_in ex c →
    locale_step c ζ c' →
    valid_system_trace (trace_extend ex ζ c') (trace_extend atr ℓ δ').
  Proof.
    intros Heatr; revert c c' δ' ζ ℓ.
    induction ex; econstructor; eauto.
  Qed.

  Lemma valid_system_trace_extend_inv ex atr c' δ' ζ ℓ:
    valid_system_trace (trace_extend ex ζ c') (trace_extend atr ℓ δ') →
    ∃ c,
      valid_system_trace ex atr ∧
      trace_ends_in ex c ∧
      locale_step c ζ c'.
  Proof. inversion 1; eauto. Qed.

  Lemma valid_system_trace_ends_in ex atr :
    valid_system_trace ex atr → ∃ c δ, trace_ends_in ex c ∧ trace_ends_in atr δ.
  Proof.
    inversion 1;
      eauto using trace_extend_ends_in, trace_singleton_ends_in,
      trace_extend_ends_in, trace_singleton_ends_in.
  Qed.

  Lemma trace_steps2_trace_steps (R : M -> mlabel M -> M -> Prop) :
    (∀ ex atr c δ c' δ' ζ ℓ,
        trace_ends_in ex c →
        trace_ends_in atr δ →
        locale_step c ζ c' →
        R δ ℓ δ') →
    ∀ ex atr, valid_system_trace ex atr → valid_exec ex ∧ trace_steps R atr.
  Proof.
    intros HR ex ex' Hexs.
    induction Hexs as [|?????????? []].
    - split; constructor.
    - split; econstructor; [done|done|done|done|eapply HR=>//|done].
  Qed.

End system_trace.

Definition inf_execution_trace Λ := inflist (olocale Λ * cfg Λ).

Section inf_execution_trace.
  Context {Λ : language}.

  Definition inf_exec_prepend ζ (c : cfg Λ)
             (iex : inf_execution_trace Λ) : inf_execution_trace Λ :=
    ((ζ, c) :: iex)%inflist.

  CoInductive valid_inf_exec :
    execution_trace Λ → inf_execution_trace Λ → Prop :=
  | valid_inf_exec_singleton ex :
      valid_exec ex → valid_inf_exec ex []%inflist
  | valid_inf_exec_step ex c c' iex ζ:
      valid_exec ex →
      trace_ends_in ex c →
      locale_step c ζ c' →
      valid_inf_exec (trace_extend ex ζ c') iex →
      valid_inf_exec ex (inf_exec_prepend ζ c' iex).

End inf_execution_trace.

Definition inf_auxiliary_trace (M : Model) := inflist ((mlabel $ M) * M).

Definition inf_auxtr_prepend {M : Model} ℓ (δ : M) (atr : inf_auxiliary_trace M) :=
  infcons (ℓ,δ) atr.

CoInductive valid_inf_system_trace {Λ M}
            (Ψ : execution_trace Λ → auxiliary_trace M → Prop) :
  execution_trace Λ → auxiliary_trace M →
  inf_execution_trace Λ → inf_auxiliary_trace M → Prop :=
| valid_inf_system_trace_singleton ex atr :
    Ψ ex atr →
    valid_inf_system_trace Ψ ex atr []%inflist []%inflist
| valid_inf_system_trace_step ex atr c c' δ' iex iatr ζ ℓ:
    Ψ ex atr →
    trace_ends_in ex c →
    locale_step c ζ c' →
    valid_inf_system_trace
      Ψ (trace_extend ex ζ c') (trace_extend atr ℓ δ') iex iatr →
    valid_inf_system_trace
      Ψ ex atr (inf_exec_prepend ζ c' iex) (inf_auxtr_prepend ℓ δ' iatr).

Lemma valid_inf_system_trace_inv {Λ M}
      (Ψ : execution_trace Λ → auxiliary_trace M → Prop) ex atr iex itr :
  valid_inf_system_trace Ψ ex atr iex itr →
  Ψ ex atr.
Proof. by inversion 1. Qed.

  Lemma valid_inf_exec_adjust {Λ : language} {ex: execution_trace Λ} {c iex ζ} :
    valid_inf_exec ex ((ζ, c) :: iex)%inflist →
    valid_inf_exec (trace_extend ex ζ c) iex.
  Proof. inversion 1; done. Qed.

  Lemma valid_inf_exe_valid_exec {Λ : language} {ex: execution_trace Λ} iex :
    valid_inf_exec ex iex → valid_exec ex.
  Proof. by destruct 1. Qed.
  Lemma valid_inf_exe_take_drop {Λ : language} {ex: execution_trace Λ} iex n :
    valid_inf_exec ex iex → valid_inf_exec (ex +trl+ inflist_take n iex) (inflist_drop n iex).
  Proof.
    revert ex iex; induction n as [|n IHn]; intros ex iex Hvl; simpl; first done.
    destruct iex as [|[??]]; simpl; first done.
    apply IHn.
    apply valid_inf_exec_adjust; done.
  Qed.

  Lemma valid_system_trace_start_or_contract {Λ : language} {M: Model}
    (ex: execution_trace Λ) (atr: auxiliary_trace M) :
    valid_system_trace ex atr →
    (ex = {tr[trace_first ex]} ∧ atr = {tr[trace_first atr]}) ∨
    (∃ ex' atr' oζ ℓ, trace_contract ex oζ ex' ∧ trace_contract atr ℓ atr').
  Proof. rewrite /trace_contract; inversion 1; simplify_eq; eauto 10. Qed.

  Lemma valid_inf_exec_prepend_valid_exec_extend {Λ : language}
    (ex: execution_trace Λ) c iex ζ:
    valid_inf_exec ex (inf_exec_prepend ζ c iex) →
    valid_exec (trace_extend ex ζ c).
  Proof.
    inversion 1 as [|???????? Hex]; simplify_eq.
    inversion Hex; done.
  Qed.

  Definition trace_extend_uncurry {M: Model}
    (tr: auxiliary_trace M) xy := trace_extend tr xy.2 xy.1.

Section simulation.
  Context {Λ : language} {M : Model}.
  Variable (labels_match : olocale Λ → mlabel M → Prop).

  Implicit Types ex : execution_trace Λ.
  Implicit Types atr : auxiliary_trace M.

  Definition continued_simulation_pre
             (φ : execution_trace Λ → auxiliary_trace M → Prop)
             (continued_simulation :
                execution_trace Λ → auxiliary_trace M → Prop) :
    execution_trace Λ → auxiliary_trace M → Prop :=
    λ ex atr,
      φ ex atr ∧
      ∀ c c' ζ,
        trace_ends_in ex c →
        locale_step c ζ c' →
        ∃ δ' ℓ, continued_simulation (trace_extend ex ζ c') (trace_extend atr ℓ δ').

  Local Definition continued_simulation_pre_curried
        (φ : execution_trace Λ → auxiliary_trace M → Prop) :
    (execution_trace Λ * auxiliary_trace M → Prop) →
    (execution_trace Λ * auxiliary_trace M → Prop) :=
    λ ψ (exatr : execution_trace Λ * auxiliary_trace M),
    (continued_simulation_pre φ (λ ex atr, ψ (ex, atr)) exatr.1 exatr.2).

  Lemma continued_simulation_pre_curried_mono
        (φ : execution_trace Λ → auxiliary_trace M → Prop) :
    monotone (continued_simulation_pre_curried φ).
  Proof.
    intros P Q HPQ [ex atr].
    intros [? HP]. split; [done|].
    intros ?????.
    edestruct HP as (?&?&?); eauto.
  Qed.

  Definition continued_simulation (φ : execution_trace Λ → auxiliary_trace M → Prop) :=
    λ ex atr, GFX (continued_simulation_pre_curried φ) (ex, atr).

  Lemma continued_simulation_unfold
        (φ : execution_trace Λ → auxiliary_trace M → Prop) ex atr :
    continued_simulation φ ex atr ↔
    continued_simulation_pre φ (continued_simulation φ) ex atr.
  Proof.
    symmetry; rewrite /continued_simulation /=.
    apply (λ H, GFX_fixpoint (continued_simulation_pre_curried φ) H (_, _)).
    apply continued_simulation_pre_curried_mono.
  Qed.

  Lemma continued_simulation_rel Φ ex tr:
    continued_simulation Φ ex tr → Φ ex tr.
  Proof.
    rewrite continued_simulation_unfold /continued_simulation_pre; intuition.
  Qed.

  Lemma continued_simulation_next_aux_state_exists
             (φ : execution_trace Λ → auxiliary_trace M → Prop)
             (ex : execution_trace Λ) (atr : auxiliary_trace M)
             (c : cfg Λ) ζ:
    continued_simulation φ ex atr →
    valid_exec (trace_extend ex ζ c) →
    ∃ δℓ, continued_simulation φ (trace_extend ex ζ c) (trace_extend atr δℓ.2 δℓ.1).
  Proof.
    rewrite continued_simulation_unfold /continued_simulation_pre.
    intros (HΦ & Hext) Hvex.
    apply valid_exec_exec_extend_inv in Hvex as [Hvex (c1 & Hc1 & Hstep)].
    edestruct Hext as (?&?&?); [done..|].
    by eexists (_,_).
  Qed.

  Lemma simulation_does_continue es σ δ φ :
    continued_simulation φ (trace_singleton (es, σ)) (trace_singleton δ) →
    ∀ ex, trace_starts_in ex (es, σ) →
          valid_exec ex →
          ∃ atr, trace_starts_in atr δ ∧ continued_simulation φ ex atr.
  Proof.
    intros Hsm ex Hexstr Hex.
    induction Hex as [|? ? ? ? ? ? ? IHex].
    - apply trace_singleton_starts_in_inv in Hexstr as ->.
      exists (trace_singleton δ). done.
    - destruct IHex as [atr [Hstarts Hsim]].
      { eapply trace_extend_starts_in_inv; eauto. }
      edestruct (continued_simulation_next_aux_state_exists φ ex atr) as ([??]&?);
        [done| |].
      { econstructor; eauto. }
      eexists. split; [|done].
      by apply trace_extend_starts_in.
  Qed.

  Lemma continued_simulation_impl (Φ Ψ: execution_trace Λ → auxiliary_trace M → Prop) ex tr:
    (∀ ex tr, Φ ex tr → Ψ ex tr) →
    continued_simulation Φ ex tr → continued_simulation Ψ ex tr.
  Proof.
    intros Himpl Hphi.
    rewrite /continued_simulation /GFX.
    exists (λ '(ex, atr), continued_simulation Φ ex atr).
    split; [done|].
    intros [? ?] ?.
    rewrite /continued_simulation_pre_curried /continued_simulation_pre /=.
    split.
    { by eapply Himpl, continued_simulation_rel. }
    intros c c' ζ ? ?.
    move: H.
    rewrite continued_simulation_unfold /continued_simulation_pre.
    intros [? ?]. eauto.
  Qed.

End simulation.

Section simulation2.
  Context {Λ : language} {M : Model}
          (φ : execution_trace Λ → auxiliary_trace M → Prop).

  Implicit Types ex : execution_trace Λ.
  Implicit Types iex : inf_execution_trace Λ.
  Implicit Types atr : auxiliary_trace M.
  Implicit Types ζ : olocale Λ.
  Implicit Types ℓ : mlabel M.

  Lemma produce_inf_aux_trace_next_aux_state_exists
        (ex : execution_trace Λ) (atr : auxiliary_trace M)
        (Hcsm : continued_simulation φ ex atr)
        (c : cfg Λ)
        (ζ: olocale Λ)
        (iex : inf_execution_trace Λ)
        (Hvex : valid_inf_exec ex (inf_exec_prepend ζ c iex)) :
    ∃ δℓ, continued_simulation φ (trace_extend ex ζ c) (trace_extend atr δℓ.2 δℓ.1).
  Proof.
    eapply continued_simulation_next_aux_state_exists; first done.
    eapply valid_inf_exec_prepend_valid_exec_extend; eauto.
  Qed.

  Definition produce_inf_aux_trace_next_aux_state
             (ex : execution_trace Λ) (atr : auxiliary_trace M)
             (Hcsm : continued_simulation φ ex atr)
             (c : cfg Λ)
             (ζ: olocale Λ)
             (iex : inf_execution_trace Λ)
             (Hvex : valid_inf_exec ex (inf_exec_prepend ζ c iex))
    : (M * mlabel M)%type :=
    epsilon
      (produce_inf_aux_trace_next_aux_state_exists ex atr Hcsm c ζ iex Hvex).

  Lemma produce_inf_aux_trace_next_aux_state_continued_simulation
        (ex : execution_trace Λ) (atr : auxiliary_trace M)
        (Hcsm : continued_simulation φ ex atr)
        (c : cfg Λ)
        (ζ: olocale Λ)
        (iex : inf_execution_trace Λ)
        (Hvex : valid_inf_exec ex (inf_exec_prepend ζ c iex)) :
    continued_simulation
      φ
      (trace_extend ex ζ c)
      (trace_extend_uncurry
         atr (produce_inf_aux_trace_next_aux_state ex atr Hcsm c ζ iex Hvex)).
  Proof.
    rewrite /produce_inf_aux_trace_next_aux_state.
    apply epsilon_correct.
  Qed.

  CoFixpoint produce_inf_aux_trace
          (ex : execution_trace Λ) (atr : auxiliary_trace M)
          (Hcsm : continued_simulation φ ex atr)
          (iex : inf_execution_trace Λ)
          (Hvex : valid_inf_exec ex iex) :
    inf_auxiliary_trace M :=
    match iex as l return valid_inf_exec ex l → inf_auxiliary_trace M with
    | [] => λ _, []
    | (ζ, c) :: iex' =>
      λ Hvex',
      let δℓ :=
          produce_inf_aux_trace_next_aux_state ex atr Hcsm c ζ iex' Hvex'
      in
      (δℓ.2, δℓ.1) :: (produce_inf_aux_trace
              (trace_extend ex ζ c)
              (trace_extend atr δℓ.2 δℓ.1)
              (produce_inf_aux_trace_next_aux_state_continued_simulation
                 ex atr Hcsm c ζ iex' Hvex')
              iex'
              (valid_inf_exec_adjust Hvex'))
    end%inflist Hvex.

  Theorem produced_inf_aux_trace_valid_inf
          (ex : execution_trace Λ) (atr : auxiliary_trace M)
          (Hst : valid_system_trace ex atr)
          (Hcsm : continued_simulation φ ex atr)
          (iex : inf_execution_trace Λ)
          (Hvex : valid_inf_exec ex iex)
    : valid_inf_system_trace
        (continued_simulation φ)
        ex atr
        iex
        (produce_inf_aux_trace ex atr Hcsm iex Hvex).
  Proof.
    revert ex atr Hcsm Hst iex Hvex; cofix CIH; intros ex atr Hcsm Hst iex Hvex.
    destruct iex as [|[ζ c] iex].
    - rewrite [produce_inf_aux_trace _ _ _ _ _]inflist_unfold_fold /=.
      constructor; trivial.
    - rewrite [produce_inf_aux_trace _ _ _ _ _]inflist_unfold_fold /=.
      pose proof (produce_inf_aux_trace_next_aux_state_continued_simulation
                    ex atr Hcsm c ζ iex Hvex) as Hcsm'.
      assert (valid_system_trace
                (ex :tr[ζ]: c)
                (trace_extend_uncurry
                   atr (produce_inf_aux_trace_next_aux_state ex atr Hcsm c ζ iex Hvex)))
             as Hst'.
      { inversion Hvex; simplify_eq.
        econstructor; try done. }
      apply valid_system_trace_extend_inv in Hst' as (?&?&?&?).
      econstructor; eauto using valid_system_trace_step.
  Qed.

End simulation2.

Section simulation_cond.
  Context {Λ : language} {M : Model}.
  Variable (labels_match : olocale Λ → mlabel M → Prop).

  Implicit Types ex : execution_trace Λ.
  Implicit Types atr : auxiliary_trace M.

  Definition continued_simulation_cond_pre
             (φ : execution_trace Λ → auxiliary_trace M → Prop)
             (C: execution_trace Λ → Prop)
             (continued_simulation :
                execution_trace Λ → auxiliary_trace M → Prop) :
    execution_trace Λ → auxiliary_trace M → Prop :=
    λ ex atr,
      C ex ->
      φ ex atr ∧
      ∀ c c' ζ,
        trace_ends_in ex c →
        locale_step c ζ c' →
        ∃ δ' ℓ, continued_simulation (trace_extend ex ζ c') (trace_extend atr ℓ δ').

  Local Definition continued_simulation_cond_pre_curried
        (φ : execution_trace Λ → auxiliary_trace M → Prop)
        (C: execution_trace Λ → Prop) :
    (execution_trace Λ * auxiliary_trace M → Prop) →
    (execution_trace Λ * auxiliary_trace M → Prop) :=
    λ ψ (exatr : execution_trace Λ * auxiliary_trace M),
    (continued_simulation_cond_pre φ C (λ ex atr, ψ (ex, atr)) exatr.1 exatr.2).

  Lemma continued_simulation_cond_pre_curried_mono
        (φ : execution_trace Λ → auxiliary_trace M → Prop)
        (C: execution_trace Λ → Prop) :
    monotone (continued_simulation_cond_pre_curried φ C).
  Proof.
    intros P Q HPQ [ex atr].
    intros ?.
    intros PASS. specialize (H PASS) as [? HP].
    split; [done|].
    intros ?????.
    edestruct HP as (?&?&?); eauto.
  Qed.

  Definition continued_simulation_cond
    (φ : execution_trace Λ → auxiliary_trace M → Prop)
    (C: execution_trace Λ → Prop) :=
    λ ex atr, GFX (continued_simulation_cond_pre_curried φ C) (ex, atr).

  Lemma continued_simulation_cond_unfold
        (φ : execution_trace Λ → auxiliary_trace M → Prop)
        (C: execution_trace Λ → Prop) ex atr :
    continued_simulation_cond φ C ex atr ↔
    continued_simulation_cond_pre φ C (continued_simulation_cond φ C) ex atr.
  Proof.
    symmetry; rewrite /continued_simulation_cond /=.
    apply (λ H, GFX_fixpoint (continued_simulation_cond_pre_curried φ C) H (_, _)).
    apply continued_simulation_cond_pre_curried_mono.
  Qed.

  Lemma continued_simulation_cond_rel Φ C ex tr
    `{forall ex, Decision (C ex)}:
    continued_simulation_cond Φ C ex tr → Φ ex tr ∨ ¬ C ex.
  Proof.
    rewrite continued_simulation_cond_unfold /continued_simulation_cond_pre.
    destruct (decide (C ex)); [| tauto]. 
    intuition.
  Qed.

  Definition filter_pref_closed (C: execution_trace Λ → Prop) :=
    forall ex τ c, C (trace_extend ex τ c) -> C ex. 

  Lemma continued_simulation_cond_next_aux_state_exists
             (φ : execution_trace Λ → auxiliary_trace M → Prop)
             C
             (PCL: filter_pref_closed C)
             `{forall ex, Decision (C ex)}
             `{Inhabited (mlabel M)}
             (ex : execution_trace Λ) (atr : auxiliary_trace M)
             (c : cfg Λ) ζ:
    continued_simulation_cond φ C ex atr →
    valid_exec (trace_extend ex ζ c) →
    ∃ δℓ, continued_simulation_cond φ C (trace_extend ex ζ c) (trace_extend atr δℓ.2 δℓ.1).
  Proof using.
    clear labels_match. 
    rewrite continued_simulation_cond_unfold /continued_simulation_cond_pre.
    destruct (decide (C (ex :tr[ ζ ]: c))) as [PASS' | FAIL'].
    2: { intros _ _.
         inversion H0 as [ℓ].
         exists (trace_last atr, ℓ).
         rewrite continued_simulation_cond_unfold /continued_simulation_cond_pre.
         tauto. }
    apply PCL in PASS'.
    intros X Hvex. specialize (X PASS'). destruct X as (HΦ & Hext).
    apply valid_exec_exec_extend_inv in Hvex as [Hvex (c1 & Hc1 & Hstep)].
    edestruct Hext as (?&?&?); [done..|].
    by eexists (_,_).
  Qed.

  Lemma simulation_cond_does_continue es σ δ φ C
             (PCL: filter_pref_closed C)
             `{forall ex, Decision (C ex)}
             `{Inhabited (mlabel M)}:
    continued_simulation_cond φ C (trace_singleton (es, σ)) (trace_singleton δ) →
    ∀ ex, trace_starts_in ex (es, σ) →
          valid_exec ex →
          ∃ atr, trace_starts_in atr δ ∧ continued_simulation_cond φ C ex atr.
  Proof.
    intros Hsm ex Hexstr Hex.
    induction Hex as [|? ? ? ? ? ? ? IHex].
    - apply trace_singleton_starts_in_inv in Hexstr as ->.
      exists (trace_singleton δ). done.
    - destruct IHex as [atr [Hstarts Hsim]].
      { eapply trace_extend_starts_in_inv; eauto. }
      edestruct (continued_simulation_cond_next_aux_state_exists φ C PCL ex atr) as ([??]&?);
        [done| |].
      { econstructor; eauto. }
      eexists. split; [|done].
      by apply trace_extend_starts_in.
  Qed.

  (* TODO: its original version is unused? *)
  (* Lemma continued_simulation_cond_impl (Φ Ψ: execution_trace Λ → auxiliary_trace M → Prop) C ex tr: *)
  (*   (∀ ex tr, Φ ex tr → Ψ ex tr) → *)
  (*   continued_simulation_cond Φ C ex tr → continued_simulation_cond Ψ C ex tr. *)
  (* Proof. *)
  (*   intros Himpl Hphi. *)
  (*   rewrite /continued_simulation_cond /GFX. *)
  (*   exists (λ '(ex, atr), continued_simulation_cond Φ C ex atr). *)
  (*   split; [done|]. *)
  (*   intros [? ?] ?. *)
  (*   rewrite /continued_simulation_cond_pre_curried /continued_simulation_cond_pre /=. *)
  (*   split. *)
  (*   { eapply Himpl. *)
  (*   rewrite /continued_simulation_cond /GFX in H.  *)

  (*   unfold continued_simulation_cond_pre_curried, continued_simulation_cond_pre in H.  *)
  (*     specialize (H H0).  *)
  (*     eapply continued_simulation_cond_rel. } *)
  (*   intros c c' ζ ? ?. *)
  (*   move: H. *)
  (*   rewrite continued_simulation_unfold /continued_simulation_pre. *)
  (*   intros [? ?]. eauto. *)
  (* Qed. *)

End simulation_cond.

Section simulation2.
  Context {Λ : language} {M : Model}
          (φ : execution_trace Λ → auxiliary_trace M → Prop)
          (C: execution_trace Λ → Prop).

  Context (PCL: filter_pref_closed C)
    {C_DEC: forall ex, Decision (C ex)}
    {ML_INH: Inhabited (mlabel M)}. 

  Implicit Types ex : execution_trace Λ.
  Implicit Types iex : inf_execution_trace Λ.
  Implicit Types atr : auxiliary_trace M.
  Implicit Types ζ : olocale Λ.
  Implicit Types ℓ : mlabel M.

  Lemma produce_inf_aux_trace_next_aux_state_cond_exists
        (ex : execution_trace Λ) (atr : auxiliary_trace M)
        (Hcsm : continued_simulation_cond φ C ex atr)
        (c : cfg Λ)
        (ζ: olocale Λ)
        (iex : inf_execution_trace Λ)
        (Hvex : valid_inf_exec ex (inf_exec_prepend ζ c iex)) :
    ∃ δℓ, continued_simulation_cond φ C (trace_extend ex ζ c) (trace_extend atr δℓ.2 δℓ.1).
  Proof.
    eapply continued_simulation_cond_next_aux_state_exists; eauto. 
    eapply valid_inf_exec_prepend_valid_exec_extend; eauto.
  Qed.

  Definition produce_inf_aux_trace_next_aux_state_cond
             (ex : execution_trace Λ) (atr : auxiliary_trace M)
             (Hcsm : continued_simulation_cond φ C ex atr)
             (c : cfg Λ)
             (ζ: olocale Λ)
             (iex : inf_execution_trace Λ)
             (Hvex : valid_inf_exec ex (inf_exec_prepend ζ c iex))
    : (M * mlabel M)%type :=
    epsilon
      (produce_inf_aux_trace_next_aux_state_cond_exists ex atr Hcsm c ζ iex Hvex).

  Lemma produce_inf_aux_trace_next_aux_state_continued_simulation_cond
        (ex : execution_trace Λ) (atr : auxiliary_trace M)
        (Hcsm : continued_simulation_cond φ C ex atr)
        (c : cfg Λ)
        (ζ: olocale Λ)
        (iex : inf_execution_trace Λ)
        (Hvex : valid_inf_exec ex (inf_exec_prepend ζ c iex)) :
    continued_simulation_cond
      φ C
      (trace_extend ex ζ c)
      (trace_extend_uncurry
         atr (produce_inf_aux_trace_next_aux_state_cond ex atr Hcsm c ζ iex Hvex)).
  Proof.
    rewrite /produce_inf_aux_trace_next_aux_state_cond.
    apply epsilon_correct.
  Qed.

  CoFixpoint produce_inf_aux_trace_cond
          (ex : execution_trace Λ) (atr : auxiliary_trace M)
          (Hcsm : continued_simulation_cond φ C ex atr)
          (iex : inf_execution_trace Λ)
          (Hvex : valid_inf_exec ex iex) :
    inf_auxiliary_trace M :=
    match iex as l return valid_inf_exec ex l → inf_auxiliary_trace M with
    | [] => λ _, []
    | (ζ, c) :: iex' =>
      λ Hvex',
      let δℓ :=
          produce_inf_aux_trace_next_aux_state_cond ex atr Hcsm c ζ iex' Hvex'
      in
      (δℓ.2, δℓ.1) :: (produce_inf_aux_trace_cond
              (trace_extend ex ζ c)
              (trace_extend atr δℓ.2 δℓ.1)
              (produce_inf_aux_trace_next_aux_state_continued_simulation_cond
                 ex atr Hcsm c ζ iex' Hvex')
              iex'
              (valid_inf_exec_adjust Hvex'))
    end%inflist Hvex.

  Theorem produced_inf_aux_trace_valid_inf_cond
          (ex : execution_trace Λ) (atr : auxiliary_trace M)
          (Hst : valid_system_trace ex atr)
          (Hcsm : continued_simulation_cond φ C ex atr)
          (iex : inf_execution_trace Λ)
          (Hvex : valid_inf_exec ex iex)
    : valid_inf_system_trace
        (continued_simulation_cond φ C)
        ex atr
        iex
        (produce_inf_aux_trace_cond ex atr Hcsm iex Hvex).
  Proof.
    revert ex atr Hcsm Hst iex Hvex; cofix CIH; intros ex atr Hcsm Hst iex Hvex.
    destruct iex as [|[ζ c] iex].
    - rewrite [produce_inf_aux_trace_cond _ _ _ _ _]inflist_unfold_fold /=.
      constructor; trivial.
    - rewrite [produce_inf_aux_trace_cond _ _ _ _ _]inflist_unfold_fold /=.
      pose proof (produce_inf_aux_trace_next_aux_state_continued_simulation_cond
                    ex atr Hcsm c ζ iex Hvex) as Hcsm'.
      assert (valid_system_trace
                (ex :tr[ζ]: c)
                (trace_extend_uncurry
                   atr (produce_inf_aux_trace_next_aux_state_cond ex atr Hcsm c ζ iex Hvex)))
             as Hst'.
      { inversion Hvex; simplify_eq.
        econstructor; try done. }
      apply valid_system_trace_extend_inv in Hst' as (?&?&?&?).
      econstructor; eauto using valid_system_trace_step.
  Qed.

End simulation2.
