From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.program_logic Require Import adequacy.
From trillium.traces Require Import utils_logic inftraces.

Section exec_trace.
  Context {Λ : language}.
  Context `{EqDecision (locale Λ)}.

  Definition locale_enabled (ζ : locale Λ) (c: cfg Λ) :=
    ∃ e, from_locale c.1 ζ = Some e ∧ to_val e = None.

  Definition tid_match (ζ : locale Λ) (oζ': olocale Λ) :=
    oζ' = Some ζ.

  Definition extrace Λ := trace (cfg Λ) (olocale Λ).

  (* Definition fair_ex ζ (extr: extrace Λ): Prop := *)
  (*   fair_by locale_enabled tid_match ζ extr.  *)

  CoInductive extrace_valid: extrace Λ -> Prop :=
  | extrace_valid_singleton c: extrace_valid ⟨c⟩
  | extrace_valid_cons c oζ tr:
      locale_step c oζ (trfirst tr) ->
      extrace_valid tr →
      extrace_valid (c -[oζ]-> tr).

  Lemma to_trace_preserves_validity ex iex:
    extrace_valid (to_trace (trace_last ex) iex) -> valid_exec ex -> valid_inf_exec ex iex.
  Proof.
    revert ex iex. cofix CH. intros ex iex Hexval Hval.
    rewrite (trace_unfold_fold (to_trace _ _)) in Hexval.
    destruct iex as [|[??] iex]; first by econstructor. cbn in Hexval.
    inversion Hexval. simplify_eq.
    econstructor; try done.
    - by destruct iex as [|[??]?].
    - apply CH; eauto. econstructor; try done. by destruct iex as [|[??]?].
  Qed.

  Lemma from_trace_preserves_validity (extr: extrace Λ) ex:
    extrace_valid extr ->
    valid_exec ex ->
    trace_last ex = trfirst extr ->
    valid_inf_exec ex (from_trace extr).
  Proof.
    revert ex extr. cofix CH. intros ex extr Hexval Hval Heq.
    rewrite (inflist_unfold_fold (from_trace extr)). destruct extr as [c|c tid tr]; cbn;
     first by econstructor.
    inversion Hexval; simplify_eq; econstructor; eauto. apply CH; eauto.
      by econstructor.
  Qed.

  Lemma from_trace_preserves_validity_singleton (extr: extrace Λ):
    extrace_valid extr ->
    valid_inf_exec (trace_singleton (trfirst extr)) (from_trace extr).
  Proof.
    intros ?. eapply from_trace_preserves_validity; eauto. econstructor.
  Qed.

  (* TODO: use across the development *)
  Lemma extrace_valid_alt etr:
    extrace_valid etr <-> trace_valid locale_step etr.
  Proof using.
    split.
    - revert etr. pcofix CIH. 
      intros etr VALID. 
      pfold.
      inversion VALID; subst.
      { constructor. }
      constructor; auto.
    - revert etr. cofix CIH. 
      intros etr VALID.
      punfold VALID.
      2: { apply trace_valid_mono. }
      inversion VALID; subst.
      { constructor. }
      constructor; auto.
      apply CIH. destruct H0; [| done]. done.
  Qed.

End exec_trace.
