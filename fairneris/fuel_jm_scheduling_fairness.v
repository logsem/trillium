From fairneris Require Import fairness fuel env_model env_model_project.


Section upto.
  Context {Λ: language}.
  Context `{GoodLang Λ}.
  Context {M: UserModel Λ}.
  Context {N: EnvModel Λ}.
  Context {LM: LiveModel Λ (joint_model M N)}.


  (* TODO: remove this, this is just a translation between two definitions of fairness. *)

  Lemma upto_stutter_fairness_ltl (auxtr: auxtrace LM) (mtr: mtrace (joint_model M N)):
    upto_stutter_aux auxtr mtr ->
    (∀ ρ, fair_aux (LM := LM) ρ auxtr) →
    fair_scheduling mtr.
  Proof.
    intros Hupto Hfair ρ.
    opose proof (upto_stutter_fairness auxtr mtr _ _ (ρ: fmrole (joint_model M N))) as Hf=>//.
    rewrite /fairness.fair_scheduling_mtr /fair_scheduling_mtr in Hf *.
    rewrite /trace_always_eventually_implies_now /trace_always_eventually_implies.
    rewrite trace_alwaysI. intros tr' [n Hsuff]. rewrite trace_impliesI. intros Hnow.
    rewrite /trace_utils.trace_implies in Hf. odestruct (Hf n _) as [m Hm].
    { rewrite /pred_at Hsuff. done. }
    rewrite /pred_at in Hm.
    rewrite trace_eventuallyI.
    destruct (after (n+m) mtr) as [mtr'|] eqn:Heq; rewrite Heq in Hm; last naive_solver.
    exists mtr'; split; last naive_solver.
    exists m. rewrite after_sum' Hsuff // in Heq.
  Qed.
End upto.
