From stdpp Require Import option countable.
From fairneris Require Export inftraces trace_utils fairness.

Record Lts lab `{Countable lab, Inhabited lab}: Type := {
  lts_state :> Type;
  lts_state_eqdec :: EqDecision lts_state;
  lts_state_inhabited :: Inhabited lts_state;

  lts_trans: lts_state → lab → lts_state → Prop;
}.

Arguments lts_state {_ _ _ _}.
Arguments lts_trans {_ _ _ _}.

Section models.
  Context (Λ: language).
  Context `{Countable (config_label Λ)}.
  Context `{Countable (action Λ)}.
  Context `{Inhabited (config_label Λ)}.
  Context `{Inhabited (action Λ)}.

Record EnvModel := {
    env_lts :> Lts (action Λ + config_label Λ);
    env_states_match : cfg Λ → env_lts.(lts_state) → Prop;
    env_apply_trans : env_lts.(lts_state) → (action Λ + config_label Λ) → env_lts.(lts_state);
    env_apply_trans_spec_both : ∀ ζ c1 m1 cl c2 m2,
      env_apply_trans m1 cl = m2 →
      locale_step c1 (sum_map (λ α, (ζ, Some α)) id cl) c2 →
      env_states_match c1 m1 →
      env_states_match c2 m2;
    env_fairness: trace env_lts.(lts_state) (action Λ + config_label Λ) → Prop;
}.

Arguments env_lts {_}.

Record UserModel := {
    usr_role : Type;

    usr_eqdec:: EqDecision usr_role;
    usr_countable:: Countable usr_role;
    usr_inhabited:: Inhabited usr_role;

    usr_lts :> Lts (usr_role * option (action Λ));

    usr_live_roles: usr_lts.(lts_state) → gset usr_role;
    usr_live_spec: ∀ s ρ α s', usr_lts.(lts_trans) s (ρ,α) s' → ρ ∈ usr_live_roles s;
}.

Arguments usr_live_roles {_}.

Inductive joint_trans {M: UserModel} {N: EnvModel} :
  (M * N) → ((usr_role M * option (action Λ)) + config_label Λ) → (M * N) → Prop :=
| UsrTrans n u1 u2 ρ : lts_trans M u1 (ρ, None) u2 → joint_trans (u1, n) (inl (ρ, None)) (u2, n)
| NetTrans u n1 n2 ℓ : lts_trans N n1 (inr ℓ) n2 → joint_trans (u, n2) (inr ℓ) (u, n2)
| SyncTrans u1 u2 n1 n2 ρ α :
  lts_trans M u1 (ρ, Some α) u2 → lts_trans N n1 (inl α) n2 →
  joint_trans (u1, n1) (inl (ρ, Some α)) (u2, n2)
.

Program Definition joint_model (M: UserModel) (N: EnvModel) : FairModel :=
{|
  fmstate := lts_state (usr_lts M) * lts_state N;
  (* Why doesn't this work??? *)
  fmrole := usr_role M;
  fmaction := option (action Λ);
  fmconfig := config_label Λ;
  fmtrans s1 ℓ s2 := joint_trans s1 ℓ s2;
  live_roles s := usr_live_roles s.1;

  (* We want somehting like: *)
  (* fmfairness tr := env_fairness _ tr; *)
  (* but it's not so easy, because this definition is not constructive... *)
  (* it may be easier to only state it on the joint model directly... *)
  fmfairness _ := True;
|}.
Next Obligation. by intros ??????; inversion 1; simplify_eq; eapply usr_live_spec. Qed.

End models.
