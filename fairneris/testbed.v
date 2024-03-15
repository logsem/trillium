From stdpp Require Import option countable.
From fairneris Require Export inftraces trace_utils fairness.

Record Lts lab : Type := {
  lts_state :> Type;
  lts_state_eqdec :: EqDecision lts_state;
  lts_state_inhabited :: Inhabited lts_state;

  lts_lab_eqdec :: EqDecision lab;
  lts_lab_countable : Countable lab;
  lts_lab_inhabited :: Inhabited lab;

  lts_trans: lts_state → lab → lts_state → Prop;
}.

Arguments lts_state {_}.
Arguments lts_trans {_}.

Record EnvModel (Λ : language) := {
    env_lts :> Lts (action Λ + config_label Λ);
    env_states_match : cfg Λ → env_lts.(lts_state) → Prop;
    env_apply_trans : env_lts.(lts_state) → config_label Λ → env_lts.(lts_state);
    env_apply_trans_spec : ∀ c1 m1 cl c2 m2,
      env_apply_trans m1 cl = m2 →
      locale_step c1 (inr cl) c2 →
      env_states_match c1 m1 →
      env_states_match c2 m2;
}.

Arguments env_lts {_}.

Record UserModel (Λ : language) := {
    usr_role : Type;
    usr_lts :> Lts (usr_role * option (action Λ));

    usr_eqdec: EqDecision usr_role;
    usr_countable: Countable usr_role;
    usr_inhabited: Inhabited usr_role;
    usr_live_roles: usr_lts.(lts_state) → gset usr_role;
    usr_live_spec: ∀ s ρ α s', usr_lts.(lts_trans) s (ρ,α) s' → ρ ∈ usr_live_roles s;
}.

Arguments usr_role {_}.
Arguments usr_lts {_}.
Arguments usr_live_roles {_ _}.

Inductive joint_trans {Λ: language} {M: UserModel Λ} {N: EnvModel Λ} :
  (M * N) → ((usr_role M * option (action Λ)) + config_label Λ) → (M * N) → Prop :=
| UsrTrans n u1 u2 ρ : lts_trans M u1 (ρ, None) u2 → joint_trans (u1, n) (inl (ρ, None)) (u2, n)
| NetTrans u n1 n2 ℓ : lts_trans N n1 (inr ℓ) n2 → joint_trans (u, n2) (inr ℓ) (u, n2)
| SyncTrans u1 u2 n1 n2 ρ α :
  lts_trans M u1 (ρ, Some α) u2 → lts_trans N n1 (inl α) n2 →
  joint_trans (u1, n2) (inl (ρ, Some α)) (u2, n2)
.

Program Definition joint_model {Λ: language} (M: UserModel Λ) (N: EnvModel Λ) : FairModel :=
{|
  fmstate := lts_state (usr_lts M) * lts_state N;
  (* Why doesn't this work??? *)
  fmrole := usr_role M;
  fmaction := option (action Λ);
  fmconfig := config_label Λ;
  fmtrans s1 ℓ s2 := joint_trans s1 ℓ s2;
  live_roles s := usr_live_roles s.1;

  fmrole_eqdec := usr_eqdec _ M;
  fmrole_countable := usr_countable _ M;
  fmrole_inhabited := usr_inhabited _ M;

  (* let's see what to do later... *)
  fmfairness _ := True;
|}.
Next Obligation. by intros ???????; inversion 1; simplify_eq; eapply usr_live_spec. Qed.
