
From stdpp Require Import option countable.
From fairneris Require Export inftraces trace_utils fairness.

Record Lts lab : Type := {
  lts_state :> Type;
  lts_state_eqdec :: EqDecision lts_state;
  lts_state_inhabited :: Inhabited lts_state;

  lts_lab_eqdec :: EqDecision lab;
  lts_lab_countable :: Countable lab;
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
    usr_lts : Lts (usr_role * action Λ);

    usr_eqdec: EqDecision usr_role;
    usr_countable: Countable usr_role;
    usr_inhabited: Inhabited usr_role;
}.

Arguments usr_role {_}.
Arguments usr_lts {_}.

Program Definition join_model {Λ: language} (M: UserModel Λ) (N: EnvModel Λ) : FairModel :=
{|
  fmstate := lts_state (usr_lts M) * lts_state N;
  (* Why doesn't this work??? *)
  fmrole := usr_role M;
  (* The error is:
Error: Cannot infer an instance of type "Lts (usr_role M)" for the variable l in
environment:
Λ : language
M : UserModel Λ
N : EnvModel Λ

What is `l`? why would anyone want such an instance?
   *)
  fmaction := action Λ;
  fmconfig := config_label Λ;
|}.
Next Obligation.
  intros ? UM _. exact (usr_role UM). (* this works, if one comments fmrole := above *)
Defined.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Eval simpl in join_model.
Print join_model_obligation_1.

Record FairModel : Type := {
  fmrole: Type;
  fmaction: Type;
  fmconfig: Type;
  fmrole_eqdec: EqDecision fmrole;
  fmrole_countable: Countable fmrole;
  fmrole_inhabited: Inhabited fmrole;

  fmtrans: fmstate → ((fmrole * fmaction) + fmconfig) → fmstate → Prop;
  fmfairness : trace fmstate ((fmrole * fmaction) + fmconfig) → Prop;
  live_roles: fmstate → gset fmrole;
  fm_live_spec: ∀ s ρ α s', fmtrans s (inl (ρ,α)) s' → ρ ∈ live_roles s;
}.

#[global] Existing Instance fmstate_eqdec.

(* From fairneris.aneris_lang Require Import aneris_lang. *)

(* Lemma test (X: EnvModel aneris_lang) : Countable X.(lts_state _). *)
