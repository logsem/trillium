From stdpp Require Import option countable.
From fairneris Require Export inftraces fairness ltl_lite.

Class GoodLang (Λ : language)
  `{Countable (config_label Λ), Inhabited (config_label Λ)}
  `{Countable (action Λ)}
  `{Countable (locale Λ)}
  := {}.



Record Lts lab `{Countable lab, Inhabited lab}: Type := {
  lts_state :> Type;
  lts_state_eqdec :: EqDecision lts_state;
  lts_state_inhabited :: Inhabited lts_state;

  lts_trans: lts_state → lab → lts_state → Prop;
}.


Arguments lts_state {_ _ _ _}.
Arguments lts_trans {_ _ _ _}.

Definition lts_trace {L} `{Countable L, Inhabited L} (LTS: Lts L) := trace LTS.(lts_state) L.
Definition lts_label {L} `{Countable L, Inhabited L} (LTS: Lts L) := L.

Section models.
Context (Λ: language).
Context `{GoodLang Λ}.

Record EnvModel := {
    env_lts :> Lts (action Λ + config_label Λ);
    env_states_match : cfg Λ → env_lts.(lts_state) → Prop;
    env_state_coh : state Λ → Prop;
    env_apply_trans : env_lts.(lts_state) → config_label Λ → env_lts.(lts_state);
    env_apply_trans_spec_trans : ∀ m1 m2 cl c1 c2,
      locale_step c1 (inr cl) c2 →
      env_states_match c1 m1 →
      env_apply_trans m1 cl = m2 →
      lts_trans env_lts m1 (inr cl) m2;
    env_apply_trans_spec_both : ∀ c1 m1 cl c2 m2,
      env_apply_trans m1 cl = m2 →
      locale_step c1 (inr cl) c2 →
      env_state_coh c1.2 →
      env_states_match c1 m1 →
      env_states_match c2 m2;
    env_match_internal_step : ∀ ζ c1 m c2,
      env_state_coh c1.2 →
      locale_step c1 (inl (ζ, None)) c2 →
      env_states_match c1 m →
      env_states_match c2 m;
    env_state_coh_preserved c1 c2 ζ :
      locale_step c1 ζ c2 →
      env_state_coh c1.2 →
      env_state_coh c2.2;
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

    usr_fl : usr_lts.(lts_state) → nat;
}.

Arguments usr_live_roles {_}.

Section user_fairness.
  Context `{M: UserModel}.

  Definition usr_trans_valid (mtr : lts_trace M) :=
     match mtr with
     | ⟨s⟩ => True
     | (s -[l]-> tr) => lts_trans _ s l (trfirst tr)
     end.

  Definition usr_trace_valid (mtr : lts_trace M) :=
    trace_always usr_trans_valid mtr.

  Definition usr_fair_scheduling_mtr (ρ : M.(usr_role)) : lts_trace M → Prop :=
    trace_always_eventually_implies_now
      (λ (δ: M) _, ρ ∈ usr_live_roles δ)
      (λ δ (ℓ : option (usr_role M * option (action Λ))), ρ ∉ usr_live_roles δ ∨ ∃ α, ℓ = Some (ρ, α)).

  Definition usr_fair_scheduling (mtr : lts_trace M) : Prop :=
    ∀ ρ, usr_fair_scheduling_mtr ρ mtr.

  (* Lemma eventually_my_step (P: M → Prop) (ρ : usr_role M) (mtr : lts_trace M): *)
  (*   usr_fair_scheduling mtr → *)
  (*   usr_trace_valid mtr → *)
  (*   (∀ s1 s2 ρ' l, ρ ≠ ρ' → lts_trans M s1 (ρ', l) s2 → P s1 → P s2) → *)
  (*   (↓ (λ s _, P s)) mtr → *)
  (*   (◊ ↓ (λ s l, match l with Some (ρ', _) => ρ' = ρ ∧ P s | None => False end)) mtr. *)
  (* Proof. Admitted. *)

  (* Lemma eventually_my_step_loop (s: M) (ρ : usr_role M) (mtr : lts_trace M): *)
  (*   usr_fair_scheduling mtr → *)
  (*   usr_trace_valid mtr → *)
  (*   (∀ s1 s2 ρ' l, ρ ≠ ρ' → lts_trans M s1 (ρ', l) s2 → s1 = s2) → *)
  (*   (↓ (λ s' _, s' = s)) mtr → *)
  (*   (◊ ↓ (λ s' l, match l with Some (ρ', _) => ρ' = ρ ∧ s' = s | None => False end)) mtr. *)
  (* Proof. *)
  (*   intros ?? Ht Hnow. apply (eventually_my_step (λ s', s' = s))=>//. *)
  (*   intros s1 s2 ρ' l Hneq Htrans <-. symmetry. eapply Ht=>//. *)
  (* Qed. *)
End user_fairness.

Inductive joint_trans {M: UserModel} {N: EnvModel} :
  (M * N) → ((usr_role M * option (action Λ)) + config_label Λ) → (M * N) → Prop :=
| UsrTrans n u1 u2 ρ : lts_trans M u1 (ρ, None) u2 → joint_trans (u1, n) (inl (ρ, None)) (u2, n)
| NetTrans u n1 n2 ℓ : lts_trans N n1 (inr ℓ) n2 → joint_trans (u, n1) (inr ℓ) (u, n2)
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
  fm_fl s := usr_fl _ s.1;

  (* We want somehting like: *)
  (* fmfairness tr := env_fairness _ tr; *)
  (* but it's not so easy, because this definition is not constructive... *)
  (* it may be easier to only state it on the joint model directly... *)
  fmfairness _ := True;
|}.
Next Obligation. by intros ??????; inversion 1; simplify_eq; eapply usr_live_spec. Qed.

End models.

Arguments usr_role {_ _ _}.
Arguments usr_lts {_ _ _}.
Arguments usr_fl {_ _ _ _}.
Arguments usr_live_roles {_ _ _ _}.
Arguments env_lts {_ _ _}.
Arguments env_states_match {_ _ _ _ _ _ _}.
Arguments env_state_coh {_ _ _ _ _ _ N} _ : rename.
Arguments env_state_coh_preserved {_ _ _ _ _ _ N} _ : rename.
Arguments joint_model {_ _ _ _ _ _}.
Arguments joint_trans {_ _ _ _ _ _}.
Arguments usr_trace_valid {_ _ _ _} _.
Arguments usr_fair_scheduling {_ _ _ _} _.
Arguments usr_fair_scheduling_mtr {_ _ _ _} _ _.
