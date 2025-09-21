(* From stdpp Require Import option. *)
(* From Paco Require Import paco1 paco2 pacotac. *)
(* From trillium.fairness Require Export inftraces. *)

(* Record FairModel : Type := { *)
(*   fmstate:> Type; *)
(*   fmstate_eqdec: EqDecision fmstate; *)
(*   fmstate_inhabited: Inhabited fmstate; *)

(*   fmrole: Type; *)
(*   fmrole_eqdec: EqDecision fmrole; *)
(*   fmrole_countable: Countable fmrole; *)
(*   fmrole_inhabited: Inhabited fmrole; *)

(*   fmtrans: fmstate -> option fmrole -> fmstate -> Prop; *)

(*   live_roles: fmstate -> gset fmrole; *)
(*   fm_live_spec: forall s ρ s', fmtrans s (Some ρ) s' -> ρ ∈ live_roles s; *)
(* }. *)

(* #[global] Existing Instance fmrole_eqdec. *)
(* #[global] Existing Instance fmrole_countable. *)
(* #[global] Existing Instance fmrole_inhabited. *)
(* #[global] Existing Instance fmstate_inhabited. *)


(* Section model_traces. *)
(*   Context `{M: FairModel}. *)

(*   Definition role_enabled_model ρ (s: M) := ρ ∈ M.(live_roles) s. *)

(*   Definition fair_model_trace ρ (mtr: mtrace M): Prop  := *)
(*     forall n, pred_at mtr n (λ δ _, role_enabled_model ρ δ) -> *)
(*          ∃ m, pred_at mtr (n+m) (λ δ _, ¬role_enabled_model ρ δ) *)
(*               ∨ pred_at mtr (n+m) (λ _ ℓ, ℓ = Some (Some ρ)). *)

(*   Lemma fair_model_trace_after ℓ tr tr' k: *)
(*     after k tr = Some tr' -> *)
(*     fair_model_trace ℓ tr -> fair_model_trace ℓ tr'. *)
(*   Proof. *)
(*     intros Haf Hf n Hp. *)
(*     have Hh:= Hf (k+n). *)
(*     have Hp': pred_at tr (k + n) (λ δ _, role_enabled_model ℓ δ). *)
(*     { rewrite (pred_at_sum _ k) Haf /= //. } *)
(*     have [m Hm] := Hh Hp'. exists m. *)
(*     by rewrite <- Nat.add_assoc, !(pred_at_sum _ k), Haf in Hm. *)
(*   Qed. *)

(*   Lemma fair_model_trace_cons ℓ δ ℓ' r: *)
(*     fair_model_trace ℓ (δ -[ℓ']-> r) -> fair_model_trace ℓ r. *)
(*   Proof. intros Hfm. by eapply (fair_model_trace_after ℓ _ r 1) =>//. Qed. *)

(*   Lemma fair_model_trace_cons_forall δ ℓ' r: *)
(*     (∀ ℓ, fair_model_trace ℓ (δ -[ℓ']-> r)) -> (∀ ℓ, fair_model_trace ℓ r). *)
(*   Proof. eauto using fair_model_trace_cons. Qed. *)

(*   Inductive mtrace_valid_ind (mtrace_valid_coind: mtrace M -> Prop) : *)
(*     mtrace M -> Prop := *)
(*   | mtrace_valid_singleton δ: mtrace_valid_ind _ ⟨δ⟩ *)
(*   | mtrace_valid_cons δ ℓ tr: *)
(*       fmtrans _ δ ℓ (trfirst tr) -> *)
(*       mtrace_valid_coind tr → *)
(*       mtrace_valid_ind _ (δ -[ℓ]-> tr). *)
(*   Definition mtrace_valid := paco1 mtrace_valid_ind bot1. *)

(*   Lemma mtrace_valid_mono : *)
(*     monotone1 mtrace_valid_ind. *)
(*   Proof. *)
(*     unfold monotone1. intros x0 r r' IN LE. *)
(*     induction IN; try (econstructor; eauto; done). *)
(*   Qed. *)
(*   Hint Resolve mtrace_valid_mono : paco. *)

(*   Lemma mtrace_valid_after (mtr mtr' : mtrace M) k : *)
(*     after k mtr = Some mtr' → mtrace_valid mtr → mtrace_valid mtr'. *)
(*   Proof. *)
(*     revert mtr mtr'. *)
(*     induction k; intros mtr mtr' Hafter Hvalid. *)
(*     { destruct mtr'; simpl in *; by simplify_eq. } *)
(*     punfold Hvalid. *)
(*     inversion Hvalid as [|??? Htrans Hval']; simplify_eq. *)
(*     eapply IHk; [done|]. *)
(*     by inversion Hval'. *)
(*   Qed. *)

(* End model_traces. *)

(* Global Hint Resolve fair_model_trace_cons: core. *)
(* Global Hint Resolve mtrace_valid_mono : paco. *)
