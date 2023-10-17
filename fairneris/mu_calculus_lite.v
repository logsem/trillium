From stdpp Require Import option.
From fairneris Require Export inftraces.

Definition mu_pred (S L : Type) : Type := trace S L → Prop.

Section mu_defs.
  Context {S L : Type}.

  Notation mu_pred := (mu_pred S L).

  Definition trtail (tr : trace S L) : option (L * trace S L) :=
    match tr with
    | ⟨s⟩ => None
    | s -[ℓ]-> r => Some (ℓ,r)
    end.

  Definition mu_now (P : S → Prop) : mu_pred :=
    λ tr, P $ trfirst tr.
  Definition mu_box (P : L → Prop) (ϕ : mu_pred) : mu_pred := 
    λ tr, ∃ l tr', trtail tr = Some (l, tr') ∧ P l ∧ ϕ tr'.

  Definition mu_pred_mono (F : mu_pred → mu_pred) : Prop :=
    ∀ (ϕ ψ : mu_pred), (∀ tr, ϕ tr → ψ tr) → (∀ tr, F ϕ tr → F ψ tr).

  Definition mu_mu {A} (F : (A → Prop) → (A → Prop)) : (A → Prop) :=
    λ tr, ∃ (ϕ : (A → Prop)), (∀ tr, ϕ tr → F ϕ tr) ∧ ϕ tr.
  Definition mu_nu  {A} (F : (A → Prop) → (A → Prop)) : (A → Prop) :=
    λ tr, ∀ (ϕ : (A → Prop)), (∀ tr, F ϕ tr → ϕ tr) → ϕ tr.

  (* Definition mu_mu (F : mu_pred → mu_pred) : mu_pred := *)
  (*   λ tr, ∃ (ϕ : mu_pred), (∀ tr, ϕ tr → F ϕ tr) ∧ ϕ tr. *)
  (* Definition mu_nu (F : mu_pred → mu_pred) : mu_pred := *)
  (*   λ tr, ∀ (ϕ : mu_pred), (∀ tr, F ϕ tr → ϕ tr) → ϕ tr. *)

  Class MonoPred {A : Type} (F : (A → Prop) → (A → Prop)) := {
      mono_pred (Φ Ψ : A → Prop) : (∀ x, Φ x → Ψ x) → ∀ x, F Φ x → F Ψ x;
    }.
  
  Lemma least_fixpoint_unfold_2 {A} (F : (A → Prop) → (A → Prop)) `{!MonoPred F} x :
    F (mu_nu F) x → mu_nu F x.
  Proof using Type*.
    rewrite /mu_nu /=. intros HF ϕ Hincl.
    apply Hincl. eapply mono_pred; [|by apply HF].
    intros y H'. apply H'. apply Hincl.
  Qed.

  Lemma least_fixpoint_unfold_1 {A} (F : (A → Prop) → (A → Prop)) `{!MonoPred F} x :
    mu_nu F x → F (mu_nu F) x.
  Proof using Type*.
    intros HF. apply HF.
    intros y Hy. eapply mono_pred; [|by apply HF].
    intros z ?. by apply least_fixpoint_unfold_2.
  Qed.

  Corollary least_fixpoint_unfold {A} (F : (A → Prop) → (A → Prop)) `{!MonoPred F} x :
    mu_nu F x ↔ F (mu_nu F) x.
  Proof using Type*.
    split; [by apply least_fixpoint_unfold_1|by apply least_fixpoint_unfold_2].
  Qed.

End mu_defs.
