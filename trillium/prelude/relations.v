From Coq.Unicode Require Import Utf8.
From stdpp Require Import base tactics.

Notation rel A B := (A → B → Prop).

Definition rel_compose {A B C} (R : rel A B) (S : rel B C) : rel A C :=
  λ a c, ∃ b, R a b ∧ S b c.

#[global] Instance rel_equiv {A B} : Equiv (rel A B) := λ R1 R2, ∀ a b, R1 a b ↔ R2 a b.

Infix ">>" := rel_compose (at level 20, right associativity).

Lemma rel_compose_assoc {A B C D} (R : rel A B) (S : rel B C) (T : rel C D) :
  R >> (S >> T) ≡ (R >> S) >> T.
Proof. unfold rel_compose. intros a d; naive_solver. Qed.
