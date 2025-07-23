From stdpp Require Import finite.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.bi.lib Require Import fixpoint.
From iris.base_logic.lib Require Import wsat later_credits.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Import quantifiers iris_extraction finitary classical_instances.
From trillium.program_logic Require Export weakestpre traces.

Set Default Proof Using "Type".
Import uPred.

(* TODO: move *)
Lemma step_tp_length {Λ} c c' oζ:
  locale_step (Λ := Λ) c oζ c' → length c.1 ≤ length c'.1.
Proof.
  inversion 1; simplify_eq; last done.
  rewrite !app_length /= !app_length; lia.
Qed.

Lemma valid_exec_length {Λ} ex (tp1 tp2 : list $ expr Λ) σ1 σ2:
  valid_exec ex ->
  trace_starts_in ex (tp1, σ1) ->
  trace_ends_in ex (tp2, σ2) ->
  length tp1 ≤ length tp2.
Proof.
    revert σ1 σ2 tp1 tp2. induction ex as [| ex IH oζ c']; intros σ1 σ2 tp1 tp2.
    - intros ? -> Heq. inversion Heq; simplify_eq; done.
    - intros Hval Hstarts Hends.
      inversion Hval as [A B|A [tp' σ'] C D E Hstep]. simplify_eq.
      etransitivity; first eapply IH =>//.
      pose proof (step_tp_length _ _ _ Hstep) as Hlen. simpl in *.
      rewrite ->Hends in Hlen. simpl in Hlen. lia.
Qed.

(* Notation posts_of t Φs := *)
(*   ([∗ list] vΦ ∈ *)
(*     (omap (λ x, (λ v, (v, x.2)) <$> to_val x.1) *)
(*           (zip_with (λ x y, (x, y)) t Φs)), vΦ.2 vΦ.1)%I. *)
Definition posts_of {Λ: language} {Σ: gFunctors} (t: list (expr Λ)) (Φs: list (val Λ -> iProp Σ)): iProp Σ :=
  ([∗ list] vΦ ∈
    (omap (λ x, (λ v, (v, x.2)) <$> to_val x.1)
          (zip_with (λ x y, (x, y)) t Φs)), vΦ.2 vΦ.1)%I.

Lemma posts_of_app {Λ Σ} (t1 t2: list (language.expr Λ)) (Φs1 Φs2: list (val Λ -> iProp Σ))
  (MATCH1: length t1 = length Φs1):
  posts_of t1 Φs1 ∗ posts_of t2 Φs2 ⊣⊢ posts_of (t1 ++ t2) (Φs1 ++ Φs2).
Proof using.
  rewrite /posts_of.
  rewrite zip_with_app; [| done].
  rewrite omap_app. rewrite big_sepL_app. done.
Qed.

Lemma zip_with_cons_both {A B C: Type} (F: A -> B -> C) a b (la: list A) (lb: list B):
  zip_with F (a :: la) (b :: lb) = F a b :: zip_with F la lb.
Proof using. done. Qed.

Lemma posts_of_cons {Λ Σ} e (t: list (language.expr Λ)) Φ (Φs: list (val Λ -> iProp Σ)):
  from_option Φ ⌜ True ⌝ (to_val e) ∗ posts_of t Φs ⊣⊢ posts_of (e :: t) (Φ :: Φs).
Proof using.
  rewrite /posts_of. rewrite zip_with_cons_both.
  rewrite (omap_app _ [(e, Φ)]). rewrite big_sepL_app.
  iApply sep_proper; [| done].
  simpl. destruct (to_val e); try set_solver.
  simpl. by rewrite sep_emp.
Qed.

Notation locales_equiv_from t0 t0' t1 t1' :=
  (Forall2 (λ '(t, e) '(t', e'), locale_of t e = locale_of t' e')
           (prefixes_from t0 t1) (prefixes_from t0' t1')).

Section locales_helpers.
  Context {Λ: language}.

  Lemma locales_equiv_from_app (t0 t0' t1 t1' t2 t2': list (expr Λ)):
    locales_equiv_from t0 t0' t1 t1' ->
    locales_equiv_from (t0 ++ t1) (t0' ++ t1') t2 t2' ->
    locales_equiv_from t0 t0' (t1 ++ t2) (t1' ++ t2').
  Proof.
    revert t0 t0' t1 t2 t2'. induction t1' ; intros t0 t0' t1 t2 t2' Hequiv1 Hequiv2.
    - destruct t1; last by apply Forall2_cons_nil_inv in Hequiv1. simpl.
      clear Hequiv1. revert t0 t0' t2 Hequiv2; induction t2'; intros t0 t0' t2 Hequiv2.
      + destruct t2; last by apply Forall2_cons_nil_inv in Hequiv2. constructor.
      + destruct t2; first by inversion Hequiv2.
        rewrite !(right_id_L [] (++)) // in Hequiv2.
    - destruct t1; first by inversion Hequiv1.
      replace ((e :: t1) ++ t2) with (e :: (t1 ++ t2)); last by list_simplifier.
      replace ((a :: t1') ++ t2') with (a :: (t1' ++ t2')); last by list_simplifier.
      simpl. constructor.
      + inversion Hequiv1 =>//.
      + apply IHt1'.
        * inversion Hequiv1 =>//.
        * by list_simplifier.
  Qed.

  Lemma prefixes_from_length {A} (t0 t1: list A):
    length (prefixes_from t0 t1) = length t1.
  Proof. revert t0; induction t1; intros ?; [done|]; rewrite /= IHt1 //. Qed.

  Lemma locales_equiv_from_impl (t0 t0' t1 t1' t2 t2': list (expr Λ)):
    length t2 = length t2' ->
    locales_equiv_from t0 t0' (t1 ++ t2) (t1' ++ t2') ->
    locales_equiv_from (t0 ++ t1) (t0' ++ t1') t2 t2'.
  Proof.
    revert t0 t0' t1 t1' t2. induction t2'; intros t0 t0' t1 t1' t2 Hlen Hequiv.
    - destruct t2 ; simpl in *; done.
    - destruct t2; first done.
      revert e a t0 t0' t1 t2' t2 IHt2' Hlen Hequiv. induction t1'; intros x y t0 t0' t1 t2' t2 IHt2' Hlen Hequiv.
      + destruct t1; first by simpl; constructor; list_simplifier.
        apply Forall2_length in Hequiv. rewrite !prefixes_from_length app_length /= in Hequiv.
        simpl in Hlen. lia.
      + destruct t1.
        { apply Forall2_length in Hequiv. rewrite !prefixes_from_length !app_length /= in Hequiv.
          simpl in Hlen. lia. }
        assert (H: locales_equiv_from (t0 ++ e :: t1) (t0' ++ a :: t1')
                    (x :: t2) (y :: t2')).
        { replace (t0 ++ e :: t1) with ((t0 ++ [e]) ++ t1); last by list_simplifier.
          replace (t0' ++ a :: t1') with ((t0' ++ [a]) ++ t1'); last by list_simplifier.
          apply IHt1' =>//.
          by list_simplifier. }
        simpl; constructor; [inversion H =>// |].
        apply IHt2'; first by simpl in Hlen; lia. done.
  Qed.

  Lemma locales_equiv_from_refl (t0 t0' t: list (expr Λ)):
    locales_equiv t0 t0' ->
    locales_equiv_from t0 t0' t t.
  Proof.
    revert t0 t0'; induction t; intros t0 t0' H; simpl; constructor =>//.
    { apply locale_equiv =>//. }
    apply IHt. apply locales_equiv_from_app =>//. simpl.
    constructor; [ by apply locale_equiv | done].
  Qed.

  Lemma locales_equiv_refl (t: list (expr Λ)):
    locales_equiv t t.
  Proof. apply locales_equiv_from_refl. constructor. Qed.

  Lemma locales_equiv_snoc t0 t0' (e e' : expr Λ) t1 t1':
    locales_equiv t0 t0' ->
    locales_equiv_from t0 t0' t1 t1' ->
    locale_of (t0 ++ t1) e = locale_of (t0' ++ t1') e' ->
    locales_equiv_from t0 t0' (t1 ++ [e]) (t1' ++ [e']).
  Proof.
    intros ???.
    apply locales_equiv_from_app =>//.
    simpl. by constructor.
  Qed.

  Lemma locales_equiv_snoc_same t0 (e e' : expr Λ) t1:
    locale_of (t0 ++ t1) e = locale_of (t0 ++ t1) e' ->
    locales_equiv_from t0 t0 (t1 ++ [e]) (t1 ++ [e']).
  Proof.
    intros ?. apply locales_equiv_snoc =>//; apply locales_equiv_from_refl; apply locales_equiv_refl.
  Qed.

  Lemma locales_equiv_from_middle t0 (e e' : expr Λ) t1 t2:
    locale_of (t0 ++ t1) e = locale_of (t0 ++ t1) e' ->
    locales_equiv_from t0 t0 (t1 ++ e :: t2) (t1 ++ e' :: t2).
  Proof.
    intros ?.
    apply locales_equiv_from_app.
    - apply locales_equiv_from_refl. apply locales_equiv_refl.
    - simpl. constructor; first done.
      apply locales_equiv_from_impl =>//=.
      constructor =>//. apply locales_equiv_from_refl.
      apply locales_equiv_snoc_same. by list_simplifier.
  Qed.

  Lemma locales_equiv_middle (e e' : expr Λ) t1 t2:
    locale_of t1 e = locale_of t1 e' ->
    locales_equiv (t1 ++ e :: t2) (t1 ++ e' :: t2).
  Proof.
    intros ?. apply locales_equiv_from_middle.
    by list_simplifier.
  Qed.

  Lemma locale_step_equiv (c c' : cfg Λ) oζ:
    locale_step c oζ c' ->
    locales_equiv c.1 (take (length c.1) c'.1).
  Proof.
    intros H. inversion H as [? ? e1 ? e2 ? efs t1 t2|]; simplify_eq; simpl.
    - replace (t1 ++ e2 :: t2 ++ efs) with ((t1 ++ e2 :: t2) ++ efs); last by list_simplifier.
      replace (length (t1 ++ e1 :: t2)) with (length (t1 ++ e2 :: t2)); last first.
      { rewrite !app_length //=. }
      rewrite take_app_length. apply locales_equiv_middle.
      eapply locale_step_preserve =>//.
    - rewrite take_ge =>//. apply locales_equiv_refl.
  Qed.

  Lemma locales_equiv_from_take (t0 t0' t1 t1' : list $ expr Λ) n:
    locales_equiv_from t0 t0' t1 t1' ->
    locales_equiv_from t0 t0' (take n t1) (take n t1').
  Proof.
    revert t0 t0' t1 t1'. induction n as [|n IHn]; intros t0 t0' t1 t1' Hequiv; first constructor.
    destruct t1 as [|e1 t1]; destruct t1' as [|e1' t1']; try by inversion Hequiv.
    simpl. constructor; first by inversion Hequiv.
    apply IHn. by inversion Hequiv.
  Qed.

  Lemma locales_equiv_take (t1 t2 : list $ expr Λ) n:
    locales_equiv t1 t2 ->
    locales_equiv (take n t1) (take n t2).
  Proof. apply locales_equiv_from_take. Qed.

  Lemma locales_equiv_from_transitive (s1 s2 s3 t1 t2 t3 : list $ expr Λ):
    locales_equiv s1 s2 ->
    locales_equiv s2 s3 ->
    locales_equiv_from s1 s2 t1 t2 ->
    locales_equiv_from s2 s3 t2 t3 ->
    locales_equiv_from s1 s3 t1 t3.
  Proof.
    revert s1 s2 s3 t1 t2. induction t3 as [|e3 t3] ; intros s1 s2 s3 t1 t2 Hpref1 Hpref2 Hequiv1 Hequiv2;
      destruct t2 as [|e2 t2]; try by inversion Hequiv2; simplify_eq.
    destruct t1 as [|e1 t1]; try by inversion Hequiv1; simplify_eq.
    simpl; constructor; first by etransitivity; [inversion Hequiv1 | inversion Hequiv2].
    eapply (IHt3 _ (s2 ++ [e2]) _ _ t2).
    - inversion Hequiv1; simplify_eq =>//. by apply locales_equiv_snoc =>//.
    - inversion Hequiv2; simplify_eq =>//. by apply locales_equiv_snoc =>//.
    - inversion Hequiv1 =>//.
    - inversion Hequiv2 => //.
  Qed.

  Lemma locales_equiv_transitive (t1 t2 t3 : list $ expr Λ):
    locales_equiv t1 t2 ->
    locales_equiv t2 t3 ->
    locales_equiv t1 t3.
  Proof. apply locales_equiv_from_transitive; constructor. Qed.

  Lemma locale_valid_exec ex (tp1 tp2 : list $ expr Λ) σ1 σ2:
    valid_exec ex ->
    trace_starts_in ex (tp1, σ1) ->
    trace_ends_in ex (tp2, σ2) ->
    locales_equiv tp1 (take (length tp1) tp2).
  Proof.
    revert σ1 σ2 tp1 tp2. induction ex as [| ex IH oζ c']; intros σ1 σ2 tp1 tp2.
    - intros ? -> Heq. inversion Heq; simplify_eq.
      rewrite take_ge //. apply locales_equiv_refl.
    - intros Hval Hstarts Hends.
      inversion Hval as [A B|A [tp' σ'] C D E Hstep]. simplify_eq.
      eapply locales_equiv_transitive.
      eapply IH =>//.
      pose proof (locale_step_equiv _ _ _ Hstep) as Hequiv.
      rewrite /trace_ends_in /trace_last in Hends.
      rewrite Hends in Hequiv.
      apply (locales_equiv_take _ _ (length tp1)) in Hequiv.
      rewrite take_take in Hequiv.
      assert (length tp1 ≤ length tp').
      { eapply (valid_exec_length ex ) =>//. }
      simpl in Hequiv.
      replace (length tp1 `min` length tp') with (length tp1) in Hequiv;
        [done|lia].
  Qed.

End locales_helpers.

Section from_locale.
  Context {Λ: language}.
  Context `{ EqDecision (locale Λ)}.

  Fixpoint from_locale_from tp0 tp ζ :=
    match tp with
    | [] => None
    | e::tp' => if decide (locale_of tp0 e = ζ) then Some e else from_locale_from (tp0 ++ [e]) tp' ζ
    end.

  Definition from_locale tp ζ := from_locale_from [] tp ζ.

  (* Other possibility is:
  Definition from_locale tp ζ := list_find (λ '(tp, e), locale_of tp e = ζ) (prefixes tp).*)

  Lemma from_locale_from_Some_app tp0 tp tp' ζ e :
    from_locale_from tp0 tp ζ = Some e ->
    from_locale_from tp0 (tp ++ tp') ζ = Some e.
  Proof.
    revert tp0 tp'. induction tp as [|e' tp IH]; first by list_simplifier.
    simpl. intros tp0 tp' Hfl.
    destruct (decide (locale_of tp0 e' = ζ)) =>//.
    apply IH =>//.
  Qed.

  Lemma from_locale_from_is_Some_app tp0 tp tp' ζ :
    is_Some (from_locale_from tp0 tp ζ) ->
    is_Some (from_locale_from tp0 (tp ++ tp') ζ).
  Proof.
    intros [? HS]. eapply from_locale_from_Some_app in HS. eauto.
  Qed.

  Lemma from_locale_from_equiv tp0 tp0' tp tp' ζ :
    locales_equiv tp0 tp0' ->
    locales_equiv_from tp0 tp0' tp tp' ->
    is_Some (from_locale_from tp0 tp ζ) ->
    is_Some (from_locale_from tp0' tp' ζ).
  Proof.
    revert tp0 tp0' tp'. induction tp as [|e tp IH]; intros tp0 tp0' tp' Heq0 Heq [eζ Heζ];
      destruct tp' as [|e' tp']; try by apply Forall2_length in Heq.
    simpl in *.
    destruct (decide (locale_of tp0 e' = ζ)).
    - rewrite decide_True //; eauto. erewrite <-locale_equiv =>//.
    - rewrite decide_False; last by erewrite <-locale_equiv.
      apply Forall2_cons_1 in Heq as [Hlocs ?].
      rewrite decide_False // in Heζ; last by erewrite Hlocs, <-locale_equiv =>//.
      apply (IH (tp0 ++ [e])); eauto.
      apply locales_equiv_snoc =>//.
  Qed.

  Lemma from_locale_step tp1 tp2 ζ oζ σ1 σ2 :
    locale_step (tp1, σ1) oζ (tp2, σ2) →
    is_Some(from_locale tp1 ζ) →
    is_Some(from_locale tp2 ζ).
  Proof.
    intros Hstep. inversion Hstep; simplify_eq=>//.
    intros HiS. replace (t1 ++ e2 :: t2 ++ efs) with ((t1 ++ e2 :: t2) ++ efs);
                  last by list_simplifier.
    apply from_locale_from_is_Some_app.
    eapply from_locale_from_equiv; eauto; [constructor|].
    apply locales_equiv_from_middle. list_simplifier. by eapply locale_step_preserve.
  Qed.

  Lemma from_locale_from_Some tp0 tp1 tp e :
    (tp, e) ∈ prefixes_from tp0 tp1 →
    from_locale_from tp0 tp1 (locale_of tp e) = Some e.
  Proof.
    revert tp0 tp e; induction tp1 as [| e1 tp1 IH]; intros tp0 tp e Hin; first set_solver.
    apply elem_of_cons in Hin as [Heq|Hin].
    { simplify_eq. rewrite /= decide_True //. }
    rewrite /= decide_False; first by apply IH.
    fold (prefixes_from (A := expr Λ)) in Hin.
    by eapply locale_injective.
  Qed.

End from_locale.

(* TODO: Move *)
Lemma Forall2_eq {A B} (f : A → B) xs ys :
  Forall2 (λ x y, f x = f y) xs ys ↔ f <$> xs = f <$> ys.
Proof.
  split.
  - revert ys.
    induction xs as [|x xs IHxs]; intros ys Hforall.
    { eapply Forall2_nil_inv_l in Hforall. by simplify_eq. }
    destruct ys as [|y ys].
    { by apply Forall2_cons_nil_inv in Hforall. }
    apply Forall2_cons_1 in Hforall as [Hf Hforall]=> /=.
    f_equiv; [done|by apply IHxs].
  - revert ys.
    induction xs as [|x xs IHxs]; intros ys Hf.
    { rewrite fmap_nil comm in Hf. eapply fmap_nil_inv in Hf. by simplify_eq. }
    rewrite fmap_cons comm in Hf.
    apply fmap_cons_inv in Hf as (y & ys' & Hfxy & Hf & ->).
    apply Forall2_cons. split; [done|by apply IHxs].
Qed.

Section locales_utils.
  Context {Λ: language}.

  Definition locales_of_list_from tp0 (tp: list $ expr Λ): list $ locale Λ :=
    (λ '(t, e), locale_of t e) <$> (prefixes_from tp0 tp).
  Notation locales_of_list tp := (locales_of_list_from [] tp).

  Lemma locales_of_list_from_cons es' (e : expr Λ) es :
    locales_of_list_from es' (e :: es) =
    locale_of es' e :: locales_of_list_from (es' ++ [e]) es.
  Proof. done. Qed.

  Lemma locales_of_list_equiv (tp0 tp0' tp1 tp2 : list $ expr Λ) :
    locales_equiv_from tp0 tp0' tp1 tp2 ↔
    locales_of_list_from tp0 tp1 = locales_of_list_from tp0' tp2.
  Proof.
    split; intros Heq.
    - apply (Forall2_impl _ (λ x y, uncurry locale_of x = uncurry locale_of y))
        in Heq; [|by intros [] [] HP].
      by rewrite Forall2_eq in Heq.
    - apply (Forall2_impl (λ x y, uncurry locale_of x = uncurry locale_of y));
        [|by intros [] [] HP].
      by rewrite Forall2_eq.
  Qed.

  Lemma locales_of_list_step_incl σ1 σ2 oζ tp1 tp2 :
    locale_step (tp1, σ1) oζ (tp2, σ2) ->
    locales_of_list tp1 ⊆ locales_of_list tp2.
  Proof.
    intros H. inversion H; simplify_eq=>//.
    replace (t1 ++ e2 :: t2 ++ efs) with ((t1 ++ e2 :: t2) ++ efs); last by list_simplifier.
    rewrite /locales_of_list_from. rewrite [in X in _ ⊆ X]prefixes_from_app /= fmap_app.
    assert ((λ '(t, e), locale_of t e) <$> prefixes (t1 ++ e1 :: t2) = (λ '(t, e), locale_of t e) <$> prefixes (t1 ++ e2 :: t2))
      as ->; last set_solver.
    apply locales_of_list_equiv, locales_equiv_middle. by eapply locale_step_preserve.
  Qed.

  Lemma locales_of_list_from_locale_from `{EqDecision (locale Λ)} tp0 tp1 ζ:
    is_Some (from_locale_from tp0 tp1 ζ) ->
    ζ ∈ locales_of_list_from tp0 tp1.
  Proof.
    revert tp0; induction tp1 as [|e1 tp1 IH]; intros tp0.
    { simpl. intros H. inversion H. congruence. }
    simpl. intros [e Hsome]. rewrite /locales_of_list_from /=.
    destruct (decide (locale_of tp0 e1 = ζ)); simplify_eq; first set_solver.
    apply elem_of_cons; right. apply IH. eauto.
  Qed.

  Definition locales_equiv_prefix_from {Λ} (tp0 tp1 tp2 : list $ expr Λ) :=
    locales_equiv_from tp0 tp0 tp1 (take (length tp1) tp2).
  Notation locales_equiv_prefix tp1 tp2 := (locales_equiv_prefix_from [] tp1 tp2).

  Lemma locales_equiv_from_length (tp0 tp0' tp1 tp2 : list $ expr Λ) :
    locales_equiv_from tp0 tp0' tp1 tp2 → length tp1 = length tp2.
  Proof. intros Heq%Forall2_length. by rewrite !prefixes_from_length in Heq. Qed.

  Lemma locales_equiv_prefix_from_length (tp0 tp1 tp2 : list $ expr Λ) :
    locales_equiv_prefix_from tp0 tp1 tp2 → length tp1 ≤ length tp2.
  Proof.
    rewrite /locales_equiv_prefix_from.
    intros ->%locales_equiv_from_length.
    revert tp2. induction tp1; [simpl; lia|].
    destruct tp2; [done|by apply le_n_S].
  Qed.

  Lemma locales_equiv_prefix_from_trans (tp0 tp1 tp2 tp3 : list $ expr Λ) :
    locales_equiv_prefix_from tp0 tp1 tp2 →
    locales_equiv_prefix_from tp0 tp2 tp3 →
    locales_equiv_prefix_from tp0 tp1 tp3.
  Proof.
    rewrite /locales_equiv_prefix_from. intros.
    assert (length tp1 ≤ length tp2);
      [by eapply locales_equiv_prefix_from_length|].
    eapply locales_equiv_from_transitive;
      [apply locales_equiv_refl..|done|].
    assert (length tp1 = length tp1 `min` length tp2) as Heq by lia.
    rewrite {2}Heq -take_take. by apply locales_equiv_from_take.
  Qed.

  Lemma locales_equiv_prefix_trans (tp1 tp2 tp3 : list $ expr Λ) :
    locales_equiv_prefix tp1 tp2 →
    locales_equiv_prefix tp2 tp3 →
    locales_equiv_prefix tp1 tp3.
  Proof. intros. by eapply locales_equiv_prefix_from_trans. Qed.

  Lemma locales_equiv_from_comm (tp0 tp0' tp1 tp2 : list $ expr Λ) :
    locales_equiv_from tp0 tp0' tp1 tp2 →
    locales_equiv_from tp0' tp0 tp2 tp1.
  Proof. by rewrite !locales_of_list_equiv. Qed.

  Lemma locales_equiv_from_locale_of (tp0 tp0' tp1 tp2 tp3 : list $ expr Λ) :
    locales_equiv tp0 tp0' →
    locales_equiv_from tp0 tp1 tp2 tp3 ↔
    locales_equiv_from tp0' tp1 tp2 tp3.
  Proof.
    rewrite !locales_of_list_equiv. intros Heq.
    split.
    - intros <-.
      rewrite -locales_of_list_equiv.
      rewrite -locales_of_list_equiv in Heq.
      apply locales_equiv_from_refl.
      by apply locales_equiv_from_comm.
    - intros <-.
      rewrite -locales_of_list_equiv.
      rewrite -locales_of_list_equiv in Heq.
      by apply locales_equiv_from_refl.
  Qed.

  Lemma locales_equiv_prefix_from_drop (tp0 tp1 tp2 : list $ expr Λ) :
    locales_equiv_prefix_from tp0 tp1 tp2 →
    locales_equiv_from tp0 tp0 tp2 (tp1 ++ (drop (length tp1) tp2)).
  Proof.
    revert tp0 tp2.
    induction tp1 as [|e1 tp1 IHtp1]; intros tp0 tp2 Heq.
    { by rewrite /locales_equiv_prefix_from !locales_of_list_equiv. }
    destruct tp2 as [|e2 tp2].
    { by rewrite /locales_equiv_prefix_from !locales_of_list_equiv
        /locales_of_list_from in Heq. }
    rewrite /locales_equiv_prefix_from !locales_of_list_equiv
      /locales_of_list_from in Heq.
    rewrite /locales_of_list_from=> /=.
    inversion Heq as [[Hlocale Htail]].
    f_equiv; [done|].
    rewrite /locales_of_list_from in IHtp1.
    eapply (locales_equiv_from_locale_of _ (tp0 ++ [e1])).
    { apply locales_equiv_from_app;
        [by apply locales_equiv_refl|by apply Forall2_cons]. }
    apply IHtp1, locales_equiv_from_comm.
    apply (locales_equiv_from_locale_of (tp0 ++ [e1]) (tp0 ++ [e2])).
    { apply locales_equiv_from_app;
        [by apply locales_equiv_refl|by apply Forall2_cons]. }
    apply locales_equiv_from_comm.
    rewrite /locales_equiv_prefix_from locales_of_list_equiv
            /locales_of_list_from.
    by apply Htail.
  Qed.

  Lemma locales_equiv_from_drop (t0 t1 t2 t2' : list $ expr Λ) :
    locales_equiv_prefix_from t0 t1 t2 →
    locales_equiv_prefix_from t0 t1 t2' →
    locales_equiv_from t0 t0 t2 t2' →
    locales_equiv_from (t0++t1) (t0++t1) (drop (length t1) t2) (drop (length t1) t2').
  Proof.
    intros Hprefix1 Hprefix2 Hequiv.
    apply locales_equiv_from_impl.
    { apply Forall2_length in Hequiv. rewrite !prefixes_from_length in Hequiv.
      by rewrite !skipn_length Hequiv. }
    apply locales_equiv_prefix_from_drop in Hprefix1.
    apply locales_equiv_prefix_from_drop in Hprefix2.
    apply locales_equiv_from_comm in Hprefix1.
    assert (locales_equiv_from t0 t0 (t1 ++ drop (length t1) t2) t2').
    { eapply locales_equiv_from_transitive.
      - apply locales_equiv_refl.
      - apply locales_equiv_refl.
      - apply Hprefix1.
      - apply Hequiv. }
    assert (locales_equiv_from t0 t0 (t1 ++ drop (length t1) t2) (t1 ++ drop (length t1) t2')).
    { eapply locales_equiv_from_transitive.
      - apply locales_equiv_refl.
      - apply locales_equiv_refl.
      - apply H.
      - apply Hprefix2. }
    done.
  Qed.

  (* TODO: Find an alternative to this. Used to resolve coercions. *)
  Lemma fmap_fmap : forall (A B C:Type)(f:A->B)(g:B->C) (l : list A),
    g <$> (f <$> l) = (fun x => g (f x)) <$> l.
  Proof. apply map_map. Qed.

  (* TODO: this can likely be removed by redefining [locale_of]
   to take one argument *)
  Lemma locales_of_list_from_fork_post `{!irisG Λ M Σ}
        (xs ys : list ((list $ expr Λ) * (expr Λ))) :
    (λ '(t,e), locale_of t e) <$> xs =
    (λ '(t,e), locale_of t e) <$> ys →
    (λ '(t,e) v, fork_post (locale_of t e) v) <$> xs =
    (λ '(t,e) v, fork_post (locale_of t e) v) <$> ys.
  Proof.
    intros.
    set f := locale_of.
    set g := (λ ζ, λ v, flip weakestpre.fork_post v ζ).
    assert (∀ (xs : list ((list $ expr Λ) * (expr Λ))),
              g <$> ((λ '(x,y), f x y) <$> xs) =
              ((λ '(x,y), g (f x y)) <$> xs)) as Hmap.
    { intros. rewrite fmap_fmap. f_equiv. apply FunExt. by intros []. }
    rewrite /f /g in Hmap. rewrite -!Hmap. clear Hmap. by f_equiv.
  Qed.

  Lemma locales_equiv_prefix_from_drop_alt (tp0 tp1 tp2 : list $ expr Λ) :
    locales_equiv_prefix_from tp0 tp1 tp2 →
    (λ '(t, e), locale_of t e) <$> prefixes_from (tp0 ++ tp1) (drop (length tp1) tp2) =
    drop (length tp1) ((λ '(t, e), locale_of t e) <$> prefixes_from tp0 tp2).
  Proof.
    revert tp0 tp2.
    induction tp1; intros tp0 tp2 Hprefix; [by rewrite right_id|].
    destruct tp2; [done|].
    rewrite /locales_equiv_prefix_from in Hprefix. simpl in *.
    apply Forall2_cons in Hprefix as [Hlocale Hprefix].
    rewrite -IHtp1; last first.
    { eapply locales_equiv_from_locale_of;
        [by apply locales_equiv_snoc_same|done]. }
    rewrite -locales_of_list_equiv.
    eapply locales_equiv_from_locale_of;
      [|apply locales_equiv_from_refl, locales_equiv_refl].
    rewrite -assoc. by eapply locales_equiv_middle.
  Qed.

  Lemma locales_equiv_prefix_drop_alt (tp0 tp1 : list $ expr Λ) :
    locales_equiv_prefix tp0 tp1 →
    (λ '(t, e), locale_of t e) <$> prefixes_from tp0 (drop (length tp0) tp1) =
    drop (length tp0) ((λ '(t, e), locale_of t e) <$> prefixes tp1).
  Proof. apply (locales_equiv_prefix_from_drop_alt []). Qed.

End locales_utils.
Notation locales_of_list tp := (locales_of_list_from [] tp).
Notation locales_equiv_prefix tp1 tp2 := (locales_equiv_prefix_from [] tp1 tp2).

Section adequacy_helper_lemmas.
  Context `{!irisG Λ M Σ}.

  Lemma wp_ctx_take_step s Φ ex atr tp1 K e1 tp2 σ1 e2 σ2 efs ζ:
    let (E1, E2) := (ectx_fill K e1, ectx_fill K e2) in
    valid_exec ex →
    prim_step e1 σ1 e2 σ2 efs →
    trace_ends_in ex (tp1 ++ E1 :: tp2, σ1) →
    locale_of tp1 E1 = ζ ->
    state_interp ex atr -∗
    WP e1 @ s; ζ; ⊤ {{ v, Φ v } } ={⊤,∅}=∗ |={∅}▷=>^(S $ trace_length ex)
                                             |={∅,⊤}=>
    ∃ δ' ℓ,
      state_interp (trace_extend ex (Some ζ) (tp1 ++ E2 :: tp2 ++ efs, σ2))
                   (trace_extend atr ℓ δ') ∗
      WP e2 @ s; ζ; ⊤ {{ v, Φ v } } ∗
      ([∗ list] i↦ef ∈ efs,
        WP ef @ s; locale_of (tp1 ++ E1 :: tp2 ++ take i efs) ef; ⊤
        {{ v, fork_post (locale_of (tp1 ++ E1 :: tp2 ++ take i efs) ef) v }}).
  Proof.
    iIntros (Hex Hstp Hei Hlocale) "HSI Hwp".
    rewrite wp_unfold /wp_pre.
    destruct (to_val e1) eqn:He1.
    { erewrite val_stuck in He1; done. }
    iMod ("Hwp" $! _ _ K with "[//] [] [] HSI") as "[Hs Hwp]".
    1, 2: done. 
    iDestruct ("Hwp" with "[]") as "Hwp"; first done.
    iModIntro.
    iApply (step_fupdN_wand with "[Hwp]"); first by iApply "Hwp".
    iIntros "Hwp".
    (* rewrite !ectx_fill_emp. *)
    iMod "Hwp" as (δ' ℓ) "(? & ? & ?)".
    iModIntro; iExists _, _; iFrame; done.
  Qed.    


  Lemma wp_take_step s Φ ex atr tp1 e1 tp2 σ1 e2 σ2 efs ζ:
    valid_exec ex →
    prim_step e1 σ1 e2 σ2 efs →
    trace_ends_in ex (tp1 ++ e1 :: tp2, σ1) →
    locale_of tp1 e1 = ζ ->
    state_interp ex atr -∗
    WP e1 @ s; ζ; ⊤ {{ v, Φ v } } ={⊤,∅}=∗ |={∅}▷=>^(S $ trace_length ex)
                                             |={∅,⊤}=>
    ∃ δ' ℓ,
      state_interp (trace_extend ex (Some ζ) (tp1 ++ e2 :: tp2 ++ efs, σ2))
                   (trace_extend atr ℓ δ') ∗
      WP e2 @ s; ζ; ⊤ {{ v, Φ v } } ∗
      ([∗ list] i↦ef ∈ efs,
        WP ef @ s; locale_of (tp1 ++ e1 :: tp2 ++ take i efs) ef; ⊤
        {{ v, fork_post (locale_of (tp1 ++ e1 :: tp2 ++ take i efs) ef) v }}).
  Proof.
    iIntros "**".
    iPoseProof (wp_ctx_take_step _ _ _ _ _ ectx_emp with "[$] [$]") as "STEP".
    all: rewrite ?ectx_fill_emp; eauto.
  Qed.

  Lemma wp_not_stuck ex atr K tp1 tp2 σ e s Φ ζ :
    valid_exec ex →
    trace_ends_in ex (tp1 ++ ectx_fill K e :: tp2, σ) →
    locale_of tp1 e = ζ ->
    state_interp ex atr -∗
    WP e @ s; ζ; ⊤ {{ v, Φ v }} ={⊤}=∗
    state_interp ex atr ∗
    WP e @ s; ζ; ⊤ {{ v, Φ v }} ∗
    ⌜s = NotStuck → not_stuck e (trace_last ex).2⌝.
  Proof.
    iIntros (???) "HSI Hwp".
    rewrite /not_stuck assoc.
    iApply fupd_plain_keep_r; iFrame.
    iIntros "[HSI Hwp]".
    rewrite wp_unfold /wp_pre.
    destruct (to_val e) eqn:He.
    - iModIntro; iPureIntro; eauto.
    - iApply fupd_plain_mask.
      iMod ("Hwp" with "[] [] [] HSI") as "[Hs Hwp]"; [done| by erewrite locale_fill|done|].
      erewrite last_eq_trace_ends_in; last done; simpl.
      iModIntro; destruct s; [iDestruct "Hs" as %?|]; iPureIntro; by eauto.
  Qed.

  Lemma wp_of_val_post e s Φ ζ:
    WP e @ s; ζ; ⊤ {{ v, Φ v }} ={⊤}=∗
    from_option (λ v, |~{⊤}~| Φ v) True (to_val e) ∗
    (from_option (λ v, |~{⊤}~| Φ v) True (to_val e) -∗
     WP e @ s; ζ; ⊤ {{ v, Φ v }}).
  Proof.
    iIntros "Hwp".
    rewrite wp_unfold /wp_pre.
    destruct (to_val e) eqn:He; simpl.
    - iSplitL.
      + by iIntros "!>!>".
      + by iIntros "!> Hwp".
    - iModIntro.
      iSplit; first by iClear "Hwp".
      iIntros "_"; done.
  Qed.

  Definition newelems {A: Type} (t t': list A) := (drop (length t) t').
  Definition newposts t t' :=
    ((λ '(tnew, e), fork_post (locale_of tnew e)) <$>
        (prefixes_from t (newelems t t'))).

  Lemma newposts_locales_equiv_helper (t0 t0' t1 t1' t : list (expr Λ)):
    length t1 = length t1' ->
    locales_equiv t0 t0' ->
    (λ '(tnew, e0), fork_post (locale_of tnew e0)) <$>
        (prefixes_from t0 (newelems t1 t)) =
    (λ '(tnew, e0), fork_post (locale_of tnew e0)) <$>
        (prefixes_from t0' (newelems t1' t)).
  Proof.
    intros Hlen1 H.
    assert (Hlen2: length t0 = length t0').
    { apply Forall2_length in H. rewrite !prefixes_from_length // in H. }
    revert t0 t0' t1 t1' Hlen1 Hlen2 H. induction t; intros t0 t0' t1 t1' Hlen1 Hlen2 H.
    - rewrite /newelems. rewrite !drop_nil //.
    - destruct t1; destruct t1' =>//.
      + simpl; f_equal; first erewrite locale_equiv=> //.
        specialize (IHt (t0 ++ [a]) (t0' ++ [a]) _ _ Hlen1).
        simpl in IHt. rewrite /newelems in IHt. rewrite !drop_0 in IHt. apply IHt.
        * rewrite !app_length. lia.
        * apply locales_equiv_snoc =>//. list_simplifier. apply locale_equiv =>//.
      + simpl. apply IHt =>//. simpl in Hlen1. lia.
  Qed.

  Lemma forkposts_locales_equiv (t0 t0' t1 t1' : list (expr Λ)):
    locales_equiv_from t0 t0' t1 t1' ->
    (λ '(tnew, e0), fork_post (locale_of tnew e0)) <$>
        (prefixes_from t0 t1) =
    (λ '(tnew, e0), fork_post (locale_of tnew e0)) <$>
        (prefixes_from t0' t1').
  Proof.
    intros H.
    revert t0 t0' t1' H. induction t1; intros t0 t0' t1' H.
    - destruct t1' =>//. inversion H.
    - destruct t1' =>//; first inversion H.
      inversion H; simplify_eq.
      simpl; f_equal; first by f_equal.
      by apply IHt1.
  Qed.

  Lemma newposts_locales_equiv t0 t0' t:
    locales_equiv t0 t0' ->
    newposts t0 t = newposts t0' t.
  Proof.
    intros H; apply newposts_locales_equiv_helper =>//.
    eapply Forall2_length in H. rewrite !prefixes_from_length // in H.
  Qed.

  Lemma newposts_same_empty t:
    newposts t t = [].
  Proof. rewrite /newposts /newelems. rewrite drop_ge //. Qed.

End adequacy_helper_lemmas.

(** Fixpoint definition of the soundness goal of Trillium *)
Definition fupd_to_bupd_aux `{invGS_gen hlc Σ}
           (rec : coPset → iProp Σ) (E1 : coPset) : iProp Σ :=
  ∀ (P : iProp Σ) E2, ((|={E1,E2}=> rec E2 -∗ P) ==∗ ◇ P).

Definition fupd_to_bupd `{invGS_gen hlc Σ} :=
  bi_greatest_fixpoint fupd_to_bupd_aux.

Instance fupd_to_bupd_aux_bi_mono `{invGS_gen hlc Σ} :
  BiMonoPred (fupd_to_bupd_aux).
Proof.
  split.
  - iIntros (Φ Ψ HΦne HΨne) "#H". iIntros (E1) "HE". iIntros (P E2) "HP".
    iApply "HE"; iMod "HP"; iModIntro. by iIntros; iApply "HP"; iApply "H".
  - iIntros (Φ HΦne). by intros ??? ->%leibniz_equiv.
Qed.

Lemma fupd_to_bupd_unfold `{invGS_gen hlc Σ} E :
  fupd_to_bupd E ≡ fupd_to_bupd_aux fupd_to_bupd E.
Proof. by rewrite /fupd_to_bupd greatest_fixpoint_unfold. Qed.

Lemma fupd_to_bupd_soundness_no_lc `{!invGpreS Σ} (Q : iProp Σ) :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, fupd_to_bupd ⊤ -∗ Q) → ⊢ |==> Q.
Proof.
  iIntros (Hfupd).
  iMod (@wsat_alloc _ (invGpreS0.(invGpreS_wsat))) as (Hw) "[Hw HE]".
  iMod (@later_credits.le_upd.lc_alloc _ (invGpreS0.(invGpreS_lc)) 0) as (Hc) "_".
  set (Hi := InvG HasNoLc _ Hw Hc).
  iApply (@Hfupd Hi).
  assert (NonExpansive (λ E, wsat ∗ ownE E)%I).
  { by intros ??? ->%leibniz_equiv. }
  iApply (greatest_fixpoint_coiter _ (λ E, wsat ∗ ownE E)%I with "[] [$Hw $HE]").
  iIntros "!>" (E1) "?".
  iIntros (P E2) "HP".
  rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def /=.
  iMod ("HP" with "[$]") as ">(Hw & HE & HP)".
  do 2 iModIntro; iApply "HP"; iFrame.
Qed.

Lemma fupd_to_bupd_soundness_no_lc' `{!invGpreS Σ} (Q : iProp Σ) `{!Plain Q} :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, fupd_to_bupd ⊤ -∗ Q) → ⊢ Q.
Proof. iIntros; iMod fupd_to_bupd_soundness_no_lc; done. Qed.


Lemma f2b_helper `{invGS_gen HasNoLc Σ} E1 E2 P
  {PLAIN: Plain P}:
  fupd_to_bupd E1 -∗ (|={E1, E2}=> fupd_to_bupd E2 -∗ ▷ P) -∗ ▷ P.
Proof using.
  iIntros "FB X".
  rewrite {1}fupd_to_bupd_unfold. rewrite /fupd_to_bupd_aux.
  iApply except_0_later.
  iApply bupd_elim.
  iApply "FB".
  done.
Qed.


Notation wptp_from t0 s t Φs := ([∗ list] tp1_e;Φ ∈ (prefixes_from t0 t);Φs, WP tp1_e.2 @ s; locale_of tp1_e.1 tp1_e.2; ⊤ {{ Φ }})%I.
Notation wptp s t Φs := (wptp_from [] s t Φs).

Definition config_wp `{!irisG Λ M Σ} : iProp Σ :=
  □ ∀ ex atr c1 σ2 ,
      ⌜valid_exec ex⌝ →
      ⌜trace_ends_in ex c1⌝ →
      ⌜config_step c1.2 σ2⌝ →
      state_interp ex atr ={⊤,∅}=∗ |={∅}▷=>^(S $ trace_length ex) |={∅,⊤}=>
         ∃ δ2 ℓ, state_interp (trace_extend ex None (c1.1, σ2))
                              (trace_extend atr ℓ δ2).

#[global] Instance config_wp_persistent `{!irisG Λ M Σ} : Persistent config_wp.
Proof. apply _. Qed.

#[global] Typeclasses Opaque config_wp.

Section Wptp.
  Context `{!irisG Λ M Σ}.

  Lemma wptp_from_same_locales t0' t0 s tp Φs:
    locales_equiv t0 t0' ->
    wptp_from t0' s tp Φs -∗ wptp_from t0 s tp Φs.
  Proof.
    revert Φs t0 t0'. induction tp; intros Φs t0 t0'; iIntros (Hequiv) "H" =>//.
    simpl.
    iDestruct (big_sepL2_cons_inv_l with "H") as (Φ Φs' ->) "[??]".
    rewrite big_sepL2_cons. simpl. erewrite <-locale_equiv =>//. iFrame.
    iApply IHtp =>//. apply locales_equiv_snoc =>//.
    apply locale_equiv =>//.
  Qed.

  Lemma wptp_not_stuck ex atr σ tp t0 t0' trest s Φs :
    Forall2 (λ '(t, e) '(t', e'), locale_of t e = locale_of t' e') (prefixes t0) (prefixes t0') ->
    valid_exec ex →
    trace_ends_in ex (t0 ++ tp ++ trest, σ) →
    state_interp ex atr -∗ wptp_from t0' s tp Φs ={⊤}=∗
    state_interp ex atr ∗ wptp_from t0 s tp Φs ∗
    ⌜∀ e, e ∈ tp → s = NotStuck → not_stuck e (trace_last ex).2⌝.
  Proof.
    iIntros (Hsame Hexvalid Hex) "HSI Ht".
    rewrite assoc.
    iDestruct (wptp_from_same_locales t0' with "Ht") as "Ht"; first done.
    iApply fupd_plain_keep_r; iFrame.
    iIntros "[HSI Ht]".
    iIntros (e He).
    apply elem_of_list_split in He as (t1 & t2 & ->).
    rewrite prefixes_from_app.
    iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2') "[-> [Ht1 Het2]]".
    iDestruct (big_sepL2_cons_inv_l with "Het2") as (Φ Φs2) "[-> [He Ht2]]".
    iMod (wp_not_stuck _ _ ectx_emp with "HSI He") as "(_ & _ & ?)";
      [done| rewrite ectx_fill_emp // | |done].
    - replace (t0 ++ (t1 ++ e :: t2) ++ trest) with ((t0 ++ t1) ++ e :: (t2 ++ trest)) in Hex.
      + simpl. done.
      + list_simplifier. done.
    - done.
  Qed.

  Lemma wptp_not_stuck_same ex atr σ tp t0 trest s Φs :
    valid_exec ex →
    trace_ends_in ex (t0 ++ tp ++ trest, σ) →
    state_interp ex atr -∗ wptp_from t0 s tp Φs ={⊤}=∗
    state_interp ex atr ∗ wptp_from t0 s tp Φs ∗
    ⌜∀ e, e ∈ tp → s = NotStuck → not_stuck e (trace_last ex).2⌝.
  Proof.
    iIntros (??) "??". iApply (wptp_not_stuck with "[$] [$]") =>//.
    eapply Forall2_lookup. intros i. destruct (prefixes t0 !! i) as [[??]|]; by constructor.
  Qed.

  Lemma wptp_app' s t0 t1 Φs1 t2 Φs2
    (MATCH1: length t1 = length Φs1):
    wptp_from t0 s (t1 ++ t2) (Φs1 ++ Φs2) ⊢ wptp_from t0 s t1 Φs1 ∗ wptp_from (t0 ++ t1) s t2 Φs2. 
  Proof.
    rewrite prefixes_from_app.
    iIntros. iDestruct (big_sepL2_app_inv with "[$]") as "(?&?)".
    2: { iFrame. }
    rewrite prefixes_from_length. tauto.  
  Qed.

  Lemma wptp_app s t0 t1 t0t1 Φs1 t2 Φs2 :
    t0t1 = t0 ++ t1 ->
    wptp_from t0 s t1 Φs1 -∗ wptp_from t0t1 s t2 Φs2 -∗ wptp_from t0 s (t1 ++ t2) (Φs1 ++ Φs2).
  Proof.
    iIntros (->) "H1 H2". rewrite prefixes_from_app.
    iApply (big_sepL2_app with "[H1] [H2]"); eauto.
  Qed.

  Lemma wptp_cons_r s e Φ Φs t0 t1:
    WP e @ s; locale_of (t0 ++ t1) e; ⊤ {{v, Φ v}} -∗ wptp_from t0 s t1 Φs
                              -∗ wptp_from t0 s (t1 ++ [e]) (Φs ++ [Φ]).
  Proof.
    iIntros "H1 H2". rewrite !prefixes_from_app.
    iApply (big_sepL2_app with "[H2] [H1]"); eauto.
    rewrite big_sepL2_singleton. done.
  Qed.

  Lemma wptp_cons_l s e Φ t Φs t0:
    WP e @ s; locale_of t0 e; ⊤ {{v, Φ v}} -∗
    wptp_from (t0 ++[e]) s t Φs -∗
    wptp_from t0 s (e :: t) (Φ :: Φs).
  Proof. iIntros "? ?"; rewrite big_sepL2_cons; iFrame. Qed.

  Lemma wptp_of_val_post t s Φs t0:
    wptp_from t0 s t Φs -∗ |~{⊤}~|
    posts_of t Φs ∗
    (posts_of t Φs -∗ wptp_from t0 s t Φs).
  Proof.
    iIntros "Ht"; simpl.
    iInduction t as [|e t IHt] "IH" forall (Φs t0); simpl.
    { iDestruct (big_sepL2_nil_inv_l with "Ht") as %->; eauto.
      iIntros "!>". eauto. }
    iDestruct (big_sepL2_cons_inv_l with "Ht") as (Φ Φs') "[-> [He Ht]] /=".
    iMod (wp_of_val_post with "He") as "[Hpost Hback]".
    iMod ("IH" with "Ht") as "[Ht Htback]".
    rewrite -posts_of_cons.
    rewrite -bi.sep_assoc.
    (* TODO: implement Frame instance for pre_step *)
    destruct (to_val e); simpl.
    - iApply (pre_step_comm with "[$]").
      iApply (pre_step_comm with "[Ht]").
      { by iModIntro. }
      iIntros "!>".
      iIntros "[Hpost Htpost]".
      iSplitL "Hpost Hback"; [iApply "Hback"|iApply "Htback"]; iFrame.
      by iIntros "!>".
    - iIntros "!>".
      iFrame.
      iIntros "[_ Hefspost]".
      iSplitL "Hback"; [iApply "Hback"|iApply "Htback"]; iFrame; done.
  Qed.

  Lemma new_threads_wptp_from s t efs:
    (([∗ list] i ↦ ef ∈ efs,
      WP ef @ s; locale_of (t ++ take i efs) ef ; ⊤
      {{ v, fork_post (locale_of (t ++ take i efs) ef) v }})
    ⊣⊢ wptp_from t s efs (newposts t (t ++ efs))).
  Proof.
    (* TODO: factorize the two halves *)
    rewrite big_sepL2_alt; iSplit.
    - iIntros "H". iSplit.
      { rewrite /newposts /newelems. 
        rewrite drop_app_length // map_length !prefixes_from_length //. }
      iInduction efs as [|ef efs] "IH" forall (t); first done.
      rewrite /newposts /newelems. rewrite /= !drop_app_length //=.
      iDestruct "H" as "[H1 H]". rewrite (right_id [] (++)). iFrame.
      replace (map (λ '(tnew, e), fork_post (locale_of tnew e))
                   (prefixes_from (t ++ [ef]) efs))
        with
          (newposts (t ++[ef]) ((t ++ [ef]) ++ efs)).
      + iApply "IH". iApply (big_sepL_impl with "H").
        iIntros "!>" (k e Hin) "H". by list_simplifier.
      + list_simplifier.
        replace (t ++ ef :: efs) with ((t ++ [ef]) ++ efs); last by list_simplifier.
        rewrite /newposts /newelems. rewrite drop_app_length //.
    - iIntros "[_ H]".
      iInduction efs as [|ef efs] "IH" forall (t); first done.
      rewrite /newposts /newelems. rewrite /= !drop_app_length //=.
      iDestruct "H" as "[H1 H]". rewrite (right_id [] (++)). iFrame.
      replace (map (λ '(tnew, e), fork_post (locale_of tnew e))
                   (prefixes_from (t ++ [ef]) efs))
        with
          (newposts (t ++[ef]) ((t ++ [ef]) ++ efs)).
      + iSpecialize ("IH" with "H"). iApply (big_sepL_impl with "IH").
        iIntros "!>" (k e Hin) "H". by list_simplifier.
      + list_simplifier.
        replace (t ++ ef :: efs) with ((t ++ [ef]) ++ efs); last by list_simplifier.
        rewrite /newposts /newelems. rewrite drop_app_length //.
  Qed.

  Lemma take_step s Φs ex atr c c' oζ:
    valid_exec ex →
    trace_ends_in ex c →
    locale_step c oζ c' →
    config_wp -∗
    state_interp ex atr -∗
    wptp s c.1 Φs ={⊤,∅}=∗ |={∅}▷=>^(S (trace_length ex))
                                             |={∅,⊤}=>
    ⌜∀ e2, s = NotStuck → e2 ∈ c'.1 → not_stuck e2 c'.2⌝ ∗
    ∃ δ' ℓ,
      state_interp (trace_extend ex oζ c') (trace_extend atr ℓ δ') ∗
      wptp s  c'.1 (Φs ++ newposts c.1 c'.1). 
  Proof.
    iIntros (Hexvalid Hexe Hstep) "config_wp HSI Hc1".
    inversion Hstep as
        [ρ1 ρ2 e1 σ1 e2 σ2 efs t1 t2 -> -> Hpstep | ρ1 ρ2 σ1 σ2 t -> -> Hcfgstep].
    - rewrite /= !prefixes_from_app.
      iDestruct (big_sepL2_app_inv_l with "Hc1") as
          (Φs1 Φs2') "[-> [Ht1 Het2]]".
      iDestruct (big_sepL2_cons_inv_l with "Het2") as (Φ Φs2) "[-> [He Ht2]]".
      iDestruct (wp_take_step with "HSI He") as "He"; [done|done|done|done|].
      simpl. 
      iMod "He" as "He". iModIntro. iMod "He" as "He". iModIntro. iNext.
      iMod "He" as "He". iModIntro.
      iApply (step_fupdN_wand with "[He]"); first by iApply "He".
      iIntros "He".
      iMod "He" as (δ' ℓ) "(HSI & He2 & Hefs) /=".
      iAssert (wptp_from (t1 ++ e2 :: t2) s efs (newposts (t1 ++ e2 :: t2) ((t1 ++ e2 :: t2) ++ efs)))
        with "[Hefs]" as "Hefs".
      { rewrite -new_threads_wptp_from. iApply (big_sepL_impl with "Hefs").
        iIntros "!#" (i e Hin) "Hwp". list_simplifier.
        erewrite locale_equiv; first by iFrame.
        apply locales_equiv_middle. erewrite locale_step_preserve =>//. }
      assert (valid_exec (ex :tr[Some (locale_of t1 e1)]: (t1 ++ e2 :: t2 ++ efs, σ2))).
      { econstructor; eauto. }
      iMod (wptp_not_stuck_same _ _ σ2 _ _ [] with "HSI Hefs") as "[HSI [Hefs %]]"; [done| | ].
      { list_simplifier. done. }
      iMod (wptp_not_stuck_same _ _ σ2 _ _ (e2 :: (t2 ++ efs)) with "HSI Ht1") as "[HSI [Ht1 %]]"; [done|  |].
      {  list_simplifier. done. }
      iMod (wptp_not_stuck _ _ σ2 _ (t1 ++ [e2]) _ efs with "HSI Ht2") as "[HSI [Ht2 %]]"; [| done | |].
      { rewrite !prefixes_from_app. apply Forall2_app.
        - apply locales_equiv_refl.
        - constructor; last constructor. list_simplifier. erewrite <-locale_step_preserve =>//. }
      { list_simplifier. done. }
      iMod (wp_not_stuck _ _ ectx_emp with "HSI He2") as "[HSI [He2 %]]";
        [done|by rewrite ectx_fill_emp|by erewrite <-locale_step_preserve|].
      
      iDestruct (wptp_app with "Ht2 Hefs") as "Ht2efs".
      { by list_simplifier. }
      erewrite (locale_step_preserve e1 e2) =>//.
      iDestruct (wptp_cons_l with "He2 Ht2efs") as "He2t2efs".
      iDestruct (wptp_app with "Ht1 He2t2efs") as "Hc2"; [by list_simplifier|].
      iDestruct (wptp_of_val_post with "Hc2") as "Hc2".
      iMod (pre_step_elim with "HSI Hc2") as "[HSI [Hc2posts Hc2back]]".
      iModIntro; simpl in *.
      iSplit.
      { iPureIntro; set_solver. }
      iExists δ', ℓ.
      rewrite -!app_assoc.
      iFrame.
      list_simplifier.
      erewrite newposts_locales_equiv;
        [iFrame | apply locales_equiv_middle; erewrite <-locale_step_preserve =>//].
      iDestruct ("Hc2back" with "[$]") as "X". iFrame. 
      rewrite prefixes_from_app //.
    - rewrite /= /config_wp.
      iDestruct ("config_wp" with "[] [] [] HSI") as "Hcfg"; [done|done|done|].
      iMod "Hcfg". iModIntro. iMod "Hcfg". iModIntro.
      iNext. iMod "Hcfg". iModIntro.
      iApply (step_fupdN_wand with "[Hcfg]"); first by iApply "Hcfg".
      iIntros "Hcfg".
      iMod "Hcfg" as (δ2 ℓ) "HSI".
      assert (valid_exec (ex :tr[None]: ((t, σ1).1, σ2))).
      { econstructor; eauto. }
      iMod (wptp_not_stuck _ _ σ2 _ _ _ [] with "HSI Hc1") as "[HSI [Hc1 %]]";
        [apply locales_equiv_refl|done|by list_simplifier|].
      iDestruct (wptp_of_val_post with "Hc1") as "Hc1".
      iMod (pre_step_elim with "HSI Hc1") as "[HSI [Hc1posts Hc1back]]".
      iModIntro.
      iSplit; first by auto.
      iExists δ2, ℓ.
      rewrite newposts_same_empty. list_simplifier.
      iFrame.
      by iApply "Hc1back". 
  Qed.  

End Wptp.


Definition rel_finitary {A B C D}
           (ξ : finite_trace A B → finite_trace C D → Prop) :=
  ∀ (ex : finite_trace A B) (atr : finite_trace C D) c' oζ,
    smaller_card (sig (λ '(δ', ℓ), ξ (ex :tr[oζ]: c') (atr :tr[ℓ]: δ'))) nat.

Section finitary_lemma.
  Lemma rel_finitary_impl {A B C D} `{EqDecision C, EqDecision D}
        (ξ ξ' : finite_trace A B -> finite_trace C D -> Prop):
    (∀ ex aux, ξ ex aux -> ξ' ex aux) ->
    rel_finitary ξ' ->
    rel_finitary ξ.
  Proof.
    intros Himpl Hξ' ex aux c' oζ.
    assert (
        ∀ ξ x, ProofIrrel
                 (match x return Prop with (δ', ℓ) =>
                    ξ (ex :tr[ oζ ]: c') (aux :tr[ ℓ ]: δ')
                  end)).
    { intros ?[??]. apply make_proof_irrel. }
    apply finite_smaller_card_nat.
    specialize (Hξ' ex aux c' oζ). apply smaller_card_nat_finite in Hξ'.
    eapply (in_list_finite (map proj1_sig (@enum _ _ Hξ'))).
    intros [δ' ℓ] ?. apply elem_of_list_fmap.
    assert ((λ '(δ', ℓ), ξ' (ex :tr[ oζ ]: c') (aux :tr[ ℓ ]: δ')) (δ', ℓ)) by eauto.
    exists ((δ', ℓ) ↾ ltac:(eauto)). split =>//.
    apply elem_of_enum.
  Qed.
End finitary_lemma.
