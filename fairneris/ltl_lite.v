From Paco Require Import paconotation pacotac paco2.
From fairneris Require Export inftraces.

Declare Scope trace_scope.
Delimit Scope trace_scope with trace.
Bind Scope trace_scope with trace.

Definition ltl_pred S L := trace S L → Prop.

Section ltl_constructors.
  Context {S L : Type}.

  Notation ltl_pred := (ltl_pred S L).

  (* Primitive operators *)
  Definition trace_now P : ltl_pred := λ tr, pred_at tr 0 P.
  Definition trace_label P : ltl_pred := λ tr, pred_at tr 0 (λ st lab, match lab with
                                                                           | Some l => P l
                                                                           | None => False
                                                                           end).
  Definition trace_not P : ltl_pred := λ tr, ¬ P tr.
  Definition trace_or P Q : ltl_pred := λ tr, P tr ∨ Q tr.
  Definition trace_next P : ltl_pred :=
    λ tr, ∃ tr', after 1 tr = Some tr' ∧ P tr'.
  Inductive trace_until P Q : ltl_pred :=
  | trace_until_here tr : Q tr -> trace_until P Q tr
  | trace_until_next s l tr : P (s -[l]-> tr) → trace_until P Q tr → trace_until P Q (s -[l]-> tr).

  (* Derived operators *)
  Definition trace_and P Q := (trace_not (trace_or (trace_not P) (trace_not Q))).
  Definition trace_implies P Q := (trace_or (trace_not P) Q).
  Definition trace_biimplies P Q :=
    (trace_and (trace_implies P Q) (trace_implies Q P)).
  Definition trace_true := (trace_now (λ _ _, True)).
  Definition trace_false := (trace_now (λ _ _,False)).
  Definition trace_eventually P := (trace_until trace_true P).
  Definition trace_always P := (trace_not $ trace_eventually (trace_not P)).
  Definition trace_weak_until (P Q : trace S L → Prop) : ltl_pred :=
    trace_or (trace_until P Q) (trace_always P).

  (* Custom constructors *)
  Definition trace_always_eventually_implies
             (P Q : trace S L → Prop) : ltl_pred :=
    trace_always (trace_implies P (trace_eventually Q)).

  Definition trace_always_eventually_implies_now
             (P Q : S → option L → Prop) : ltl_pred :=
    trace_always_eventually_implies (trace_now P) (trace_now Q).

  Lemma trace_eventually_ind (P P0 : trace S L → Prop) :
    (∀ tr : trace S L, P tr → P0 tr) →
    (∀ (s : S) (l : L) (tr : trace S L),
         trace_eventually P tr → P0 tr → P0 (s -[ l ]-> tr)) →
    ∀ t : trace S L, trace_eventually P t → P0 t.
  Proof.
    intros ? IH ??.
    eapply (trace_until_ind trace_true); [done|by intros; apply IH|done].
  Qed.

End ltl_constructors.

Arguments trace_eventually_ind : clear implicits.

Notation "○ P" := (trace_next P) (at level 20, right associativity) : trace_scope.
Notation "□ P" := (trace_always P) (at level 20, right associativity) : trace_scope.
Notation "◊ P" := (trace_eventually P) (at level 20, right associativity) : trace_scope.
Notation "↓ P" := (trace_now P) (at level 20, right associativity) : trace_scope.
Notation "ℓ↓ P" := (trace_label P) (at level 20, right associativity) : trace_scope.
Notation "P → Q" := (trace_implies P Q)
                      (at level 99, Q at level 200,
                         format "'[' P  →  '/' '[' Q ']' ']'") : trace_scope.

(* TODO: Replace existing library lemma with this *)
Lemma not_exists_forall_not_alt {A} (P : A → Prop) x : ¬ (∃ x, P x) → ¬ P x.
Proof. intros Hnex HP; apply Hnex; eauto. Qed.

Section ltl_lemmas.
  Context {S L : Type}.

  (* TODO: Move this *)
  Lemma after_is_Some_le (tr : trace S L) n m :
    m ≤ n → is_Some $ after n tr → is_Some $ after m tr.
  Proof.
    revert tr m.
    induction n; intros tr m Hle.
    { intros. assert (m = 0) as -> by lia. done. }
    intros.
    destruct m; [done|].
    simpl in *.
    destruct tr; [done|].
    apply IHn. lia. done.
  Qed.

  Lemma after_is_Some_lt (tr : trace S L) n m :
    m < n → is_Some $ after n tr → is_Some $ after m tr.
  Proof.
    revert tr m.
    induction n; intros tr m Hle.
    { intros. assert (m = 0) as -> by lia. done. }
    intros.
    destruct m; [done|].
    simpl in *.
    destruct tr; [done|].
    apply IHn. lia. done.
  Qed.

  Lemma after_levis n m (tr1 tr2 tr3: trace S L):
    n ≤ m →
    after n tr1 = Some tr2 →
    after m tr1 = Some tr3 →
    after (m - n) tr2 = Some tr3.
  Proof.
    intros Hle Haftern Hafterm.
    pose proof (Nat.le_exists_sub n m Hle) as [p [-> Hle']].
    rewrite Nat.add_comm Nat.add_sub'.
    by rewrite after_sum Haftern in Hafterm.
  Qed.

  (** trace_true lemmas *)

  Lemma trace_trueI (tr : trace S L) : trace_true tr.
  Proof. destruct tr; done. Qed.

  (** trace_not lemmas *)

  Lemma trace_notI (P : trace S L → Prop) tr :
    trace_not P tr ↔ ¬ P tr.
  Proof. done. Qed.

  Lemma trace_not_idemp (P : trace S L → Prop) (tr : trace S L) :
    trace_not (trace_not P) tr ↔ P tr.
  Proof. rewrite /trace_not. split; [apply NNP_P|apply P_NNP]. Qed.

  Lemma trace_not_mono (P Q : trace S L → Prop) tr :
    (Q tr → P tr) → trace_not P tr → trace_not Q tr.
  Proof. intros HQP HP HQ. apply HP. by apply HQP. Qed.

  (** trace_next lemmas *)

  Lemma trace_next_intro (P : trace S L → Prop) s l (tr : trace S L) :
    P tr → (○ P) (s -[l]-> tr).
  Proof. intros ?. exists tr. simpl in *. by simplify_eq. Qed.

  Lemma trace_next_elim (P : trace S L → Prop) s l tr :
    (○ P) (s -[l]-> tr) → P tr.
  Proof. inversion 1. naive_solver. Qed.

  Lemma trace_next_elim_inv (P : trace S L → Prop) tr :
    (○ P) tr → ∃ s l tr', tr = s -[l]-> tr' ∧ P tr'.
  Proof. inversion 1. destruct tr; naive_solver. Qed.

  (** trace_implies lemmas *)

  Lemma trace_impliesI (P Q : trace S L → Prop) tr :
    trace_implies P Q tr ↔ (P tr → Q tr).
  Proof.
    split; [by intros [|]|].
    intros HPQ.
    assert (P tr ∨ ¬ P tr) as [HP|HP] by apply ExcludedMiddle.
    + by right; apply HPQ.
    + by left.
  Qed.

  Lemma trace_implies_refl (P : trace S L → Prop) tr :
    trace_implies P P tr.
  Proof. by apply trace_impliesI. Qed.

  (** trace_or lemmas *)

  Lemma trace_orI (P Q : trace S L → Prop) (tr : trace S L) :
    trace_or P Q tr ↔ P tr ∨ Q tr.
  Proof. done. Qed.

  Lemma trace_or_l (P Q : trace S L → Prop) (tr : trace S L) :
    P tr → trace_or P Q tr.
  Proof. intros HP. by left. Qed.

  Lemma trace_or_r (P Q : trace S L → Prop) (tr : trace S L) :
    Q tr → trace_or P Q tr.
  Proof. intros HP. by right. Qed.

  (** trace_and lemmas *)

  Lemma trace_andI (P Q : trace S L → Prop) (tr : trace S L) :
    trace_and P Q tr ↔ P tr ∧ Q tr.
  Proof.
    split.
    - intros HPQ.
      assert (P tr ∨ ¬ P tr) as [HP|HP] by apply ExcludedMiddle; last first.
      { eapply trace_not_mono in HPQ; [|by apply trace_or_l]. done. }
      assert (Q tr ∨ ¬ Q tr) as [HQ|HQ] by apply ExcludedMiddle; last first.
      { eapply trace_not_mono in HPQ; [|by apply trace_or_r]. done. }
      done.
    - intros [HP HQ] [HP'|HQ']; done.
  Qed.

  (** trace_now lemmas *)

  Definition trfirst_label (tr: trace S L) : option L :=
    match tr with
    | ⟨_⟩ => None
    | _ -[ℓ]-> _ => Some ℓ
    end.

  Lemma trace_now_mono_strong (P Q : S → option L → Prop) tr :
    (∀ s l, trfirst tr = s → trfirst_label tr = l → P s l → Q s l) →
    (↓P) tr → (↓Q) tr.
  Proof.
    destruct tr as [s|s l tr].
    - rewrite /trace_now /pred_at /=. intros HPQ Htr. by apply HPQ.
    - rewrite /trace_now /pred_at /=. intros HPQ Htr. by apply HPQ.
  Qed.

  Lemma trace_now_mono (P Q : S → option L → Prop) tr :
    (∀ s l, P s l → Q s l) → (↓P) tr → (↓Q) tr.
  Proof. intros. eapply trace_now_mono_strong; [|done]. by eauto. Qed.

  Lemma trace_now_not P (tr : trace S L) :
    (↓ (λ s l, ¬ P s l)) tr ↔ trace_not (↓ P) tr.
  Proof. by destruct tr. Qed.

  Lemma trace_now_exists {A} (P : A → S → option L → Prop) (tr : trace S L) :
    (↓ (λ s l, ∃ (x:A), P x s l)) tr → ∃ (x:A), (↓ P x) tr.
  Proof. rewrite /trace_now /pred_at. intros H. by destruct tr. Qed.

  Lemma trace_now_or (P Q : S → option L → Prop) tr :
    (↓ (P \2/ Q)) tr → (↓ P) tr ∨ (↓ Q) tr.
  Proof. rewrite /trace_now /pred_at. by destruct tr=>/=. Qed.

  Lemma trace_now_and P Q (tr : trace S L) :
    (↓ (P /2\ Q)) tr ↔ trace_and (↓P) (↓Q) tr .
  Proof. rewrite trace_andI. destruct tr; done. Qed.

  (* TODO: Maybe remove *)
  Lemma trace_now_split P Q (tr : trace S L) :
    (↓ P) tr → (↓ Q) tr → (↓ (P /2\ Q)) tr.
  Proof. intros. apply trace_now_and. rewrite trace_andI. done. Qed.

  (** trace_eventually lemmas *)

  Lemma trace_eventually_intro P (tr : trace S L) :
    P tr → (◊ P) tr.
  Proof. by constructor 1. Qed.

  Lemma trace_eventually_cons (P : trace S L → Prop) s l (tr : trace S L) :
    (◊ P) tr → (◊ P) (s -[l]-> tr).
  Proof. intros. by constructor 2. Qed.

  Lemma trace_eventually_idemp (P : trace S L → Prop) (tr : trace S L) :
    (◊◊P) tr → (◊P) tr.
  Proof.
    intros Htr. induction Htr using trace_eventually_ind; [done|].
    apply trace_eventually_cons. done.
  Qed.

  Lemma trace_eventuallyI_alt (P : trace S L → Prop) tr :
    (◊ P) tr ↔ (∃ tr', trace_suffix_of tr' tr ∧ (◊ P) tr').
  Proof.
    split.
    - intros Heventually.
      induction Heventually using trace_eventually_ind.
      { exists tr. split; [apply trace_suffix_of_refl|].
        by apply trace_eventually_intro. }
      destruct IHHeventually as [tr' [Hsuffix HP]].
      exists tr'.
      split; [|done].
      by apply trace_suffix_of_cons_r.
    - intros [tr' [Hsuffix Htr']].
      induction Htr' using trace_eventually_ind.
      { destruct Hsuffix as [n Hafter].
        revert tr tr0 Hafter H.
        induction n; intros tr tr0 Hafter HP.
        { simpl in *. simplify_eq. by apply trace_eventually_intro. }
        destruct tr; [done|].
        constructor 2; [done|].
        by eapply IHn. }
      apply IHHtr'.
      by eapply trace_suffix_of_cons_l.
  Qed.

  Lemma trace_eventuallyI (P : trace S L → Prop) tr :
    (◊ P) tr ↔ (∃ tr', trace_suffix_of tr' tr ∧ P tr').
  Proof.
    split.
    - intros Heventually.
      induction Heventually using trace_eventually_ind.
      { exists tr. split; [apply trace_suffix_of_refl|]. done. }
      destruct IHHeventually as [tr' [Hsuffix HP]].
      exists tr'.
      split; [|done].
      by apply trace_suffix_of_cons_r.
    - intros [tr' [Hsuffix Htr']].
      apply trace_eventuallyI_alt. exists tr'. split=>//.
      by apply trace_eventually_intro.
  Qed.

  Lemma trace_eventually_until (P : trace S L → Prop) (tr : trace S L) :
    (◊P) tr → trace_until (trace_not P) (P) tr.
  Proof.
    assert (∀ tr, P tr ∨ ¬ P tr) as Hdec by by intros; apply ExcludedMiddle.
    induction 1 using trace_eventually_ind; [by constructor|].
    specialize (Hdec (s -[l]-> tr)) as [H1|H2].
    - by apply trace_until_here.
    - by apply trace_until_next.
  Qed.

  Lemma trace_eventually_mono_strong (P Q : trace S L → Prop) tr :
    (∀ tr', trace_suffix_of tr' tr → P tr' → Q tr') → (◊P) tr → (◊Q) tr.
  Proof.
    intros HPQ.
    induction 1 using trace_eventually_ind.
    { apply HPQ, trace_eventually_intro in H. done. apply trace_suffix_of_refl. }
    constructor 2; [done|].
    apply IHtrace_eventually.
    intros tr' Hsuffix HP.
    apply HPQ; [|done].
    destruct Hsuffix as [n Heq].
    exists (Datatypes.S n). done.
  Qed.

  Lemma trace_eventually_mono (P Q : trace S L → Prop) tr :
    (∀ tr, P tr → Q tr) → (◊P) tr → (◊Q) tr.
  Proof.
    intros. eapply trace_eventually_mono_strong; [|done]. intros. by apply H.
  Qed.

  Lemma trace_eventually_next (P : trace S L → Prop) (tr : trace S L) :
    (◊ ○ P) tr → (◊ P) tr.
  Proof.
    intros Hnext.
    induction Hnext using trace_eventually_ind.
    { destruct tr; [inversion H; naive_solver|].
      constructor 2; [done|]. constructor. by eapply trace_next_elim. }
    constructor 2; [done|]. apply IHHnext.
  Qed.

  Lemma trace_eventually_suffix_of (P : trace S L → Prop) tr1 tr2 :
    trace_suffix_of tr1 tr2 → (◊P) tr1 → (◊P) tr2.
  Proof. intros Hsuffix HP. apply trace_eventuallyI_alt. by exists tr1. Qed.

  Lemma trace_eventually_or (P Q : trace S L → Prop) tr :
    (◊ (P \1/ Q)) tr → (◊ P) tr ∨ (◊ Q) tr.
  Proof.
    intros Hdisj.
    induction Hdisj using trace_eventually_ind.
    { inversion H; [left; by constructor|right; by constructor]. }
    inversion IHHdisj.
    - left. by constructor 2.
    - right. by constructor 2.
  Qed.

  (** trace_always lemmas *)

  Lemma trace_always_cons (P : trace S L → Prop) s l (tr : trace S L) :
    (□ P) (s -[l]-> tr) → (□ P) tr.
  Proof.
    intros Htr Htr'. apply Htr. clear Htr. by apply trace_eventually_cons.
  Qed.

  Lemma trace_always_idemp P (tr : trace S L) :
    (□ P) tr → (□ □ P) tr.
  Proof.
    intros Htr Htr'. induction Htr'; [by apply H|].
    apply IHHtr'. by apply trace_always_cons in Htr.
  Qed.

  Lemma trace_always_elim (P : trace S L → Prop) (tr : trace S L) :
    (□P) tr → P tr.
  Proof.
    intros Htr.
    assert (P tr ∨ ¬ P tr) as [|HP] by apply ExcludedMiddle; [done|].
    rewrite /trace_always in Htr.
    assert (trace_not (trace_not P) tr).
    { intros Htr'. apply Htr. apply trace_eventually_intro. done. }
    done.
  Qed.

  Lemma trace_always_mono (P Q : trace S L → Prop) tr :
    (∀ tr, trace_implies P Q tr) → (□P) tr → (□Q) tr.
  Proof.
    intros HPQ HP HQ. apply HP. eapply trace_eventually_mono; [|done].
    clear HP HQ. intros tr' HP HQ. apply HP.
    specialize (HPQ tr'). rewrite trace_impliesI in HPQ. by apply HPQ.
  Qed.

  Lemma trace_always_mono_strong (P Q : trace S L → Prop) tr :
    (∀ tr', trace_suffix_of tr' tr → trace_implies P Q tr') → (□P) tr → (□Q) tr.
  Proof.
    intros HPQ HP HQ. apply HP. eapply trace_eventually_mono_strong; [|done].
    clear HP HQ. intros tr' Htr' HP HQ. apply HP.
    specialize (HPQ tr'). rewrite trace_impliesI in HPQ. by apply HPQ.
  Qed.

  Lemma trace_alwaysI_alt (P : trace S L → Prop) tr :
    (□P) tr ↔ (∀ tr', trace_suffix_of tr' tr → (□ P) tr').
  Proof.
    split.
    - intros Htr tr' Hsuffix Htr'.
      apply Htr.
      induction Htr' using trace_eventually_ind.
      { eapply trace_eventuallyI_alt. exists tr0. split; [done|].
        by apply trace_eventually_intro. }
      apply IHHtr'. by eapply trace_suffix_of_cons_l.
    - intros Htr' Htr.
      induction Htr using trace_eventually_ind.
      { specialize (Htr' tr). apply Htr'.
        { apply trace_suffix_of_refl. }
        by apply trace_eventually_intro. }
      apply IHHtr. intros tr' Htsuffix. apply Htr'.
      by eapply trace_suffix_of_cons_r.
  Qed.

  Lemma trace_always_suffix_of (P : trace S L → Prop) tr1 tr2 :
    trace_suffix_of tr2 tr1 → (□P) tr1 → (□P) tr2.
  Proof. rewrite (trace_alwaysI_alt _ tr1). intros Hsuffix HP. by eapply HP. Qed.

  Lemma trace_alwaysI (P : trace S L → Prop) tr :
    (□P) tr ↔ (∀ tr', trace_suffix_of tr' tr → P tr').
  Proof.
    split.
    - intros HP tr' Hsuff. rewrite trace_alwaysI_alt in HP.
      apply trace_always_elim. eauto.
    - intros H Habs. apply trace_eventuallyI in Habs as (tr'&Hsuff&?).
      by specialize (H _ Hsuff).
  Qed.

  Lemma trace_always_eventually_always_until (P : trace S L → Prop) (tr : trace S L) :
    (□ ◊P) tr → (□ trace_until (trace_not P) (P)) tr.
  Proof.
    rewrite !trace_alwaysI. intros He tr' Hsuff.
    apply trace_eventually_until. apply He=>//.
  Qed.

  Lemma trace_always_forall {A} (P : A → trace S L → Prop) tr :
    (∀ (x:A), (□ (P x)) tr) ↔ (□ (λ tr', ∀ x, P x tr')) tr.
  Proof.
    split.
    - intros Htr Htr'.
      induction Htr' using trace_eventually_ind.
      { apply H. intros x. specialize (Htr x).
        apply trace_always_elim in Htr. apply Htr. }
      apply IHHtr'.
      intros x. specialize (Htr x).
      by apply trace_always_cons in Htr.
    - intros Htr x Htr'.
      induction Htr' using trace_eventually_ind.
      { apply H. apply trace_always_elim in Htr. apply Htr. }
      apply IHHtr'. by apply trace_always_cons in Htr.
  Qed.

  (* TODO: This breaks naming convention *)
  Lemma trace_always_universal (P : trace S L → Prop) (tr : trace S L) :
    (∀ tr, P tr) → (□P) tr.
  Proof.
    intros ? H. induction H using trace_eventually_ind; [|done].
    simplify_eq. specialize (H0 tr). done.
  Qed.

  (* TODO: This is a bit of a weird statement *)
  Lemma trace_always_implies (P Q : trace S L → Prop) tr :
    (□(P → Q)) tr → (□P) tr → (□ Q) tr.
  Proof.
    intros HPQ HP.
    eapply trace_always_mono_strong; [|done].
    intros tr' Hsuffix.
    apply trace_always_elim.
    by eapply trace_always_suffix_of.
  Qed.

  Lemma trace_always_eventually P (tr : trace S L) :
    (□ P) tr → (◊ P) tr.
  Proof.
    intros Halways. eapply trace_eventuallyI_alt. exists tr.
    split; [apply trace_suffix_of_refl|]. apply trace_eventually_intro.
    by apply trace_always_elim in Halways.
  Qed.

  Lemma trace_always_eventually_suffix_of tr1 tr2 (P : trace S L → Prop) :
    trace_suffix_of tr1 tr2 → (□◊ P) tr1 → (□◊ P) tr2.
  Proof.
    intros [n Hn] H1.
    apply trace_alwaysI.
    intros tr' [m Hm].
    apply trace_eventuallyI_alt.
    destruct (decide (m ≤ n)).
    - exists tr1. split.
      + exists (n - m). eapply after_levis =>//.
      + by apply trace_always_elim in H1.
    - exists tr'. split=>//.
      + exists 0. done.
      + assert (Hsuff: trace_suffix_of tr' tr1).
        * exists (m - n). assert (n ≤ m) by lia. eapply after_levis =>//.
        * rewrite trace_alwaysI_alt in H1. specialize (H1 tr' Hsuff).
          by apply trace_always_elim in H1.
  Qed.

  Lemma trace_always_eventually_always_implies (P Q : trace S L → Prop) tr :
    trace_always_eventually_implies P Q tr → (□P) tr → (◊Q) tr.
  Proof.
    intros HPQ HP.
    eapply trace_always_implies in HP; [|done].
    by apply trace_always_elim.
  Qed.

  Lemma trace_always_eventually_always_mono (P1 P2 Q1 Q2 : trace S L → Prop) tr :
    (∀ tr, trace_implies P2 P1 tr) → (∀ tr, trace_implies Q1 Q2 tr) →
    trace_always_eventually_implies P1 Q1 tr → trace_always_eventually_implies P2 Q2 tr.
  Proof.
    setoid_rewrite trace_impliesI.
    intros HP HQ Htr.
    eapply trace_always_mono; [|done].
    intros Htr'.
    apply trace_impliesI.
    rewrite !trace_impliesI.
    intros HPQ HP2.
    eapply trace_eventually_mono; [apply HQ|by apply HPQ; apply HP].
  Qed.

  Lemma trace_always_not_not_eventually (P : trace S L → Prop) (tr : trace S L) :
    (□ (trace_not P)) tr ↔ trace_not (◊ P) tr.
  Proof.
    split.
    - intros Halways Heventually.
      induction Heventually.
      { apply Halways. apply trace_eventually_intro. by apply P_NNP. }
      apply IHHeventually.
      by apply trace_always_cons in Halways.
    - intros Heventually Halways.
      induction Halways using trace_eventually_ind.
      { apply Heventually. apply trace_eventually_intro.
        eapply trace_not_mono in Heventually; [|by apply trace_eventually_intro].
        done. }
      apply IHHalways.
      intros Heventually'. apply Heventually. by apply trace_eventually_cons.
  Qed.

  Lemma trace_eventually_not_not_always (P : trace S L → Prop) (tr : trace S L) :
    (◊ trace_not P) tr ↔ (trace_not (□ P)) tr.
  Proof.
    split.
    - intros Heventually. apply P_NNP. done.
    - intros Halways. apply NNP_P in Halways. done.
  Qed.

  Lemma trace_always_and P Q (tr : trace S L) :
    (□ trace_and P Q) tr ↔ ((□ P) tr ∧ (□ Q) tr).
  Proof.
    split.
    - intros HPQ.
      assert ((□ P) tr ∨ ¬ (□ P) tr) as [|HP] by apply ExcludedMiddle; last first.
      { apply NNP_P in HP. induction HP using trace_eventually_ind.
        { apply trace_always_elim in HPQ. apply trace_andI in HPQ as [HP HQ].
          done. }
        apply trace_always_cons in HPQ. apply IHHP in HPQ.
        destruct HPQ as [HP' HQ].
        apply trace_eventually_not_not_always in HP. done. }
      assert ((□ Q) tr ∨ ¬ (□ Q) tr) as [|HQ] by apply ExcludedMiddle; last first.
      { apply NNP_P in HQ. induction HQ using trace_eventually_ind.
        { apply trace_always_elim in HPQ. apply trace_andI in HPQ as [HP HQ].
          done. }
        apply trace_always_cons in HPQ.
        apply trace_always_cons in H.
        apply IHHQ in HPQ; [|done].
        destruct HPQ as [HP HQ'].
        apply trace_eventually_not_not_always in HQ. done. }
      done.
    - intros [HP HQ] HPQ. induction HPQ.
      { apply H. apply trace_andI. apply trace_always_elim in HP, HQ. done. }
      by apply IHHPQ; eapply trace_always_cons.
  Qed.

  Lemma trace_weak_until_always P Q (tr : trace S L) :
    (□P) tr → trace_weak_until P Q tr.
  Proof. intros HP. by apply trace_or_r. Qed.

  (* TODO: Remove? *)
  Lemma trace_always_implies_always (P Q : trace S L → Prop) (tr : trace S L) :
    (∀ tr, (□P) tr → Q tr) → ((□P) tr → (□ Q) tr).
  Proof.
    intros HPQ HP%trace_always_idemp. eapply trace_always_mono; [|done].
    intros ?. apply trace_impliesI, HPQ.
  Qed.

  Lemma trace_eventually_until_eventually (Q P : trace S L → Prop) tr :
    (◊ P) tr ↔ (◊ (trace_until Q P)) tr.
  Proof.
    split.
    - intros [tr' [Hsuff HP]]%trace_eventuallyI. apply trace_eventuallyI.
      exists tr'; split=>//. by constructor.
    - intros [tr' [Hsuff HP]]%trace_eventuallyI. induction HP as [|????? IH].
      + apply trace_eventuallyI. naive_solver.
      + apply IH. by eapply trace_suffix_of_cons_l.
  Qed.

  Lemma trace_always_eventually_label_infinite P (tr : trace S L) :
    (□◊ℓ↓P) tr → infinite_trace tr.
  Proof.
    intros Hltl n. revert tr Hltl. induction n as [|n IH]; first naive_solver.
    intros tr Hltl.
    destruct tr as [s|s ℓ tr].
    - apply trace_always_elim in Hltl.
      rewrite trace_eventuallyI in Hltl.
      destruct Hltl as (tr'&Hsuff&Hltl).
      destruct Hsuff as [[|m] Hafter]=>//. simpl in Hafter. by simplify_eq.
    - simpl. apply IH. by eapply trace_always_cons.
  Qed.
End ltl_lemmas.

Section ltl_theorems.
  Context {S L : Type}.

  (* Strong fairness implies our (network) fairness *)
  Lemma SF_implies_OF (P Q: trace S L → Prop) tr :
    ((□◊ P) → (□◊ Q))%trace tr → (□ ((□◊ P) → (◊ Q))) tr.
  Proof.
    intros Hsf. apply trace_alwaysI. intros tr' Hsuff.
    apply trace_impliesI. intros Hae.
    eapply trace_always_eventually_suffix_of in Hae =>//.
    rewrite trace_impliesI in Hsf. specialize (Hsf Hae).
    apply trace_always_elim. by eapply trace_always_suffix_of.
  Qed.

  Lemma OF_implies_SF (P Q: trace S L → Prop) tr :
    (□ ((□◊ P) → (◊ Q))) tr → ((□◊ P) → (□◊ Q))%trace tr.
  Proof.
    intros Hsf. apply trace_impliesI.
    intros HP. apply trace_always_idemp in HP. revert HP.
    by apply trace_always_implies.
  Qed.

  Theorem SF_equiv_OF (P Q: trace S L → Prop) tr :
    ((□◊ P) → (□◊ Q))%trace tr ≡ (□ ((□◊ P) → (◊ Q))) tr.
  Proof. split; [apply SF_implies_OF|apply OF_implies_SF]. Qed.

  (* Our (scheduling) Fairness implies Strong Fairness *)
  Lemma OF_implies_SF' (P Q: trace S L → Prop) tr :
    (□ (P → (◊ Q)))%trace tr → ((□◊ P) → (□◊ Q))%trace tr.
  Proof.
    intros Htr. apply trace_impliesI.
    apply trace_always_implies.
    rewrite trace_alwaysI_alt in Htr.
    rewrite trace_alwaysI.
    intros tr' Hsuffix.
    specialize (Htr tr' Hsuffix).
    apply trace_impliesI.
    intros HP.
    rewrite trace_eventuallyI in HP.
    destruct HP as [tr'' [Hsuffix' HP]].
    rewrite trace_alwaysI in Htr.
    specialize (Htr tr'' Hsuffix').
    rewrite trace_impliesI in Htr.
    rewrite trace_eventuallyI_alt.
    exists tr''. split; [done|].
    apply Htr. done.
  Qed.

End ltl_theorems.

Section stutter.
  Context {St S' L L': Type}.
  Context (Us: St -> S').
  Context (Ul: L -> option L').

  Notation upto_stutter := (upto_stutter Us Ul).

  Definition ltl_se (P: ltl_pred St L) (Q: ltl_pred S' L') :=
    ∀ tr tr', upto_stutter tr tr' → (P tr ↔ Q tr').

  #[local] Lemma upto_stutter_mono' :
    monotone2 (upto_stutter_ind Us Ul).
  Proof. exact (upto_stutter_mono Us Ul). Qed.
  Hint Resolve upto_stutter_mono' : paco.

  Definition trace_silent_filter : St → option L → Prop :=
    λ _ ℓ, match ℓ with | Some ℓ' => Ul ℓ' = None | None => False end.
  Instance trace_silent_filter_decision st ℓ : Decision (trace_silent_filter st ℓ).
  Proof. unfold trace_silent_filter. destruct ℓ; solve_decision. Defined.

  Definition trace_silent := ↓ trace_silent_filter.

  Lemma ltl_se_now P P':
    (∀ l, P l ↔ (∃ l', Ul l = Some l' ∧ P' l')) →
    ltl_se (trace_until trace_silent (ℓ↓ P)) (ℓ↓ P').
  Proof.
    intros Hp tr tr' Hupto; split.
    - induction 1 as [tr Hnow| s ℓ tr Hsil Htu IH].
      + destruct tr as [s|s ℓ tr], tr' as [s'|s' ℓ' tr'] =>//=.
        * punfold Hupto. inversion Hupto; simplify_eq.
          rewrite /trace_label /pred_at /= in Hnow. naive_solver.
        * punfold Hupto. inversion Hupto; simplify_eq;
          rewrite /trace_label /pred_at /= in Hnow; naive_solver.
      + rewrite /trace_silent /trace_now /pred_at /= in Hsil.
        punfold Hupto. inversion Hupto; simplify_eq.
        apply IH. by pfold.
    - punfold Hupto. induction Hupto as [s|tr tr' s ℓ Hsil Hs1 Hs2 IH|tr tr' s ℓ s' ℓ' Hs Hl].
      + rewrite /trace_label /pred_at //=.
      + intros Hnow. constructor 2; naive_solver.
      + rewrite {1}/trace_label /pred_at //=. intros Hnow. constructor 1.
        apply Hp. naive_solver.
  Qed.

  Lemma ltl_se_always P P':
    ltl_se P P' →
    ltl_se (□ P) (□ P').
  Proof.
    intros Hse tr1 tr2 Hupto. rewrite !trace_alwaysI. split.
    - intros Hal tr2' Hsuff. destruct (upto_stutter_suffix_of _ _ _ _ _ Hupto Hsuff) as (?&?&Hupto').
      apply (Hse _ _ Hupto'). by apply Hal.
    - intros Hal tr1' Hsuff. destruct (upto_stutter_suffix_of_inv _ _ _ _ _ Hupto Hsuff) as (?&?&Hupto').
      apply (Hse _ _ Hupto'). by apply Hal.
  Qed.

  Lemma ltl_se_eventually P P':
    ltl_se P P' →
    ltl_se (◊ P) (◊ P').
  Proof.
    intros Hse tr1 tr2 Hupto. rewrite !trace_eventuallyI. split.
    - intros (?&Hsuff&?). destruct (upto_stutter_suffix_of_inv _ _ _ _ _ Hupto Hsuff) as (?&?&Hupto').
      eexists _; split=>//. apply (Hse _ _ Hupto'). naive_solver.
    - intros (?&Hsuff&?). destruct (upto_stutter_suffix_of _ _ _ _ _ Hupto Hsuff) as (?&?&Hupto').
      eexists _; split=>//. apply (Hse _ _ Hupto'). naive_solver.
  Qed.

  Lemma ltl_se_eventually_now P P':
    (∀ l, P l ↔ (∃ l', Ul l = Some l' ∧ P' l')) →
    ltl_se (◊ ((ℓ↓ P))) (◊ (ℓ↓ P')).
  Proof.
    intros ?. have Hccl: ltl_se (◊ (trace_until trace_silent (ℓ↓ P))) (◊ (ℓ↓ P')).
    { by apply ltl_se_eventually, ltl_se_now. }
    intros tr tr' ?. rewrite (trace_eventually_until_eventually trace_silent).
    by apply Hccl.
  Qed.

  Lemma ltl_se_impl P P' Q Q':
    ltl_se P P' →
    ltl_se Q Q' →
    ltl_se (P → Q) (P' → Q').
  Proof.
    intros HseP HseQ tr1 tr2 Hupto. rewrite !trace_impliesI.
    split; intros Himpl H%(HseP _ _ Hupto); apply (HseQ _ _ Hupto); naive_solver.
  Qed.

  Lemma ltl_se_forall {X} P P':
    (∀ (x : X), ltl_se (P x) (P' x)) →
    ltl_se (λ tr, ∀ x, P x tr) (λ tr, ∀ x, P' x tr).
  Proof. intros Hse tr1 tr2 Hupto. naive_solver. Qed.
End stutter.

Section traces_match.
  Context {L1 L2 S1 S2: Type}.
  Context (Rl: L1 -> L2 -> Prop) (Rs: S1 -> S2 -> Prop).
  Context (trans1: S1 -> L1 -> S1 -> Prop).
  Context (trans2: S2 -> L2 -> S2 -> Prop).

  Notation tm := (traces_match Rl Rs trans1 trans2).

  Definition ltl_tme (P: ltl_pred S1 L1) (Q: ltl_pred S2 L2) :=
    ∀ tr tr', tm tr tr' → (P tr ↔ Q tr').

  Lemma ltl_tme_now P P':
    (∀ l1 l2, Rl l1 l2 → (P l1 ↔ P' l2)) →
    ltl_tme (ℓ↓ P) (ℓ↓ P').
  Proof.
    intros Heq tr1 tr2 Htm. rewrite /trace_label /pred_at.
    destruct tr1, tr2=>//=; inversion Htm; simplify_eq. naive_solver.
  Qed.

  Lemma ltl_tme_always P P':
    ltl_tme P P' →
    ltl_tme (□ P) (□ P').
  Proof.
    intros Hse tr1 tr2 Htm. rewrite !trace_alwaysI. split.
    - intros Hal tr2' Hsuff. destruct (traces_match_suffix_of _ _ _ _ _ _ _ Htm Hsuff) as (?&?&Htm').
      apply (Hse _ _ Htm'). by apply Hal.
    - intros Hal tr1' Hsuff. destruct (traces_match_suffix_of_inv _ _ _ _ _ _ _ Htm Hsuff) as (?&?&Htm').
      apply (Hse _ _ Htm'). by apply Hal.
  Qed.

  Lemma ltl_tme_eventually P P':
    ltl_tme P P' →
    ltl_tme (◊ P) (◊ P').
  Proof.
    intros Hse tr1 tr2 Htm. rewrite !trace_eventuallyI. split.
    - intros (?&Hsuff&?). destruct (traces_match_suffix_of_inv _ _ _ _ _ _ _ Htm Hsuff) as (?&?&Htm').
      eexists _; split=>//. apply (Hse _ _ Htm'). naive_solver.
    - intros (?&Hsuff&?). destruct (traces_match_suffix_of _ _ _ _ _ _ _ Htm Hsuff) as (?&?&Htm').
      eexists _; split=>//. apply (Hse _ _ Htm'). naive_solver.
  Qed.

  Lemma ltl_tme_impl P P' Q Q':
    ltl_tme P P' →
    ltl_tme Q Q' →
    ltl_tme (P → Q) (P' → Q').
  Proof.
    intros HseP HseQ tr1 tr2 Htm. rewrite !trace_impliesI.
    split; intros Himpl H%(HseP _ _ Htm); apply (HseQ _ _ Htm); naive_solver.
  Qed.

  Lemma ltl_tme_forall {X} P P':
    (∀ (x : X), ltl_tme (P x) (P' x)) →
    ltl_tme (λ tr, ∀ x, P x tr) (λ tr, ∀ x, P' x tr).
  Proof. intros Hse tr1 tr2 Hupto. naive_solver. Qed.
End traces_match.
