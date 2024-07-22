From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.fairness Require Export inftraces.
From trillium.fairness Require Import utils.

Definition trace_implies {S L} (P Q : S → option L → Prop) (tr : trace S L) : Prop :=
  ∀ n, pred_at tr n P → ∃ m, pred_at tr (n+m) Q.

Lemma trace_implies_after {S L : Type} (P Q : S → option L → Prop) tr tr' k :
  after k tr = Some tr' →
  trace_implies P Q tr → trace_implies P Q tr'.
Proof.
  intros Haf Hf n Hp.
  have Hh:= Hf (k+n).
  have Hp': pred_at tr (k + n) P.
  { rewrite (pred_at_sum _ k) Haf /= //. }
  have [m Hm] := Hh Hp'. exists m.
  by rewrite <- Nat.add_assoc, !(pred_at_sum _ k), Haf in Hm.
Qed.

Lemma trace_implies_cons {S L : Type} (P Q : S → option L → Prop) s l tr :
  trace_implies P Q (s -[l]-> tr) → trace_implies P Q tr.
Proof. intros H. by eapply (trace_implies_after _ _ (s -[l]-> tr) tr 1). Qed.

Lemma pred_at_or {S L : Type} (P1 P2 : S → option L → Prop) tr n :
  pred_at tr n (λ s l, P1 s l ∨ P2 s l) ↔
  pred_at tr n P1 ∨
  pred_at tr n P2.
Proof.
  split.
  - revert tr.
    induction n as [|n IHn]; intros tr Htr.
    + destruct tr; [done|].
      rewrite !pred_at_0. rewrite !pred_at_0 in Htr.
      destruct Htr as [Htr | Htr]; [by left|by right].
    + destruct tr; [done|by apply IHn].
  - revert tr.
    induction n as [|n IHn]; intros tr Htr.
    + destruct tr; [done|].
      rewrite !pred_at_0 in Htr. rewrite !pred_at_0.
      destruct Htr as [Htr | Htr]; [by left|by right].
    + by destruct tr; [by destruct Htr as [Htr|Htr]|apply IHn].
Qed.


Definition trace_now {S T} (tr : trace S T) P := pred_at tr 0 P.
Definition trace_always {S T} (tr : trace S T) P := ∀ n, pred_at tr n P.
Definition trace_eventually {S T} (tr : trace S T) P := ∃ n, pred_at tr n P.
Definition trace_until {S T} (tr : trace S T) P Q :=
  ∃ n, pred_at tr n Q ∧ ∀ m, m < n → pred_at tr m P.

(* works for possibly finite traces *)
Definition trace_always' {S T} (tr : trace S T) P := 
  ∀ n, is_Some (after n tr) -> pred_at tr n P.

Lemma trace_always_always' {S T} (tr : trace S T) P:
  trace_always tr P -> trace_always' tr P.
Proof. rewrite /trace_always /trace_always'. done. Qed.

Section Match.
  Context {S1 S2 L1 L2: Type}. 

  Lemma traces_match_impl 
    (Rℓ1: L1 -> L2 -> Prop) (Rs1: S1 -> S2 -> Prop)
    (Rℓ2: L1 -> L2 -> Prop) (Rs2: S1 -> S2 -> Prop)
    (trans1: S1 -> L1 -> S1 -> Prop)
    (trans2: S2 -> L2 -> S2 -> Prop)
    tr1 tr2 :
    (∀ ℓ1 ℓ2, Rℓ1 ℓ1 ℓ2 → Rℓ2 ℓ1 ℓ2) →
    (∀ s1 s2, Rs1 s1 s2 → Rs2 s1 s2) →
    traces_match Rℓ1 Rs1 trans1 trans2 tr1 tr2 →
    traces_match Rℓ2 Rs2 trans1 trans2 tr1 tr2.
  Proof.
    intros HRℓ HRs. revert tr1 tr2. cofix IH. intros tr1 tr2 Hmatch.
    inversion Hmatch; simplify_eq.
    - constructor 1. by apply HRs.
    - constructor 2; [by apply HRℓ|by apply HRs|done|done|]. by apply IH.
  Qed.

  Context (Rℓ: L1 -> L2 -> Prop) (Rs: S1 -> S2 -> Prop)
      (trans1: S1 -> L1 -> S1 -> Prop) (trans2: S2 -> L2 -> S2 -> Prop). 

  Lemma traces_match_flip tr1 tr2 :
    traces_match Rℓ Rs trans1 trans2 tr1 tr2 ↔
      traces_match (flip Rℓ) (flip Rs) trans2 trans1 tr2 tr1.
  Proof.
    split.
    - revert tr1 tr2. cofix CH.
      intros tr1 tr2 Hmatch. inversion Hmatch; simplify_eq.
      { by constructor. }
      constructor; [done..|].
      by apply CH.
    - revert tr1 tr2. cofix CH.
      intros tr1 tr2 Hmatch. inversion Hmatch; simplify_eq.
      { by constructor. }
      constructor; [done..|].
      by apply CH.
  Qed.
  
  Lemma traces_match_infinite_trace tr1 tr2 :
    traces_match Rℓ Rs trans1 trans2 tr1 tr2 → infinite_trace tr1 → infinite_trace tr2.
  Proof.
    intros Hmatch Hinf n.
    specialize (Hinf n) as [tr' Hafter].
    apply traces_match_flip in Hmatch.
    by eapply traces_match_after in Hafter as [tr'' [Hafter' _]].
  Qed.

  Lemma traces_match_traces_implies 
    (P1 Q1 : S1 → option L1 → Prop)
    (P2 Q2 : S2 → option L2 → Prop)
    tr1 tr2 :
    traces_match Rℓ Rs trans1 trans2 tr1 tr2 →
    (∀ s1 s2 oℓ1 oℓ2, Rs s1 s2 →
                      match oℓ1, oℓ2 with
                      | Some ℓ1, Some ℓ2 => Rℓ ℓ1 ℓ2
                      | None, None => True
                      | _, _ => False
                      end →
                      P2 s2 oℓ2 → P1 s1 oℓ1) →
    (∀ s1 s2 oℓ1 oℓ2, Rs s1 s2 →
                      match oℓ1, oℓ2 with
                      | Some ℓ1, Some ℓ2 => Rℓ ℓ1 ℓ2
                      | None, None => True
                      | _, _ => False
                      end → Q1 s1 oℓ1 → Q2 s2 oℓ2) →
    trace_implies P1 Q1 tr1 → trace_implies P2 Q2 tr2.
  Proof.
    intros Hmatch HP HQ Htr1.
    intros n Hpred_at.
    rewrite /pred_at in Hpred_at.
    assert (traces_match (flip Rℓ)
              (flip Rs)
              trans2 trans1
              tr2 tr1) as Hmatch'.
    { by rewrite -traces_match_flip. }
    destruct (after n tr2) as [tr2'|] eqn:Htr2eq; [|done].
    eapply (traces_match_after) in Hmatch as (tr1' & Htr1eq & Hmatch); [|done].
    specialize (Htr1 n).
    rewrite {1}/pred_at in Htr1.
    rewrite Htr1eq in Htr1.
    destruct tr1' as [|s ℓ tr']; inversion Hmatch; simplify_eq; try by done.
    - assert (P1 s None) as HP1 by by eapply (HP _ _ _ None).
      destruct (Htr1 HP1) as [m Htr1'].
      exists m. rewrite pred_at_sum. rewrite pred_at_sum in Htr1'.
      destruct (after n tr1) as [tr1'|] eqn:Htr1eq'; [|done].
      eapply (traces_match_after) in Hmatch' as (tr2' & Htr2eq' & Hmatch'); [|done].
      rewrite Htr2eq'.
      rewrite /pred_at.
      rewrite /pred_at in Htr1'.
      destruct (after m tr1') as [tr1''|] eqn:Htr1eq''; [|done].
      eapply (traces_match_after) in Hmatch' as (tr2'' & Htr2eq'' & Hmatch''); [|done].
      rewrite Htr2eq''.
      destruct tr1''; inversion Hmatch''; simplify_eq; try by done.
      + by eapply (HQ _ _ None None).
      + by (eapply (HQ _ _ (Some _) _)).
    - assert (P1 s (Some ℓ)) as HP1 by by (eapply (HP _ _ _ (Some _))).
      destruct (Htr1 HP1) as [m Htr1'].
      exists m. rewrite pred_at_sum. rewrite pred_at_sum in Htr1'.
      destruct (after n tr1) as [tr1'|] eqn:Htr1eq'; [|done].
      eapply (traces_match_after) in Hmatch' as (tr2' & Htr2eq' & Hmatch'); [|done].
      rewrite Htr2eq'.
      rewrite /pred_at.
      rewrite /pred_at in Htr1'.
      destruct (after m tr1') as [tr1''|] eqn:Htr1eq''; [|done].
      eapply (traces_match_after) in Hmatch' as (tr2'' & Htr2eq'' & Hmatch''); [|done].
      rewrite Htr2eq''.
      destruct tr1''; inversion Hmatch''; simplify_eq; try by done.
      + by eapply (HQ _ _ None None).
      + by (eapply (HQ _ _ (Some _) _)).
  Qed.

  Lemma traces_match_after_None 
    tr1 tr2 n :
    traces_match Rℓ Rs trans1 trans2 tr1 tr2 ->
    after n tr2 = None ->
    after n tr1 = None.
  Proof.
    revert tr1 tr2.
    induction n; intros tr1 tr2; [done|].
    move=> /= Hm Ha.
    destruct tr1; first by inversion Hm.
    inversion Hm; simplify_eq. by eapply IHn.
  Qed.

  Lemma traces_match_trace_always'_state_2 tr1 tr2 (P: S2 -> Prop):
    traces_match Rℓ Rs trans1 trans2 tr1 tr2 ->
    (forall s1 s2, Rs s1 s2 -> P s2) ->
    trace_always' tr2 (fun s _ => P s).
  Proof.
    intros MATCH IMPL.
    red. intros n [atr2 AFTER2].
    red. rewrite AFTER2.
    eapply traces_match_after in MATCH as (atr1 & AFTER1 & MATCH'); eauto.
    apply traces_match_first in MATCH'.
    apply IMPL in MATCH'. by destruct atr2.
  Qed.     

End Match.

Fixpoint trace_take {S L} (n : nat) (tr : trace S L) : finite_trace S L :=
  match tr with
  | ⟨s⟩ => {tr[s]}
  | s -[ℓ]-> r => match n with
                  | 0 => {tr[s]}
                  | S n => (trace_take n r) :tr[ℓ]: s
                  end
  end.

Fixpoint trace_filter {S L} (f : S → L → Prop)
           `{∀ s l, Decision (f s l)}
           (tr : finite_trace S L) : finite_trace S L :=
  match tr with
  | {tr[s]} => {tr[s]}
  | tr :tr[ℓ]: s => if (bool_decide (f s ℓ))
                    then trace_filter f tr :tr[ℓ]: s
                    else trace_filter f tr
  end.

Fixpoint count_labels {S L} (ft : finite_trace S L) : nat :=
  match ft with
  | {tr[_]} => 0
  | ft' :tr[_]: _ => Datatypes.S (count_labels ft')
  end.

Lemma count_labels_sum {S L} (P : S → L → Prop)
           `{∀ s l, Decision (P s l)} n m mtr mtr' :
  after n mtr = Some mtr' →
  count_labels (trace_filter P $ trace_take (n+m) mtr) =
  count_labels ((trace_filter P $ trace_take n mtr)) +
    count_labels ((trace_filter P $ trace_take m mtr')).
Proof.
  revert mtr mtr'.
  induction n=> /=; intros mtr mtr' Hafter.
  { simplify_eq. by destruct mtr'. }
  destruct mtr; [done|]. simpl.
  case_bool_decide.
  - simpl. f_equiv. by apply IHn.
  - by apply IHn.
Qed.

Lemma pred_at_impl {S L} (tr:trace S L) n (P Q : S → option L → Prop) :
  (∀ s l, P s l → Q s l) → pred_at tr n P → pred_at tr n Q.
Proof.
  rewrite /pred_at. intros HPQ HP.
  destruct (after n tr); [|done].
  by destruct t; apply HPQ.
Qed.

Lemma pred_at_neg {S L} (tr:trace S L) n (P : S → option L → Prop) :
  is_Some (after n tr) →
  ¬ pred_at tr n P ↔ pred_at tr n (λ s l, ¬ P s l).
Proof.
  rewrite /pred_at. intros Hafter. split.
  - intros HP.
    destruct (after n tr).
    + by destruct t.
    + by apply is_Some_None in Hafter.
  - intros HP.
    destruct (after n tr).
    + by destruct t.
    + by apply is_Some_None in Hafter.
Qed.

Lemma infinite_trace_after' {S T} n (tr : trace S T) :
  infinite_trace tr -> ∃ tr', after n tr = Some tr' ∧ infinite_trace tr'.
Proof. 
  revert tr.
  induction n; intros tr Hinf.
  { exists tr. done. }
  pose proof (IHn _ Hinf) as [tr' [Hafter Hinf']].
  pose proof (Hinf' 1) as [tr'' Htr'].
  exists tr''.
  replace (Datatypes.S n) with (n + 1) by lia.
  rewrite after_sum'. rewrite Hafter. split; [done|].
  intros n'.
  specialize (Hinf' (Datatypes.S n')).
  destruct tr'; [done|].
  simpl in *. simplify_eq. done.
Qed.

Lemma infinite_trace_after'' {S T} n (tr tr' : trace S T) :
  after n tr = Some tr' → infinite_trace tr → infinite_trace tr'.
Proof.
  intros Hafter Hinf m. specialize (Hinf (n+m)).
  rewrite after_sum' in Hinf. rewrite Hafter in Hinf. done.
Qed.

Fixpoint finite_trace_to_trace {S L} (tr : finite_trace S L) : trace S L :=
  match tr with
  | {tr[s]} => ⟨s⟩
  | tr :tr[ℓ]: s => s -[ℓ]-> (finite_trace_to_trace tr)
  end.


Lemma pred_at_after_is_Some {S T} (tr : trace S T) n P :
  pred_at tr n P → is_Some $ after n tr.
Proof. rewrite /pred_at. by case_match. Qed.

Lemma after_is_Some_le {S T} (tr : trace S T) n m :
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

Lemma trace_eventually_until {S T} (tr : trace S T) P :
  trace_eventually tr P → trace_until tr (λ s l, ¬ P s l) P.
Proof.
  intros [n Hn].
  induction n as [n IHn] using lt_wf_ind.
  assert ((∀ m, m < n → pred_at tr m (λ s l, ¬ P s l)) ∨
            ¬ (∀ m, m < n → pred_at tr m (λ s l, ¬ P s l))) as [HP|HP];
    [|by eexists _|].
  { apply ExcludedMiddle. }
  eapply not_forall_exists_not in HP as [n' HP].
  apply Classical_Prop.imply_to_and in HP as [Hlt HP].
  apply pred_at_neg in HP; last first.
  { eapply after_is_Some_le; [|by eapply pred_at_after_is_Some]. lia. }
  eapply pred_at_impl in HP; last first.
  { intros s l H. apply NNP_P. apply H. }
  specialize (IHn n' Hlt HP) as [n'' [H' H'']].
  exists n''. done.
Qed.

Lemma trace_eventually_cons {S T} s l (tr : trace S T) P :
  trace_eventually tr P → trace_eventually (s -[l]-> tr) P.
Proof. intros [n HP]. by exists (Datatypes.S n). Qed.


Lemma trace_always_inf {S T} (tr : trace S T) P:
  trace_always tr P -> infinite_trace tr.
Proof. 
  intros ALW. red. intros n.
  destruct (after n tr) eqn:NTH; [done| ].
  red in ALW. rewrite /pred_at in ALW.
  specialize (ALW n). by rewrite NTH in ALW.
Qed. 


(* TODO: move, find existing *)
Lemma forall2_comm {A B: Type} (P: A -> B -> Prop):
  (forall a b, P a b) <-> (forall b a, P a b).
Proof. done. Qed.

(* TODO: move, find existing *)
Lemma ex_all_impl {A: Type} (P: A -> Prop) (Q: Prop):
  ((exists x, P x) -> Q) <-> (forall x, P x -> Q).
Proof. set_solver. Qed. 

Lemma trace_always'_state_after {S T} (tr : trace S T) P:
  trace_always' tr (fun s _ => P s) <-> forall tr' i (AFTER: after i tr = Some tr'), P (trfirst tr').
Proof. 
  rewrite /trace_always'.
  rewrite forall2_comm. apply forall_proper. intros i.
  rewrite /is_Some. rewrite ex_all_impl. apply forall_proper. intros tr'.
  apply and_iff_pre. intros AFTER.
  rewrite /pred_at. rewrite AFTER. by destruct tr'. 
Qed.

(* TODO: move *)
Lemma after_after {St L: Type} (tr1 tr2 tr3: trace St L) i j
  (AFTERi: after i tr1 = Some tr2)
  (AFTERj: after j tr2 = Some tr3):
  after (i + j) tr1 = Some tr3.
Proof. 
  generalize dependent tr3. induction j.
  { simpl. rewrite Nat.add_0_r. congruence. }
  intros. 
  rewrite -Nat.add_1_r in AFTERj. rewrite after_sum' in AFTERj.
  destruct (after j tr2) eqn:Aj; [| done].
  specialize (IHj _ eq_refl).
  rewrite Nat.add_succ_r -Nat.add_1_r. by rewrite after_sum' IHj.
Qed. 

Lemma trace_always'_after {S T} (tr tr' : trace S T) i P
  (AFTER: after i tr = Some tr'):
  trace_always' tr P -> trace_always' tr' P.
Proof. 
  rewrite /trace_always'. intros ALW n [atr' AFTER'].
  opose proof * (after_after tr tr') as AFTER''; eauto.
  ospecialize * ALW.
  { red. eexists. apply AFTER''. }
  red in ALW. rewrite AFTER'' in ALW.
  red. rewrite AFTER'. done.
Qed. 

Section Upto.
  Context {St S' L L': Type} (Us: St -> S') (Ul: L -> option L'). 

  Lemma trace_eventually_stutter_preserves           
    tr1 tr2 P :
    upto_stutter Us Ul tr1 tr2 →
    trace_eventually tr2 P →
    trace_eventually tr1 (λ s l, P (Us s) (l ≫= Ul)).
  Proof.
    intros Hstutter [n Heventually].
    revert tr1 tr2 Hstutter Heventually.
    induction n as [|n IHn]; intros tr1 tr2 Hstutter Heventually.
    - punfold Hstutter; [|apply upto_stutter_mono].
      induction Hstutter.
      + rewrite /pred_at in Heventually. simpl in *. exists 0. rewrite /pred_at. simpl in *. done.
      + destruct (IHHstutter Heventually) as [n Heventually'].
        exists (1 + n). rewrite /pred_at. rewrite after_sum'. simpl.
        done.
      + rewrite /pred_at in Heventually. simpl in *. exists 0. rewrite /pred_at. simpl.
        simplify_eq. rewrite H0. done.
    - punfold Hstutter; [|apply upto_stutter_mono].
      induction Hstutter.
      + rewrite /pred_at in Heventually. simpl in *. exists 0. rewrite /pred_at. simpl in *. done.
      + destruct (IHHstutter Heventually) as [n' Heventually'].
        exists (1 + n'). rewrite /pred_at. rewrite after_sum'. simpl.
        done.
      + apply trace_eventually_cons.
        assert (pred_at str n P) as Heventually'.
        { rewrite /pred_at in Heventually.
          simpl in *. done. }
        eapply IHn; [|done].
        rewrite /upaco2 in H1. destruct H1; [done|done].
  Qed.

  (* TODO: move? *)
  Lemma upto_stutter_trfirst btr str
    (CORR: upto_stutter Us Ul btr str):
    trfirst str = Us (trfirst btr). 
  Proof.
    punfold CORR; [| apply upto_stutter_mono]. by inversion CORR.
  Qed. 

  Lemma upto_preserves_trace_always'_state
    tr1 tr2 (P: S' -> Prop) :
    upto_stutter Us Ul tr1 tr2 →
    trace_always' tr1 (λ s _, P (Us s)) ->
    trace_always' tr2 (fun s _ => P s).
  Proof.
    intros UPTO ALW1.
    red. intros n2 [atr2 AFTER2]. red. rewrite AFTER2.
    opose proof * upto_stutter_after as (n1 & atr1 & AFTER1 & UPTO'); eauto.
    enough (P (trfirst atr2)); [by destruct atr2| ].
    apply upto_stutter_trfirst in UPTO'. rewrite UPTO'.
    red in ALW1. ospecialize * ALW1; eauto.
    red in ALW1. rewrite AFTER1 in ALW1.
    by destruct atr1. 
  Qed.

End Upto.
