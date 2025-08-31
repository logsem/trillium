From fairness Require Import inftraces trace_lookup trace_len.
From Paco Require Import paco1 paco2 pacotac.
From iris.proofmode Require Import tactics.



Section dec_unless.
  Context {St S' L L': Type}.
  Context (Us: St -> S').
  Context (Ul: L -> option L').

  Definition dec_unless Ψ (tr: trace St L) :=
    ∀ n, match after n tr with
         | Some ⟨ _ ⟩ | None => True
         | Some (s -[ℓ]-> tr') =>
           (∃ ℓ', Ul ℓ = Some ℓ') ∨
           (Ψ (trfirst tr') < Ψ s ∧ Us s = Us (trfirst tr'))
         end.

  Lemma dec_unless_next Ψ s ℓ tr (Hdec: dec_unless Ψ (s -[ℓ]-> tr)): dec_unless Ψ tr.
  Proof.
    intros n. specialize (Hdec (n+1)). rewrite (after_sum 1) // in Hdec.
  Qed.

End dec_unless.


Section destuttering.
  Context {St S' L L': Type}.
  Context (Us: St -> S').
  Context (Ul: L -> option L').

  Inductive upto_stutter_ind (upto_stutter_coind: trace St L -> trace S' L' -> Prop):
    trace St L -> trace S' L' -> Prop :=
  | upto_stutter_singleton s:
      upto_stutter_ind upto_stutter_coind ⟨s⟩ ⟨Us s⟩
  | upto_stutter_stutter btr str s ℓ:
      Ul ℓ = None ->
      (* (Us s = Us (trfirst btr) -> (or something like this...?) *)
      Us s = Us (trfirst btr) ->
      Us s = trfirst str ->
      upto_stutter_ind upto_stutter_coind btr str ->
      upto_stutter_ind upto_stutter_coind (s -[ℓ]-> btr) str
  | upto_stutter_step btr str s ℓ s' ℓ':
      Us s = s' ->
      Ul ℓ = Some ℓ' ->
      upto_stutter_coind btr str ->
      upto_stutter_ind upto_stutter_coind (s -[ℓ]-> btr) (s' -[ℓ']-> str).

  Definition upto_stutter := paco2 upto_stutter_ind bot2.

  Lemma upto_stutter_mono :
    monotone2 (upto_stutter_ind).
  Proof.
    unfold monotone2. intros x0 x1 r r' IN LE.
    induction IN; try (econstructor; eauto; done).
  Qed.
  Hint Resolve upto_stutter_mono : paco.

  Lemma upto_stutter_after {btr str} n {str'}:
    upto_stutter btr str ->
    after n str = Some str' ->
    ∃ n' btr', after n' btr = Some btr' ∧ upto_stutter btr' str'.
  Proof.
    assert (Hw: ∀ (P: nat -> Prop), (∃ n, P (S n)) -> (∃ n, P n)).
    { intros P [x ?]. by exists (S x). }
    revert btr str str'. induction n as [|n IH]; intros btr str str' Hupto Hafter.
    { injection Hafter => <-. clear Hafter. exists 0, btr. done. }
    revert str' Hafter. punfold Hupto. induction Hupto as
        [s|btr str s ℓ HUl HUs1 HUs2 Hind IHH|btr str s ℓ s' ℓ' ?? Hind].
    - intros str' Hafter. done.
    - intros str' Hafter.
      apply Hw. simpl. by apply IHH.
    - intros str' Hafter. simpl in Hafter.
      apply Hw. simpl. eapply IH; eauto. 
      by destruct Hind.
  Qed.

  Local Ltac gd t := generalize dependent t.

  Lemma upto_stutter_after'
    {btr : trace St L} {str : trace S' L'} (n : nat) {btr' : trace St L}:
    upto_stutter btr str
    → after n btr = Some btr'
      → ∃ (n' : nat) (str' : trace S' L'),
          after n' str = Some str' ∧ upto_stutter btr' str'.
  Proof.
    have Hw: ∀ (P: nat -> Prop), (∃ n, P (S n)) -> (∃ n, P n).
    { intros P [x ?]. by exists (S x). }

    intros. 
    gd btr. gd str. gd btr'. induction n as [|n IH]; intros btr' str btr Hupto Hafter.
    { injection Hafter => <-. clear Hafter. exists 0, str. done. }
    punfold Hupto.
    inversion Hupto; subst. 
    - done.
    - simpl in Hafter. rename btr0 into btr. 
      specialize (IH btr' str btr).
      eapply IH; eauto. 
      by pfold.
    - simpl in Hafter. rename btr0 into btr. rename str0 into str.
      specialize (IH btr' str btr).
      assert (upto_stutter btr str) as UPTO'.
      { inversion H1; eauto. done. }
      specialize (IH UPTO' Hafter) as (?&?&?&?). 
      eauto. 
  Qed. 

  Lemma upto_stutter_after_None {btr str} n:
    upto_stutter btr str ->
    after n str = None ->
    ∃ n', after n' btr = None.
  Proof.
    assert (Hw: ∀ (P: nat -> Prop), (∃ n, P (S n)) -> (∃ n, P n)).
    { intros P [x ?]. by exists (S x). }
    revert btr str. induction n as [|n IH]; intros btr str Hupto Hafter.
    { exists 0. done. }
    revert Hafter. punfold Hupto. induction Hupto as
        [s|btr str s ℓ HUl HUs1 HUs2 Hind IHH|btr str s ℓ s' ℓ' ?? Hind].
    - intros Hafter. by exists 1.
    - intros Hafter.
      apply Hw. simpl. by apply IHH.
    - intros Hafter. simpl in Hafter.
      apply Hw. simpl. eapply IH; eauto.
      by destruct Hind.
  Qed.

  Lemma upto_stutter_infinite_trace tr1 tr2 :
    upto_stutter tr1 tr2 → infinite_trace tr1 → infinite_trace tr2.
  Proof.
    intros Hstutter Hinf n.
    revert tr1 tr2 Hstutter Hinf.
    induction n as [|n IHn]; intros tr1 tr2 Hstutter Hinf.
    - punfold Hstutter.
    - punfold Hstutter.
      induction Hstutter.
      + specialize (Hinf (1 + n)).
        rewrite after_sum' in Hinf. simpl in *. apply is_Some_None in Hinf. done.
      + apply IHHstutter.
        intros m. specialize (Hinf (1 + m)).
        rewrite after_sum' in Hinf. simpl in *. done.
      + simpl. eapply (IHn btr str); [by destruct H1|].
        intros m. specialize (Hinf (1 + m)).
        rewrite after_sum' in Hinf. simpl in *. done.
  Qed.

  Lemma upto_stutter_trfirst btr str
    (CORR: upto_stutter btr str):
    trfirst str = Us (trfirst btr). 
  Proof.
    punfold CORR. by inversion CORR.
  Qed. 

  Program Fixpoint destutter_once_step N Ψ (btr: trace St L) :
    Ψ (trfirst btr) < N →
    dec_unless Us Ul Ψ btr →
    S' + (S' * L' * { btr' : trace St L | dec_unless Us Ul Ψ btr'}) :=
    match N as n return
          Ψ (trfirst btr) < n →
          dec_unless Us Ul Ψ btr →
          S' + (S' * L' * { btr' : trace St L | dec_unless Us Ul Ψ btr'})
    with
    | O => λ Hlt _, False_rect _ (Nat.nlt_0_r _ Hlt)
    | S N' =>
      λ Hlt Hdec,
      match btr as z return btr = z → S' + (S' * L' * { btr' : trace St L | dec_unless Us Ul Ψ btr'}) with
      | tr_singl s => λ _, inl (Us s)
      | tr_cons s l btr' =>
        λ Hbtreq,
        match Ul l as z return Ul l = z → S' + (S' * L' * { btr' : trace St L | dec_unless Us Ul Ψ btr'}) with
        | Some l' => λ _, inr (Us s, l', exist _ btr' _)
        | None => λ HUll, destutter_once_step N' Ψ btr' _ _
        end eq_refl
      end eq_refl
    end.
  Next Obligation.
  Proof.
    intros _ Ψ btr N' Hlt Hdec s l btr' -> l' HUll; simpl.
    eapply dec_unless_next; done.
  Qed.
  Next Obligation.
  Proof.
    intros _ Ψ btr N' Hlt Hdec s l btr' -> HUll; simpl in *.
    pose proof (Hdec 0) as [[? ?]|[? ?]]; [congruence|lia].
  Qed.
  Next Obligation.
  Proof.
    intros _ Ψ btr N' Hlt Hdec s l btr' -> HUll; simpl.
    eapply dec_unless_next; done.
  Qed.

  CoFixpoint destutter_gen Ψ N (btr: trace St L) :
    Ψ (trfirst btr) < N ->
    dec_unless Us Ul Ψ btr → trace S' L' :=
    λ Hlt Hdec,
    match destutter_once_step N Ψ btr Hlt Hdec with
    | inl s' => tr_singl s'
    | inr (s', l', z) => tr_cons s' l' (destutter_gen Ψ  (S (Ψ (trfirst $ proj1_sig z)))
                                                 (proj1_sig z) (Nat.lt_succ_diag_r _) (proj2_sig z))
    end.

  Definition destutter Ψ (btr: trace St L) :
    dec_unless Us Ul Ψ btr → trace S' L' :=
    λ Hdec,
    destutter_gen Ψ (S (Ψ (trfirst btr))) btr (Nat.lt_succ_diag_r _) Hdec.

  Lemma destutter_same_Us N Ψ btr Hlt Hdec:
    match destutter_once_step N Ψ btr Hlt Hdec with
    | inl s' | inr (s', _, _) => Us (trfirst btr) = s'
    end.
  Proof.
    revert btr Hlt Hdec. induction N as [|N]; first lia.
    intros btr Hlt Hdec. simpl.
    destruct btr as [s|s ℓ btr']; first done.
    generalize (destutter_once_step_obligation_1 Ψ (s -[ ℓ ]-> btr') N
                Hlt Hdec s ℓ btr' eq_refl).
    generalize (destutter_once_step_obligation_2 Ψ (s -[ ℓ ]-> btr') N Hlt Hdec s ℓ btr' eq_refl).
    generalize (destutter_once_step_obligation_3 Ψ (s -[ ℓ ]-> btr') N Hlt Hdec s ℓ btr' eq_refl).
    intros HunlessNone HltNone HdecSome.
    destruct (Ul ℓ) as [ℓ'|] eqn:Heq; cbn; first done.
    unfold dec_unless in Hdec.
    destruct (Hdec 0) as [[??]|[? Hsame]]; first congruence.
    rewrite Hsame. apply IHN.
  Qed.

  Lemma destutter_spec_ind N Ψ (btr: trace St L) (Hdec: dec_unless Us Ul Ψ btr)
    (Hlt: Ψ (trfirst btr) < N):
    upto_stutter btr (destutter_gen Ψ N btr Hlt Hdec).
  Proof.
    revert N btr Hlt Hdec.
    pcofix CH. pfold.
    induction N.
    { intros; lia. }
    intros btr Hlt Hdec.
    rewrite (trace_unfold_fold (destutter_gen _ _ _ _ _)).
    destruct btr as [s|s ℓ btr'].
    { simpl in *. econstructor. }
    cbn.
    generalize (destutter_once_step_obligation_1 Ψ (s -[ ℓ ]-> btr') N
                Hlt Hdec s ℓ btr' eq_refl).
    generalize (destutter_once_step_obligation_2 Ψ (s -[ ℓ ]-> btr') N Hlt Hdec s ℓ btr' eq_refl).
    generalize (destutter_once_step_obligation_3 Ψ (s -[ ℓ ]-> btr') N Hlt Hdec s ℓ btr' eq_refl).
    intros HunlessNone HltNone HdecSome.
    destruct (Ul ℓ) as [ℓ'|] eqn:Heq; cbn.
    - econstructor 3 =>//. right. apply (CH (S (Ψ $ trfirst btr'))).
    - econstructor 2=>//.
      + destruct (Hdec 0) as [[??]|[??]];congruence.
      + have ?: Us s = Us (trfirst btr').
        { destruct (Hdec 0) as [[??]|[? Hsame]]; congruence. }
        have HH := destutter_same_Us N Ψ btr' (HltNone eq_refl) (HunlessNone eq_refl).
        destruct (destutter_once_step N Ψ btr' (HltNone eq_refl) (HunlessNone eq_refl)) as
            [|[[??][??]]]eqn:Heq'; simpl in *; congruence.
      + rewrite -trace_unfold_fold.
        specialize (IHN btr' (HltNone eq_refl) (HunlessNone eq_refl)).
        match goal with
          [H : context[upto_stutter_ind]  |- ?Y] => let X := type of H in
                          suffices <-: X <-> Y; first done
        end.
        f_equiv.
        rewrite {1}(trace_unfold_fold (destutter_gen _ _ _ _ _)) /= -trace_unfold_fold //.
  Qed.

  Lemma destutter_spec Ψ (btr: trace St L) (Hdec: dec_unless Us Ul Ψ btr):
    upto_stutter btr (destutter Ψ btr Hdec).
  Proof. eapply destutter_spec_ind. Qed.

  Lemma can_destutter Ψ (btr: trace St L) (Hdec: dec_unless Us Ul Ψ btr):
    ∃ str, upto_stutter btr str.
  Proof. exists (destutter Ψ btr Hdec). apply destutter_spec. Qed.

End destuttering.


Section Lookup.
  Context {St S' L L' : Type}.
  Context {Us : St → S'}.
  Context (Ul: L -> option L').

  Lemma upto_stutter_trace_label_lookup {btr : trace St L} {str : trace S' L'} 
    (n : nat) st ℓ st' l:
    upto_stutter Us Ul btr str →
    btr !! n = Some (st, Some (ℓ, st')) ->
    Ul ℓ = Some l ->
    ∃ (n' : nat), str L!! n' = Some l.
  Proof.
    intros UPTO NTH MATCH.
    pose proof (trace_has_len btr) as [? LEN].
    apply trace_lookup_after_strong in NTH as (atr' & AFTER & A0). 
    ogeneralize * (upto_stutter_after' _ _ n UPTO); eauto.
    intros (n' & str' & AFTER' & UPTOn).
    exists n'.
    rewrite -(Nat.add_0_r n'). erewrite <- label_lookup_after; eauto.
    punfold UPTOn; [| by apply upto_stutter_mono].
    inversion UPTOn; subst; try congruence.
    rewrite label_lookup_0. congruence.  
  Qed.

  Lemma upto_stutter_state_lookup {btr : trace St L} {str : trace S' L'} n' st':
    upto_stutter Us Ul btr str
    → str S!! n' = Some st' ->
      ∃ n st, btr S!! n = Some st /\ Us st = st'.
  Proof.
    intros UPTO NTH.
    pose proof (trace_has_len str) as [? LEN]. 
    pose proof (proj1 (state_lookup_dom _ _ LEN n') (mk_is_Some _ _ NTH)) as BOUND.
    pose proof (proj2 (LEN _) BOUND) as [str_n AFTER].
    ogeneralize * (upto_stutter_after _ _ n' UPTO); eauto.
    intros (n & btr' & AFTER' & UPTOn).
    exists n.
    rewrite -(Nat.add_0_r n). erewrite <- state_lookup_after; eauto.
    rewrite state_lookup_0. f_equal.
    eexists. split; [reflexivity| ].
    etransitivity.
    { symmetry. eapply upto_stutter_trfirst; eauto. }
    apply Some_inj. rewrite -state_lookup_0.
    erewrite state_lookup_after; eauto. by rewrite Nat.add_0_r.
  Qed. 

  Lemma upto_stutter_state_lookup' {btr : trace St L} {str : trace S' L'} (n : nat) bst:
    upto_stutter Us Ul btr str
    → btr S!! n = Some bst ->
      ∃ (n' : nat),
        str S!! n' = Some (Us bst).
  Proof.
    intros UPTO NTH.
    pose proof (trace_has_len btr) as [? LEN]. 
    pose proof (proj1 (state_lookup_dom _ _ LEN n) (mk_is_Some _ _ NTH)) as BOUND.
    pose proof (proj2 (LEN _) BOUND) as [btr_n AFTER].
    ogeneralize * (upto_stutter_after' _ _ n UPTO); eauto.
    intros (n' & str' & AFTER' & UPTOn).
    exists n'.
    rewrite -(Nat.add_0_r n'). erewrite <- state_lookup_after; eauto.
    rewrite state_lookup_0. f_equal.     
    erewrite upto_stutter_trfirst; [..| apply UPTOn]; eauto.
    f_equal. apply Some_inj.
    rewrite -state_lookup_0.
    erewrite state_lookup_after; eauto. by rewrite Nat.add_0_r.
  Qed. 

End Lookup.
