From trillium.fairness Require Import fuel.
From Paco Require Import paco1 paco2 pacotac.

Definition auxtrace {Λ M} `{Countable (locale Λ)} (LM: LiveModel Λ M) := trace LM.(lm_ls) LM.(lm_lbl).

Section aux_trace.
  Context `{Countable (locale Λ)} `{LM: LiveModel Λ M}.

  Definition role_enabled ρ (δ: LiveState Λ M) := ρ ∈ M.(live_roles) δ.

  Definition fair_aux ρ (auxtr: auxtrace LM): Prop  :=
    forall n, pred_at auxtr n (λ δ _, role_enabled ρ δ) ->
         ∃ m, pred_at auxtr (n+m) (λ δ _, ¬role_enabled ρ δ)
              ∨ pred_at auxtr (n+m) (λ _ ℓ, ∃ tid, ℓ = Some (Take_step ρ tid)).

  Lemma fair_aux_after ρ auxtr n auxtr':
    fair_aux ρ auxtr ->
    after n auxtr = Some auxtr' ->
    fair_aux ρ auxtr'.
  Proof.
    rewrite /fair_aux => Hfair Hafter m Hpa.
    specialize (Hfair (n+m)).
    rewrite -> (pred_at_sum _ n) in Hfair. rewrite Hafter in Hfair.
    destruct (Hfair Hpa) as (p&Hp).
    exists (p). by rewrite <-Nat.add_assoc, ->!(pred_at_sum _ n), Hafter in Hp.
  Qed.

  CoInductive auxtrace_valid: auxtrace LM -> Prop :=
  | auxtrace_valid_singleton δ: auxtrace_valid ⟨δ⟩
  | auxtrace_valid_cons (δ: LiveState Λ M) ℓ (tr: auxtrace LM):
      LM.(lm_ls_trans) δ ℓ (trfirst tr) ->
      auxtrace_valid tr →
      auxtrace_valid (δ -[ℓ]-> tr).

  Lemma auxtrace_valid_forall (tr: auxtrace LM) :
    auxtrace_valid tr ->
    ∀ n, match after n tr with
         | Some ⟨ _ ⟩ | None => True
         | Some (δ -[ℓ]-> tr') => LM.(lm_ls_trans) δ ℓ (trfirst tr')
         end.
  Proof.
    intros Hval n. revert tr Hval. induction n as [|n]; intros tr Hval;
      destruct (after _ tr) as [trn|] eqn: Heq =>//; simpl in Heq;
      simplify_eq; destruct trn =>//; inversion Hval; simplify_eq; try done.
    specialize (IHn _ H1) (* TODO *). rewrite Heq in IHn. done.
  Qed.

End aux_trace.

Ltac SS :=
  epose proof ls_fuel_dom;
  (* epose proof ls_mapping_dom; *)
  set_solver.

Definition live_tids `{Countable (locale Λ)} `{LM:LiveModel Λ M}
           (c : cfg Λ) (δ : LM.(lm_ls)) : Prop :=
  (∀ ρ ζ, ls_mapping δ !! ρ = Some ζ -> is_Some (from_locale c.1 ζ)) ∧
  ∀ ζ e, from_locale c.1 ζ = Some e -> (to_val e ≠ None) ->
         ∀ ρ, ls_mapping δ !! ρ = Some ζ → ρ ∉ M.(live_roles) δ. 

Definition exaux_traces_match  `{Countable (locale Λ)} `{LM:LiveModel Λ M} :
  extrace Λ → auxtrace LM → Prop :=
  traces_match labels_match
               live_tids
               locale_step
               LM.(lm_ls_trans).

Section fairness_preserved.
  Context `{Countable (locale Λ)}.
  Context `{LM: LiveModel Λ M}.
  Implicit Type δ : LiveState Λ M.

  Lemma exaux_preserves_validity extr (auxtr : auxtrace LM):
    exaux_traces_match extr auxtr ->
    auxtrace_valid auxtr.
  Proof.
    revert extr auxtr. cofix CH. intros extr auxtr Hmatch.
    inversion Hmatch; first by constructor.
    constructor =>//. by eapply CH.
  Qed.

  Lemma exaux_preserves_termination extr (auxtr : auxtrace LM) :
    exaux_traces_match extr auxtr ->
    terminating_trace auxtr ->
    terminating_trace extr.
  Proof.
    intros Hmatch [n HNone].
    revert extr auxtr Hmatch HNone. induction n as [|n IHn]; first done.
    intros extr auxtr Hmatch HNone.
    replace (S n) with (1 + n) in HNone =>//.
    rewrite (after_sum' _ 1) in HNone.
    destruct auxtr as [s| s ℓ auxtr'];
      first by inversion Hmatch; simplify_eq; exists 1.
    simpl in HNone.
    inversion Hmatch; simplify_eq.
    apply terminating_trace_cons.
    eapply IHn =>//.
  Qed.

  Lemma traces_match_labels tid ℓ c δ rex (raux : auxtrace LM) :
    exaux_traces_match (c -[Some tid]-> rex) (δ -[ℓ]-> raux) ->
    ((∃ ρ, ℓ = Take_step ρ tid) ∨ (ℓ = Silent_step tid)).
  Proof.
    intros Hm. inversion Hm as [|?????? Hlab]; simplify_eq.
    destruct ℓ; eauto; inversion Hlab; simplify_eq; eauto.
  Qed.

  Lemma mapping_live_role (δ: LiveState Λ M) ρ:
    ρ ∈ M.(live_roles) δ ->
    is_Some (ls_mapping (Λ := Λ) δ !! ρ).
  Proof. rewrite -elem_of_dom ls_same_doms. SS. Qed.
  Lemma fuel_live_role (δ: LiveState Λ M) ρ:
    ρ ∈ M.(live_roles) δ ->
    is_Some (ls_fuel (Λ := Λ) δ !! ρ).
  Proof. rewrite -elem_of_dom. SS. Qed.

  Local Hint Resolve mapping_live_role: core.
  Local Hint Resolve fuel_live_role: core.

  Lemma match_locale_enabled (extr : extrace Λ) (auxtr : auxtrace LM) ζ ρ:
    ρ ∈ M.(live_roles) (trfirst auxtr) →
    exaux_traces_match extr auxtr ->
    ls_mapping (trfirst auxtr) !! ρ = Some ζ ->
    locale_enabled ζ (trfirst extr).
  Proof.
    intros Hlive Hm Hloc.
    rewrite /locale_enabled. have [HiS Hneqloc] := traces_match_first _ _ _ _ _ _ Hm.
    have [e Hein] := (HiS _ _ Hloc). exists e. split; first done.
    destruct (to_val e) eqn:Heqe =>//.
    exfalso. specialize (Hneqloc ζ e Hein). rewrite Heqe in Hneqloc.
    have Hv: Some v ≠ None by []. by specialize (Hneqloc Hv ρ Hloc).
  Qed.

  Local Hint Resolve match_locale_enabled: core.
  Local Hint Resolve pred_first_trace: core.

  Definition fairness_induction_stmt ρ fm f m ζ extr (auxtr : auxtrace LM) δ c :=
      (infinite_trace extr ->
       (forall ζ, fair_ex ζ extr) ->
       fm = (f, m) ->
       exaux_traces_match extr auxtr ->
       c = trfirst extr -> δ = trfirst auxtr ->
       ls_fuel δ !! ρ = Some f ->
       ls_mapping δ !! ρ = Some ζ ->
       (pred_at extr m (λ c _, ¬locale_enabled ζ c) ∨ pred_at extr m (λ _ oζ, oζ = Some (Some ζ))) ->
      ∃ M, pred_at auxtr M (λ δ _, ¬role_enabled ρ δ)
           ∨ pred_at auxtr M (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0))).

  Local Lemma case1 ρ f m (extr' : extrace Λ) (auxtr' : auxtrace LM) δ ℓ :
    (∀ m0 : nat * nat,
         strict lt_lex m0 (f, m)
         → ∀ (f m: nat) (ζ: locale Λ) (extr : extrace Λ) (auxtr : auxtrace LM)
             (δ : LiveState Λ M) (c : cfg Λ), fairness_induction_stmt ρ m0 f m ζ extr auxtr δ c) ->
    (ρ ∈ dom (ls_fuel (trfirst auxtr')) → oless (ls_fuel (trfirst auxtr') !! ρ) (ls_fuel δ !! ρ)) ->
    exaux_traces_match extr' auxtr' ->
    infinite_trace extr' ->
    ls_fuel δ !! ρ = Some f ->
    (∀ ζ, fair_ex ζ extr') ->
    ∃ M0 : nat,
      pred_at (δ -[ ℓ ]-> auxtr') M0
              (λ δ0 _, ¬ role_enabled ρ δ0)
      ∨ pred_at (δ -[ ℓ ]-> auxtr') M0
                (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)).
    Proof.
      intros IH Hdec Hmatch Hinf Hsome Hfair.
      unfold oless in Hdec.
      simpl in *.
      rewrite -> Hsome in *.
      destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq.
      - destruct (decide (ρ ∈ live_roles M (trfirst auxtr'))) as [Hρlive'|]; last first.
        { exists 1. left. unfold pred_at. simpl. destruct auxtr'; eauto. }
        have [ζ' Hζ'] : is_Some (ls_mapping (trfirst auxtr') !! ρ) by eauto.

        have Hloc'en: pred_at extr' 0 (λ (c : cfg Λ) (_ : option (olocale Λ)),
                          locale_enabled ζ' c).
        { rewrite /pred_at /= pred_first_trace. eauto. }

        have [p Hp] := (Hfair ζ' 0 Hloc'en).
        have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ (δ0 : LiveState Λ M) _, ¬ role_enabled ρ δ0)
                                  ∨ pred_at auxtr' M0 (λ (_ : LiveState Λ M) ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)).
        { eapply (IH _ _ _ p _ extr'); eauto.
          Unshelve. unfold strict, lt_lex. specialize (Hdec ltac:(by eapply elem_of_dom_2)). lia. }
        exists (1+P). rewrite !pred_at_sum. simpl. done.
      - exists 1. left. rewrite /pred_at /=. rewrite /role_enabled.
        destruct auxtr' =>/=.
        + apply not_elem_of_dom in Heq; eapply not_elem_of_weaken; last (by apply ls_fuel_dom); set_solver.
        + apply not_elem_of_dom in Heq; eapply not_elem_of_weaken; last (by apply ls_fuel_dom); set_solver.
    Qed.

  Lemma fairness_preserved_ind ρ:
    ∀ fm f m ζ (extr: extrace Λ) (auxtr: auxtrace LM) δ c,
      fairness_induction_stmt ρ fm f m ζ extr auxtr δ c.
  Proof.
    induction fm as [fm IH] using lex_ind.
    intros f m ζ extr auxtr δ c Hexinfin Hfair -> Htm -> -> Hfuel Hmapping Hexen.
    destruct extr as [|c ζ' extr'] eqn:Heq.
    { have [??] := Hexinfin 1. done. }
    have Hfair': (forall ζ, fair_ex ζ extr').
    { intros. by eapply fair_ex_cons. }
    destruct auxtr as [|δ ℓ auxtr']; first by inversion Htm.
    destruct (decide (ρ ∈ live_roles M δ)) as [Hρlive|]; last first.
    { exists 0. left. unfold pred_at. simpl. intros contra. eauto. }
    destruct (decide (Some ζ = ζ')) as [Hζ|Hζ].
    - rewrite <- Hζ in *.
      destruct (traces_match_labels _ _ _ _ _ _ Htm) as [[ρ' ->]| ->]; last first.
      + inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
        unfold ls_trans in Hls.
        destruct Hls as (? & Hlsdec & Hlsincr).
        unfold fuel_decr in Hlsdec.
        have Hmustdec: must_decrease ρ None δ (trfirst auxtr') (Some ζ).
        { constructor; eauto. }
        eapply case1 =>//.
        * move=> Hinfuel; apply Hlsdec => //; first set_solver.
        * eapply infinite_cons =>//.
      + (* Three cases: *)
(*            (1) ρ' = ρ and we are done *)
(*            (2) ρ' ≠ ρ but they share the same ρ -> ρ decreases *)
(*            (3) ρ' ≠ ρ and they don't have the same tid -> *)
(*            impossible because tid and the label must match! *)
        inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
        destruct (decide (ρ = ρ')) as [->|Hρneq].
        { exists 0. right. rewrite /pred_at /=. eauto. }
        destruct Hls as (?&Hsame&Hdec&Hnotinc&_).
        rewrite -Hsame /= in Hmapping.
        have Hmustdec: must_decrease ρ (Some ρ') δ (trfirst auxtr') (Some ζ).
        { constructor; eauto; congruence. }
        (* Copy and paste begins here *)
        eapply case1 =>//; last by eauto using infinite_cons.
        intros Hinfuels. apply Hdec =>//. SS.
    - (* Another thread is taking a step. *)
      destruct (decide (ρ ∈ live_roles M (trfirst auxtr'))) as [Hρlive'|]; last first.
      { exists 1. left. unfold pred_at. simpl. destruct auxtr'; eauto. }
      have [ζ'' Hζ''] : is_Some (ls_mapping (trfirst auxtr') !! ρ) by eauto.
      destruct (decide (ζ = ζ'')) as [<-|Hchange].
      + have [f' [Hfuel' Hff']] : exists f', ls_fuel (trfirst auxtr') !! ρ = Some f' ∧ f' ≤ f.
        { destruct ζ' as [ζ'|]; last first; simpl in *.
          - inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
            simpl in *. destruct ℓ; try done. destruct Hls as [_ [_ [Hnoninc _]]].
            have HnotNone: Some ρ ≠ None by congruence.
            specialize (Hnoninc ρ ltac:(SS) HnotNone).
            unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
            destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [|set_solver].
            eexists; split =>//. destruct Hnoninc as [Hnoninc|Hnoninc]=>//.
            apply elem_of_dom_2 in Heq. set_solver.
          - inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
            simpl in *. destruct ℓ as [ρ0 ζ0| ζ0|]; try done.
            + destruct Hls as (?&?&?&Hnoninc&?).
              unfold fuel_must_not_incr in Hnoninc.
              have Hneq: Some ρ ≠ Some ρ0 by congruence.
              specialize (Hnoninc ρ ltac:(SS) Hneq).
              unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
              destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [|set_solver].
              eexists; split =>//. destruct Hnoninc as [Hnoninc|Hnoninc]=>//.
              apply elem_of_dom_2 in Heq. set_solver.
            + destruct Hls as (?&?&Hnoninc&?).
              unfold fuel_must_not_incr in Hnoninc.
              have Hneq: Some ρ ≠ None by congruence.
              specialize (Hnoninc ρ ltac:(SS) Hneq).
              unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
              destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [|set_solver].
              eexists; split =>//. destruct Hnoninc as [Hnoninc|Hnoninc]=>//.
              apply elem_of_dom_2 in Heq. set_solver. }

        unfold fair_ex in *.
        have Hζ'en: pred_at extr' 0 (λ (c : cfg Λ) _, locale_enabled ζ c).
        { rewrite /pred_at /= pred_first_trace. inversion Htm; eauto. }
        destruct m as [| m'].
        { rewrite -> !pred_at_0 in Hexen. destruct Hexen as [Hexen|Hexen].
          - exfalso. apply Hexen. unfold locale_enabled. by eapply (match_locale_enabled _ _ _ _ _ Htm).
          - simplify_eq. }

        have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ δ0 _, ¬ role_enabled ρ δ0)
                        ∨ pred_at auxtr' M0 (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)).
        { eapply (IH _ _ _ m' _ extr'); eauto. by eapply infinite_cons. by inversion Htm. 
          Unshelve.
          - done.
          - unfold strict, lt_lex. lia. }
        exists (1+P). rewrite !pred_at_sum. simpl. done.
      + have [f' [Hfuel' Hff']] : exists f', ls_fuel (trfirst auxtr') !! ρ = Some f' ∧ f' < f.
        { destruct ζ' as [ζ'|]; last first; simpl in *.
          - inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
            simpl in *. destruct ℓ; try done. destruct Hls as [_ [Hdec _]].
            unfold fuel_decr in Hdec.
            have Hmd: must_decrease ρ None δ (trfirst auxtr') None.
            { econstructor. congruence. rewrite Hζ''. eauto. }
            specialize (Hdec ρ ltac:(SS) ltac:(SS) Hmd).
            unfold oleq in Hdec. rewrite Hfuel in Hdec.
            destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [by eexists|done].
          - inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
            simpl in *. destruct ℓ as [ρ0 ζ0| ζ0|]; try done.
            + destruct Hls as (?&?&Hdec&?&?).
              unfold fuel_decr in Hdec. simplify_eq.
              have Hmd: must_decrease ρ (Some ρ0) δ (trfirst auxtr') (Some ζ0).
              { econstructor 2. congruence. rewrite Hζ''; eauto. }
              specialize (Hdec ρ ltac:(SS) ltac:(SS) Hmd).
              unfold oleq in Hdec. rewrite Hfuel in Hdec.
              destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [by eexists|done].
            + destruct Hls as (?&Hdec&_).
              unfold fuel_decr in Hdec. simplify_eq.
              have Hmd: must_decrease ρ None δ (trfirst auxtr') (Some ζ0).
              { econstructor 2. congruence. rewrite Hζ''; eauto. }
              specialize (Hdec ρ ltac:(SS) ltac:(SS) Hmd).
              unfold oleq in Hdec. rewrite Hfuel in Hdec.
              destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [by eexists|done]. }

        unfold fair_ex in *.
        have: pred_at extr' 0 (λ c _, locale_enabled ζ'' c).
        { rewrite /pred_at /= pred_first_trace. inversion Htm; eauto. }
        have Hζ'en: pred_at extr' 0 (λ c _, locale_enabled ζ'' c).
        { rewrite /pred_at /= pred_first_trace. inversion Htm; eauto. }
        have [p Hp] := (Hfair' ζ'' 0 Hζ'en).
        have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ δ0 _, ¬ role_enabled ρ δ0)
                        ∨ pred_at auxtr' M0 (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)).
        { eapply (IH _ _ _ p _ extr'); eauto. by eapply infinite_cons. by inversion Htm.
          Unshelve. unfold strict, lt_lex. lia. }
        exists (1+P). rewrite !pred_at_sum. simpl. done.
  Qed.

  Theorem fairness_preserved (extr: extrace Λ) (auxtr: auxtrace LM):
    infinite_trace extr ->
    exaux_traces_match extr auxtr ->
    (forall ζ, fair_ex ζ extr) -> (forall ρ, fair_aux ρ auxtr).
  Proof.
    intros Hinfin Hmatch Hex ρ n Hn.
    unfold pred_at in Hn.
    destruct (after n auxtr) as [tr|] eqn:Heq =>//.
    setoid_rewrite pred_at_sum. rewrite Heq.
    have Hen: role_enabled ρ (trfirst tr) by destruct tr.
    have [ζ Hζ] : is_Some(ls_mapping (trfirst tr) !! ρ) by eauto.
    have [f Hfuel] : is_Some(ls_fuel (trfirst tr) !! ρ) by eauto.
    have Hex' := Hex ζ n.
    have [tr1' [Heq' Htr]] : exists tr1', after n extr = Some tr1' ∧ exaux_traces_match tr1' tr
     by eapply traces_match_after.
    have Hte: locale_enabled ζ (trfirst tr1').
    { rewrite /locale_enabled. have [HiS Hneqζ] := traces_match_first _ _ _ _ _ _ Htr.
      have [e Hein] := (HiS _ _ Hζ). exists e. split; first done.
      destruct (to_val e) eqn:Heqe =>//.
      exfalso. specialize (Hneqζ ζ e Hein). rewrite Heqe in Hneqζ.
      have HnotNull: Some v ≠ None by []. specialize (Hneqζ HnotNull ρ Hζ). done. }
    setoid_rewrite pred_at_sum in Hex'. rewrite Heq' in Hex'.
    have Hpa: pred_at extr n (λ c _, locale_enabled ζ c).
    { unfold pred_at. rewrite Heq'. destruct tr1'; eauto. }
    destruct (Hex' Hpa) as [m Hm].
    have ?: infinite_trace tr1'.
    { have Hinf := infinite_trace_after n extr Hinfin. by rewrite Heq' in Hinf. }
    eapply (fairness_preserved_ind ρ _ f m ζ _ tr); eauto.
    intros ?. by eapply fair_ex_after.
  Qed.

  Tactic Notation "inv" open_constr(P) := match goal with
                | [H: P |- _] => inversion H; clear H; simplify_eq
                                          end.

  (* TODO: Why do we need explicit [LM] here? *)
  Lemma valid_inf_system_trace_implies_traces_match_strong
        (φ : execution_trace Λ -> auxiliary_trace LM -> Prop)
        (ψ : _ → _ → Prop)
        ex atr iex iatr progtr (auxtr : auxtrace LM):
    (forall (ex: execution_trace Λ) (atr: auxiliary_trace LM),
        φ ex atr -> live_tids (LM:=LM) (trace_last ex) (trace_last atr)) ->
    (forall (ex: execution_trace Λ) (atr: auxiliary_trace LM),
        φ ex atr -> valid_state_evolution_fairness ex atr) ->
    (∀ extr auxtr, φ extr auxtr → ψ (trace_last extr) (trace_last auxtr)) →
    exec_trace_match ex iex progtr ->
    exec_trace_match atr iatr auxtr ->
    valid_inf_system_trace φ ex atr iex iatr ->
    traces_match labels_match
                 (λ σ δ, live_tids (LM := LM) σ δ ∧ ψ σ δ)
                 locale_step
                 LM.(lm_ls_trans) progtr auxtr.
  Proof.
    intros Hφ1 Hφ2 Hφψ.
    revert ex atr iex iatr auxtr progtr. cofix IH.
    intros ex atr iex iatr auxtr progtr Hem Ham Hval.
    inversion Hval as [?? Hphi |ex' atr' c [? σ'] δ' iex' iatr' oζ ℓ Hphi [=] ? Hinf]; simplify_eq.
    - inversion Hem; inversion Ham. econstructor; eauto.
      pose proof (Hφ1 ex atr Hphi).
      split; [by simplify_eq|]. simplify_eq. by apply Hφψ.
    - inversion Hem; inversion Ham. subst.
      pose proof (valid_inf_system_trace_inv _ _ _ _ _ Hinf) as Hphi'.
      destruct (Hφ2 (ex :tr[ oζ ]: (l, σ')) (atr :tr[ ℓ ]: δ') Hphi') as (?&?&?).
      econstructor.
      + eauto.
      + eauto.
      + match goal with
        | [H: exec_trace_match _ iex' _ |- _] => inversion H; clear H; simplify_eq
        end; done.
      + match goal with
        | [H: exec_trace_match _ iatr' _ |- _] => inversion H; clear H; simplify_eq
        end; done.
      + eapply IH; eauto.
  Qed.

  (* TODO: Why do we need explicit [LM] here? *)
  Lemma valid_inf_system_trace_implies_traces_match
        (φ: execution_trace Λ -> auxiliary_trace LM -> Prop)
        ex atr iex iatr progtr (auxtr : auxtrace LM):
    (forall (ex: execution_trace Λ) (atr: auxiliary_trace LM),
        φ ex atr -> live_tids (LM:=LM) (trace_last ex) (trace_last atr)) ->
    (forall (ex: execution_trace Λ) (atr: auxiliary_trace LM),
        φ ex atr -> valid_state_evolution_fairness ex atr) ->
    exec_trace_match ex iex progtr ->
    exec_trace_match atr iatr auxtr ->
    valid_inf_system_trace φ ex atr iex iatr ->
    exaux_traces_match progtr auxtr.
  Proof.
    intros Hφ1 Hφ2.
    revert ex atr iex iatr auxtr progtr. cofix IH.
    intros ex atr iex iatr auxtr progtr Hem Ham Hval.
    inversion Hval as [?? Hphi |ex' atr' c [? σ'] δ' iex' iatr' oζ ℓ Hphi [=] ? Hinf]; simplify_eq.
    - inversion Hem; inversion Ham. econstructor; eauto.
      pose proof (Hφ1 ex atr Hphi).
      by simplify_eq.
    - inversion Hem; inversion Ham. subst.
      pose proof (valid_inf_system_trace_inv _ _ _ _ _ Hinf) as Hphi'.
      destruct (Hφ2 (ex :tr[ oζ ]: (l, σ')) (atr :tr[ ℓ ]: δ') Hphi') as (?&?&?).
      econstructor.
      + eauto.
      + eauto.
      + match goal with
        | [H: exec_trace_match _ iex' _ |- _] => inversion H; clear H; simplify_eq
        end; done.
      + match goal with
        | [H: exec_trace_match _ iatr' _ |- _] => inversion H; clear H; simplify_eq
        end; done.
      + eapply IH; eauto.
  Qed.

End fairness_preserved.

Section fuel_dec_unless.
  Context `{Countable (locale Λ)}.
  Context `{LM: LiveModel Λ Mdl}.
  Implicit Type δ : LiveState Λ Mdl.

  Definition Ul (ℓ: LM.(mlabel)) :=
    match ℓ with
    | Take_step ρ _ => Some (Some ρ)
    | _ => None
    end.

  Definition Ψ (δ: LiveState Λ Mdl) :=
    (size $ ls_fuel δ) + [^ Nat.add map] ρ ↦ f ∈ ls_fuel δ, f.

  Lemma fuel_dec_unless (auxtr: auxtrace LM) :
    auxtrace_valid auxtr ->
    dec_unless (λ x, ls_under (ls_data x)) Ul Ψ auxtr.
  Proof.
    intros Hval n. revert auxtr Hval. induction n; intros auxtr Hval; last first.
    { edestruct (after (S n) auxtr) as [auxtrn|] eqn:Heq; rewrite Heq =>//.
      simpl in Heq;
      simplify_eq. destruct auxtrn as [|δ ℓ auxtr']=>//; last first.
      inversion Hval as [|???? Hmatch]; simplify_eq =>//.
      specialize (IHn _ Hmatch). rewrite Heq // in IHn. }
    edestruct (after 0 auxtr) as [auxtrn|] eqn:Heq; rewrite Heq =>//.
    simpl in Heq; simplify_eq. destruct auxtrn as [|δ ℓ auxtr']=>//; last first.

    inversion Hval as [|??? Htrans Hmatch]; simplify_eq =>//.
    destruct ℓ as [| tid' |];
      [left; eexists; done| right | inversion Htrans; naive_solver ].
    destruct Htrans as (Hne&Hdec&Hni&Hincl&Heq). rewrite -> Heq in *. split; last done.

    destruct (decide (dom $ ls_fuel δ = dom $ ls_fuel (trfirst auxtr'))) as [Hdomeq|Hdomneq].
    - destruct Hne as [ρ Hρtid].

      assert (ρ ∈ dom $ ls_fuel δ) as Hin by rewrite -ls_same_doms elem_of_dom //.
      pose proof Hin as Hin'. pose proof Hin as Hin''.
      apply elem_of_dom in Hin as [f Hf].
      rewrite Hdomeq in Hin'. apply elem_of_dom in Hin' as [f' Hf'].
      rewrite /Ψ -!size_dom Hdomeq.
      apply Nat.add_lt_mono_l.

      rewrite /Ψ (big_opM_delete (λ _ f, f) (ls_fuel $ ls_data (trfirst _)) ρ) //.
      rewrite (big_opM_delete (λ _ f, f) (ls_fuel  δ) ρ) //.
      apply Nat.add_lt_le_mono.
      { rewrite /fuel_decr in Hdec. specialize (Hdec ρ). rewrite Hf Hf' /= in Hdec.
        apply Hdec; [set_solver | set_solver | by econstructor]. }

      apply big_addM_leq_forall => ρ' Hρ'.
      rewrite dom_delete_L in Hρ'.
      have Hρneqρ' : ρ ≠ ρ' by set_solver.
      rewrite !lookup_delete_ne //.
      destruct (decide (ρ' ∈ dom $ ls_fuel δ)) as [Hin|Hnotin]; last set_solver.
      rewrite /fuel_must_not_incr in Hni.
      destruct (Hni ρ' ltac:(done) ltac:(done)); [done|set_solver].
    - assert (size $ ls_fuel (trfirst auxtr') < size $ ls_fuel δ).
      { rewrite -!size_dom. apply subset_size. set_solver. }
      apply Nat.add_lt_le_mono =>//.
      apply big_addM_leq_forall => ρ' Hρ'.
      destruct (Hni ρ' ltac:(set_solver) ltac:(done)); [done|set_solver].
  Qed.
End fuel_dec_unless.

Section destuttering_auxtr.
  Context `{Countable (locale Λ)}.
  Context `{LM: LiveModel Λ M}.

  (* Why is [LM] needed here? *)
  Definition upto_stutter_auxtr :=
    upto_stutter (λ x, ls_under (Λ:=Λ) (M:=M) (ls_data x)) (Ul (LM := LM)).

  Lemma can_destutter_auxtr auxtr:
    auxtrace_valid auxtr →
    ∃ mtr, upto_stutter_auxtr auxtr mtr.
  Proof.
    intros ?. eapply can_destutter.
    eapply fuel_dec_unless =>//.
  Qed.

End destuttering_auxtr.

Section upto_preserves.
  Context `{Countable (locale Λ)}.
  Context `{LM: LiveModel Λ M}.

  Lemma upto_stutter_mono' :
    monotone2 (upto_stutter_ind (λ x, ls_under (Λ:=Λ) (M:=M) (ls_data x)) (Ul (LM:=LM))).
  Proof.
    unfold monotone2. intros x0 x1 r r' IN LE.
    induction IN; try (econstructor; eauto; done).
  Qed.
  Hint Resolve upto_stutter_mono' : paco.

  Lemma upto_preserves_validity (auxtr : auxtrace LM) mtr:
    upto_stutter_auxtr auxtr mtr ->
    auxtrace_valid auxtr ->
    mtrace_valid mtr.
  Proof.
    revert auxtr mtr. pcofix CH. intros auxtr mtr Hupto Hval.
    punfold Hupto.
    induction Hupto as [| |btr str δ ????? IH].
    - pfold. constructor.
    - apply IHHupto. inversion Hval. assumption.
    - pfold; constructor=>//.
      + subst. inversion Hval as [| A B C Htrans E F ] =>//. subst. unfold ls_trans in *.
        destruct ℓ; try done. simpl in *. simplify_eq.
        destruct Htrans as [??].
        have <- //: ls_under $ trfirst btr = trfirst str.
        { destruct IH as [IH|]; last done. punfold IH. inversion IH =>//. }
      + right. eapply CH.
        { destruct IH =>//. }
        subst. by inversion Hval.
  Qed.

End upto_preserves.

Section upto_stutter_preserves_fairness_and_termination.
  Context `{Countable (locale Λ)}.
  Context `{LM: LiveModel Λ M}.

  Notation upto_stutter_aux := (upto_stutter (λ x, ls_under (Λ := Λ) (ls_data x)) (Ul (Λ := Λ) (LM := LM))).

  Lemma upto_stutter_mono'' : (* TODO fix this proliferation *)
    monotone2 (upto_stutter_ind (λ x, ls_under (Λ:=Λ) (M:=M) (ls_data x)) (Ul (LM:=LM))).
  Proof.
    unfold monotone2. intros x0 x1 r r' IN LE.
    induction IN; try (econstructor; eauto; done).
  Qed.
  Hint Resolve upto_stutter_mono' : paco.

  Lemma upto_stutter_fairness_0 ρ auxtr (mtr: mtrace M):
    upto_stutter_aux auxtr mtr ->
    (* role_enabled_model ρ (trfirst mtr) -> *)
    (∃ n, pred_at auxtr n (λ δ _, ¬role_enabled (Λ := Λ) ρ δ)
          ∨ pred_at auxtr n (λ _ ℓ, ∃ ζ, ℓ = Some (Take_step ρ ζ))) ->
    ∃ m, pred_at mtr m (λ δ _, ¬role_enabled_model ρ δ)
         ∨ pred_at mtr m (λ _ ℓ, ℓ = Some $ Some ρ).
    Proof.
      intros Hupto (* Hre *) [n Hstep].
      revert auxtr mtr Hupto (* Hre *) Hstep.
      induction n as [|n]; intros auxtr mtr Hupto (* Hre *) Hstep.
      - punfold Hupto. inversion Hupto; simplify_eq.
        + destruct Hstep as [Hpa|[??]]; try done.
          exists 0. left. rewrite /pred_at /=. rewrite /pred_at //= in Hpa.
        + rewrite -> !pred_at_0 in Hstep. exists 0.
          destruct Hstep as [Hstep| [tid Hstep]]; [left|right].
          * rewrite /pred_at /=. destruct mtr; simpl in *; try congruence.
          * exfalso. injection Hstep => Heq. rewrite -> Heq in *.
            unfold Ul in *. congruence.
        + rewrite -> !pred_at_0 in Hstep. exists 0.
          destruct Hstep as [Hstep| [tid Hstep]]; [left|right].
          * rewrite /pred_at //=.
          * rewrite /pred_at //=. injection Hstep. intros Heq. simplify_eq.
            unfold Ul in *. congruence.
      - punfold Hupto. inversion Hupto as [| |?????? ?? IH ]; simplify_eq.
        + destruct Hstep as [?|?]; done.
        + rewrite -> !pred_at_S in Hstep.
          eapply IHn; eauto.
          by pfold.
        + destruct (decide (ℓ' = Some ρ)).
          * simplify_eq.
            exists 0. right. rewrite pred_at_0 //.
          * have Hw: ∀ (P: nat -> Prop), (∃ n, P (S n)) -> (∃ n, P n).
            { intros P [x ?]. by exists (S x). }
            apply Hw. setoid_rewrite pred_at_S.
            eapply IHn; eauto.
            { destruct IH as [|]; done. }
    Qed.

  Lemma upto_stutter_fairness (auxtr:auxtrace LM) (mtr: mtrace M):
    upto_stutter_aux auxtr mtr ->
    (∀ ρ, fair_aux ρ auxtr) ->
    (∀ ρ, fair_model_trace ρ mtr).
  Proof.
    intros Hupto Hfa ρ n Hpmod.
    unfold pred_at in Hpmod.
    destruct (after n mtr) as [mtr'|] eqn:Heq; last done.
    destruct (upto_stutter_after _ _ n Hupto Heq) as (n'&auxtr'&Heq'&Hupto').
    have Hre: role_enabled_model ρ (trfirst mtr') by destruct mtr'.
    specialize (Hfa ρ).
    have Henaux : role_enabled ρ (trfirst auxtr').
    { have HUs: ls_under (trfirst auxtr') = trfirst mtr'.
      - punfold Hupto'. by inversion Hupto'.
      - unfold role_enabled, role_enabled_model in *.
        rewrite HUs //. }
    have Hfa' := (fair_aux_after ρ auxtr n' auxtr' Hfa Heq' 0).
    have Hpredat: pred_at auxtr' 0 (λ δ _, role_enabled ρ δ).
    { rewrite /pred_at /=. destruct auxtr'; done. }
    destruct (upto_stutter_fairness_0 ρ auxtr' mtr' Hupto' (Hfa' Hpredat)) as (m&Hres).
    exists m. rewrite !(pred_at_sum _ n) Heq //.
  Qed.

  Lemma upto_stutter_finiteness auxtr (mtr: mtrace M):
    upto_stutter_aux auxtr mtr ->
    terminating_trace mtr ->
    terminating_trace auxtr.
  Proof.
    intros Hupto [n Hfin].
    have [n' ?] := upto_stutter_after_None _ _ n Hupto Hfin.
    eexists; done.
  Qed.

End upto_stutter_preserves_fairness_and_termination.
