From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap.
From trillium.program_logic Require Export weakestpre adequacy.
From trillium.fairness Require Import action_model resources fuel.
From trillium.fairness.heap_lang Require Export lang tactics notation.

Set Default Proof Using "Type".


Class heapGpreS Σ `(LM: LiveModel heap_lang M) := HeapPreG {
  heapGpreS_inv :> invGpreS Σ;
  heapGpreS_gen_heap :> gen_heapGpreS loc val Σ;
  heapGpreS_fairness :> fairnessGpreS M Σ;
}.

Class heapGS Σ `(LM:LiveModel heap_lang M) := HeapG {
  heap_inG :> heapGpreS Σ LM;
  heap_invGS : invGS_gen HasNoLc Σ;
  heap_gen_heapGS :> gen_heapGS loc val Σ;
  heap_fairnessGS :> fairnessGS M Σ;
}.

Definition heapΣ (M: FairModel) : gFunctors :=
  #[ invΣ; gen_heapΣ loc val; fairnessΣ heap_lang M ].

Global Instance subG_heapPreG {Σ} `{LM:LiveModel heap_lang M} :
  subG (heapΣ M) Σ → heapGpreS Σ LM.
Proof. solve_inG. Qed.

#[global] Instance heapG_irisG `{LM: LiveModel heap_lang M}
 `{!heapGS Σ LM} : irisG heap_lang LM Σ := {
    iris_invGS := heap_invGS;
    state_interp extr auxtr :=
      (⌜valid_state_evolution_fairness extr auxtr⌝ ∗
       gen_heap_interp (trace_last extr).2.(heap) ∗
       model_state_interp (trace_last extr).1 (trace_last auxtr))%I ;
    fork_post tid := λ _, (tid ↦M ∅)%I;
}.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (pointsto (L:=loc) (V:=val) l (DfracOwn q) v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (pointsto (L:=loc) (V:=val) l (DfracOwn 1) v%V) (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl : core.
Hint Extern 1 (head_step _ _ _ _ _) => econstructor : core.
Hint Extern 0 (head_step (CmpXchg _ _ _) _ _ _ _) => eapply CmpXchgS : core.
Hint Extern 0 (head_step (AllocN _ _) _ _ _ _) => apply alloc_fresh : core.
Hint Resolve to_of_val : core.

#[global] Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
#[global] Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

#[global] Instance rec_atomic s f x e : Atomic s (Rec f x e).
Proof. solve_atomic. Qed.
#[global] Instance pair_atomic s v1 v2 : Atomic s (Pair (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
#[global] Instance injl_atomic s v : Atomic s (InjL (Val v)).
Proof. solve_atomic. Qed.
#[global] Instance injr_atomic s v : Atomic s (InjR (Val v)).
Proof. solve_atomic. Qed.
(** The instance below is a more general version of [Skip] *)
#[global] Instance beta_atomic s f x v1 v2 : Atomic s (App (RecV f x (Val v1)) (Val v2)).
Proof. destruct f, x; solve_atomic. Qed.
#[global] Instance unop_atomic s op v : Atomic s (UnOp op (Val v)).
Proof. solve_atomic. Qed.
#[global] Instance binop_atomic s op v1 v2 : Atomic s (BinOp op (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
#[global] Instance if_true_atomic s v1 e2 : Atomic s (If (Val $ LitV $ LitBool true) (Val v1) e2).
Proof. solve_atomic. Qed.
#[global] Instance if_false_atomic s e1 v2 : Atomic s (If (Val $ LitV $ LitBool false) e1 (Val v2)).
Proof. solve_atomic. Qed.
#[global] Instance fst_atomic s v : Atomic s (Fst (Val v)).
Proof. solve_atomic. Qed.
#[global] Instance snd_atomic s v : Atomic s (Snd (Val v)).
Proof. solve_atomic. Qed.

#[global] Instance fork_atomic s e : Atomic s (Fork e).
Proof. solve_atomic. Qed.

#[global] Instance allocN_atomic s v w : Atomic s (AllocN (Val v) (Val w)).
Proof. solve_atomic. Qed.
#[global] Instance alloc_atomic s v : Atomic s (Alloc (Val v)).
Proof. solve_atomic. Qed.
#[global] Instance load_atomic s v : Atomic s (Load (Val v)).
Proof. solve_atomic. Qed.
#[global] Instance store_atomic s v1 v2 : Atomic s (Store (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
#[global] Instance cmpxchg_atomic s v0 v1 v2 : Atomic s (CmpXchg (Val v0) (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
#[global] Instance faa_atomic s v1 v2 : Atomic s (FAA (Val v1) (Val v2)).
Proof. solve_atomic. Qed.

Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
Local Ltac solve_pure_exec :=
  subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

(** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] and [wp_lam] reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] and [wp_lam] do reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)
Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
#[global] Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
#[global] Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

#[global] Instance pure_recc f x (erec : expr) :
  PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
Proof. solve_pure_exec. Qed.
#[global] Instance pure_pairc (v1 v2 : val) :
  PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
Proof. solve_pure_exec. Qed.
#[global] Instance pure_injlc (v : val) :
  PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
Proof. solve_pure_exec. Qed.
#[global] Instance pure_injrc (v : val) :
  PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
  PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
Proof. unfold AsRecV in *. solve_pure_exec. Qed.

#[global] Instance pure_unop op v v' :
  PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
Proof. solve_pure_exec. Qed.

#[global] Instance pure_binop op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
Proof. solve_pure_exec. Qed.
(* Higher-priority instance for [EqOp]. *)
#[global] Instance pure_eqop v1 v2 :
  PureExec (vals_compare_safe v1 v2) 1
    (BinOp EqOp (Val v1) (Val v2))
    (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
Proof.
  intros Hcompare.
  cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
  { intros. revert Hcompare. solve_pure_exec. }
  rewrite /bin_op_eval /= decide_True //.
Qed.

#[global] Instance pure_if_true e1 e2 : PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
Proof. solve_pure_exec. Qed.

#[global] Instance pure_if_false e1 e2 : PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
Proof. solve_pure_exec. Qed.

#[global] Instance pure_fst v1 v2 :
  PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_snd v1 v2 :
  PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_case_inl v e1 e2 :
  PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_case_inr v e1 e2 :
  PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
Proof. solve_pure_exec. Qed.


(* TODO: move to corresponding files? *)
Section SSWP_MU.
  Context `{LM: LiveModel heap_lang M}.
  Context `{hGS: !heapGS Σ LM}.
  
  Definition sswp (s : stuckness) E e1 (Φ : expr → iProp Σ) : iProp Σ :=
    match to_val e1 with
    | Some v => |={E}=> (Φ (of_val v))
    | None => ∀ σ1,
        gen_heap_interp σ1.(heap) ={E,∅}=∗
        ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
        ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅}▷=∗ |={∅,E}=>
        gen_heap_interp σ2.(heap) ∗ Φ e2 ∗ ⌜efs = []⌝
    end%I.

  Lemma sswp_wand s e E (Φ Ψ : expr → iProp Σ) :
    (∀ e, Φ e -∗ Ψ e) -∗ sswp s E e Φ -∗ sswp s E e Ψ.
  Proof.
    rewrite /sswp. iIntros "HΦΨ HΦ".
    destruct (to_val e); [by iApply "HΦΨ"|].
    iIntros (?) "H". iMod ("HΦ" with "H") as "[%Hs HΦ]".
    iModIntro. iSplit; [done|]. iIntros (????).
    iDestruct ("HΦ" with "[//]") as "HΦ".
    iMod "HΦ". iIntros "!>!>". iMod "HΦ". iIntros "!>". iMod "HΦ" as "(?&?&?)".
    iIntros "!>". iFrame. by iApply "HΦΨ".
  Qed.

  Definition HL_LM_trace_interp' (extr: execution_trace heap_lang)
    (lmtr: auxiliary_trace LM) (τ: locale heap_lang): iProp Σ :=
    match extr with
    | {tr[ _ ]} => False
    | extr' :tr[oζ]: c' =>
        let c := trace_last extr' in
        let δ := trace_last lmtr in
        gen_heap_interp c'.2.(heap) ∗
        model_state_interp c.1 δ ∗
        ⌜ tids_smaller c.1 δ ⌝ ∗
        ⌜ oζ = Some τ ⌝ ∗
        ⌜ locale_step c (Some τ) c' ⌝
    end.

    Definition MU E ζ (P : iProp Σ) : iProp Σ :=
    ∀ extr atr,
      HL_LM_trace_interp' extr atr ζ ={E}=∗
      ∃ δ2 ℓ, state_interp extr (trace_extend atr ℓ δ2) ∗ P.

  Lemma MU_wand E ζ (P Q : iProp Σ) :
    (P -∗ Q) -∗ MU E ζ P -∗ MU E ζ Q.
  Proof.
    rewrite /MU. iIntros "HPQ HMU".
    iIntros (extr atr) "Hσ".
    iMod ("HMU" with "Hσ") as (??) "[Hσ HP]". iModIntro.
    iExists _, _. iFrame. by iApply "HPQ".
  Qed.

  Lemma MU_mask_weaken E1 E2 ζ (P: iProp Σ)
    (SUB: E1 ⊆ E2):
    MU E1 ζ P -∗ MU E2 ζ P.
  Proof.
    rewrite /MU. iIntros "MU".
    iIntros "**".
    iApply fupd_mask_mono; eauto.
    by iApply "MU". 
  Qed.

  From iris.base_logic.lib Require Import invariants.

  Lemma MU_inv E ns ζ P Q
    (NS: ↑ ns ⊆ E):
    inv ns Q ⊢ (▷ Q -∗ MU (E ∖ ↑ ns) ζ (P ∗ ▷ Q)) -∗ MU E ζ P.
  Proof. 
    iIntros "#INV SUB".
    rewrite /MU. iIntros (extr atr) "Hσ".
    iMod (inv_acc with "INV") as "[Q CLOS]"; [done| ].
    iMod ("SUB" with "[$] [$]") as "SUB".
    iDestruct "SUB" as "(%&%&SI&P&Q)".
    iFrame.
    iMod ("CLOS" with "[$]"). done.
  Qed. 

  (* TODO: move *)
  Lemma pre_step_inv E ns P Q
    (NS: ↑ ns ⊆ E):
    inv ns Q ⊢ (▷ Q -∗ |~{ E ∖ ↑ ns }~| (P ∗ ▷ Q)) -∗ |~{ E }~| P.
  Proof. 
    iIntros "#INV SUB".
    rewrite trillium.program_logic.weakestpre.pre_step_unseal /pre_step_def. 
    iIntros (extr atr) "Hσ".
    iMod (inv_acc with "INV") as "[Q CLOS]"; [done| ].
    iMod ("SUB" with "[$] [$]") as "SUB".
    iDestruct "SUB" as "(SI&P&Q)".
    iFrame.
    iMod ("CLOS" with "[$]"). done.
  Qed. 

  (* TODO: unify with existing locales_of_list_from_locale_from, 
     remove restriction for Λ *)
  Lemma locales_of_list_from_locale_from' {Λ: language} `{EqDecision (locale Λ)}
    tp0 tp1 ζ:
    ζ ∈ locales_of_list_from tp0 tp1 (Λ := Λ) ->
    is_Some (from_locale_from tp0 tp1 ζ).
  Proof.
    clear -tp0 tp1 ζ.
    revert tp0; induction tp1 as [|e1 tp1 IH]; intros tp0.
    { simpl. intros H. inversion H. }
    simpl.
    rewrite /locales_of_list_from /=. intros.
    destruct (decide (language.locale_of tp0 e1 = ζ)); simplify_eq; first set_solver.
    apply elem_of_cons in H as [?| ?]; [done| ].
    set_solver.
  Qed.

  (* TODO: have similar proof in other repo *)
  Lemma MSI_tids_smaller (σ: list expr) δ:
    ⊢ model_state_interp σ δ -∗ ⌜tids_smaller σ δ⌝.
  Proof. 
    rewrite /model_state_interp.
    iIntros "(%fm & %LE & %DEAD & %TP & X)".
    iPureIntro. red. intros.
    apply locales_of_list_from_locale_from'.
    destruct (decide (ζ ∈ locales_of_list σ)); [done| ].
    red in TP. specialize (TP _ n).
    red in LE. apply proj2 in LE. rewrite -LE in H.
    by apply not_elem_of_dom in TP. 
  Qed. 
  
  Lemma sswp_MU_wp_fupd s E E' ζ e Φ
    (NVAL: language.to_val e = None)
    :
    let sswp_post := λ e', (MU E' ζ ((|={E',E}=> WP e' @ s; ζ; E {{ Φ }})))%I in
      (|={E,E'}=> sswp s E' e sswp_post)%I -∗
      WP e @ s; ζ; E {{ Φ }}.
  Proof.
    simpl. rewrite wp_unfold /wp_pre.
    iIntros "Hsswp". rewrite NVAL. 
    iIntros (extr atr K tp1 tp2 σ1 Hvalid Hζ Hextr) "Hσ".
    iMod "Hsswp" as "foo".
    rewrite /sswp. rewrite NVAL.
    iSimpl in "Hσ". iDestruct "Hσ" as "(%EV & HEAP & MSI)".
    iSpecialize ("foo" with "HEAP").
    iMod "foo" as (Hs) "Hsswp".
    red in Hextr. rewrite Hextr. 
    iModIntro. iSplit.
    { iPureIntro. by rewrite Hextr in Hs. }
    iIntros (e2 σ2 efs Hstep).
    iDestruct ("Hsswp" with "[//]") as "Hsswp".
    iApply (step_fupdN_le 1); [| done| ].
    { pose proof (trace_length_at_least extr). lia. }
    simpl.
    iApply (step_fupd_wand with "Hsswp").
    iIntros ">(Hσ & HMU & ->)".
    rewrite /MU. iSpecialize ("HMU" $! (_ :tr[Some ζ]: _)  with "[MSI Hσ]").
    { rewrite /HL_LM_trace_interp'.
      iPoseProof (MSI_tids_smaller with "MSI") as "%TS".
      remember (trace_last extr) as xx. destruct xx as [tp h].
      inversion Hextr as [[TP H]]. 
      rewrite -TP in TS. 
      iApply bi.sep_assoc. iSplitL.
      2: { iPureIntro. repeat split; eauto.
           { replace tp with (tp, h).1 in TS by done.
             rewrite Heqxx in TS. apply TS. }
           simpl in Hζ. 
           rewrite -Hζ. simpl.
           (* rewrite locale_fill'.  *)
           eapply locale_step_atomic.
           3: { eapply @fill_step. apply Hstep. } 
           { rewrite -Heqxx Hextr. simpl. reflexivity. }
           reflexivity. }
      rewrite -Heqxx TP. simpl. iFrame. }
    iMod ("HMU") as (??) "[Hσ Hwp]". iMod "Hwp". iModIntro.
    iExists _, _. rewrite right_id_L. by iFrame.
  Qed.

  Lemma sswp_MU_wp s E ζ e (Φ : val → iProp Σ)
    (NVAL: language.to_val e = None):
    sswp s E e (λ e', MU E ζ (WP e' @ s; ζ;  E {{ Φ }})) -∗
      WP e @ s; ζ; E {{ Φ }}.
  Proof.
    iIntros "Hsswp". iApply sswp_MU_wp_fupd; auto. iModIntro.
    iApply (sswp_wand with "[] Hsswp").
    iIntros (?) "HMU". iApply (MU_wand with "[] HMU"). by iIntros "$ !>".
  Qed.

End SSWP_MU.
