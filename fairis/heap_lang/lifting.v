From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl.
From iris.base_logic Require Export gen_heap.
From trillium.prelude Require Import classical_instances.
From trillium.program_logic Require Export weakestpre adequacy.
From trillium.fairness Require Export fairness resources fair_termination fuel fuel_termination.
From trillium.program_logic Require Import ectx_lifting.
From trillium.fairness.heap_lang Require Export lang.
From trillium.fairness.heap_lang Require Import tactics notation.
Set Default Proof Using "Type".

Canonical Structure ModelO (M : FairModel) := leibnizO M.
Canonical Structure RoleO (M : FairModel) := leibnizO (M.(fmrole)).

Class heapGpreS Σ `(LM: LiveModel heap_lang M) := HeapPreG {
  heapGpreS_inv :> invGpreS Σ;
  heapGpreS_gen_heap :> gen_heapGpreS loc val Σ;
  heapGpreS_fairness :> fairnessGpreS LM Σ;
}.

Class heapGS Σ `(LM:LiveModel heap_lang M) := HeapG {
  heap_inG :> heapGpreS Σ LM;
  heap_invGS : invGS_gen HasNoLc Σ;
  heap_gen_heapGS :> gen_heapGS loc val Σ;
  heap_fairnessGS :> fairnessGS LM Σ;
}.

Definition heapΣ (M : FairModel) : gFunctors :=
  #[ invΣ; gen_heapΣ loc val; fairnessΣ heap_lang M ].

Global Instance subG_heapPreG {Σ} `{LM : LiveModel heap_lang M} :
  subG (heapΣ M) Σ → heapGpreS Σ LM.
Proof. solve_inG. Qed.

#[global] Instance heapG_irisG `{LM:LiveModel heap_lang M} `{!heapGS Σ LM} : irisG heap_lang LM Σ := {
    iris_invGS := heap_invGS;
    state_interp extr auxtr :=
      (⌜valid_state_evolution_fairness extr auxtr⌝ ∗
       gen_heap_interp (trace_last extr).2.(heap) ∗
       model_state_interp (trace_last extr).1 (trace_last auxtr))%I ;
    fork_post tid := λ _, (tid ↦M ∅)%I;
}.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l (DfracOwn q) v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=val) l (DfracOwn 1) v%V) (at level 20) : bi_scope.
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

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl : core.
Local Hint Extern 1 (head_step _ _ _ _ _) => econstructor : core.
Local Hint Extern 0 (head_step (CmpXchg _ _ _) _ _ _ _) => eapply CmpXchgS : core.
Local Hint Extern 0 (head_step (AllocN _ _) _ _ _ _) => apply alloc_fresh : core.
Local Hint Resolve to_of_val : core.

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

Section lifting.
Context `{LM:LiveModel heap_lang M}.
Context `{!heapGS Σ LM}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.
Implicit Types tid : nat.

Definition sswp (s : stuckness) E e1 (Φ : expr → iProp Σ) : iProp Σ :=
  match to_val e1 with
  | Some v => |={E}=> (Φ (of_val v))
  | None => ∀ σ1,
      gen_heap_interp σ1.(heap) ={E,∅}=∗
       ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
       ∀ e2 σ2 efs,
         ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅}▷=∗ |={∅,E}=>
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

Lemma has_fuels_decr E tid fs :
  tid ↦M++ fs -∗ |~{E}~| tid ↦M fs.
Proof.
  iIntros "Hf". rewrite weakestpre.pre_step_unseal.
  iIntros (extr atr) "[%Hvse [Hσ Hm]]".
  iMod (model_state_interp_has_fuels_decr with "Hm Hf") as "[$ $]". by iFrame.
Qed.

Lemma has_fuels_dealloc E tid fs ρ δ :
  ρ ∉ live_roles _ δ → frag_model_is δ -∗ tid ↦M fs -∗
  |~{E}~| frag_model_is δ ∗ tid ↦M (delete ρ fs).
Proof.
  iIntros (Hnin) "Hst Hf". rewrite weakestpre.pre_step_unseal.
  iIntros (extr atr) "[%Hvse [Hσ Hm]]".
  iMod (model_state_interp_has_fuels_dealloc with "Hm Hst Hf") as "[Hm Hf]";
    [done|by iFrame].
Qed.

(* Rule from the Trillium article *)
Lemma wp_role_dealloc s tid E e fs ρ δ Φ :
  ρ ∉ live_roles _ δ → frag_model_is δ -∗ tid ↦M fs -∗
  (frag_model_is δ -∗ tid ↦M (delete ρ fs) -∗ WP e @ s; tid; E {{ Φ }}) -∗
  WP e @ s; tid; E {{ Φ }}.
Proof.
  iIntros (Hnin) "HM Hfuels Hwp".
  iMod (has_fuels_dealloc with "HM Hfuels") as "[HM Hfuels]"; [done|].
  by iApply ("Hwp" with "HM Hfuels").
Qed.

Lemma wp_step_model s tid ρ (f1 : nat) fs fr s1 s2 E e Φ :
  TCEq (to_val e) None →
  fmtrans M s1 (Some ρ) s2 →
  M.(live_roles) s2 ⊆ M.(live_roles) s1 →
  ρ ∉ dom fs →
  ▷ frag_model_is s1 -∗
  ▷ tid ↦M ({[ρ:=f1]} ∪ fmap S fs) -∗
  ▷ frag_free_roles_are fr -∗
  sswp s E e (λ e', frag_model_is s2 -∗
                    tid ↦M ({[ρ:=(LM.(lm_fl) s2)]} ∪ fs) -∗
                    frag_free_roles_are fr -∗
                    WP e' @ s; tid; E {{ Φ }} ) -∗
  WP e @ s; tid; E {{ Φ }}.
Proof.
  iIntros (Hval Htrans Hlive Hdom) ">Hst >Hfuel1 >Hfr Hwp".
  rewrite wp_unfold /wp_pre.
  rewrite /sswp. simpl. rewrite Hval.
  iIntros (extr atr K tp1 tp2 σ1 Hvalid Hloc Hexend) "(% & Hsi & Hmi)".
  iMod ("Hwp" with "Hsi") as (Hred) "Hwp". iIntros "!>".
  iSplitR; [by rewrite Hexend in Hred|]. iIntros (????). rewrite Hexend.
  iMod ("Hwp" with "[//]") as "Hwp". iIntros "!>!>". iMod "Hwp". iIntros "!>".
  iApply step_fupdN_intro; [done|]. iIntros "!>".
  iMod "Hwp" as "[Hσ [Hwp ->]]".
  iDestruct (model_agree' with "Hmi Hst") as %Hmeq. iFrame.
  rewrite /trace_ends_in in Hexend. rewrite -Hexend.
  iMod (update_model_step with "Hfuel1 Hst Hmi") as
    (δ2 Hvse) "(Hfuel & Hst & Hmod)"; eauto.
  - rewrite -Hloc. eapply locale_step_atomic; eauto. by apply fill_step.
  - iModIntro; iExists δ2, (Take_step ρ tid). rewrite big_sepL_nil. iFrame.
    iSplit; [done|]. iDestruct ("Hwp" with "Hst Hfuel Hfr") as "Hwp". by iFrame.
Qed.

Lemma wp_step_model_singlerole s tid ρ (f1 : nat) fr s1 s2 E e Φ :
  TCEq (to_val e) None →
  fmtrans M s1 (Some ρ) s2 →
  M.(live_roles) s2 ⊆ M.(live_roles) s1 →
  ▷ frag_model_is s1 -∗ ▷ tid ↦M {[ρ := f1]} -∗ ▷ frag_free_roles_are fr -∗
  sswp s E e (λ e', frag_model_is s2 -∗
                    tid ↦M {[ρ := (LM.(lm_fl) s2)]} -∗
                    frag_free_roles_are fr -∗
                    WP e' @ s; tid; E {{ Φ }} ) -∗
  WP e @ s; tid; E {{ Φ }}.
Proof.
  iIntros (Hval Htrans Hlive) ">Hst >Hfuel1 >Hfr Hwp".
  replace ({[ρ := f1]}) with ({[ρ := f1]} ∪ (fmap S ∅:gmap _ _)); last first.
  { rewrite fmap_empty. rewrite right_id_L. done. }
  iApply (wp_step_model with "Hst Hfuel1 Hfr"); [done|set_solver|done|].
  iApply (sswp_wand with "[] Hwp"). iIntros (e') "Hwp Hst Hfuel1 Hfr".
  rewrite right_id_L. iApply ("Hwp" with "Hst Hfuel1 Hfr").
Qed.

Lemma wp_step_fuel s tid E e fs Φ :
  fs ≠ ∅ → ▷ tid ↦M++ fs -∗
  sswp s E e (λ e', tid ↦M fs -∗ WP e' @ s; tid; E {{ Φ }} ) -∗
  WP e @ s; tid; E {{ Φ }}.
Proof.
  iIntros (?) ">HfuelS Hwp". rewrite wp_unfold /wp_pre /sswp /=.
  destruct (to_val e).
  { iMod (has_fuels_decr with "HfuelS") as "Hfuel".
    iDestruct ("Hwp" with "Hfuel") as "Hwp".
    iDestruct (wp_value_inv with "Hwp") as "Hwp". by iMod "Hwp". }
  iIntros (extr atr K tp1 tp2 σ1 Hvalid Hloc Hends) "(%Hvalid' & Hsi & Hmi)".
  rewrite Hends. iMod ("Hwp" with "Hsi") as (Hred) "Hwp". iModIntro.
  iSplit; [done|]. iIntros (e2 σ2 efs Hstep).
  iMod ("Hwp" with "[//]") as "Hwp".
  iIntros "!>!>". iMod "Hwp". iIntros "!>".
  iApply step_fupdN_intro; [done|]. iIntros "!>". iMod "Hwp". rewrite -Hends.
  iMod (update_fuel_step with "HfuelS Hmi") as (δ2) "(%Hvse & Hfuel & Hmod)" =>//.
  { rewrite Hends -Hloc. eapply locale_step_atomic; eauto. by apply fill_step. }
  iIntros "!>". iDestruct "Hwp" as "[Hsi [Hwp ->]]".
  iExists _, (Silent_step tid). iFrame. iSplit; [done|].
  iDestruct ("Hwp" with "Hfuel") as "Hwp". iSplit; [|done].
  iApply (wp_wand with "Hwp"). iIntros (v) "HΦ'". by iFrame.
Qed.

(* TODO: Move this somewhere else *)
Lemma heap_lang_locales_equiv_from_length (es10 es1 es20 es2 : list expr) :
  length es10 = length es20 → length es1 = length es2 →
  locales_equiv_from es10 es20 es1 es2.
Proof.
  revert es10 es20 es2.
  induction es1 as [|e es1 IHes1]; intros es10 es20 es2 Hlen; [by destruct es2|].
  destruct es2; [done|]=> /=. constructor; [done|].
  apply IHes1; [by rewrite !app_length=> /=;f_equiv|lia].
Qed.

Lemma heap_lang_locales_equiv_length (es1 es2 : list expr) :
  length es1 = length es2 → locales_equiv es1 es2.
Proof. intros Hlen. by apply heap_lang_locales_equiv_from_length. Qed.  

Lemma wp_role_fork s tid E e Φ R1 R2 (Hdisj: R1 ##ₘ R2) (Hnemp: R1 ∪ R2 ≠ ∅):
  tid ↦M++ (R1 ∪ R2) -∗
  (∀ tid', ▷ (tid' ↦M R2 -∗ WP e @ s; tid'; ⊤ {{ _, tid' ↦M ∅ }})) -∗
  ▷ (tid ↦M R1 ={E}=∗ Φ (LitV LitUnit)) -∗
  WP Fork e @ s; tid; E {{ Φ }}.
Proof.
  iIntros "Htid He HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "(% & Hsi & Hmi)".
  iMod (update_fork_step R1 R2 _
       (tp1 ++ ectx_language.fill K (Val $ LitV LitUnit) :: tp2 ++ [e])
       _ _ _ e _ σ1 with "Htid Hmi") as
    (δ2 Hvse) "(Hfuels1 & Hfuels2 & Hmi)".
  { done. }
  { done. }
  { rewrite /trace_ends_in in Hexend. rewrite Hexend. done. }
  { rewrite -Hloc. rewrite -(language.locale_fill _ _ K).
    rewrite /trace_ends_in in Hexend. rewrite Hexend.
    econstructor 1 =>//.
    apply fill_step, head_prim_step. econstructor. }
  { list_simplifier. exists (tp1 ++ fill K #() :: tp2).
    rewrite /trace_ends_in in Hexend. rewrite Hexend.
    split; first by list_simplifier.
    apply heap_lang_locales_equiv_length. simpl.
    rewrite !app_length //=. }
  iModIntro. iSplit. iPureIntro; first by eauto. iNext.
  iIntros (e2 σ2 efs Hstep).
  have [-> [-> ->]] : σ2 = σ1 ∧ efs = [e] ∧ e2 = Val $ LitV LitUnit by inv_head_step.
  iMod ("HΦ" with "Hfuels1") as "HΦ". iModIntro. iExists δ2, (Silent_step tid).
  iFrame. rewrite Hexend /=. iFrame "Hsi". iSplit; [by iPureIntro|].
  iSplit; [|done]. iApply "He". by list_simplifier.
Qed.

Lemma sswp_pure_step s E e1 e2 (Φ : Prop) Ψ :
  PureExec Φ 1 e1 e2 → Φ → ▷ Ψ e2 -∗ sswp s E e1 Ψ%I.
Proof.
  iIntros (Hpe HΦ) "HΨ".
  assert (pure_step e1 e2) as Hps.
  { specialize (Hpe HΦ). by apply nsteps_once_inv in Hpe. }
  rewrite /sswp /=.
  assert (to_val e1 = None) as ->.
  { destruct Hps as [Hred _]. specialize (Hred (Build_state ∅ ∅)).
    by eapply reducible_not_val. }
  iIntros (σ) "Hσ".
  iMod fupd_mask_subseteq as "Hclose"; last iModIntro; [by set_solver|].
  iSplit.
  { destruct s; [|done]. by destruct Hps as [Hred _]. }
  iIntros (e2' σ2 efs Hstep) "!>!>!>".
  iMod "Hclose". iModIntro. destruct Hps as [_ Hstep'].
  apply Hstep' in Hstep as [-> [-> ->]]. by iFrame.
Qed.

(** Heap *)
(** The usable rules for [allocN] stated in terms of the [array] proposition
are derived in te file [array]. *)
Lemma heap_array_to_seq_meta l vs (n : nat) :
  length vs = n →
  ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
  [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
Proof.
  iIntros (<-) "Hvs". iInduction vs as [|v vs] "IH" forall (l)=> //=.
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma heap_array_to_seq_mapsto l v (n : nat) :
  ([∗ map] l' ↦ v ∈ heap_array l (replicate n v), l' ↦ v) -∗
  [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v.
Proof.
  iIntros "Hvs". iInduction n as [|n] "IH" forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma wp_allocN_seq s E v n (Φ : expr → iProp Σ) :
  0 < n →
  ▷ (∀ (l:loc), ([∗ list] i ∈ seq 0 (Z.to_nat n),
                 (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤) -∗ Φ #l) -∗
  sswp s E (AllocN (Val $ LitV $ LitInt $ n) (Val v)) Φ.
Proof.
  iIntros (HnO) "HΦ".
  rewrite /sswp. simpl.
  iIntros (σ) "Hσ".
  iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
  iSplit.
  { iPureIntro. destruct s; [|done]. apply head_prim_reducible. eauto. }
  iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
  iMod "Hclose".
  apply head_reducible_prim_step in Hstep; [|eauto].
  inv_head_step.
  iMod (gen_heap_alloc_big _ (heap_array l (replicate (Z.to_nat n) v)) with "Hσ")
    as "(Hσ & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite replicate_length Z2Nat.id ?Hexend; auto with lia. }
  iFrame.
  iModIntro.
  iSplit; [|done].
  iApply "HΦ".
  iApply big_sepL_sep. iSplitL "Hl".
  + by iApply heap_array_to_seq_mapsto.
  + iApply (heap_array_to_seq_meta with "Hm"). by rewrite replicate_length.
Qed.

Lemma wp_alloc s E v (Φ : expr → iProp Σ) :
  ▷ (∀ l, l ↦ v -∗ meta_token l ⊤ -∗ Φ (LitV (LitLoc l))) -∗
  sswp s E (Alloc v) Φ.
Proof.
  iIntros "HΦ". iApply wp_allocN_seq; [lia|].
  iIntros "!>" (l) "[[Hl Hm] _]". rewrite loc_add_0.
  iApply ("HΦ" with "Hl Hm").
Qed.

Lemma wp_choose_nat s E (Φ : expr → iProp Σ) :
  ▷ (∀ (n:nat), Φ $ Val $ LitV (LitInt n)) -∗
  sswp s E ChooseNat Φ.
Proof.
  iIntros "HΦ".
  rewrite /sswp. simpl.
  iIntros (σ) "Hσ".
  iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
  iSplit.
  { iPureIntro. destruct s; [|done]. apply head_prim_reducible. eauto. }
  iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
  iMod "Hclose".
  apply head_reducible_prim_step in Hstep; [|eauto].
  inv_head_step.
  iFrame.
  iModIntro.
  iSplit; [|done].
  iApply "HΦ".
  Unshelve. all: apply O.
Qed.

Lemma wp_load s E l q v (Φ : expr → iProp Σ) :
  ▷ l ↦{q} v -∗
  ▷ (l ↦{q} v -∗ Φ v) -∗
  sswp s E (Load (Val $ LitV $ LitLoc l)) Φ.
Proof.
  iIntros ">Hl HΦ".
  rewrite /sswp. simpl.
  iIntros (σ) "Hσ".
  iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
  iDestruct (@gen_heap_valid with "Hσ Hl") as %Hheap.
  iSplit.
  { iPureIntro. destruct s; [|done]. apply head_prim_reducible. eauto. }
  iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
  iMod "Hclose".
  apply head_reducible_prim_step in Hstep; [|eauto].
  inv_head_step.
  iFrame.
  iModIntro.
  iSplit; [|done].
  by iApply "HΦ".
Qed.

Lemma wp_store s E l v' v (Φ : expr → iProp Σ) :
  ▷ l ↦ v' -∗
  ▷ (l ↦ v -∗ Φ $ LitV LitUnit) -∗
  sswp s E (Store (Val $ LitV (LitLoc l)) (Val v)) Φ.
Proof.
  iIntros ">Hl HΦ". simpl.
  iIntros (σ1) "Hsi".
  iDestruct (gen_heap_valid with "Hsi Hl") as %Hheap.
  iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
  iSplit.
  { destruct s; [|done]. iPureIntro. apply head_prim_reducible. by eauto. }
  iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
  iMod "Hclose".
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  iFrame.
  apply head_reducible_prim_step in Hstep; [|by eauto].
  inv_head_step. iFrame. iModIntro. iSplit; [|done]. by iApply "HΦ".
Qed.

Lemma wp_cmpxchg_fail s E l q v' v1 v2 (Φ : expr → iProp Σ) :
  v' ≠ v1 → vals_compare_safe v' v1 →
  ▷ l ↦{q} v' -∗
  ▷ (l ↦{q} v' -∗ Φ $ PairV v' (LitV $ LitBool false)) -∗
  sswp s E (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) Φ.
Proof.
  iIntros (??) ">Hl HΦ". simpl.
  iIntros (σ1) "Hsi".
  iDestruct (gen_heap_valid with "Hsi Hl") as %Hheap.
  iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
  iSplit.
  { destruct s; [|done]. iPureIntro. apply head_prim_reducible. by eauto. }
  iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
  iMod "Hclose".
  iFrame.
  apply head_reducible_prim_step in Hstep; [|by eauto].
  inv_head_step.
  rewrite bool_decide_false //. iFrame. iModIntro.
  iSplit; [|done].
  by iApply "HΦ".
Qed.

Lemma wp_cmpxchg_suc s E l v' v1 v2 (Φ : expr → iProp Σ) :
  v' = v1 → vals_compare_safe v' v1 →
  ▷ l ↦ v' -∗
  ▷ (l ↦ v2 -∗ Φ $ PairV v' (LitV $ LitBool true)) -∗
  sswp s E (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) Φ.
Proof.
  iIntros (??) ">Hl HΦ". simpl.
  iIntros (σ1) "Hsi".
  iDestruct (gen_heap_valid with "Hsi Hl") as %Hheap.
  iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
  iSplit.
  { destruct s; [|done]. iPureIntro. apply head_prim_reducible. by eauto. }
  iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  iMod "Hclose".
  iFrame.
  apply head_reducible_prim_step in Hstep; [|by eauto].
  inv_head_step.
  rewrite bool_decide_true //. iFrame. iModIntro.
  iSplit; [|done].
  by iApply "HΦ".
Qed.

End lifting.
