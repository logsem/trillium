From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination fairness_finiteness.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness.heap_lang Require Export lang lifting tactics notation adequacy.
From trillium.fairness.heap_lang.examples Require Import env_am split_model.
From trillium.fairness.heap_lang.examples.yesno Require Import yesno.

From stdpp Require Import finite.


Section product_of_orders.
  Variables (A B : Type) (leA : relation A) (leB : relation B).
  Context `{HlAtrans: Transitive _ leA}.

  Lemma prod_trans :
     transitive _ leA ->
     transitive _ leB ->
     transitive _ (prod_relation leA leB).
   Proof.
     intros tA tB [x1 y1] [x2 y2] [x3 y3] H.
     inversion H; subst; clear H.
     intros H.
     inversion H; subst; clear H.
     split; eauto.
   Qed.

   Theorem wf_prod :
     well_founded leA ->
     well_founded leB ->
     well_founded (prod_relation leA leB).
   Proof.
     intros wfA wfB [x y]. generalize dependent y.
     induction (wfA x) as [x _ IHx]; clear wfA.
     intros y.
     induction (wfB y) as [y _ IHy]; clear wfB.
     constructor.
     intros [x' y'] H.
     now inversion H; subst; clear H; eauto.
   Qed.

   Theorem wf_prod_strict :
     well_founded (strict leA) ->
     well_founded (strict leB) ->
     well_founded (strict (prod_relation leA leB)).
   Proof.
     intros wfA wfB [x y]. generalize dependent y.
     induction (wfA x) as [x _ IHx]; clear wfA.
     intros y.
     generalize dependent x.
     induction (wfB y) as [y _ IHy]; clear wfB.
     intros x IH.
     constructor.
     intros [x' y'] H.
     inversion H as [[??] [?|?]%Classical_Prop.not_and_or]; subst; clear H; first by apply IH.
     apply IHy; first done. intros ???. eapply IH, strict_transitive_l =>//.
   Qed.

  Global Instance prod_relation_antisym :
    AntiSymm eq leA → AntiSymm eq leB → AntiSymm eq (prod_relation leA leB).
  Proof.
    intros ??[??] [??] [??] [??].
    f_equal; firstorder eauto.
  Qed.

  Global Instance prod_relation_preorder :
    PreOrder leA → PreOrder leB → PreOrder (prod_relation leA leB).
  Proof. firstorder eauto. Qed.

  Global Instance prod_relation_partialorder :
    PartialOrder leA → PartialOrder leB → PartialOrder (prod_relation leA leB).
  Proof.
    intros. split; first (firstorder eauto).
    typeclasses eauto.
  Qed.
End product_of_orders.

Section unstrict_order.
  Context {A B : Type}.
  Variables (lt : relation A).

  Definition unstrict x y :=
    x = y ∨ lt x y.
End unstrict_order.

Definition the_order := unstrict (lexprod _ _ (strict Nat.le) (strict bool_le)).

Ltac inv_lexs :=
  repeat match goal with
    [ H: lexprod _ _ _ _ _ _ |- _ ] => inversion H; clear H; simplify_eq
         end.

Lemma lexprod_lexico x y:
  lexprod _ _ (strict Nat.le) (strict bool_le) x y <-> lexico x y.
Proof.
  split.
  - intros [???? H|x' y' z' H].
    + left =>/=. compute. compute in H. lia.
    + right =>/=. compute; split=>//. compute in H. destruct y'; destruct z' =>//; intuition.
  - destruct x as [x1 x2]. destruct y as [y1 y2]. intros [H|[Heq H]]; simpl in *.
    + left =>/=. compute. compute in H. lia.
    + rewrite Heq. right =>/=. destruct x2; destruct y2 =>//; intuition. constructor =>//. eauto.
Qed.

#[local] Instance the_order_po: PartialOrder the_order.
Proof.
  constructor.
  - constructor.
    + intros ?. by left.
    + unfold the_order. intros [x1 x2] [y1 y2] [z1 z2] [|H1] [|H2]; simplify_eq; try (by left); right; eauto.
      rewrite -> lexprod_lexico in *. etransitivity =>//.
  - intros [x1 x2] [y1 y2] [|H1] [|H2]; simplify_eq =>//.
    inversion H1; inversion H2; simplify_eq; try (compute in *; lia).
    destruct x2; destruct y2; compute in *; intuition.
Qed.

Definition the_decreasing_role (s: amSt yn_AM): YN :=
  match s with
  | (0%nat, false) => Y
  | (_, true) => Y
  | (_, false) => No
  end.

#[local] Instance eq_antisymm A: Antisymmetric A eq eq.
Proof. by intros ??. Qed.

Lemma strict_unstrict {A} (R: relation A):
  forall x y, strict (unstrict R) x y -> R x y.
Proof.
  unfold strict, unstrict.
  intros x y.
  intros [[?|?] [Hneq HnR]%Classical_Prop.not_or_and] =>//.
Qed.

Lemma wf_bool_le: well_founded (strict bool_le).
Proof.
  intros b. destruct b; constructor; intros b' h; destruct b'; inversion h as [h1 h2];
              [done| | inversion h1| done]. clear h1 h2.
  constructor; intros b' h'; inversion h' as [h1 h2]; destruct b'; [inversion h1 | exfalso; eauto].
Qed.

#[local] Instance lex_trans `{Transitive A R1, Transitive B R2}: Transitive (lexprod A B R1 R2).
Proof.
  intros [x x'] [y y'] [z z'] Ha Hb.
  inversion Ha; inversion Hb; simplify_eq.
  - constructor 1. etransitivity =>//.
  - by constructor 1.
  - by constructor 1.
  - constructor 2. etransitivity =>//.
Qed.

(* #[local] Program Instance the_model_terminates: FairTerminatingModel the_fair_model := *)
(*   {| *)
(*   ftm_leq := the_order; *)
(*   ftm_decreasing_role := the_decreasing_role; *)
(*   |}. *)
(* Next Obligation. *)
(*   unfold the_order. *)
(*   assert (H: well_founded (lexprod nat bool (strict Nat.le) (strict bool_le))). *)
(*   + apply wf_lexprod; last apply wf_bool_le. *)
(*     eapply (wf_projected _ id); last apply Nat.lt_wf_0. *)
(*     intros ??[??]. simpl. lia. *)
(*   + eapply (wf_projected _ id); last exact H. *)
(*     intros ???. apply strict_unstrict => //. *)
(* Qed. *)
(* Next Obligation. *)
(*   intros [N B] Hex. *)
(*   destruct B. *)
(*   - split. *)
(*     + simpl. destruct N. *)
(*       * destruct Hex as [ρ' [s' Hex]]. *)
(*         inversion Hex; subst.  *)
(*         2: { inversion STEP. } *)
(*         inversion STEP; subst; lia. *)
(*       * apply yn_AM_live_roles. simpl.   *)
(*         destruct N; set_solver. *)
(*     + intros [??] H. inversion H; simplify_eq. *)
(*       * split. *)
(*         ** inversion STEP; subst. *)
(*            2: { by destruct n. } *)
(*            right. right. compute. done. *)
(*         ** compute; intros [?|contra] =>//. *)
(*            { inversion H0. subst. destruct n; inversion STEP. }  *)
(*            destruct N; inversion STEP; subst.  *)
(*            all: inversion contra; subst; tauto.  *)
(*   - split. *)
(*     + destruct N; simpl. *)
(*       * destruct Hex as [ρ' [s' Hex]]. *)
(*         inversion Hex; subst.  *)
(*         2: { inversion STEP. } *)
(*         inversion STEP; subst; lia. *)
(*       * apply yn_AM_live_roles. simpl. *)
(*         destruct N; set_solver. *)
(*     + intros [[|?] ?] H. *)
(*       * inversion H; simplify_eq. *)
(*         unfold strict, the_order; split. *)
(*         ** right; left. compute. split; [lia| ]. *)
(*            intros ->%Nat.le_0_r. inversion STEP. lia.   *)
(*         ** intros [|contra] =>//. *)
(*            { inversion H0. subst. inversion STEP. lia. }  *)
(*            destruct N; inversion STEP; subst.  *)
(*            all: inversion contra; subst; try lia || tauto. *)
(*            red in H1. apply proj1 in H1. lia.  *)
(*       * inversion H; simplify_eq. split. *)
(*         ** destruct N; inversion STEP; subst.   *)
(*            right;left; compute; tauto || lia. *)
(*         ** intros [|contra] =>//. *)
(*            { inversion H0. subst. inversion STEP. } *)
(*            inversion contra; simplify_eq. *)
(*            2: { inversion STEP. subst. lia. } *)
(*            destruct N; inversion STEP; subst. *)
(*            compute in *. lia. *)
(* Qed. *)
(* Next Obligation. *)
(*   intros [N B]  [N' B'] ρ Htrans Hnex. *)
(*   inversion Htrans; subst; [| by inversion STEP]. *)
(*   inversion STEP; simplify_eq; eauto; simpl in *; *)
(*     try (destruct N'; eauto); try lia; (try (destruct N'; done)); try done. *)
(* Qed. *)
(* Next Obligation. *)
(*   intros [N B] ρ [N' B'] Htrans. *)
(*   inversion Htrans; subst; [| by inversion STEP]. *)
(*   destruct r. *)
(*   { inversion STEP; simplify_eq; simpl; try reflexivity. *)
(*     right; constructor 2; by compute. } *)
(*   inversion STEP; simplify_eq; simpl; try reflexivity. *)
(*   right; constructor 1; compute. lia. *)
(* Qed. *)


#[local] Instance proof_irrel_trans s x:
  ProofIrrel ((let '(s', ℓ) := x in am_fmtrans yn_AM s ℓ s'): Prop).
Proof. apply make_proof_irrel. Qed.

Lemma model_finitary (s: amSt yn_AM):
  Finite { '(s', ℓ) | am_fmtrans yn_AM s ℓ s'}.
Proof.
  eapply (in_list_finite ((fun '(x, y, z) => (x, z)) <$> amfb_ns s)).
  intros [[??]?] ?. apply elem_of_list_fmap.
  apply am_fmtrans_action in H as [??]. 
  eexists (_, _, _). split; [reflexivity| ].
  eapply amfb_ns_spec. eauto. 
Qed.

Let M := the_fair_model EnvUnitAM. 
Let LM := the_model EnvUnitAM.
Let PM := @FM UnitAM. 


Let wholeΣ: gFunctors := #[yesnoΣ EnvUnitAM; SplitΣ UnitAM yn_AM].

(* TODO: move *)
Global Instance subG_wholeΣ {Σ} : subG wholeΣ Σ → SplitPreGS Σ UnitAM yn_AM. 
Proof. solve_inG. Qed. 
 

From iris.base_logic.lib Require Import invariants.

Theorem yesno_terminates
        (N : nat)
        (HN: N > 1)
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [start #N]):
  (∀ tid, fair_ex tid extr) -> terminating_trace extr.
Proof.
  assert (heapGpreS wholeΣ LM) as HPreG.
  { apply _. }
  assert (SplitPreGS wholeΣ UnitAM yn_AM) as sPreG. 
  { apply _. }
  eapply (simulation_adequacy_terminate_ftm NotStuck _ ((tt, (N, true)): fmstate M) ∅) =>//.
  - eapply valid_state_evolution_finitary_fairness_simple.
    intros ?. simpl.
    (* apply (model_finitary s1). *)
    Unshelve. all: admit.
  - simpl. rewrite (prod_indep_live_roles _ _ (unit_indep_l yn_AM)). 
    rewrite yn_AM_live_roles'. simpl.  
    destruct N as [|[|]]; try lia. set_solver.     
  - intros ?.

    iStartProof. iIntros "!> Hm HFR Hf !>".

    iMod (split_init (tt: amSt UnitAM) ((N, true): amSt yn_AM)) as (γ__s) "(PROD & LEFT & RIGHT)".
    set (sGS := {| γ__split := γ__s; spre := sPreG |}). 
    iMod (inv_alloc Ns__split _ (split_inv_inner) with "[PROD Hm]") as "#SPLIT".
    { iNext. iFrame. }

    simpl. rewrite (prod_indep_live_roles _ _ (unit_indep_l yn_AM)).
    rewrite subseteq_empty_difference_L; [| done].
    rewrite unit_lr set_map_empty union_empty_l_L. 
    rewrite !yn_AM_live_roles'. simpl.  
    simpl.
    iApply (start_spec EnvUnitAM _ _ 61 with "[RIGHT Hf HFR]"); eauto.
    Unshelve. 2: apply unit_indep_l. 
    iFrame "#∗".     
    do 2 (destruct N; first lia).
    iFrame. iSplit; last (iPureIntro; lia).
    
    iApply has_fuels_proper; [reflexivity| | by iFrame].
    rewrite union_comm_L. rewrite set_map_union_L !set_map_singleton_L.
    rewrite !gset_to_gmap_union_singleton utils.gset_to_gmap_singleton.
    done. 
Admitted. 
