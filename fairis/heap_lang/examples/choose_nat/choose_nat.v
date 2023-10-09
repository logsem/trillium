From stdpp Require Import finite decidable.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness Require Import fairness fair_termination.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.

Import derived_laws_later.bi.

Set Default Proof Using "Type".

(** The program verify liveness for *)
(** Recursion is "off by one" to allow immediate termination after storing 0 *)
Definition decr_loop_prog (l : loc) : val :=
  rec: "go" <> :=
    let: "x" := !#l in
    if: "x" = #1 then #l <- ("x" - #1)
    else #l <- ("x" - #1);; "go" #().
Definition choose_nat_prog (l : loc) : val :=
  λ: <>,
     #l <- (ChooseNat + #1);;
     decr_loop_prog l #().

(** The model state *)
Inductive CN := Start | N (n : nat).

(** A mapping of model state to "program state" *)
Definition CN_Z (cn : CN) : Z :=
  match cn with
  | Start => -1
  | N n => n
  end.

#[global] Instance CN_eqdec: EqDecision CN.
Proof. solve_decision. Qed.

#[global] Instance CN_inhabited: Inhabited CN.
Proof. exact (populate Start). Qed.

Inductive cntrans : CN → option unit → CN -> Prop :=
| start_trans n : cntrans Start (Some ()) (N n)
| decr_trans n : cntrans (N $ S n) (Some ()) (N n).

(* Free construction of the active labels on each state by [cntrans] *)
Definition cn_live_roles (cn : CN) : gset unit :=
  match cn with N 0 => ∅ | _ => {[ () ]} end.

Lemma cn_live_spec_holds s ρ s' : cntrans s (Some ρ) s' -> ρ ∈ cn_live_roles s.
Proof. destruct s; [set_solver|]. destruct n; [|set_solver]. inversion 1. Qed.

Definition cn_fair_model : FairModel.
Proof.
  refine({|
            fmstate := CN;
            fmrole := unit;
            fmtrans := cntrans;
            live_roles := cn_live_roles;
            fm_live_spec := cn_live_spec_holds;
          |}).
Defined.

(** Show that the model is fairly terminating *)

Inductive cn_order : CN → CN → Prop :=
  | cn_order_Start cn : cn_order cn Start
  | cn_order_N (n1 n2 : nat) : n1 ≤ n2 → cn_order (N n1) (N n2).

Local Instance the_order_po: PartialOrder cn_order.
Proof.
  split.
  - split.
    + by intros []; constructor.
    + intros [] [] [] Hc12 Hc23; try constructor.
      * inversion Hc23.
      * inversion Hc12.
      * inversion Hc23.
      * inversion Hc12. inversion Hc23. simplify_eq. lia.
  - intros [] []; inversion 1; simplify_eq; try eauto; try inversion 1.
    simplify_eq. f_equal. lia.
Qed.

Definition cn_decreasing_role (s : fmstate cn_fair_model) : unit :=
  match s with | _ => () end.

#[global] Program Instance cn_model_terminates :
  FairTerminatingModel cn_fair_model :=
  {|
    ftm_leq := cn_order;
    ftm_decreasing_role := cn_decreasing_role;
  |}.
Next Obligation.
  assert (∀ n, Acc (strict cn_order) (N n)).
  { intros n.
    induction n as [n IHn] using lt_wf_ind.
    constructor. intros cn [Hcn1 Hcn2].
    inversion Hcn1 as [|n1 n2]; simplify_eq.
    destruct (decide (n = n1)) as [->|Hneq]; [done|].
    apply IHn. lia. }
  constructor. intros [] [Hc1 Hc2]; [|done].
  inversion Hc1; simplify_eq. done.
Qed.
Next Obligation.
  intros cn [ρ' [cn' Htrans]].
  split.
  - rewrite /cn_decreasing_role. simpl. rewrite /cn_live_roles.
    destruct cn; [set_solver|].
    destruct n; [inversion Htrans|set_solver].
  - intros cn'' Htrans'.
    destruct cn.
    + split; [constructor|].
      intros Hrel. inversion Hrel; simplify_eq. inversion Htrans'.
    + split.
      * destruct cn''.
        -- inversion Htrans'.
        -- inversion Htrans'; simplify_eq. constructor. lia.
      * intros Hrel.
        inversion Htrans'; simplify_eq.
        inversion Hrel; simplify_eq.
        lia.
Qed.
Next Obligation. done. Qed.
Next Obligation.
  intros cn1 ρ cn2 Htrans.
  destruct cn1.
  - inversion Htrans; simplify_eq. constructor.
  - inversion Htrans; simplify_eq. constructor. lia.
Qed.

Definition cn_model : LiveModel heap_lang cn_fair_model :=
  {| lm_fl _ := 40%nat |}.

(** Determine additional restriction on relation to obtain finite branching *)
Definition ξ_cn (l:loc) (extr : execution_trace heap_lang)
           (auxtr : finite_trace cn_fair_model (option unit)) :=
  ∃ (cn:CN), (trace_last extr).2.(heap) !!! l = #(CN_Z cn) ∧
             (trace_last auxtr) = cn.

(** Verify that the program refines the model *)

(* Set up necessary RA constructions *)
Class choose_natG Σ := ChooseNatG { choose_nat_G :> inG Σ (excl_authR ZO) }.

Definition choose_natΣ : gFunctors :=
  #[ heapΣ cn_fair_model; GFunctor (excl_authR ZO) ].

Global Instance subG_choosenatΣ {Σ} : subG choose_natΣ Σ → choose_natG Σ.
Proof. solve_inG. Qed.

Definition Ns := nroot .@ "choose_nat".

Section proof.
  Context `{!heapGS Σ cn_model, choose_natG Σ}.

  (** Determine invariant so we can eventually derive ξ_cn from it *)
  Definition choose_nat_inv_inner (γ : gname) (l:loc) : iProp Σ :=
    ∃ (cn:CN), frag_model_is cn ∗ l ↦ #(CN_Z cn) ∗ own γ (●E (CN_Z cn)).

  Definition choose_nat_inv (γ : gname) (l:loc) :=
    inv Ns (choose_nat_inv_inner γ l).

  Lemma decr_loop_spec γ tid l (n:nat) (f:nat) :
    7 ≤ f → f ≤ 38 →
    choose_nat_inv γ l -∗
    {{{ tid ↦M {[ () := f ]} ∗ frag_free_roles_are ∅ ∗
        own γ (◯E (Z.of_nat (S n))) }}}
      decr_loop_prog l #() @ tid ; ⊤
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Hle1 Hle2) "#IH".
    iIntros "!>" (Φ) "(Hf & Hr & Hm) HΦ".
    iInduction n as [|n] "IHn" forall (f Hle1 Hle2).
    { wp_lam.
      (* Load - with invariant *)
      wp_bind (Load _).
      iApply wp_atomic.
      iInv Ns as ">HI" "Hclose".
      iDestruct "HI" as (cn) "(Hs & Hl & Hcn)".
      iDestruct (own_valid_2 with "Hcn Hm") as %Hvalid%excl_auth_agree_L.
      iModIntro.
      wp_load.
      iModIntro.
      iMod ("Hclose" with "[Hs Hl Hcn]") as "_"; [ iExists _; iFrame | ].
      iModIntro.
      rewrite Hvalid. clear cn Hvalid.
      (* Store - with invariant *)
      wp_pures.
      replace (Z.of_nat 1 - 1)%Z with 0%Z by lia.
      wp_bind (Store _ _).
      iApply wp_atomic.
      iInv Ns as ">HI" "Hclose".
      iDestruct "HI" as (cn) "(Hs & Hl & Hcn)".
      iDestruct (own_valid_2 with "Hcn Hm") as %Hvalid%excl_auth_agree_L.
      iModIntro.
      assert (cn = N 1) as ->.
      { destruct cn; inversion Hvalid. by simplify_eq. }
      (* Update the model state to maintain program correspondence *)
      iApply (wp_step_model_singlerole _ _ (():fmrole cn_fair_model) (f - 7)
               with "Hs [Hf] Hr").
      { constructor. }
      { set_solver. }
      { by replace (f - 1 - 1 - 1 - 1 - 1 - 1 - 1)%nat with (f - 7)%nat by lia. }
      iApply (wp_store with "Hl").
      iIntros "!> Hl Hs Hf Hr".
      iMod (has_fuels_dealloc _ _ _ (():fmrole cn_fair_model) with "Hs Hf")
        as "[Hs Hf]"; [done|].
      wp_pures.
      iMod (own_update_2 _ _ _ with "Hcn Hm") as "[Hcn Hm]".
      { apply (excl_auth_update _ _ 0%Z). }
      iMod ("Hclose" with "[Hs Hl Hcn]") as "_".
      { iExists (N 0). iFrame. }
      iApply fupd_mask_intro; [done|].
      iIntros "H". iMod "H".
      iModIntro. by iApply "HΦ". }
    wp_lam.
    (* Load - with invariant *)
    wp_bind (Load _).
    iApply wp_atomic.
    iInv Ns as ">HI" "Hclose".
    iModIntro.
    iDestruct "HI" as (cn) "(Hs & Hl & Hcn)".
    wp_load.
    iDestruct (own_valid_2 with "Hcn Hm") as %Hvalid%excl_auth_agree_L.
    iModIntro. iMod ("Hclose" with "[Hs Hl Hcn]") as "_".
    { iExists _. iFrame. }
    iModIntro.
    rewrite Hvalid. clear cn Hvalid.
    wp_pures.
    case_bool_decide as Heq; [inversion Heq; lia|clear Heq].
    wp_pures.
    replace (Z.of_nat (S (S n))  - 1)%Z with (Z.of_nat (S n)) %Z by lia.
    (* Store - with invariant *)
    wp_bind (Store _ _).
    iApply wp_atomic.
    iInv Ns as ">HI" "Hclose".
    iModIntro.
    iDestruct "HI" as (cn) "(Hs & Hl & Hcn)".
    iDestruct (own_valid_2 with "Hcn Hm") as %Hvalid%excl_auth_agree_L.
    assert (cn = N (S (S n))) as ->.
    { destruct cn; inversion Hvalid. by simplify_eq. }
    (* Update the model state to maintain program correspondence *)
    iApply (wp_step_model_singlerole _ _ (():fmrole cn_fair_model) (f - 7)
             with "Hs [Hf] Hr").
    { constructor. }
    { set_solver. }
    { by replace (f - 1 - 1 - 1 - 1 - 1 - 1 - 1)%nat with (f - 7)%nat by lia. }
    iApply (wp_store with "Hl").
    iIntros "!> Hl Hs Hf Hr".
    wp_pures.
    iMod (own_update_2 _ _ _ with "Hcn Hm") as "[Hcn Hm]".
    { apply (excl_auth_update _ _ (Z.of_nat (S n))%Z). }
    iMod ("Hclose" with "[Hs Hl Hcn]") as "_".
    { iExists (N (S n)). iFrame. }
    iApply fupd_mask_intro; [done|].
    iIntros "H". iMod "H".
    iModIntro. simpl. wp_pures.
    iApply ("IHn" with "[] [] Hf Hr Hm"); [iPureIntro; lia..|done].
  Qed.

  Lemma choose_nat_spec γ l tid (f:nat) :
    12 ≤ f → f ≤ 40 →
    choose_nat_inv γ l -∗
    {{{ tid ↦M {[ () := f ]} ∗ frag_free_roles_are ∅ ∗ own γ (◯E (-1)%Z) }}}
      choose_nat_prog l #() @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Hle1 Hle2) "#IH".
    iIntros "!>" (Φ) "(Hf & Hr & Hm) HΦ".
    wp_lam.
    wp_bind ChooseNat.
    iApply (wp_step_fuel with "[Hf]").
    2: { rewrite has_fuels_gt_1; last by solve_fuel_positive.
         rewrite fmap_insert fmap_empty. done. }
    { set_solver. }
    iApply wp_choose_nat.
    iIntros "!>" (n) "Hf".
    wp_pures.
    iModIntro.
    wp_pures.
    (* Store - with invariant *)
    wp_bind (Store _ _).
    iApply wp_atomic.
    iInv Ns as ">HI" "Hclose".
    iModIntro.
    iDestruct "HI" as (cn) "(Hs & Hl & Hcn)".
    iDestruct (own_valid_2 with "Hcn Hm") as %Hvalid%excl_auth_agree_L.
    assert (cn = Start) as ->.
    { destruct cn; inversion Hvalid; [done|]. lia. }
    (* Update the model state to maintain program correspondence *)
    iApply (wp_step_model_singlerole _ _ (():fmrole cn_fair_model) (f - 3)
                                     _ _ (N (S n))
             with "Hs [Hf] Hr").
    { constructor. }
    { set_solver. }
    { by replace (f - 1 - 1 - 1)%nat with (f - 3)%nat by lia. }
    iApply (wp_store with "Hl").
    iIntros "!> Hl Hs Hf Hr".
    wp_pures.
    iMod (own_update_2 _ _ _ with "Hcn Hm") as "[Hcn Hm]".
    { apply (excl_auth_update _ _ (Z.of_nat (S n))%Z). }
    iMod ("Hclose" with "[Hs Hl Hcn]") as "_".
    { replace (Z.of_nat n + 1)%Z with (Z.of_nat (S n)) by lia.
      iExists (N (S n)). iFrame. }
    iApply fupd_mask_intro; [done|].
    iIntros "H". iMod "H".
    iModIntro. simpl. wp_pures.
    by iApply (decr_loop_spec with "IH [$Hm $Hr $Hf]"); [lia|lia|].
  Qed.

End proof.
