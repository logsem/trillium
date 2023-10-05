From stdpp Require Import decidable.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.

Import derived_laws_later.bi.

Open Scope nat.

Set Default Proof Using "Type".

Definition incr_loop : val :=
  rec: "incr_loop" "l" "n" :=
    (if: CAS "l" "n" ("n"+#1)
     then "incr_loop" "l" ("n" + #2)
     else "incr_loop" "l" "n").

Definition start : val :=
  λ: "l",
    let: "x" := !"l" in
    (Fork (incr_loop "l" "x") ;;
    Fork (incr_loop "l" ("x"+#1))).

(** * Definition of the model! *)

Inductive EO := ρEven | ρOdd.

#[global] Instance EO_eqdec: EqDecision EO.
Proof. solve_decision. Qed.

#[global] Instance EO_countable: Countable EO.
Proof.
  refine
    ({|
        encode eo := match eo with ρEven => 1 | ρOdd => 2 end;
        decode p := match p with 1 => Some ρEven | 2 => Some ρOdd | _ => None end;
      |})%positive.
  intros eo. by destruct eo.
Qed.

#[global] Instance EO_inhabited: Inhabited EO.
Proof. exact (populate ρEven). Qed.

Inductive eotrans: nat -> option EO -> nat -> Prop :=
| even_trans n : Nat.even n → eotrans n (Some ρEven) (S n)
| even_fail n : Nat.odd n → eotrans n (Some ρEven) n
| odd_trans n : Nat.odd n → eotrans n (Some ρOdd) (S n)
| odd_fail n : Nat.even n → eotrans n (Some ρOdd) n.

Definition eo_live_roles : gset EO := {[ ρOdd; ρEven ]}.

Lemma live_spec_holds : forall s ρ s', eotrans s (Some ρ) s' -> ρ ∈ eo_live_roles.
Proof.
  intros n eo n' Htrans. rewrite /eo_live_roles.
  inversion Htrans; simplify_eq; try set_solver; try lia; destruct n'; try set_solver; lia.
Qed.

Definition the_fair_model: FairModel.
Proof.
  refine({|
            fmstate := nat;
            fmrole := EO;
            fmtrans := eotrans;
            live_roles _ := eo_live_roles;
            fm_live_spec := live_spec_holds;
          |}).
Defined.

Definition the_model: LiveModel heap_lang the_fair_model :=
  {| lm_fl (x: fmstate the_fair_model) := 61%nat; |}.

(** The CMRAs we need. *)
Class evenoddG Σ := EvenoddG {
  even_name: gname;
  odd_name: gname;
  evenodd_n_G :> inG Σ (excl_authR natO);
 }.
Class evenoddPreG Σ := {
  evenodd_PreG :> inG Σ (excl_authR natO);
 }.
Definition evenoddΣ : gFunctors :=
  #[ heapΣ the_fair_model; GFunctor (excl_authR natO) ; GFunctor (excl_authR boolO) ].

Global Instance subG_evenoddΣ {Σ} : subG evenoddΣ Σ → evenoddPreG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ the_model, !evenoddG Σ}.
  Let Ns := nroot .@ "even_odd".

  Definition even_at (n: nat) := own even_name (◯E n).
  Definition odd_at (n: nat) := own odd_name (◯E n).

  Definition auth_even_at (n: nat) := own even_name (●E n).
  Definition auth_odd_at (n: nat) := own odd_name (●E n).

  Lemma they_agree γ (N M: nat) :
    own γ (◯E N) -∗ own γ (●E M) -∗ ⌜ M = N ⌝.
  Proof.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.
  Lemma even_agree N M :
    even_at N -∗ auth_even_at M -∗ ⌜ M = N ⌝.
  Proof. apply they_agree. Qed.
  Lemma odd_agree N M :
    odd_at N -∗ auth_odd_at M -∗ ⌜ M = N ⌝.
  Proof. apply they_agree. Qed.

  Lemma they_update γ (N M P: nat) :
    own γ (●E N) ∗ own γ (◯E M) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.
  Lemma even_update P N M:
     auth_even_at M ∗ even_at N ==∗ auth_even_at P ∗ even_at P.
  Proof. apply they_update. Qed.
  Lemma odd_update P N M:
     auth_odd_at M ∗ odd_at N ==∗ auth_odd_at P ∗ odd_at P.
  Proof. apply they_update. Qed.

  Definition evenodd_inv_inner n : iProp Σ :=
    ∃ N,
      frag_free_roles_are ∅ ∗
      frag_model_is N ∗ n ↦ #N ∗
      if Nat.even N
      then auth_even_at N ∗ auth_odd_at (N+1)
      else auth_even_at (N+1) ∗ auth_odd_at N.
  Definition evenodd_inv n := inv Ns (evenodd_inv_inner n).

  Lemma even_go_spec tid n (N: nat) f (Hf: f > 40):
    {{{ evenodd_inv n ∗ tid ↦M {[ ρEven := f ]} ∗ even_at N }}}
      incr_loop #n #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ) "(#Hinv & Hf & Heven) Hk".
    wp_lam. wp_pures. wp_bind (CmpXchg _ _ _). iApply wp_atomic.
    iInv Ns as (M) "(>HFR & >Hmod & >Hn & Hauths)" "Hclose".
    destruct (Nat.even M) eqn:Heqn; iDestruct "Hauths" as "[>Hay >Han]".
    - iDestruct (even_agree with "Heven Hay") as "%Heq".
      iModIntro.
      iApply (wp_step_model_singlerole with "Hmod Hf HFR").
      { constructor. by eauto. }
      { set_solver. }
      iApply (wp_cmpxchg_suc with "Hn"); [by do 3 f_equiv|done|].
      iIntros "!> Hb Hmod Hf HFR".
      iMod (even_update (M + 2) with "[$]") as "[Hay Heven]".
      wp_pures.
      iMod ("Hclose" with "[Hmod Hay Han Hb HFR]").
      { iNext. iExists _. iFrame. subst. iEval (rewrite -Nat.add_1_r).
        rewrite Nat2Z.inj_add !Nat.add_1_r Nat.even_succ -Nat.negb_even Heqn.
        iFrame. replace (S (S N)) with (N + 2) by lia. iFrame. }
      iApply fupd_mask_intro; [done|]. iIntros "H". iMod "H".
      iModIntro. simpl. wp_pures.
      replace (Z.of_nat N + 2)%Z with (Z.of_nat (N + 2)) by lia.
      iApply ("Hg" with "[] [Heven Hf] [$]"); last first.
      { iFrame "∗#". subst. iFrame. }
      iPureIntro; lia.
    - iDestruct (even_agree with "Heven Hay") as "%Heq". rewrite -> Heq in *.
      iModIntro.
      iApply (wp_step_model_singlerole with "Hmod Hf HFR").
      { apply even_fail. rewrite -Nat.negb_even. rewrite Heqn. done. }
      { set_solver. }
      iApply (wp_cmpxchg_fail with "Hn"); [intros Hne; simplify_eq; lia|done|].
      iIntros "!> Hb Hmod Hf HFR".
      wp_pures.
      iMod ("Hclose" with "[Hmod Hb Hay Han HFR]").
      { iNext. simplify_eq. iExists _. iFrame.
        subst. iFrame.
        rewrite Nat.add_1_r. rewrite Heqn. iFrame. }
      iApply fupd_mask_intro; [done|]. iIntros "H". iMod "H".
      iModIntro. simpl. wp_pures.
      iApply ("Hg" with "[] [Heven Hf] [$]"); last first.
      { iFrame "∗#". }
      iPureIntro; lia.
  Qed.

  Lemma odd_go_spec tid n (N: nat) f (Hf: f > 40):
    {{{ evenodd_inv n ∗ tid ↦M {[ ρOdd := f ]} ∗ odd_at N }}}
      incr_loop #n #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ) "(#Hinv & Hf & Hodd) Hk".
    wp_lam.
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    iApply wp_atomic.
    iInv Ns as (M) "(>HFR & >Hmod & >Hn & Hauths)" "Hclose".
    destruct (Nat.even M) eqn:Heqn; iDestruct "Hauths" as "[>Hay >Han]"; last first.
    - iDestruct (odd_agree with "Hodd Han") as "%Heq".
      iModIntro.
      iApply (wp_step_model_singlerole with "Hmod Hf HFR").
      { apply odd_trans. rewrite -Nat.negb_even. rewrite Heqn. done. }
      { set_solver. }
      iApply (wp_cmpxchg_suc with "Hn"); [by do 3 f_equiv|done|].
      iIntros "!> Hb Hmod Hf HFR".
      iMod (odd_update (M + 2) with "[$]") as "[Han Hodd]".
      wp_pures.
      iMod ("Hclose" with "[Hmod Hay Han Hb HFR]").
      { iNext. iExists _. iFrame. subst.
        rewrite Nat.add_1_r Nat.even_succ -Nat.negb_even Heqn Nat.add_1_r.
        replace (S (S N)) with (N + 2) by lia. iFrame.
        iEval (rewrite -Nat.add_1_r). rewrite Nat2Z.inj_add. iFrame. }
      iApply fupd_mask_intro; [done|]. iIntros "H". iMod "H". iModIntro.
      simpl. wp_pures.
      replace (Z.of_nat N + 2)%Z with (Z.of_nat (N + 2)) by lia.
      iApply ("Hg" with "[] [Hodd Hf] [$]"); last first.
      { iFrame "∗#". simplify_eq. done. }
      iPureIntro; lia.
    - iDestruct (odd_agree with "Hodd Han") as "%Heq". rewrite -> Heq in *.
      simplify_eq. iModIntro.
      iApply (wp_step_model_singlerole with "Hmod Hf HFR").
      { apply odd_fail. by eauto. }
      { set_solver. }
      iApply (wp_cmpxchg_fail with "Hn");
        [by intros Hneq; simplify_eq; lia|done|].
      iIntros "!> Hb Hmod Hf HFR".
      wp_pures.
      iMod ("Hclose" with "[Hmod Hb Hay Han HFR]").
      { iNext. simplify_eq. iExists _. iFrame.
        rewrite Heqn. iFrame. }
      iApply fupd_mask_intro; [done|]. iIntros "H". iMod "H". iModIntro.
      simpl. wp_pures.
      iApply ("Hg" with "[] [Hodd Hf] [$]"); last first.
      { iFrame "∗#". }
      iPureIntro; lia.
  Qed.

  Definition role_frag (eo : EO) : nat → iProp Σ :=
    match eo with
    | ρEven => even_at
    | ρOdd => odd_at
    end.

  Lemma incr_loop_spec tid n (N : nat) f (Hf: f > 40) (eo : EO) :
    {{{ evenodd_inv n ∗ tid ↦M {[ eo := f ]} ∗ (role_frag eo) N }}}
      incr_loop #n #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hf & Heo) Hk".
    destruct eo.
    - iApply (even_go_spec with "[$Hf $Heo]"); [lia|done|done].
    - iApply (odd_go_spec with "[$Hf $Heo]"); [lia|done|done].
  Qed.

End proof.

Section proof_start.
  Context `{!heapGS Σ the_model, !evenoddG Σ}.
  Let Ns := nroot .@ "even_odd".

  Lemma start_spec tid n N1 N2 f (Hf: f > 60) :
    {{{ evenodd_inv n ∗ tid ↦M {[ ρEven := f; ρOdd := f ]} ∗
        even_at N1 ∗ odd_at N2 }}}
      start #n @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using All.
    iIntros (Φ) "(#Hinv & Hf & Heven_at & Hodd_at) HΦ". unfold start.
    wp_pures.
    wp_bind (Load _).
    iApply wp_atomic.
    iInv Ns as (M) "(>HFR & >Hmod & >Hn & Hauths)" "Hclose".
    iIntros "!>". wp_load. iIntros "!>".
    destruct (Nat.even M) eqn:Heven.
    - iDestruct "Hauths" as "[Heven Hodd]".
      iDestruct (even_agree with "Heven_at Heven") as %<-.
      iDestruct (odd_agree with "Hodd_at Hodd") as %<-.
      iMod ("Hclose" with "[-Hf Heven_at Hodd_at HΦ]") as "_".
      { iIntros "!>". iExists _. iFrame. rewrite Heven. iFrame. }
      iIntros "!>". wp_pures. wp_bind (Fork _).
      iApply (wp_role_fork _ tid _ _ _ {[ρOdd := _]} {[ρEven := _]}
               with "[Hf] [Heven_at]").
      { apply map_disjoint_dom. rewrite !dom_singleton. set_solver. }
      { intros Hempty%map_positive_l. set_solver. }
      { rewrite has_fuels_gt_1; last solve_fuel_positive.
        rewrite !fmap_insert fmap_empty //.
        rewrite insert_union_singleton_l. 
        rewrite map_union_comm; [done|].
        apply map_disjoint_dom. set_solver. }
      { iIntros (tid') "!> Hf".
        iApply (incr_loop_spec with "[Heven_at $Hf]"); [lia|iFrame "#∗"|].
        by iIntros "!>?". }
      iIntros "!> Hf".
      iIntros "!>".
      wp_pures.
      iApply (wp_role_fork _ tid _ _ _ ∅ {[ρOdd := _]} with "[Hf] [Hodd_at]").
      { apply map_disjoint_dom. rewrite !dom_singleton. set_solver. }
      { rewrite map_union_comm.
        - intros Hempty%map_positive_l. set_solver.
        - apply map_disjoint_dom. rewrite dom_singleton. set_solver. }
      { rewrite has_fuels_gt_1; last solve_fuel_positive.
        rewrite !fmap_insert fmap_empty //.
        rewrite insert_union_singleton_l. 
        rewrite map_union_comm; [done|].
        apply map_disjoint_dom. set_solver. }
      { iIntros (tid') "!> Hf".
        wp_pures.
        replace (Z.of_nat M + 1)%Z with (Z.of_nat (M + 1)) by lia.
        iApply (incr_loop_spec with "[Hodd_at $Hf]"); [lia|iFrame "#∗"|].
        by iIntros "!>?". }
      iIntros "!> Hf". by iApply "HΦ".
    - iDestruct "Hauths" as "[Heven Hodd]".
      iDestruct (even_agree with "Heven_at Heven") as %<-.
      iDestruct (odd_agree with "Hodd_at Hodd") as %<-.
      iMod ("Hclose" with "[-Hf Heven_at Hodd_at HΦ]") as "_".
      { iIntros "!>". iExists _. iFrame. rewrite Heven. iFrame. }
      iIntros "!>". wp_pures. wp_bind (Fork _).
      iApply (wp_role_fork _ tid _ _ _ {[ρEven := _]} {[ρOdd := _]}
               with "[Hf] [Hodd_at]").
      { apply map_disjoint_dom. rewrite !dom_singleton. set_solver. }
      { intros Hempty%map_positive_l. set_solver. }
      { rewrite has_fuels_gt_1; last solve_fuel_positive.
        rewrite !fmap_insert fmap_empty //.
        rewrite insert_union_singleton_l. done. }
      { iIntros (tid') "!> Hf".
        iApply (incr_loop_spec with "[Hodd_at $Hf]"); [lia|iFrame "#∗"|].
        by iIntros "!>?". }
      iIntros "!> Hf !>".
      wp_pures.
      iApply (wp_role_fork _ tid _ _ _ ∅ {[ρEven := _]} with "[Hf] [Heven_at]").
      { apply map_disjoint_dom. rewrite !dom_singleton. set_solver. }
      { rewrite map_union_comm.
        - intros Hempty%map_positive_l. set_solver.
        - apply map_disjoint_dom. rewrite dom_singleton. set_solver. }
      { rewrite has_fuels_gt_1; last solve_fuel_positive.
        rewrite !fmap_insert fmap_empty //.
        rewrite insert_union_singleton_l. 
        rewrite map_union_comm; [done|].
        apply map_disjoint_dom. set_solver. }
      { iIntros (tid') "!> Hf".
        wp_pures.
        replace (Z.of_nat M + 1)%Z with (Z.of_nat (M + 1)) by lia.
        iApply (incr_loop_spec with "[Heven_at $Hf]"); [lia|iFrame "#∗"|].
        by iIntros "!>?". }
      iIntros "!> Hf". by iApply "HΦ".
  Qed.

End proof_start.
