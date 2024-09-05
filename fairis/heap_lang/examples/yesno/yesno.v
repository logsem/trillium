From stdpp Require Import decidable.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination fuel sswp_rules resources action_model.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode  notation iris_inst.

Import derived_laws_later.bi.

Open Scope nat.

Set Default Proof Using "Type".

Definition go_impl (b: bool): val :=
  rec: "go_impl" "n" "b" :=
    (if: CAS "b" #(b) #(negb b) then "n" <- !"n" - #1 else #());;
    if: #0 < !"n" then "go_impl" "n" "b" else #().

Definition yes_go : val := go_impl true.

Definition yes : val :=
  λ: "N" "b", let: "n" := Alloc "N" in yes_go "n" "b".

Definition no_go : val := go_impl false .

Definition no : val :=
  λ: "N" "b", let: "n" := Alloc "N" in no_go "n" "b".

Definition start : val :=
  λ: "N", let: "b" := Alloc #true in (Fork (yes "N" "b") ;; Fork (no "N" "b")).

(** * Definition of the model! *)

Inductive YN := Y | No.

#[global] Instance YN_eqdec: EqDecision YN.
Proof. solve_decision. Qed.

#[global] Instance YN_countable: Countable YN.
Proof.
  refine ({|
             encode yn := match yn with Y => 1 | No => 2 end;
             decode p := match p with 1 => Some Y | 2 => Some No | _ => None end;
         |})%positive.
  intros yn. by destruct yn.
Qed.

#[global] Instance YN_inhabited: Inhabited YN.
Proof. exact (populate Y). Qed.

Definition yn_act: Action := coPpick (↑ nroot .@ "yesno"). 

Inductive yntrans: nat*bool -> (Action * option YN) -> nat*bool -> Prop :=
| yes_trans n: (n > 0)%nat -> yntrans (n, true) (yn_act, Some Y) (n, false) (* < *)
| yes_fail n: (n > 1)%nat -> yntrans (n, false) (yn_act, Some Y) (n, false) (* ≤ *)
| no_trans n: yntrans (S n, false) (yn_act, Some No) (n, true) (* < *)
| no_fail n: (n > 0)%nat → yntrans (n, true) (yn_act, Some No) (n, true) (* ≤ *)
.

Definition yn_live_roles nb : gset YN :=
  match nb with
  | (0, _) => ∅
  | (1, false) => {[ No ]}
  | _ => {[ No; Y ]}
  end.

Definition yn_AM: ActionModel := {| amTrans := yntrans |}.

Instance yn_step_dec: AM_step_dec yn_AM. 
Proof. 
  red. intros [n1 b1] a oρ [n2 b2].
  Local Ltac nostep := right; intros STEP; inversion STEP; try (subst; tauto || lia). 
  destruct (decide (a = yn_act)) as [-> | ].
  2: { by nostep. }
  destruct oρ as [ρ| ]; [| by nostep].
  destruct (decide (n2 = n1 /\ b1 = true /\ b2 = false /\ ρ = Y /\ 0 < n1)) as [S| ]. 
  { destruct S as (->&->&->&->&?).
    left. simpl. by constructor. } 
  destruct (decide (n2 = n1 /\ b1 = false /\ b2 = false /\ ρ = Y /\ 1 < n1)) as [S| ]. 
  { destruct S as (->&->&->&->&?).
    left. simpl. by constructor. } 
  destruct (decide (n1 = S n2 /\ b1 = false /\ b2 = true /\ ρ = No)) as [S| ]. 
  { destruct S as (->&->&->&->).
    left. simpl. by constructor. } 
  destruct (decide (n2 = n1 /\ b1 = true /\ b2 = true /\ ρ = No /\ 0 < n1)) as [S| ]. 
  { destruct S as (->&->&->&->&?).
    left. simpl. by constructor. }
  by nostep.
Qed. 

(* (* The model is finitely branching *) *)
(* Definition steppable '(n, w): list ((nat * bool) * option YN) := *)
(*   n' ← [n; (n-1)%nat]; *)
(*   w' ← [w; negb w]; *)
(*   ℓ ← [Some Y; Some No]; *)
(*   mret ((n', w'), ℓ). *)

(* #[local] Instance proof_irrel_trans s x: *)
(*   ProofIrrel ((let '(s', ℓ) := x in yntrans s ℓ s'): Prop). *)
(* Proof. apply make_proof_irrel. Qed. *)

(* Lemma model_finitary s: *)
(*   Finite { '(s', ℓ) | yntrans s ℓ s'}. *)
(* Proof. *)
(*   assert (H: forall A (y x: A) xs, (y = x ∨ y ∈ xs) -> y ∈ x::xs) by set_solver. *)
(*   eapply (in_list_finite (steppable s)). *)
(*   intros [n w] Htrans. *)
(*   inversion Htrans; try (repeat (rewrite ?Nat.sub_0_r; simpl; *)
(*     eapply H; try (by left); right); done). *)
(* Qed. *)

Instance yn_fb: AM_fin_branch' yn_AM.
Proof.
  exists (fun '(n, b) => 
         n' ← [n; (n-1)%nat];
         w' ← [b; negb b];
         ℓ ← [Some Y; Some No];
         mret ((n', w'), yn_act, ℓ)). 
  intros [??] [??] ?? Htrans.
  repeat setoid_rewrite elem_of_list_bind.
  setoid_rewrite elem_of_list_ret.
  setoid_rewrite (and_comm (exists _, _) _).
  setoid_rewrite <- utils.ex_and_comm. rewrite utils.ex_prod'.
  setoid_rewrite (and_comm _ (_ /\ _)).
  setoid_rewrite <- (and_assoc _ _). 
  setoid_rewrite (and_comm _ (_ /\ _)).
  setoid_rewrite <- utils.ex_and_comm. rewrite utils.ex_prod'.
  eapply utils.ex_det_iff.
  { intros [[? ?] ?] (?&EQ&?). simpl in EQ.
    inversion EQ. subst. reflexivity. }
  simpl.
  inversion Htrans; subst; simpl; try set_solver.
  repeat split; try set_solver.
  rewrite Nat.sub_0_r. set_solver.
Qed. 


(* Lemma live_spec_holds: *)
(*      forall s a ρ s', yntrans s (a, Some ρ) s' <-> ρ ∈ yn_live_roles s. *)
(* Proof. *)
(*   intros [n b] a yn [n' b']. *)
(*   split.  *)
(*   - intros Htrans.  *)
(*     inversion Htrans; simplify_eq; destruct n'; try set_solver; try lia; destruct n'; try set_solver; lia. *)
(*   - simpl. destruct n as [| [| ]], b; simpl. *)
(*     all: try by intros. *)
(*     2: { rewrite elem_of_singleton; intros ->. constructor.  *)
(*     all: try ().  *)
(*     1, 2: in *)
(*     intros IN. *)
    
(*     inversion Htrans; simplify_eq; destruct n'; try set_solver; try lia; destruct n'; try set_solver; lia. *)
  
(*   symmetry. etrans; [etrans| ]. *)
(*   2: { apply (@ams_lr_spec yn_AM _ (n, b) (Some yn)). } *)
(*   -   *)
(*   rewrite <- ams_lr_spec.  *)
(*   [n' ?]. *)
  
  
(*   Htrans. rewrite /yn_live_roles. *)
(*   inversion Htrans; simplify_eq; destruct n'; try set_solver; try lia; destruct n'; try set_solver; lia. *)
(* Qed. *)

Lemma yn_AM_live_roles (nb: amSt yn_AM) ρ:
  ρ ∈ AM_live_roles nb <-> ρ ∈ yn_live_roles nb.
Proof.
  destruct nb as [n b]. 
  rewrite -AM_live_roles_spec. simpl.
  destruct n as [| [| ]], b; simpl.
  - split; [| done]. intros (?&?&STEP). inversion STEP; lia.
  - split; [| done]. intros (?&?&STEP). inversion STEP; lia.
  - split.
    + intros (?&?&STEP). inversion STEP; set_solver.
    + rewrite elem_of_union !elem_of_singleton. intros [-> | ->].
      all: do 2 eexists; constructor; lia.  
  - rewrite !elem_of_singleton. 
    split.
    + intros (?&?&STEP). inversion STEP; try lia || done.
    + intros ->. do 2 eexists. constructor.
  - split.
    + intros (?&?&STEP). inversion STEP; set_solver.
    + rewrite elem_of_union !elem_of_singleton. intros [-> | ->].
      all: do 2 eexists; constructor; lia.  
  - split.
    + intros (?&?&STEP). inversion STEP; set_solver.
    + rewrite elem_of_union !elem_of_singleton. intros [-> | ->].
      all: do 2 eexists; constructor; lia.  
Qed.

Definition the_fair_model: FairModel := AM2FM yn_AM _. 

Lemma yn_AM_live_roles' (st: amSt yn_AM):
  live_roles the_fair_model st = yn_live_roles st.
Proof. 
  apply set_eq. intros. rewrite -yn_AM_live_roles. done.
Qed. 

Definition the_model: LiveModel heap_lang the_fair_model :=
  {| lm_flm := 61%nat; |}.

(** The CMRAs we need. *)
Class yesnoG Σ := YesnoG {
  yes_name: gname;
  no_name: gname;
  yesno_n_G :> inG Σ (excl_authR natO);
  yesno_f_G :> inG Σ (excl_authR boolO);
 }.
Class yesnoPreG Σ := {
  yesno_PreG :> inG Σ (excl_authR natO);
  yesno_f_PreG :> inG Σ (excl_authR boolO);
 }.
Definition yesnoΣ : gFunctors :=
  #[ heapΣ the_fair_model; GFunctor (excl_authR natO) ; GFunctor (excl_authR boolO) ].

Global Instance subG_yesnoΣ {Σ} : subG yesnoΣ Σ → yesnoPreG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ the_model, !yesnoG Σ}.
  Let Ns := nroot .@ "yes_no".

  Definition yes_at (n: nat) := own yes_name (◯E n).
  Definition no_at (n: nat) := own no_name (◯E n).

  Definition auth_yes_at (n: nat) := own yes_name (●E n).
  Definition auth_no_at (n: nat) := own no_name (●E n).

  Lemma they_agree γ (N M: nat) :
    own γ (◯E N) -∗ own γ (●E M) -∗ ⌜ M = N ⌝.
  Proof.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.
  Lemma yes_agree N M :
    yes_at N -∗ auth_yes_at M -∗ ⌜ M = N ⌝.
  Proof. apply they_agree. Qed.
  Lemma no_agree N M :
    no_at N -∗ auth_no_at M -∗ ⌜ M = N ⌝.
  Proof. apply they_agree. Qed.

  Lemma they_update γ (N M P: nat) :
    own γ (●E N) ∗ own γ (◯E M) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.
  Lemma yes_update P N M :
     auth_yes_at M ∗ yes_at N ==∗ auth_yes_at P ∗ yes_at P.
  Proof. apply they_update. Qed.
  Lemma no_update P N M :
     auth_no_at M ∗ no_at N ==∗ auth_no_at P ∗ no_at P.
  Proof. apply they_update. Qed.

  Lemma they_finished_update γ (N M P: bool) :
    own γ (●E N) ∗ own γ (◯E M) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.

  Definition yesno_inv_inner b : iProp Σ :=
    ∃ N B, 
      ⌜(N, B) ≠ (0, false)⌝ ∗
      frag_free_roles_are ∅ ∗
      frag_model_is (N, B) ∗ b ↦ #B ∗
      if B
      then auth_yes_at N ∗ auth_no_at N
      else auth_yes_at (N-1) ∗ auth_no_at N.
  Definition yesno_inv b := inv Ns (yesno_inv_inner b).

  Lemma yes_go_spec tid n b (N: nat) f (Hf: f > 40):
    {{{ yesno_inv b ∗ tid ↦M {[ Y := f ]} ∗ n ↦ #N ∗ ⌜N > 0⌝%nat ∗
        yes_at N }}}
      yes_go #n #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ) "(#Hinv & Hf & HnN & %HN & Hyes) Hk". unfold yes_go, go_impl.
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    assert (∀ s, Atomic s (CmpXchg #b #true #false)) by apply _.
    iApply wp_atomic.
    iInv Ns as (M B) "(>%Hnever & >HFR & >Hmod & >Bb & Hauths)" "Hclose".
    destruct B; iDestruct "Hauths" as "[>Hay >Han]".
    - iDestruct (yes_agree with "Hyes Hay") as "%Heq".
      destruct (decide (M = 0)) as [->|Nneq]; first lia.
      destruct (decide (M = 1)) as [->|Nneq1].
      + iModIntro.
        iApply (wp_step_model_singlerole with "Hmod Hf").
        { simpl. do 2 econstructor. lia. }
        { rewrite !yn_AM_live_roles'. simpl. set_solver. }
        iApply (wp_cmpxchg_suc with "Bb"); [done|done|].
        iIntros "!> Hb Hmod Hf".
        iMod (yes_update 0 with "[$]") as "[Hay Hyes]".
        wp_pures.
        iMod ("Hclose" with "[Hmod Hb Hay Han HFR]").
        { iNext. iExists _, _. iFrame. simpl. iFrame. by iPureIntro. }
        iApply fupd_mask_intro; [done|]. iMod 1. iModIntro.
        simpl in *. wp_load. wp_store. wp_load. wp_pure _. simplify_eq. simpl.
        iApply wp_atomic.
        iInv Ns as (M B) "(>%Hbever' & >HFR & >Hmod & >Hb & Hauths)" "Hclose".
        destruct B.
        * iModIntro.
          iApply (wp_step_fuel with "[Hf]").
          2: { iClear "Hg". rewrite has_fuels_gt_1; last by solve_fuel_positive.
            rewrite fmap_insert fmap_empty. done. }
          { set_solver. }
          iApply sswp_pure_step; [done|].
          iIntros "!> Hf". iApply wp_pre_step. wp_pures.
          iApply fupd_mask_intro; [done|].
          iIntros "Hclose'".
          iDestruct "Hauths" as "[Hay Han]".
          iDestruct (yes_agree with "Hyes Hay") as %Heq.
          assert (M = 0) by lia. simplify_eq.
          iMod (has_fuels_dealloc _ _ _ (Y:fmrole the_fair_model)
                 with "Hmod Hf") as "[Hmod Hf]".
          { by intros IN%yn_AM_live_roles. }
          iModIntro. iMod "Hclose'".
          iMod ("Hclose" with "[Hmod Hay Han Hb HFR]").
          { iNext. iExists _, _. iFrame. done. }
          iModIntro. iApply "Hk".
          rewrite delete_insert; [|set_solver].
          iFrame "Hf".
        * iDestruct "Hauths" as "[>Hay >Han]". iDestruct (yes_agree with "Hyes Hay") as %Heq.
          assert (M = 1) by (destruct M; [done|lia]). simplify_eq.
          iModIntro.
          iApply (wp_step_fuel with "[Hf]").
          2: { iClear "Hg". rewrite has_fuels_gt_1; last by solve_fuel_positive.
               rewrite fmap_insert fmap_empty. done. }
          { set_solver. }
          iApply sswp_pure_step; [done|].
          iIntros "!> Hf". iApply wp_pre_step. wp_pures.
          iApply fupd_mask_intro; [done|].
          iIntros "Hclose'".
          iMod (has_fuels_dealloc _ _ _ (Y:fmrole the_fair_model)
                 with "Hmod Hf") as "[Hmod Hf]".
          { intros IN%yn_AM_live_roles. simpl in IN. set_solver. } 
          iModIntro. iMod "Hclose'".
          iMod ("Hclose" with "[Hmod Hay Han Hb HFR]").
          { iNext. iExists _, _. iFrame. done. }
          iModIntro. iApply "Hk".
          rewrite delete_insert; [|set_solver].
          iFrame.
      + assert (N = N) by lia. simplify_eq.
        iModIntro.
        iApply (wp_step_model_singlerole with "Hmod Hf").
        { simpl. do 2 econstructor. lia. }
        { rewrite !yn_AM_live_roles'. 
          destruct M; [set_solver | destruct M; set_solver]. }
        iApply (wp_cmpxchg_suc with "Bb"); [done|done|].
        iIntros "!> Hb Hmod Hf".
        iMod (yes_update (M-1) with "[$]") as "[Hay Hyes]".
        wp_pures. iModIntro.
        iMod ("Hclose" with "[Hmod Hay Han Hb HFR]").
        { iNext. iExists _, _. iFrame. iPureIntro. intro contra. simplify_eq. }
        iModIntro.
        simpl. wp_load. wp_store. wp_load. wp_pures.
        destruct (decide (0 < S M - 1)) as [Heq|Heq].
        * rewrite bool_decide_eq_true_2 //; last lia.
          wp_pure _.
          iApply ("Hg" with "[] [Hyes HnN Hf] [$]"); last first.
          { iFrame "∗#". iSplit; last by iPureIntro; lia.
            iClear "Hg Hinv".
            assert (∀ l v v', v = v' → l ↦ v ⊣⊢ l ↦ v') as pointsto_proper.
            { intros ??? ->. done. }
            iApply (pointsto_proper with "HnN"). do 2 f_equiv. destruct M; [done|]. lia. }
          iPureIntro; lia.
        * rewrite bool_decide_eq_false_2 //; last lia.
          have ->: M = 0 by lia. simpl. lia.
    - iDestruct (yes_agree with "Hyes Hay") as "%Heq". rewrite -> Heq in *.
      have HM: M > 0 by lia.
      iModIntro.
      iApply (wp_step_model_singlerole with "Hmod Hf").
      { simpl. do 2 econstructor. lia. }
      { set_solver. }
      iApply (wp_cmpxchg_fail with "Bb"); [done|done|].
      iIntros "!> Hb Hmod Hf".
      wp_pures. iModIntro.
      iMod ("Hclose" with "[Hmod Hb Hay Han HFR]").
      { iNext. simplify_eq. iExists _, _. iFrame. iFrame. done. }
      iModIntro.
      simpl. wp_load. wp_pure _. rewrite bool_decide_eq_true_2; last lia.
      wp_pure _.
      iApply ("Hg" with "[] [Hyes HnN Hf] [$]"); last first.
      { iFrame "∗#". iPureIntro; lia. }
      iPureIntro; lia.
  Qed.

  Lemma yes_spec tid b (N: nat) f (Hf: f > 50):
    {{{ yesno_inv b ∗ tid ↦M {[ Y := f ]} ∗ ⌜N > 0⌝ ∗ yes_at N }}}
      yes #N #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hf & %HN & Hyes) Hk". unfold yes.
    wp_pures.
    wp_bind (Alloc _).
    iApply (wp_step_fuel with "[Hf]").
    { apply map_non_empty_singleton. }
    { rewrite has_fuels_gt_1; last by solve_fuel_positive.
      rewrite fmap_insert fmap_empty. done. }
    iApply wp_alloc. iNext. iIntros (n) "HnN _ Hf". wp_pures. iModIntro. wp_pures.
    iApply (yes_go_spec with "[-Hk]"); try iFrame.
    { lia. }
    { iFrame "Hinv". iPureIntro; lia. }
  Qed.

  Lemma no_go_spec tid n b (N: nat) f (Hf: f > 40):
    {{{ yesno_inv b ∗ tid ↦M {[ No := f ]} ∗ n ↦ #N ∗ ⌜N > 0⌝ ∗ no_at N }}}
      no_go #n #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ) "(#Hinv & Hf & HnN & %HN & Hno) Hk". unfold no_go, go_impl.
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    assert (∀ s, Atomic s (CmpXchg #b #true #false)) by apply _.
    iApply wp_atomic.
    iInv Ns as (M B) "(>%Hnever & >HFR & >Hmod & >Bb & Hauths)" "Hclose".
    destruct B; iDestruct "Hauths" as "[>Hay >Han]"; last first.
    - iDestruct (no_agree with "Hno Han") as "%Heq".
      destruct (decide (M = 0)) as [->|Nneq]; first lia.
      destruct (decide (M = 1)) as [->|Nneq1].
      + iModIntro.
        iApply (wp_step_model_singlerole with "Hmod Hf").
        { simpl. do 2 econstructor. }
        { rewrite !yn_AM_live_roles'. simpl. set_solver. }
        iApply (wp_cmpxchg_suc with "Bb"); [done|done|].
        iIntros "!> Hb Hmod Hf".
        iMod (no_update 0 with "[$]") as "[Han Hno]".
        wp_pures. iModIntro.
        iMod ("Hclose" with "[Hmod Hb Hay Han HFR]").
        { iNext. iExists _, _. iFrame. simpl. iFrame. by iPureIntro. }
        iModIntro.
        simpl. wp_load. wp_store. wp_load. wp_pure _. simplify_eq. simpl.
        iApply wp_atomic.
        iInv Ns as (M B) "(>%Hbever' & >HFR & >Hmod & >Hb & Hauths)" "Hclose".
        destruct B.
        * iModIntro.
          iApply (wp_step_fuel with "[Hf]").
          2: { iClear "Hg". rewrite has_fuels_gt_1; last by solve_fuel_positive.
            rewrite fmap_insert fmap_empty. done. }
          { set_solver. }
          iApply sswp_pure_step; [done|].
          iIntros "!> Hf".
          iDestruct "Hauths" as "[Hay Han]". iDestruct (no_agree with "Hno Han") as %Heq.
          assert (M = 0) by lia. simplify_eq.
          iMod (has_fuels_dealloc _ _ _
                                  (No:fmrole the_fair_model) with "Hmod Hf")
            as "[Hmod Hf]".
          { by intros IN%yn_AM_live_roles. }
          wp_pures. iModIntro.
          iMod ("Hclose" with "[Hmod Hay Han Hb HFR]").
          { iNext. iExists _, _. iFrame. done. }
          iModIntro. iApply "Hk".
          rewrite delete_insert; [|done].
          iFrame.
        * iDestruct "Hauths" as "[>Hay >Han]". iDestruct (no_agree with "Hno Han") as %Heq.
          assert (M = 0) by lia. simplify_eq.
      + assert (N = N) by lia. simplify_eq.
        destruct M; first done.
        iModIntro.
        iApply (wp_step_model_singlerole with "Hmod Hf").
        { simpl. do 2 econstructor. }
        { rewrite !yn_AM_live_roles'. simpl.
          destruct M as [| [| ]]; try lia; done. }
        iApply (wp_cmpxchg_suc with "Bb"); [done|done|].
        iIntros "!> Hb Hmod Hf".
        iMod (no_update (M) with "[$]") as "[Han Hno]".
        wp_pures. iModIntro.
        iMod ("Hclose" with "[Hmod Hay Han Hb HFR]").
        { iNext. iExists _, _. iFrame. iSplit; [done|].
          iApply (own_proper with "Hay"). f_equiv. apply leibniz_equiv_iff. lia. }
        iModIntro. simpl. wp_load. wp_store. wp_load. wp_pures.
        destruct (decide (0 < S M - 1)) as [Heq|Heq].
        * rewrite bool_decide_eq_true_2 //; last lia.
          wp_pure _.
          iApply ("Hg" with "[] [Hno HnN Hf] [$]"); last first.
          { iFrame "∗#". assert ((S M - 1)%Z = M)%nat as -> by lia. iFrame. iPureIntro; lia. }
          iPureIntro; lia.
        * rewrite bool_decide_eq_false_2 //; last lia.
          have ->: M = 0 by lia. simpl. lia.
    - iDestruct (no_agree with "Hno Han") as "%Heq". rewrite -> Heq in *.
      have HM: M > 0 by lia.
      assert (M = N) by lia. simplify_eq. iModIntro.
      iApply (wp_step_model_singlerole with "Hmod Hf").
      { simpl. do 2 econstructor. done. }
      { rewrite !yn_AM_live_roles'. simpl. set_solver. }
      iApply (wp_cmpxchg_fail with "Bb"); [done|done|].
      iIntros "!> Hb Hmod Hf".
      wp_pures.
      iModIntro.
      iMod ("Hclose" with "[Hmod Hb Hay Han HFR]").
      { iNext. simplify_eq. iExists _, _. iFrame. iFrame. done. }
      iModIntro. simpl. wp_load. wp_pure _.
      rewrite bool_decide_eq_true_2; last lia. wp_pure _.
      iApply ("Hg" with "[] [Hno HnN Hf] [$]"); last first.
      { iFrame "∗#". iPureIntro; lia. }
      iPureIntro; lia.
  Qed.

  Lemma no_spec tid b (N: nat) f (Hf: f > 50):
    {{{ yesno_inv b ∗ tid ↦M {[ No := f ]} ∗ ⌜N > 0⌝ ∗ no_at N }}}
      no #N #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hf & %HN & Hyes) Hk". unfold no.
    wp_pures. wp_bind (Alloc _).
    iApply (wp_step_fuel with "[Hf]").
    { apply map_non_empty_singleton. }
    { rewrite has_fuels_gt_1; last by solve_fuel_positive.
      rewrite fmap_insert fmap_empty. done. }
    iApply wp_alloc. iNext. iIntros (n) "HnN _ Hf". wp_pures. iModIntro. wp_pures.
    iApply (no_go_spec with "[-Hk]"); try iFrame.
    { lia. }
    { iFrame "Hinv". done. }
  Qed.
End proof.

Section proof_start.
  Context `{!heapGS Σ the_model, !yesnoPreG Σ}.
  Let Ns := nroot .@ "yes_no".

  Lemma start_spec tid (N: nat) f (Hf: f > 60):
    {{{ frag_model_is (N, true) ∗ frag_free_roles_are ∅ ∗
        tid ↦M {[ Y := f; No := f ]} ∗ ⌜N > 0⌝ }}}
      start #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using All.
    iIntros (Φ) "[Hst [HFR [Hf %HN]]] Hkont". unfold start.
    wp_pures. wp_bind (Alloc _).
    iApply (wp_step_fuel with "[Hf]").
    2: { rewrite has_fuels_gt_1; last by solve_fuel_positive.
         rewrite !fmap_insert fmap_empty. done. }
    { rewrite insert_union_singleton_l.
      intros ?%map_positive_l. set_solver. }
    iApply wp_alloc. iNext. iIntros (l) "HnN _ Hf". wp_pures. iModIntro. wp_pures.
    (* Allocate the invariant. *)
    iMod (own_alloc (●E N  ⋅ ◯E N))%nat as (γ_yes_at) "[Hyes_at_auth Hyes_at]".
    { apply auth_both_valid_2; eauto. by compute. }
    iMod (own_alloc (●E N  ⋅ ◯E N))%nat as (γ_no_at) "[Hno_at_auth Hno_at]".
    { apply auth_both_valid_2; eauto. by compute. }
    pose (the_names := {|
     yes_name := γ_yes_at;
     no_name := γ_no_at;
    |}).
    iApply fupd_wp.
    iMod (inv_alloc Ns _ (yesno_inv_inner l) with "[-Hkont Hf Hyes_at Hno_at]") as "#Hinv".
    { iNext. unfold yesno_inv_inner. iExists N, true. iFrame. done. }
    iModIntro.
    wp_bind (Fork _).
    iApply (wp_role_fork _ tid _ _ _ {[No := _]} {[Y := _]}
             with "[Hf] [Hyes_at]").
    { apply map_disjoint_dom. rewrite !dom_singleton. set_solver. }
    { intros Hempty%map_positive_l. set_solver. }
    { rewrite has_fuels_gt_1; last solve_fuel_positive.
      rewrite !fmap_insert fmap_empty //.
      rewrite insert_union_singleton_l.
      rewrite map_union_comm; [done|].
      apply map_disjoint_dom. set_solver. }
    { iIntros (tid') "!> Hf". iApply (yes_spec with "[-]"); last first.
      + by eauto.
      + iFrame "#∗". iPureIntro. lia.
      + lia. }
    iIntros "!> Hf !>". wp_pures.
    iApply (wp_role_fork _ tid _ _ _ ∅ {[No := _]} with "[Hf] [Hno_at] [Hkont]").
    { apply map_disjoint_dom. rewrite !dom_singleton. set_solver. }
    { rewrite map_union_comm.
      - intros Hempty%map_positive_l. set_solver.
      - apply map_disjoint_dom. rewrite dom_singleton. set_solver. }
    { rewrite has_fuels_gt_1; last solve_fuel_positive.
      rewrite !fmap_insert fmap_empty //.
      rewrite insert_union_singleton_l.
      rewrite map_union_comm; [done|].
      apply map_disjoint_dom. set_solver. }
    { iIntros (tid') "!> Hf". iApply (no_spec with "[-]"); last first.
      + by eauto.
      + by iFrame "#∗".
      + lia. }
    iNext. iIntros "Hf". by iApply "Hkont".
  Qed.

End proof_start.
