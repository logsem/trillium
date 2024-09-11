From stdpp Require Import decidable.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination fuel sswp_rules resources action_model utils.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode  notation iris_inst.
From trillium.fairness.heap_lang.examples Require Import env_am split_model.
From trillium.fairness.heap_lang.examples Require Import mu_role.

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

Lemma yn_acts: forall a, is_action_of yn_AM a <-> a = yn_act.
Proof. 
  intros. rewrite /is_action_of. split.
  - intros (?&?&?&STEP). inversion STEP; eauto.
  - intros ->.
    do 3 eexists. econstructor. eauto.
Qed. 

Lemma yn_AM_live_roles' (st: amSt yn_AM):
  AM_live_roles st = yn_live_roles st.
Proof. 
  apply set_eq. intros. rewrite -yn_AM_live_roles. done.
Qed. 

Instance yn_AM_act_dec: forall a, Decision (is_action_of yn_AM a).
Proof.
  intros. eapply Decision_iff_impl; [symmetry; apply yn_acts| ].
  apply _.
Qed. 
  
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


Section FullModel.
  Context `(ENV_AM: EnvironmentAM env_AM).

  Definition FM := ProdAM env_AM yn_AM.
  
  Definition the_fair_model: FairModel := AM2FM FM _. 
  
  Definition the_model: LiveModel heap_lang the_fair_model :=
    {| lm_flm := 61%nat; |}.
  
  Definition yesnoΣ : gFunctors :=
    #[ heapΣ the_fair_model; GFunctor (excl_authR natO) ; GFunctor (excl_authR boolO) ].

  Global Instance subG_yesnoΣ {Σ} : subG yesnoΣ Σ → yesnoPreG Σ.
  Proof. solve_inG. Qed.

End FullModel.


Section proof.
  Context `(ENV_AM: EnvironmentAM env_AM).
  Context {INDEP: models_independent env_AM yn_AM}.

  Let M := the_fair_model ENV_AM.
  Let LM := the_model ENV_AM. 
  Let PM := @FM env_AM. 

  Context `{!heapGS Σ LM, !yesnoG Σ, SplitGS Σ env_AM yn_AM}.

  Let Ns := nroot .@ "yes_no".

  Definition yes_at (n: nat) := own yes_name (◯E n).
  Definition no_at (n: nat) := own no_name (◯E n).

  Definition auth_yes_at (n: nat) := own yes_name (●E n).
  Definition auth_no_at (n: nat) := own no_name (●E n).

  Lemma they_agree γ (n m: nat) :
    own γ (◯E n) -∗ own γ (●E m) -∗ ⌜ m = n ⌝.
  Proof.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.
  Lemma yes_agree n m :
    yes_at n -∗ auth_yes_at m -∗ ⌜ m = n ⌝.
  Proof. apply they_agree. Qed.
  Lemma no_agree n m :
    no_at n -∗ auth_no_at m -∗ ⌜ m = n ⌝.
  Proof. apply they_agree. Qed.

  Lemma they_update γ (n m P: nat) :
    own γ (●E n) ∗ own γ (◯E m) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.
  Lemma yes_update P n m :
     auth_yes_at m ∗ yes_at n ==∗ auth_yes_at P ∗ yes_at P.
  Proof. apply they_update. Qed.
  Lemma no_update P n m :
     auth_no_at m ∗ no_at n ==∗ auth_no_at P ∗ no_at P.
  Proof. apply they_update. Qed.

  Lemma they_finished_update γ (n m P: bool) :
    own γ (●E n) ∗ own γ (◯E m) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.

  Definition yn_corr l n b: iProp Σ := 
      (⌜(n, b) ≠ (0, false)⌝ ∗
      (* frag_right_st_is (n, b) ∗ *)
      l ↦ #b ∗
      if b
      then auth_yes_at n ∗ auth_no_at n
      else auth_yes_at (n-1) ∗ auth_no_at n)%I.

  Definition yesno_inv_inner b : iProp Σ :=
    ∃ n B,
      yn_corr b n B ∗
      frag_right_st_is (n, B). 

  Definition yesno_inv b := inv Ns (yesno_inv_inner b).

  Definition Ns__split := nroot .@ "split".

  Let yn_role (ρ: YN): amRole PM := inr ρ.

  Lemma yes_go_spec tid n b (N: nat) f (Hf: f > 40):
    {{{ split_inv Ns__split ∗ yesno_inv b ∗ tid ↦M {[ yn_role Y := f ]} ∗ n ↦ #N ∗ ⌜N > 0⌝%nat ∗
        yes_at N }}}
      yes_go #n #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using INDEP.
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ) "(#SPLIT & #Hinv & Hf & HnN & %HN & Hyes) Hk". unfold yes_go, go_impl.
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    iApply wp_atomic.
    iInv Ns as (m B) "((>%Hnever & >Bb & Hauths) & >Hmod)" "Hclose".
    iInv Ns__split as ([e ?]) "(>ST & >PROD)" "Hclose'".
    simpl. 
    iDestruct (right_agree with "PROD Hmod") as %->.

    rewrite if_arg2_comm. iDestruct "Hauths" as "[Hay Han]". 
    rewrite !if_arg_comm. iMod "Hay". iMod "Han".
    iDestruct (yes_agree with "Hyes Hay") as %Heq.
    
    assert (amTrans yn_AM (m, B) (yn_act, Some Y) (m, false)) as STEP.
    { destruct B; econstructor; lia. }

    destruct B. 
    - destruct (decide (m= 0)) as [->|Nneq]; first lia.
      iModIntro.
      subst N.

      iApply sswp_MU_wp; [done| ].
      iApply (wp_cmpxchg_suc with "[$]"); try done.
      iIntros "!> Hb". 

      iApply (MU_wand with "[-ST Hf]").
      2: { iApply (model_step_singlerole_MU with "[$] [$]"). 
           { simpl. do 2 econstructor; eauto.
             intros ?. apply action_of_step in STEP.
             edestruct INDEP; eauto. }
           simpl. rewrite !(prod_indep_live_roles _ _ INDEP). 
           rewrite !yn_AM_live_roles'. simpl.
           apply union_mono; [done| ].
           destruct m as [|[|]]; [lia| ..]; set_solver. }
      iIntros "[ST Hf]".

      iMod (yes_update (m - 1) with "[$]") as "[Hay Hyes]".
      iMod (update_right ((m, false): amSt yn_AM) with "[$] [$]") as "[PROD Hmod]".
      wp_pures.
      iModIntro. 
      iMod ("Hclose'" with "[PROD ST]") as "_".
      { iFrame. }
      iMod ("Hclose" with "[Hmod Hb Hay Han]") as "_".
      { iNext. iExists _, _. iFrame. simpl. iFrame.
        iPureIntro. by intros [=]. }
      iModIntro. 
      
      simpl in *. wp_load. wp_store. wp_load. wp_pure _.
      destruct m; [lia| ].
      destruct m. 
      + rewrite bool_decide_eq_false_2.
        2: { lia. }
        iApply wp_atomic.
        iInv Ns as (m B) "((>%Hbever' & >Hb & Hauths) & >Hmod)" "Hclose".
        clear e. iInv Ns__split as ([e ?]) "(>ST & >PROD)" "Hclose_".
        iDestruct (right_agree with "PROD Hmod") as %EQ. simpl in EQ. subst. simpl.
        rewrite if_arg2_comm. iDestruct "Hauths" as "[Hay Han]". 
        rewrite !if_arg_comm. iMod "Hay". iMod "Han".
        iDestruct (yes_agree with "Hyes Hay") as %Heq.
        
        iAssert (⌜ m= 0 /\ B = true \/ m= 1 /\ B = false ⌝)%I as %EQ.
        { iPureIntro. destruct B; [tauto| ]. 
          right. split; [| done].
          destruct m as [|[|]]; try lia. done. }
        iModIntro.

        iApply wp_pre_step. wp_pure _. 
        iApply fupd_mask_intro; [done|].
        iIntros "Hclose'".
        rewrite insert_empty.
        iMod (has_fuels_dealloc _ _ _ (yn_role Y: fmrole M) with "ST Hf") as "[ST Hf]".
        { simpl. rewrite prod_indep_live_roles. apply not_elem_of_union.
          split; [set_solver| ]. 
          intros IN%elem_of_map_inj_gset; [| by apply _]. 
          rewrite yn_AM_live_roles in IN.
          destruct EQ as [[-> ->]|[-> ->]]; set_solver. }
        iModIntro.
        iMod ("Hclose_" with "[PROD ST]").
        { iFrame. }
        iMod ("Hclose" with "[Hmod Hay Han Hb]").
        { iNext. iExists _, _. iFrame.
          destruct EQ as [[-> ->]|[-> ->]]; iFrame; done. }
        iModIntro. iApply "Hk".
        rewrite delete_insert; [|set_solver].
        iFrame "Hf".
      + rewrite bool_decide_eq_true_2 //; last lia.
        wp_pure _.
        iApply ("Hg" with "[] [Hyes HnN Hf] [$]"); last first.
        { iFrame "∗#". iSplit; last by iPureIntro; lia.
          by rewrite Nat2Z.inj_sub; [| lia]. }
        iPureIntro; lia.
    - have HM: m> 0 by lia.
      iModIntro.

      iApply sswp_MU_wp; [done| ].
      iApply (wp_cmpxchg_fail with "[$]"); try done.
      iIntros "!> Hb". 
      iApply (MU_wand with "[-ST Hf]").
      2: { iApply (model_step_singlerole_MU with "[$] [$]"). 
           { simpl. do 2 econstructor; eauto.
             intros ?. apply action_of_step in STEP. 
             edestruct INDEP; eauto. }
           set_solver. }
      iIntros "[ST Hf]".
      wp_pures. iModIntro.
      iMod ("Hclose'" with "[ST PROD]").
      { iFrame. simpl. iFrame. }
      iMod ("Hclose" with "[Hmod Hb Hay Han]").
      { iNext. simplify_eq. iExists _, _. iFrame. iFrame. done. }
      iModIntro.
      simpl. wp_load. wp_pure _. rewrite bool_decide_eq_true_2; last lia.
      wp_pure _.
      iApply ("Hg" with "[] [Hyes HnN Hf] [$]"); last first.
      { iFrame "∗#". iPureIntro; lia. }
      iPureIntro; lia.
  (* This proof works but takes forever to typecheck *)
  (* Time Qed. *)
  Abort. 

  Definition MU__drop ρ E P: iProp Σ :=  
    ∀ τ f R, τ ↦M ({[ ρ := f ]} ∪ R) ∗ ⌜ ρ ∉ dom R ⌝ -∗
              (* MU E τ (τ ↦M R ∗ P) (LM := LM). *)
               |~{ E }~| (τ ↦M R ∗ P).

  (* TODO: some of updates should drop the role *)
  Definition yes_vs l ι: iProp Σ :=
    □ |={⊤, ⊤ ∖ ↑ι}=> ∃ n b,
      (▷ yn_corr l n b) ∗
      ((⌜ if b then n > 0 else n > 1 ⌝ -∗ MU__r (yn_role Y) (⊤ ∖ ↑ι)
         (* redundancy to ease subsequent adaptation for No thread *)
           (▷ (if b then yn_corr l n false else yn_corr l n false) ={⊤ ∖ ↑ι, ⊤}=∗ True)
       ) ∧
       (⌜ n = 0 /\ b = true \/ n = 1 /\ b = false ⌝ -∗ 
        MU__drop (yn_role Y) (⊤ ∖ ↑ι) (▷ yn_corr l n b ={⊤ ∖ ↑ι, ⊤}=∗ True))
      ).

  Lemma mu_yes n (b: bool) (ns: namespace)
    (NB: if b then n > 0 else n > 1):
    inv ns (split_inv_inner) ⊢ frag_right_st_is (n, b) -∗ 
      MU__r (yn_role Y) (↑ ns) (frag_right_st_is $ if b then (n, false) else (n, false)).
  Proof using INDEP.
    rewrite /MU__r. iIntros "#INV ST" (tid f' R) "[MAP %DISJ__R]".
    (* destruct st as [[st__e st__o] st__env]. *)

    enough (exists a, amTrans yn_AM (n, b) (a, Some Y) (if b then (n, false) else (n, false))) as (a & TRANS). 
    { iApply (MU_inv with "[$]"); [done| ].
      (* TODO: avoid unfolding of MU *)
      rewrite /split_inv_inner. simpl. iIntros ">(%S & FRAG & PROD)". destruct S.
      simpl. iDestruct (right_agree with "[$] [$]") as %->.

      iMod (update_right ((if b then (n, false) else (n, false)): amSt yn_AM) with "[$] [$]") as "[PROD ST]".
      iApply (MU_wand with "[ST PROD]").
      2: { iApply (model_step_MU with "[$] [MAP]").
           1, 4: by eauto.
           { simpl. eapply am_fmtrans_action. eexists. 
             eapply pt_inner2; eauto.
             intros ?. edestruct INDEP; eauto.
             eapply action_of_step; eauto. }
           simpl. setoid_rewrite @prod_indep_live_roles; eauto.
           apply union_mono; [done| ]. apply set_map_mono; [done| ].
           erewrite !yn_AM_live_roles'.
           simpl. destruct b, n as [|[|]]; set_solver. }
      iIntros "(MAP & FRAG)".
      iFrame. }
    Unshelve. 2: by apply _.

    exists yn_act. simpl. destruct b; by constructor. 
  Qed.

  Lemma dealloc_yes n (b: bool) (ns: namespace)
    (NB: n = 0 /\ b = true \/ n = 1 /\ b = false):
    inv ns (split_inv_inner) ⊢ frag_right_st_is (n, b) -∗
        MU__drop (yn_role Y) (↑ ns) (frag_right_st_is (n, b)). 
  Proof using INDEP. 
    rewrite /MU__drop. iIntros "#INV ST" (tid f' R) "[MAP %DISJ__R]".

    iApply (pre_step_inv with "[$]"); [done| ].
    rewrite /split_inv_inner. simpl. iIntros "(%S & FRAG & PROD)". destruct S.
    iApply fupd_pre_step. iMod "FRAG". iMod "PROD". iModIntro. 
    simpl. iDestruct (right_agree with "[$] [$]") as %->.

    (* iApply (pre_step_mono with "[ST MAP]"). *)
    (* 2: { iApply (has_fuels_dealloc with "[$]").  *)
    
    iMod (has_fuels_dealloc _ _ _ (yn_role Y: fmrole M) with "FRAG MAP") as "[FRAG MAP]".
    { simpl. rewrite prod_indep_live_roles. apply not_elem_of_union.
      split; [set_solver| ].
      intros IN%elem_of_map_inj_gset; [| by apply _].
      rewrite yn_AM_live_roles in IN.
      destruct NB as [[-> ->]|[-> ->]]; set_solver. }

    iModIntro. rewrite -insert_union_singleton_l delete_insert_dom.
    2: set_solver.
    by iFrame.
  Qed. 

  (* TODO: move *)
  Lemma MU__drop_mask_weaken E1 E2 ρ (P: iProp Σ)
    (SUB: E1 ⊆ E2):
    MU__drop ρ E1 P -∗ MU__drop ρ E2 P.
  Proof.
    iIntros "MU". rewrite /MU__drop. iIntros "**".
    iMod pre_step_mask_subseteq as "CLOS"; [by apply SUB| ].
    iMod ("MU" with "[$]") as "X". iMod "CLOS".
    iModIntro. done. 
  Qed.

  (* TODO: move *)
  Lemma MU__drop_wand E ρ (P Q: iProp Σ):
    (P -∗ Q) -∗ MU__drop ρ E P -∗ MU__drop ρ E Q.
  Proof.
    iIntros "PQ MU". rewrite /MU__drop. iIntros "**".
    iSpecialize ("MU" with "[$]"). 
    iApply (pre_step_mono with "[PQ] [$]").
    iIntros "[??]". iFrame. by iApply "PQ". 
  Qed.

  Lemma yes_vs_from_invs l:
    yesno_inv l ∗ split_inv Ns__split  ⊢ yes_vs l Ns.
  Proof using INDEP.
    rewrite /yes_vs. iIntros "#[INV1 INV2]". iModIntro.
    iMod (inv_acc with "INV1") as "[OPEN CLOS]".
    { apply top_subseteq. }
    
    rewrite {1}/yesno_inv_inner. rewrite {1}/yn_corr.  
    iDestruct "OPEN" as (n b) "((>%NEQ & >LOC & AUTHS) & >RIGHT)".
    iModIntro.
    iExists _, _. iSplitL "LOC AUTHS".
    { by iFrame. }

    iSplit. 
    - iIntros "%B". 
      iApply (MU__r_mask_weaken (↑ Ns__split) with "[-]").
      { assert (Ns__split ## Ns) by solve_ndisj. set_solver. }
      iApply (MU__r_wand with "[-RIGHT]").
      2: { by iApply (mu_yes with "[$] [$]"). }
      iIntros "RIGHT CORR".
      iMod ("CLOS" with "[-]"); [| done].
      rewrite /yesno_inv_inner. iNext.
      (* some redundancy to ease subsequent "No" proofs *)
      iExists (if b then n else n), (if b then false else false).
      destruct b; iFrame.
    - iIntros "%NB". 
      iApply (MU__drop_mask_weaken (↑ Ns__split) with "[-]").
      { assert (Ns__split ## Ns) by solve_ndisj. set_solver. }
      iApply (MU__drop_wand with "[-RIGHT]"). 
      2: { by iApply (dealloc_yes with "[$]"). }
      iIntros "RIGHT CORR".
      iMod ("CLOS" with "[-]"); [| done].
      rewrite /yesno_inv_inner. iNext.
      iFrame. 
  Qed.

  Lemma yes_go_spec_vs tid n b (N: nat) f (Hf: f > 40):
    {{{ (* split_inv Ns__split ∗ *)
        (* yesno_inv b ∗ *)
        yes_vs b Ns ∗
        tid ↦M {[ yn_role Y := f ]} ∗ n ↦ #N ∗ ⌜N > 0⌝%nat ∗
        yes_at N }}}
      yes_go #n #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using INDEP.
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ) "(#VS & Hf & HnN & %HN & Hyes) Hk". unfold yes_go, go_impl.
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    iApply wp_atomic.

    iPoseProof "VS" as "-#V". 
    iMod "V" as "(%m & %B & ((>%Hnever & >Bb & Hauths) & V))".
    iDestruct (bi.and_elim_l with "V") as "MU_y".       

    (* iInv Ns__split as ([e ?]) "(>ST & >PROD)" "Hclose'". *)
    simpl. 

    (* iDestruct (right_agree with "PROD Hmod") as %->. *)

    rewrite if_arg2_comm. iDestruct "Hauths" as "[Hay Han]". 
    rewrite !if_arg_comm. iMod "Hay". iMod "Han".
    iDestruct (yes_agree with "Hyes Hay") as %Heq.
    
    (* assert (amTrans yn_AM (m, B) (yn_act, Some Y) (m, false)) as STEP. *)
    (* { destruct B; econstructor; lia. } *)

    destruct B. 
    - destruct (decide (m= 0)) as [->|Nneq]; first lia.
      iModIntro.
      subst N.

      iApply sswp_MU_wp; [done| ].
      iApply (wp_cmpxchg_suc with "[$]"); try done.
      iIntros "!> Hb". 

      iApply (MU_wand with "[-Hf MU_y]").
      2: { iSpecialize ("MU_y" with "[] [Hf]").
           { iPureIntro. lia. }
           2: { by iFrame. }
           iSplitL.
           { iApply has_fuels_proper; [reflexivity| | by iFrame].
             rewrite insert_union_singleton_l. f_equiv.
             apply leibniz_equiv_iff, fmap_empty. }
           iPureIntro. set_solver. } 

      iIntros "[Hf CLOS]".

      iMod (yes_update (m - 1) with "[$]") as "[Hay Hyes]".
      wp_pures.
      iModIntro. 
      iMod ("CLOS" with "[Hb Hay Han]") as "_".
      { iNext. iFrame. iPureIntro. by intros [=]. }
      iModIntro.

      rewrite map_union_empty. 
      simpl in *. wp_load. wp_store. wp_load. wp_pure _.
      destruct m; [lia| ].
      destruct m. 
      + rewrite bool_decide_eq_false_2; [| lia]. 
        iApply wp_atomic.

        iPoseProof "VS" as "-#V".
        clear Hnever. 
        iMod "V" as "(%m & %B & ((>%Hnever & >Bb & Hauths) & V))".
        iDestruct (bi.and_elim_r with "V") as "DEALLOC".

        rewrite if_arg2_comm. iDestruct "Hauths" as "[Hay Han]". 
        rewrite !if_arg_comm. iMod "Hay". iMod "Han".
        iDestruct (yes_agree with "Hyes Hay") as %Heq.
        
        iAssert (⌜ m= 0 /\ B = true \/ m= 1 /\ B = false ⌝)%I as %EQ.
        { iPureIntro. destruct B; [tauto| ]. 
          right. split; [| done].
          destruct m as [|[|]]; try lia. done. }
        iModIntro.

        iApply wp_pre_step. wp_pure _. 
        iApply fupd_mask_intro; [done|].
        iIntros "Hclose'".
        rewrite insert_empty.

        iSpecialize ("DEALLOC" with "[//] [Hf]").
        { iSplitL.
          { iApply has_fuels_proper; [reflexivity| | by iFrame].
            apply leibniz_equiv_iff, map_union_empty. }
          iPureIntro. set_solver. }
 
        iApply (pre_step_mono with "[-DEALLOC] [$]").
        iIntros "[MAP CORR]".
        iMod ("CORR" with "[Bb Hay Han]").
        { iNext. iFrame. iSplit; [done| ].
          destruct B; iFrame. }
        by iApply "Hk". 
      + rewrite bool_decide_eq_true_2 //; last lia.
        wp_pure _.
        iApply ("Hg" with "[] [Hf Hyes HnN] [$]"); last first.
        { iFrame "∗#". iSplit; last by iPureIntro; lia.
          by rewrite Nat2Z.inj_sub; [| lia]. }
        iPureIntro; lia.
    - have HM: m> 0 by lia.
      iModIntro.

      iApply sswp_MU_wp; [done| ].
      iApply (wp_cmpxchg_fail with "[$]"); try done.
      iIntros "!> Hb".
 
      iApply (MU_wand with "[-MU_y Hf]").
      2: { iSpecialize ("MU_y" with "[] [Hf]").
           { iPureIntro. lia. }
           2: by iFrame.
           iSplitL.
           { iApply has_fuels_proper; [reflexivity| | by iFrame].
             rewrite insert_union_singleton_l. f_equiv.
             apply leibniz_equiv_iff, fmap_empty. }
           iPureIntro. set_solver. }

      iIntros "[Hf CLOS]".
      wp_pures. iModIntro.
      iMod ("CLOS" with "[Hb Hay Han]").
      { iNext. iFrame. done. }
      iModIntro.
      rewrite map_union_empty. 
      simpl. wp_load. wp_pure _. rewrite bool_decide_eq_true_2; last lia.
      wp_pure _.
      iApply ("Hg" with "[] [Hyes HnN Hf] [$]"); last first.
      { iFrame "∗#". iPureIntro; lia. }
      iPureIntro; lia.
  Time Qed.
  
  Lemma yes_spec tid b (N: nat) f (Hf: f > 50):
    {{{ split_inv Ns__split ∗ yesno_inv b ∗ tid ↦M {[ yn_role Y := f ]} ∗ ⌜N > 0⌝ ∗ yes_at N }}}
      yes #N #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using INDEP.
    iIntros (Φ) "(#SPLIT & #Hinv & Hf & %HN & Hyes) Hk". unfold yes.
    wp_pures.
    wp_bind (Alloc _).
    iApply (wp_step_fuel with "[Hf]").
    { apply map_non_empty_singleton. }
    { rewrite has_fuels_gt_1; last by solve_fuel_positive.
      rewrite fmap_insert fmap_empty. done. }
    iApply wp_alloc. iNext. iIntros (n) "HnN _ Hf". wp_pures. iModIntro. wp_pures.
    iApply (yes_go_spec_vs with "[-Hk]"); try iFrame.
    { lia. }
    iSplit; [| done].
    iApply (yes_vs_from_invs with "[$]"). 
  Qed.

  Lemma no_go_spec tid n b (N: nat) f (Hf: f > 40):
    {{{ split_inv Ns__split ∗ yesno_inv b ∗ tid ↦M {[ yn_role No := f ]} ∗ n ↦ #N ∗ ⌜N > 0⌝ ∗ no_at N }}}
      no_go #n #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    (* iLöb as "Hg" forall (N f Hf). *)
    (* iIntros (Φ) "(#Hinv & Hf & HnN & %HN & Hno) Hk". unfold no_go, go_impl. *)
    (* wp_pures. *)
    (* wp_bind (CmpXchg _ _ _). *)
    (* assert (∀ s, Atomic s (CmpXchg #b #true #false)) by apply _. *)
    (* iApply wp_atomic. *)
    (* iInv Ns as (M B) "(>%Hnever & >HFR & >Hmod & >Bb & Hauths)" "Hclose". *)
    (* destruct B; iDestruct "Hauths" as "[>Hay >Han]"; last first. *)
    (* - iDestruct (no_agree with "Hno Han") as "%Heq". *)
    (*   destruct (decide (M = 0)) as [->|Nneq]; first lia. *)
    (*   destruct (decide (M = 1)) as [->|Nneq1]. *)
    (*   + iModIntro. *)
    (*     iApply (wp_step_model_singlerole with "Hmod Hf"). *)
    (*     { simpl. do 2 econstructor. } *)
    (*     { rewrite !yn_AM_live_roles'. simpl. set_solver. } *)
    (*     iApply (wp_cmpxchg_suc with "Bb"); [done|done|]. *)
    (*     iIntros "!> Hb Hmod Hf". *)
    (*     iMod (no_update 0 with "[$]") as "[Han Hno]". *)
    (*     wp_pures. iModIntro. *)
    (*     iMod ("Hclose" with "[Hmod Hb Hay Han HFR]"). *)
    (*     { iNext. iExists _, _. iFrame. simpl. iFrame. by iPureIntro. } *)
    (*     iModIntro. *)
    (*     simpl. wp_load. wp_store. wp_load. wp_pure _. simplify_eq. simpl. *)
    (*     iApply wp_atomic. *)
    (*     iInv Ns as (M B) "(>%Hbever' & >HFR & >Hmod & >Hb & Hauths)" "Hclose". *)
    (*     destruct B. *)
    (*     * iModIntro. *)
    (*       iApply (wp_step_fuel with "[Hf]"). *)
    (*       2: { iClear "Hg". rewrite has_fuels_gt_1; last by solve_fuel_positive. *)
    (*         rewrite fmap_insert fmap_empty. done. } *)
    (*       { set_solver. } *)
    (*       iApply sswp_pure_step; [done|]. *)
    (*       iIntros "!> Hf". *)
    (*       iDestruct "Hauths" as "[Hay Han]". iDestruct (no_agree with "Hno Han") as %Heq. *)
    (*       assert (M = 0) by lia. simplify_eq. *)
    (*       iMod (has_fuels_dealloc _ _ _ *)
    (*                               (No:fmrole the_fair_model) with "Hmod Hf") *)
    (*         as "[Hmod Hf]". *)
    (*       { by intros IN%yn_AM_live_roles. } *)
    (*       wp_pures. iModIntro. *)
    (*       iMod ("Hclose" with "[Hmod Hay Han Hb HFR]"). *)
    (*       { iNext. iExists _, _. iFrame. done. } *)
    (*       iModIntro. iApply "Hk". *)
    (*       rewrite delete_insert; [|done]. *)
    (*       iFrame. *)
    (*     * iDestruct "Hauths" as "[>Hay >Han]". iDestruct (no_agree with "Hno Han") as %Heq. *)
    (*       assert (M = 0) by lia. simplify_eq. *)
    (*   + assert (N = N) by lia. simplify_eq. *)
    (*     destruct M; first done. *)
    (*     iModIntro. *)
    (*     iApply (wp_step_model_singlerole with "Hmod Hf"). *)
    (*     { simpl. do 2 econstructor. } *)
    (*     { rewrite !yn_AM_live_roles'. simpl. *)
    (*       destruct M as [| [| ]]; try lia; done. } *)
    (*     iApply (wp_cmpxchg_suc with "Bb"); [done|done|]. *)
    (*     iIntros "!> Hb Hmod Hf". *)
    (*     iMod (no_update (M) with "[$]") as "[Han Hno]". *)
    (*     wp_pures. iModIntro. *)
    (*     iMod ("Hclose" with "[Hmod Hay Han Hb HFR]"). *)
    (*     { iNext. iExists _, _. iFrame. iSplit; [done|]. *)
    (*       iApply (own_proper with "Hay"). f_equiv. apply leibniz_equiv_iff. lia. } *)
    (*     iModIntro. simpl. wp_load. wp_store. wp_load. wp_pures. *)
    (*     destruct (decide (0 < S M - 1)) as [Heq|Heq]. *)
    (*     * rewrite bool_decide_eq_true_2 //; last lia. *)
    (*       wp_pure _. *)
    (*       iApply ("Hg" with "[] [Hno HnN Hf] [$]"); last first. *)
    (*       { iFrame "∗#". assert ((S M - 1)%Z = M)%nat as -> by lia. iFrame. iPureIntro; lia. } *)
    (*       iPureIntro; lia. *)
    (*     * rewrite bool_decide_eq_false_2 //; last lia. *)
    (*       have ->: M = 0 by lia. simpl. lia. *)
    (* - iDestruct (no_agree with "Hno Han") as "%Heq". rewrite -> Heq in *. *)
    (*   have HM: M > 0 by lia. *)
    (*   assert (M = N) by lia. simplify_eq. iModIntro. *)
    (*   iApply (wp_step_model_singlerole with "Hmod Hf"). *)
    (*   { simpl. do 2 econstructor. done. } *)
    (*   { rewrite !yn_AM_live_roles'. simpl. set_solver. } *)
    (*   iApply (wp_cmpxchg_fail with "Bb"); [done|done|]. *)
    (*   iIntros "!> Hb Hmod Hf". *)
    (*   wp_pures. *)
    (*   iModIntro. *)
    (*   iMod ("Hclose" with "[Hmod Hb Hay Han HFR]"). *)
    (*   { iNext. simplify_eq. iExists _, _. iFrame. iFrame. done. } *)
    (*   iModIntro. simpl. wp_load. wp_pure _. *)
    (*   rewrite bool_decide_eq_true_2; last lia. wp_pure _. *)
    (*   iApply ("Hg" with "[] [Hno HnN Hf] [$]"); last first. *)
    (*   { iFrame "∗#". iPureIntro; lia. } *)
    (*   iPureIntro; lia. *)
  Admitted. 

  Lemma no_spec tid b (N: nat) f (Hf: f > 50):
    {{{ split_inv Ns__split ∗ yesno_inv b ∗ tid ↦M {[ yn_role No := f ]} ∗ ⌜N > 0⌝ ∗ no_at N }}}
      no #N #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using INDEP.
    iIntros (Φ) "(#SPLIT & #Hinv & Hf & %HN & Hyes) Hk". unfold no.
    wp_pures. wp_bind (Alloc _).
    iApply (wp_step_fuel with "[Hf]").
    { apply map_non_empty_singleton. }
    { rewrite has_fuels_gt_1; last by solve_fuel_positive.
      rewrite fmap_insert fmap_empty. done. }
    iApply wp_alloc. iNext. iIntros (n) "HnN _ Hf". wp_pures. iModIntro. wp_pures.
    iApply (no_go_spec with "[-Hk]"); try iFrame.
    { lia. }
    iFrame "SPLIT Hinv". done. 
  Qed.

End proof.

Section proof_start.
  Context `(ENV_AM: EnvironmentAM env_AM).
  Context {INDEP: models_independent env_AM yn_AM}.

  Let M := the_fair_model ENV_AM.
  Let LM := the_model ENV_AM. 
  Let PM := @FM env_AM. 

  Context `{!heapGS Σ LM, !yesnoPreG Σ, SplitGS Σ env_AM yn_AM}.
  Let Ns := nroot .@ "yes_no".

  Let yn_role (ρ: YN): amRole PM := inr ρ.    

  Lemma start_spec tid (N: nat) f (Hf: f > 60):
    {{{ split_inv Ns__split ∗ frag_right_st_is (N, true) ∗ frag_free_roles_are ∅ ∗
        tid ↦M {[ yn_role Y := f; yn_role No := f ]} ∗ ⌜N > 0⌝ }}}
      start #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using All.
    iIntros (Φ) "[#SPLIT [Hst [HFR [Hf %HN]]]] Hkont". unfold start.
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
    iMod (inv_alloc Ns _ (yesno_inv_inner ENV_AM l) with "[-Hkont Hf Hyes_at Hno_at]") as "#Hinv".
    { iNext. unfold yesno_inv_inner. iExists N, true. iFrame. done. }
    iModIntro.
    wp_bind (Fork _).
    iApply (wp_role_fork _ tid _ _ _ {[yn_role No := _]} {[yn_role Y := _]}
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
    iApply (wp_role_fork _ tid _ _ _ ∅ {[yn_role No := _]} with "[Hf] [Hno_at] [Hkont]").
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
