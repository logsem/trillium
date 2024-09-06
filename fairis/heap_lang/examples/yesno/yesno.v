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

Import derived_laws_later.bi.

Section SplitModel.
  Let factor_repr (AM: ActionModel) := optionUR $ exclR $ leibnizO (amSt AM).

  Let split_cmra (AM1 AM2: ActionModel) := (authUR $ prodUR (factor_repr AM1) (factor_repr AM2)). 
  Definition SplitΣ (AM1 AM2: ActionModel) : gFunctors :=
    #[GFunctor (split_cmra AM1 AM2)].

  Class SplitPreGS Σ (AM1 AM2: ActionModel) := {
      spre_in :> inG Σ (split_cmra AM1 AM2);
  }.

  Class SplitGS Σ (AM1 AM2: ActionModel) := {
      spre :> SplitPreGS Σ AM1 AM2;
      γ__split: gname;
  }.

  Lemma split_init `{SplitPreGS Σ AM1 AM2} st1 st2:
    ⊢ |==> ∃ γ, own γ (● (Excl' st1, Excl' st2)) ∗
           own γ (◯ (Excl' st1, None)) ∗ own γ (◯ (None, Excl' st2)).
  Proof. 
    iMod (own_alloc (● (Excl' st1, Excl' st2) ⋅ ◯ _)) as (γ) "[AUTH FRAG]".
    { by apply auth_both_valid_2. }
    iFrame. rewrite -own_op -auth_frag_op -pair_op. by iFrame.
  Qed. 

  Context {AM1 AM2: ActionModel}.
  Context `{SplitGS Σ AM1 AM2}.

  Let PM := ProdAM AM1 AM2.
  Context `{AM_strong_lr PM}.
  Let M := AM2FM PM _. 

  Context {LM: LiveModel heap_lang M}. 
  
  Context {hGS: heapGS Σ LM}. 

  Definition frag_left_st_is (st: amSt AM1): iProp Σ :=
    own γ__split (◯ ((Excl' st, None): prodUR (factor_repr AM1) _)). 
  Definition frag_right_st_is (st: amSt AM2): iProp Σ :=
    own γ__split (◯ ((None, Excl' st): prodUR _ (factor_repr AM2))). 
  Definition auth_prod_st_is st1 st2: iProp Σ :=
    own γ__split (● ((Excl' st1, Excl' st2): prodUR _ (factor_repr AM2))). 

  Lemma update_left (δ δ1 δ2: amSt AM1) (δ': amSt AM2):
    auth_prod_st_is δ1 δ' -∗ frag_left_st_is δ2 ==∗ auth_prod_st_is δ δ' ∗ frag_left_st_is δ.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    iMod (own_update with "H") as "[??]"; eauto.
    2: { rewrite bi.sep_comm. by iFrame. } 
    simpl. apply auth_update.
    eapply @prod_local_update_1.
    eapply @option_local_update.
    by apply (exclusive_local_update _ ((Excl δ): exclR $ leibnizO (amSt AM1))).
  Qed.

  Lemma left_agree s1 s2 s':
    auth_prod_st_is s1 s' -∗ frag_left_st_is s2 -∗ ⌜ s1 = s2 ⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %[SUB ?]%auth_both_valid_discrete.
    apply pair_included in SUB as [SUB _]. simpl in SUB.
    by apply @Excl_included, leibniz_equiv in SUB.
  Qed.

  Lemma update_right (δ δ1 δ2: amSt AM2) (δ': amSt AM1):
    auth_prod_st_is δ' δ1 -∗ frag_right_st_is δ2 ==∗ auth_prod_st_is δ' δ ∗ frag_right_st_is δ.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    iMod (own_update with "H") as "[??]"; eauto.
    2: { rewrite bi.sep_comm. by iFrame. } 
    simpl. apply auth_update.
    eapply @prod_local_update_2.
    eapply @option_local_update.
    by apply (exclusive_local_update _ ((Excl δ): exclR $ leibnizO (amSt AM2))).
  Qed.

  Lemma right_agree s1 s2 s':
    auth_prod_st_is s' s1 -∗ frag_right_st_is s2 -∗ ⌜ s1 = s2 ⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %[SUB ?]%auth_both_valid_discrete.
    apply pair_included in SUB as [_ SUB]. simpl in SUB.
    by apply @Excl_included, leibniz_equiv in SUB.
  Qed.

  Definition split_inv_inner: iProp Σ :=
    ∃ st__G, frag_model_is st__G ∗ auth_prod_st_is st__G.1 st__G.2. 

  Definition split_inv Ns := inv Ns split_inv_inner.

End SplitModel.

Class EnvironmentAM (env_AM: ActionModel) := {
    (* eam_role_eqdec :> EqDecision (amRole env_AM); *)
    (* eam_role_cnt :> Countable (amRole env_AM); *)
    eam_st_eqdec :> EqDecision (amSt env_AM);
    eam_st_inh :> Inhabited (amSt env_AM);
    eam_env_fb :> AM_fin_branch' env_AM;
    eam_act_dec :> ∀ a, Decision (is_action_of env_AM a);
    eam_step_dec :> AM_step_dec env_AM;
  }.
Existing Instance eam_env_fb.
Existing Instance eam_step_dec. 


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

  Definition yesno_inv_inner b : iProp Σ :=
    ∃ n B, 
      ⌜(n, B) ≠ (0, false)⌝ ∗
      frag_free_roles_are ∅ ∗
      (* frag_model_is (n, B) ∗ *)
      frag_right_st_is (n, B) ∗
      b ↦ #B ∗
      if B
      then auth_yes_at n ∗ auth_no_at n
      else auth_yes_at (n-1) ∗ auth_no_at n.
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
    iInv Ns as (m B) "(>%Hnever & >HFR & >Hmod & >Bb & Hauths)" "Hclose".
    iInv Ns__split as ([e ?]) "(>ST & >PROD)" "Hclose'".
    simpl. 
    iDestruct (right_agree with "PROD Hmod") as %->.

    rewrite if_arg2_comm. iDestruct "Hauths" as "[Hay Han]". 
    rewrite !if_arg_comm. iMod "Hay". iMod "Han".
    iDestruct (yes_agree with "Hyes Hay") as %Heq.

    destruct B. 
    - destruct (decide (m= 0)) as [->|Nneq]; first lia.
      destruct (decide (m= 1)) as [->|Nneq1].
      + iModIntro.
        assert (amTrans yn_AM (1, true) (yn_act, Some Y) (1, false)) as STEP.
        { econstructor. lia. } 
        iApply (wp_step_model_singlerole with "ST Hf").
        { simpl. do 2 econstructor; eauto.
          intros ?. apply action_of_step in STEP. 
          edestruct INDEP; eauto. }
        { simpl. erewrite !prod_indep_live_roles; try by apply INDEP.
          rewrite !yn_AM_live_roles'. simpl. set_solver. }
        iApply (wp_cmpxchg_suc with "Bb"); [done|done|].
        iIntros "!> Hb ST Hf".
        iMod (yes_update 0 with "[$]") as "[Hay Hyes]".
        iMod (update_right ((1, false): amSt yn_AM) with "[$] [$]") as "[PROD Hmod]".
        wp_pures.
        iModIntro. 
        iMod ("Hclose'" with "[PROD ST]").
        { iFrame. }
        iMod ("Hclose" with "[Hmod Hb Hay Han HFR]").
        { iNext. iExists _, _. iFrame. simpl. iFrame. by iPureIntro. }
        iModIntro. 

        simpl in *. wp_load. wp_store. wp_load. wp_pure _. simplify_eq. simpl.
        iApply wp_atomic.
        iInv Ns as (m B) "(>%Hbever' & >HFR & >Hmod & >Hb & Hauths)" "Hclose".
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

        iApply (wp_step_fuel with "[Hf]").
        2: { iClear "Hg". rewrite has_fuels_gt_1; last by solve_fuel_positive.
             rewrite fmap_insert fmap_empty. done. }
        { set_solver. }
        
        iApply sswp_pure_step; [done|].
        iIntros "!> Hf". iApply wp_pre_step. wp_pures.
        iApply fupd_mask_intro; [done|].
        iIntros "Hclose'".          
        iMod (has_fuels_dealloc _ _ _ (yn_role Y: fmrole M)
               with "ST Hf") as "[ST Hf]".
        { simpl. rewrite prod_indep_live_roles. apply not_elem_of_union.
          split; [set_solver| ]. 
          intros IN%elem_of_map_inj_gset; [| by apply _]. 
          rewrite yn_AM_live_roles in IN.
          destruct EQ as [[-> ->]|[-> ->]]; set_solver. }
        iModIntro.
        iMod ("Hclose_" with "[PROD ST]").
        { iFrame. }
        iMod ("Hclose" with "[Hmod Hay Han Hb HFR]").
        { iNext. iExists _, _. iFrame.
          destruct EQ as [[-> ->]|[-> ->]]; iFrame; done. }
        iModIntro. iApply "Hk".
        rewrite delete_insert; [|set_solver].
        iFrame "Hf".
      + subst N. simplify_eq.
        iModIntro. 
        assert (amTrans yn_AM (m, true) (yn_act, Some Y) (m, false)) as STEP.
        { by econstructor. } 

        iApply (wp_step_model_singlerole with "ST Hf").
        { simpl. do 2 econstructor; eauto.
          intros ?. apply action_of_step in STEP. 
          edestruct INDEP; eauto. }
        { simpl. erewrite !prod_indep_live_roles; try by apply INDEP.
          rewrite !yn_AM_live_roles'. simpl. 
          destruct m; [set_solver | destruct m; set_solver]. }
        iApply (wp_cmpxchg_suc with "Bb"); [done|done|].
        iIntros "!> Hb ST Hf".
        iMod (yes_update (m-1) with "[$]") as "[Hay Hyes]".
        wp_pures. iModIntro.
        iMod (update_right ((m, false): amSt yn_AM) with "[$] [$]") as "[PROD Hmod]". 
        iMod ("Hclose'" with "[PROD ST]").
        { iFrame. }
        iMod ("Hclose" with "[Hmod Hay Han Hb HFR]").
        { iNext. iExists _, _. iFrame. iPureIntro. intro contra. simplify_eq. }
        iModIntro.
        simpl. wp_load. wp_store. wp_load. wp_pures.
        rewrite bool_decide_eq_true_2 //; last lia.
        wp_pure _.
        iApply ("Hg" with "[] [Hyes HnN Hf] [$]"); last first.
        { iFrame "∗#". iSplit; last by iPureIntro; lia.
          by rewrite Nat2Z.inj_sub; [| lia]. }
        iPureIntro; lia.
    - have HM: m> 0 by lia.
      iModIntro.
      
      assert (amTrans yn_AM (m, false) (yn_act, Some Y) (m, false)) as STEP.
      { econstructor. lia. } 

      iApply (wp_step_model_singlerole with "ST Hf").
      { simpl. do 2 econstructor; eauto.
        intros ?. apply action_of_step in STEP. 
        edestruct INDEP; eauto. }
      { set_solver. }
      iApply (wp_cmpxchg_fail with "Bb"); [done|done|].
      iIntros "!> Hb ST Hf".
      wp_pures. iModIntro.
      iMod ("Hclose'" with "[ST PROD]").
      { iFrame. simpl. iFrame. }
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
    iApply (yes_go_spec with "[-Hk]"); try iFrame.
    { lia. }
    iFrame "SPLIT Hinv". iPureIntro; lia. 
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
