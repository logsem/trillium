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
From trillium.fairness.heap_lang.examples.even_odd Require Import action_model threads utils.


Import derived_laws_later.bi.

Open Scope nat.

Set Default Proof Using "Type".

Definition start : val :=
  λ: "l",
    let: "x" := !"l" in
    (Fork (incr_loop "l" "x") ;;
    Fork (incr_loop "l" ("x"+#1))).


Section Models.
  
  Definition even_AM := thread_model 0. 
  Definition odd_AM := thread_model 1.

  Definition prodA: Type := PubA + (PrivA + PrivA). 
  Definition fact_TA (pa: prodA): option (amA even_AM) * option (amA odd_AM) := 
    match pa with
    | inl s => (Some $ inl s, Some $ inl s)
    | inr (inl p) => (Some $ inr p, None)
    | inr (inr p) => (None, Some $ inr p)
    end. 

  Definition prod_model := ProdAM (fact_act := fact_TA). 

  Lemma prod_AM_fin_branch': AM_fin_branch' prod_model.
  Proof. 
    unshelve eapply prod_AM_fin_branch'.  
    2, 3: apply thread_AM_fin_branch'. 
    { exact (fun '(oa1, oa2) => 
               match oa1, oa2 with
               | Some (inl pa1), Some _ => inl pa1
               | Some (inr pa1), None => inr (inl pa1)
               | None, Some (inr pa2) => inr (inr pa2)
               | _, _ => inl (step_sync 0)
               end). }
    red. intros [?|[?|?]]; reflexivity.
  Qed. 

  Lemma prod_AM_strong_lr: AM_strong_lr prod_model.
  Proof. 
    apply fin_branch_strong.
    - apply prod_AM_fin_branch'. 
    - apply prod_AM_step_dec; apply thread_AM_step_dec.
  Qed.

  Definition the_fair_model: FairModel.
    unshelve eapply (AM2FM prod_model). 
  Proof.
    apply prod_AM_strong_lr. 
  Defined.

  Definition the_model: LiveModel heap_lang the_fair_model :=
    {| lm_fl (x: fmstate the_fair_model) := 61%nat; |}.

End Models.  

(** The CMRAs we need. *)
Class evenoddPreG (Σ: gFunctors) := {
  threadPre_G :> threadPreG Σ;
  (* evenodd_PreG :> inG Σ (excl_authR natO); *)
 }.

Class evenoddG (Σ: gFunctors) := EvenoddG {
  even_name: gname;
  odd_name: gname;
  eoPreG :> evenoddPreG Σ;
 }.

(* Definition evenoddΣ : gFunctors := *)
(*   #[ heapΣ the_fair_model; GFunctor (excl_authR natO) ; GFunctor (excl_authR boolO) ]. *)

(* Global Instance subG_evenoddΣ {Σ} : subG evenoddΣ Σ → evenoddPreG Σ. *)
(* Proof. solve_inG. Qed. *)

Section proof.
  Context `{!heapGS Σ the_model, !evenoddG Σ}.

  Let Ns := nroot .@ "even_odd".

  Local Instance evenThreadG: threadG Σ := {| th_name := even_name |}. 
  Local Instance oddThreadG: threadG Σ := {| th_name := odd_name |}. 

  Definition even_at := (@th_at _ evenThreadG). 
  Definition odd_at := (@th_at _ oddThreadG). 

  Definition auth_even_at := (@auth_th_at _ evenThreadG). 
  Definition auth_odd_at := (@auth_th_at _ oddThreadG).  

  Lemma even_agree N M :
    even_at N -∗ auth_even_at M -∗ ⌜ M = N ⌝.
  Proof. apply th_agree. Qed.
  Lemma odd_agree N M :
    odd_at N -∗ auth_odd_at M -∗ ⌜ M = N ⌝.
  Proof. apply th_agree. Qed.

  Lemma even_update P N M:
     auth_even_at M ∗ even_at N ==∗ auth_even_at P ∗ even_at P.
  Proof. apply th_update. Qed.
  Lemma odd_update P N M:
     auth_odd_at M ∗ odd_at N ==∗ auth_odd_at P ∗ odd_at P.
  Proof. apply th_update. Qed.

  Definition evenodd_inv_inner n : iProp Σ :=
    ∃ N,
      frag_model_is (N, N) ∗ n ↦ #N ∗
      if Nat.even N
      then auth_even_at N ∗ auth_odd_at (N+1)
      else auth_even_at (N+1) ∗ auth_odd_at N.
  Definition evenodd_inv n := inv Ns (evenodd_inv_inner n).


  Inductive EO' := eoE | eoO.
  
  Definition eo_frag (eo: EO') : nat → iProp Σ :=
    match eo with
    | eoE => even_at
    | eoO => odd_at
    end.

  (* !!! depends on known role of thread_model *)
  Definition eo_role (eo: EO'): fmrole the_fair_model :=
    match eo with
    | eoE => inl ρT
    | eoO => inr ρT
    end.

  (* TODO: require it from thread; abstract over state type *)
  Lemma odd_syncable n (st: amSt odd_AM) (EVEN: Nat.even n):
    exists st', amTrans odd_AM st (inl (step_sync n), None) st'.
  Proof. Admitted. 
  (* TODO: require it from thread; abstract over state type *)
  Lemma even_syncable n (st: amSt even_AM) (EVEN: Nat.odd n):
    exists st', amTrans even_AM st (inl (step_sync n), None) st'.
  Proof. Admitted. 

  (* TODO: overapproximation. *)
  (* more relaxed condition would require specifying how LR of factor models
     are related to LR of the product model *)
  Lemma even_lr_nonincr (st1 st2: amSt even_AM) a ρ
    (STEP: amTrans even_AM st1 (a, ρ) st2):
    AM_live_roles (thread_AM_strong 0) st2 ⊆ AM_live_roles (thread_AM_strong 0) st1. 
  Proof. Admitted. 
  Lemma odd_lr_nonincr (st1 st2: amSt odd_AM) a ρ
    (STEP: amTrans odd_AM st1 (a, ρ) st2):
    AM_live_roles (thread_AM_strong 1) st2 ⊆ AM_live_roles (thread_AM_strong 1) st1. 
  Proof. Admitted. 
  
  Lemma tfm_live_roles' N: 
    AM_live_roles prod_AM_strong_lr (N, N) =
     set_map inl (AM_live_roles (thread_AM_strong 0) N) ∪
     set_map inr (AM_live_roles (thread_AM_strong 1) N).
  Proof.
    apply set_eq. intros ρ.
    rewrite elem_of_union. rewrite !elem_of_map. 
    setoid_rewrite <- (AM_live_roles_spec prod_AM_strong_lr).
    setoid_rewrite <- (AM_live_roles_spec (thread_AM_strong 0)).
    setoid_rewrite <- (AM_live_roles_spec (thread_AM_strong 1)).
    split.
    - intros (?&?&STEP). inversion STEP; subst.
      1, 3: by left; eexists; split; eauto. 
      all: by right; eexists; split; eauto.
    - intros [[ρ1 [-> (a1&?&STEP)]]| [ρ2 [-> (a2&?&STEP)]]].
      + simpl in a1. unfold TA in a1.
        destruct a1 as [[n]| ].
        * inversion STEP; subst. rewrite Nat.add_0_r in H3.
          edestruct (odd_syncable n n) as [st2' STEP2]; eauto.
          eexists _, (_, _). simpl.          
          eapply (@pt_sync1 _ _ _ fact_TA); eauto.
          Unshelve. 2: exact (inl (step_sync n)). done.
        * do 2 eexists. simpl. econstructor; eauto.
          Unshelve. 2: exact (inr $ inl p). done.
      + simpl in a2. unfold TA in a2.
        destruct a2 as [[n]| ].
        * inversion STEP; subst. rewrite Nat.add_1_r Nat.even_succ in H3.
          edestruct (even_syncable n n) as [st1' STEP1]; eauto.
          eexists _, (_, _). simpl.          
          eapply (@pt_sync2 _ _ _ fact_TA); eauto.
          Unshelve. 2: exact (inl (step_sync n)). done.
        * do 2 eexists. simpl. econstructor; eauto.
          Unshelve. 2: exact (inr $ inr p). done.
  Qed.

  Lemma tfm_live_roles N: 
    live_roles the_fair_model (N, N) =
     set_map inl (AM_live_roles (thread_AM_strong 0) N) ∪
     set_map inr (AM_live_roles (thread_AM_strong 1) N).
  Proof. apply tfm_live_roles'. Qed. 

  Lemma even_spec tid l (N : nat) ρ f (Hf: f > 40) :
    {{{ evenodd_inv l ∗ tid ↦M {[ inl ρ := f ]} ∗ even_at N ∗
        frag_free_roles_are ∅ }}}
      incr_loop #l #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hf & Heo & FR) Hk".
    
    iApply (@eo_go_spec 0 the_fair_model _ _ _ evenThreadG fst inl 
             with "[$Hf $FR $Heo]"); [lia| simpl; lia | |done].
    rewrite /eo_vs. iModIntro.
    iMod (inv_acc with "Hinv") as "[OPEN CLOS]".
    { apply top_subseteq. }
    iDestruct "OPEN" as (M) "(>Hmod & >Hn & Hauths)".
    rewrite if_arg2_comm. iDestruct "Hauths" as "[E O]".
    iModIntro. iExists _. iSplitL "Hmod Hn E".
    { rewrite /eo_corr. simpl. iFrame.
      simpl. iFrame. rewrite Nat.add_0_r. destruct (Nat.even M); auto. }
    simpl. rewrite Nat.add_0_r.
    destruct (Nat.even M) eqn:E.
    - iSplitL.
      2: { rewrite -Nat.negb_even E. by iIntros "%foo". }
      iIntros "_ %STEP".
      edestruct (odd_syncable M M) as [st2' STEP2]; eauto.
      (* TODO: this will be removed after abstracting threads states
             and requiring them to agree on N *)      
      assert (st2' = M + 1) by admit. subst st2'. 
      iExists ((M + 1), (M + 1)). rewrite !bi.sep_assoc. iSplitR.
      { iPureIntro. repeat split; auto.
        - econstructor. simpl. econstructor; eauto.
          Unshelve. 2: exact (inl (step_sync M)). done.
        - rewrite !tfm_live_roles'.
          apply union_mono.
          + apply set_map_mono; [done| ].
            eapply even_lr_nonincr; eauto.
          + apply set_map_mono; [done| ].
            eapply odd_lr_nonincr; eauto. }
      iIntros "(?&?&?)". iMod ("CLOS" with "[-]") as "_"; [| done].
      iNext. iFrame. simpl. 
      rewrite !Nat.add_0_r.
      rewrite even_plus1_negb E. simpl. iFrame.
    - iSplitR.
      { by iIntros "%?". }
      iIntros "%O" (a) "%STEP1".
      iExists (M, M). rewrite !bi.sep_assoc. iSplitR.
      { iPureIntro. repeat split; auto.
        econstructor. simpl. econstructor; eauto.
        Unshelve. 2: exact (inr $ inl a). done. }
      iIntros "(?&?&?)". iMod ("CLOS" with "[-]") as "_"; [| done].
      iNext. iFrame. simpl. 
      rewrite !Nat.add_0_r. rewrite E. iFrame.
  Admitted. 
  
  Lemma odd_spec tid l (N : nat) ρ f (Hf: f > 40) :
    {{{ evenodd_inv l ∗ tid ↦M {[ inr ρ := f ]} ∗ odd_at N ∗
        frag_free_roles_are ∅ }}}
      incr_loop #l #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof. Admitted. 

  Lemma incr_loop_spec (eo : EO') tid ρ__e ρ__o n (N : nat) f (Hf: f > 40) :
    {{{ evenodd_inv n ∗ tid ↦M {[ if eo then inl ρ__e else inr ρ__o := f ]} ∗ (eo_frag eo) N ∗
        frag_free_roles_are ∅ }}}
      incr_loop #n #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hf & Heo & FR) Hk".
    destruct eo; simpl in *. 
    - iApply (even_spec with "[$Hf $FR $Heo]"); [lia| ..]; done.
    - iApply (odd_spec with "[$Hf $FR $Heo]"); [lia| ..]; done.
  Qed. 

End proof.

Section proof_start.
  Context `{!heapGS Σ the_model, !evenoddG Σ}.
  Let Ns := nroot .@ "even_odd".

  (* Local Instance evenThreadG: threadG Σ := {| th_name := even_name |}.  *)
  (* Local Instance oddThreadG: threadG Σ := {| th_name := odd_name |}.  *)

  Lemma frag_free_roles_are_sep: forall fr1 fr2 (DISJ: fr1 ## fr2), 
        frag_free_roles_are (fr1 ∪ fr2) ⊣⊢ frag_free_roles_are fr1 ∗ frag_free_roles_are fr2.
  Proof.
    intros. rewrite /frag_free_roles_are /frag_free_roles_are.    
    rewrite -gset.gset_op.
    rewrite -gset.gset_disj_union; auto. 
    rewrite -own_op. by rewrite -auth_frag_op.
  Qed. 

  Let ρEven: fmrole the_fair_model := inl ρT.
  Let ρOdd: fmrole the_fair_model := inr ρT.

  Lemma start_spec tid n N1 N2 f (Hf: f > 60) :
    {{{ evenodd_inv n ∗ tid ↦M {[ inl ρT := f; inr ρT := f ]} ∗
        even_at N1 ∗ odd_at N2 ∗ frag_free_roles_are ∅ }}}
      start #n @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using All.
    iIntros (Φ) "(#Hinv & Hf & Heven_at & Hodd_at & HFR) HΦ". unfold start.
    rewrite <- (union_empty_l_L ∅). 
    iDestruct (frag_free_roles_are_sep with "HFR") as "[HFR1 HFR2]"; [set_solver| ].
    wp_pures.
    wp_bind (Load _).
    iApply wp_atomic.
    iInv Ns as (M) "(>Hmod & >Hn & Hauths)" "Hclose".
    iIntros "!>". wp_load. iIntros "!>".
    
    rewrite if_arg2_comm !if_arg_comm.
    iDestruct "Hauths" as "[Heven Hodd]".
    iDestruct (even_agree with "Heven_at Heven") as %<-.
    iDestruct (odd_agree with "Hodd_at Hodd") as %<-.

    iAssert ((if Nat.even M then auth_even_at else auth_odd_at) M ∗
             (if Nat.even M then auth_odd_at else auth_even_at) (M + 1))%I
      with "[Heven Hodd] "as "[CUR_AUTH NEXT_AUTH]".
    { destruct (Nat.even M); iFrame. }

    iAssert ((if Nat.even M then even_at else odd_at) M ∗
             (if Nat.even M then odd_at else even_at) (M + 1))%I
      with "[Heven_at Hodd_at] "as "[CUR NEXT]".
    { destruct (Nat.even M); iFrame. }

    iMod ("Hclose" with "[-Hf CUR NEXT HΦ HFR1 HFR2]") as "_".
    { iIntros "!>". iExists _. iFrame.
      destruct (Nat.even M); iFrame. }
    iIntros "!>". wp_pures. wp_bind (Fork _).
    iApply (wp_role_fork _ tid _ _ _ {[if Nat.even M then ρOdd else ρEven := _]}
                         {[if Nat.even M then ρEven else ρOdd := _]}
             with "[Hf ] [CUR HFR1]"). 
    { apply map_disjoint_dom. rewrite !dom_singleton.
      destruct (Nat.even M); set_solver. }
    { intros Hempty%map_positive_l. set_solver. }
    { rewrite has_fuels_gt_1; last solve_fuel_positive.
      rewrite !fmap_insert fmap_empty //.      
      iApply has_fuels_proper; [..| by iFrame]; auto.
      rewrite !insert_union_singleton_l map_union_empty.
      destruct (Nat.even M); try reflexivity.
      f_equiv. rewrite map_union_comm; auto. apply map_disjoint_dom. set_solver. }
    { iIntros (tid') "!> Hf".
      iApply (incr_loop_spec (if Nat.even M then eoE else eoO) with "[-]").
      2: { destruct (Nat.even M); iFrame "#∗". }
      { lia. }
      intuition. }

    iIntros "!> Hf".
    iIntros "!>".
    wp_pures.
    iApply (wp_role_fork _ tid _ _ _ ∅ _ with "[Hf] [NEXT HFR2]").
    { apply map_disjoint_dom. apply map_disjoint_dom. apply map_disjoint_empty_l. }
    2: { rewrite has_fuels_gt_1; last solve_fuel_positive.
         rewrite !fmap_insert fmap_empty //.
         rewrite insert_union_singleton_l. 
         rewrite map_union_comm; [done|].
         apply map_disjoint_dom. set_solver. }
    { rewrite map_empty_union. destruct (Nat.even M); set_solver. }
    { iIntros (tid') "!> Hf".
      wp_pures.
      replace (Z.of_nat M + 1)%Z with (Z.of_nat (M + 1)) by lia.
      iApply (incr_loop_spec (if Nat.even M then eoO else eoE) with "[-]").
      2: { destruct (Nat.even M); iFrame "#∗". }
      { lia. }
      intuition. }

    iIntros "!> Hf". by iApply "HΦ".
  Qed.

End proof_start.
