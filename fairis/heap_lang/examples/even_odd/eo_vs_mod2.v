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
From trillium.fairness.heap_lang.examples.even_odd Require Import action_model interface utils.
Import derived_laws_later.bi.

Open Scope nat.

Set Default Proof Using "Type".


Section Models.
  
  Context {even_impl: EvenModel}. 
  Context {odd_impl: OddModel}.

  Let even_AM := @even_AM even_impl. 
  Let odd_AM := @odd_AM odd_impl. 

  Definition prodA: Type := PubA + (@ePriv even_impl + @oPriv odd_impl). 
  Definition fact_TA (pa: prodA): option (amA even_AM) * option (amA odd_AM) := 
    match pa with
    | inl s => (Some $ inl s, Some $ inl s)
    | inr (inl p) => (Some $ inr p, None)
    | inr (inr p) => (None, Some $ inr p)
    end. 

  Definition prod_model := ProdAM (fact_act := fact_TA).

  Existing Instance even_AME. 
  Existing Instance odd_AME.

  Lemma prod_AM_fin_branch': AM_fin_branch' prod_model.
  Proof. 
    unshelve eapply prod_AM_fin_branch'.
    3: apply odd_AME. 
    2: apply even_AME. 
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
    - unshelve eapply prod_AM_step_dec.
      + apply even_AME.
      + apply odd_AME. 
  Qed.

  Definition the_fair_model: FairModel.
    unshelve eapply (AM2FM prod_model). 
  Proof using even_impl odd_impl.
    apply prod_AM_strong_lr. 
  Defined.

  Definition the_model: LiveModel heap_lang the_fair_model :=
    {| lm_fl (x: fmstate the_fair_model) := 61%nat; |}.

End Models.  

(** The CMRAs we need. *)
Class evenoddPreG (Σ: gFunctors) := {
}.

Class evenoddG (Σ: gFunctors) := EvenoddG {
  even_name: gname;
  odd_name: gname;
  eoPreG :> evenoddPreG Σ;
 }.

Section proof.
  Context {even_impl: EvenModel} {odd_impl: OddModel}.
  Context `{!heapGS Σ (@the_model even_impl odd_impl), !evenoddG Σ}.
  Context {th_preG: threadPreG Σ}. 

  Existing Instance even_AME. 
  Existing Instance odd_AME.

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

  Definition evenodd_inv_inner l : iProp Σ :=
    ∃ st__e st__o N,
      frag_model_is (st__e, st__o) ∗ ⌜ cur_even _ st__e N ⌝ ∗ ⌜ cur_odd _ st__o N ⌝ ∗ 
      l ↦ #N ∗
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
   
  Let even_AM := @even_AM even_impl. 
  Let odd_AM := @odd_AM odd_impl. 

  Lemma lr_pres_even_sync ρ__e st__e st__o M st__o'
    (CUR__E : cur_even _ st__e M)
    (CUR__O : cur_odd _ st__o M)
    (E : Nat.even M = true)
    (st__e' : amSt even_AM)
    (STEP : amTrans even_AM st__e (inl (step_sync M), Some ρ__e) st__e')    
    (CUR__E' : cur_even _ st__e' (M + 1))
    (STEP2 : amTrans odd_AM st__o (inl (step_sync M), None) st__o')
    (LR__e : AM_live_roles ame_strong st__e'
          ⊆ AM_live_roles ame_strong (st__e: amSt even_AM)):
  AM_live_roles prod_AM_strong_lr (st__e', st__o')
  ⊆ AM_live_roles prod_AM_strong_lr (st__e, st__o).
  Proof.
    apply elem_of_subseteq. intros ρ.
    setoid_rewrite <- (AM_live_roles_spec prod_AM_strong_lr).
    intros (a&st''&STEP').
    simpl in STEP'.

    destruct ρ as [ρ__e' | ρ__o'].
    { (* TODO: is it possible to unify these proofs in _sync and _priv? *)
      clear -STEP' LR__e M Ns CUR__E STEP2 CUR__E' E. 

      inversion STEP'; subst.
      - (* role under consideration makes private step in new state *)        
        assert (ρ__e' ∈ AM_live_roles ame_strong (st__e: amSt even_AM)) as IN.
        { apply LR__e. apply AM_live_roles_spec. eauto. }
        apply AM_live_roles_spec in IN as (ae_ & st_ & STEP_).
        destruct ae_ as [[k]| ].
        + (* in old state it could make a _public_ step *)
          assert (k = M) as ->.
          { eapply even_sync_step_inv; eauto.
            apply STEP_. }
          do 2 eexists. simpl. eapply @pt_sync1; eauto.
          Unshelve. 2: exact (inl $ step_sync M). done.
        + do 2 eexists. eapply @pt_inner1; [| eauto].
          Unshelve. 2: exact (inr $ inl e). done.
      - destruct a1 as [[k]| ]. 
        2: { clear -LBL. destruct a; simpl in *; [set_solver| ].
             destruct s; set_solver. }
        eapply even_sync_step_inv in STEP1 as [-> ?]; eauto.
        rewrite even_plus1_negb in H. by rewrite E in H. }

    (* TODO: is it possible to unify these proofs in _sync and _priv? *)
    clear -STEP' Ns STEP2 E CUR__O.
 
    assert (ρ__o' ∈ AM_live_roles ame_strong st__o) as IN.
    { eapply odd_sync_lr_nonincr; eauto.  
      apply AM_live_roles_spec.
      inversion STEP'; eauto. }
    apply AM_live_roles_spec in IN as (ao_ & st_ & STEP_).
    destruct ao_ as [[k]| ].
    + (* in old state it could make a _public_ step *)
      eapply odd_sync_step_inv in STEP_ as [-> ?]; eauto.
      rewrite -Nat.negb_even E in H. done.
    + do 2 eexists. eapply @pt_inner2; [| eauto].
      Unshelve. 2: exact (inr $ inr o). done.
  Qed. 

  Lemma lr_pres_even_priv ρ__e st__e st__o M (st__e': amSt even_AM) (a__e : ePriv _)
  (CUR__E : cur_even _ st__e M)
  (CUR__O : cur_odd _ (st__o: amSt odd_AM) M)
  (O : Nat.odd M)
  (STEP : amTrans even_AM st__e (inr a__e, Some ρ__e) st__e')
  (CUR__E' : cur_even _ st__e' M)
  (LR__e : AM_live_roles ame_strong st__e'
      ⊆ AM_live_roles ame_strong (st__e: amSt even_AM)):
  AM_live_roles prod_AM_strong_lr (st__e', st__o)
  ⊆ AM_live_roles prod_AM_strong_lr (st__e, st__o).
  Proof. 
    assert (Nat.even M = false) as E.
    { rewrite -Nat.negb_odd. by destruct (Nat.odd M). } 
    apply elem_of_subseteq. intros ρ.
    setoid_rewrite <- (AM_live_roles_spec prod_AM_strong_lr).
    intros (a&st''&STEP').
    simpl in STEP'.

    destruct ρ as [ρ__e' | ρ__o'].
    { (* TODO: is it possible to unify these proofs in _sync and _priv? *)
      clear -STEP' LR__e Ns CUR__E CUR__E' E. 
      
      inversion STEP'; subst.
      - (* role under consideration makes private step in new state *)
        assert (ρ__e' ∈ AM_live_roles ame_strong (st__e: amSt even_AM)) as IN.
        { apply LR__e.
          apply AM_live_roles_spec. eauto. }
        apply AM_live_roles_spec in IN as (ae_ & st_ & STEP_).
        destruct ae_ as [[k]| ].
        + (* in old state it could make a _public_ step *)
          eapply even_sync_step_inv in STEP_ as [-> ?]; eauto.
          by rewrite E in H. 
        + do 2 eexists. eapply @pt_inner1; [| eauto].
           Unshelve. 2: exact (inr $ inl e). done.
      - destruct a1 as [[k]| ]. 
        2: { clear -LBL. destruct a; simpl in *; [set_solver| ].
             destruct s; set_solver. }
        eapply even_sync_step_inv in STEP1 as [-> ?]; eauto.
        by rewrite E in H. }

    (* TODO: is it possible to unify these proofs in _sync and _priv? *)
    clear -STEP' Ns CUR__O CUR__E.
    inversion STEP'; subst.
    - do 2 eexists. eapply @pt_inner2; eauto.
    - destruct a2 as [[k]| ]. 
      2: { clear -LBL. destruct a; simpl in *; [set_solver| ].
           destruct s; set_solver. }
      pose proof STEP2 as XX. eapply odd_sync_step_inv in XX as [EQ ?]; eauto. 
      edestruct (even_syncable _ M st__e) as (st__e_ & STEP1_ & ?); eauto.
      do 2 eexists. eapply @pt_sync2. 
      2, 3: eauto.
      Unshelve. 2: exact (inl (step_sync M)). simpl. subst k. done.
  Qed.

  Lemma lr_pres_odd_sync ρ__o st__e st__o st__e' st__o' M 
    (CUR__E : cur_even _ st__e M)
    (CUR__O : cur_odd _ st__o M)
    (O : Nat.odd M = true)    
    (STEP : amTrans odd_AM st__o (inl (step_sync M), Some ρ__o) st__o')    
    (CUR__O' : cur_odd _ st__o' (M + 1))
    (STEP2 : amTrans even_AM st__e (inl (step_sync M), None) st__e')
    (LR__o : AM_live_roles ame_strong st__o'
          ⊆ AM_live_roles ame_strong st__o):
  AM_live_roles prod_AM_strong_lr (st__e', st__o')
  ⊆ AM_live_roles prod_AM_strong_lr (st__e, st__o).
  Proof.
    apply elem_of_subseteq. intros ρ.
    setoid_rewrite <- (AM_live_roles_spec prod_AM_strong_lr).
    intros (a&st''&STEP').
    simpl in STEP'.

    destruct ρ as [ρ__e' | ρ__o'];
      revgoals. 
    { (* TODO: is it possible to unify these proofs in _sync and _priv? *)
      clear -STEP' LR__o M Ns CUR__O STEP2 CUR__O' O. 

      inversion STEP'; subst.
      - (* role under consideration makes private step in new state *)        
        assert (ρ__o' ∈ AM_live_roles ame_strong st__o) as IN.
        { apply LR__o. apply AM_live_roles_spec. eauto. }
        apply AM_live_roles_spec in IN as (ao_ & st_ & STEP_).
        destruct ao_ as [[k]| ].
        + (* in old state it could make a _public_ step *)
          assert (k = M) as ->.
          { eapply odd_sync_step_inv; eauto.
            apply STEP_. }
          do 2 eexists. eapply @pt_sync2; eauto.
          Unshelve. 2: exact (inl $ step_sync M). done.
        + do 2 eexists. eapply @pt_inner2; [| eauto].
          Unshelve. 2: exact (inr $ inr o). done.
      - destruct a2 as [[k]| ]. 
        2: { clear -LBL. destruct a; simpl in *; [set_solver| ].
             destruct s; set_solver. }
        eapply odd_sync_step_inv in STEP0 as [-> ?]; eauto.
        rewrite odd_plus1_negb in H. by rewrite O in H. }

    (* TODO: is it possible to unify these proofs in _sync and _priv? *)
    clear -STEP' Ns STEP2 O CUR__E.
 
    assert (ρ__e' ∈ AM_live_roles ame_strong (st__e: amSt even_AM)) as IN.
    { eapply even_sync_lr_nonincr; eauto.  
      apply AM_live_roles_spec.
      inversion STEP'; eauto. }
    apply AM_live_roles_spec in IN as (ae_ & st_ & STEP_).
    destruct ae_ as [[k]| ].
    + (* in old state it could make a _public_ step *)
      eapply even_sync_step_inv in STEP_ as [-> ?]; eauto.
      rewrite -Nat.negb_odd O in H. done.
    + do 2 eexists. eapply @pt_inner1; [| eauto].
      Unshelve. 2: exact (inr $ inl e). done.
  Qed. 

  Lemma lr_pres_odd_priv ρ__o st__e st__o (st__o': amSt odd_AM) M (a__o : oPriv _)
  (CUR__E : cur_even _ (st__e: amSt even_AM) M)
  (CUR__O : cur_odd _ st__o M)
  (E : Nat.even M)  
  (STEP : amTrans odd_AM st__o (inr a__o, Some ρ__o) st__o')
  (CUR__O' : cur_odd _ st__o' M)
  (LR__o : AM_live_roles ame_strong st__o'
      ⊆ AM_live_roles ame_strong st__o):
  AM_live_roles prod_AM_strong_lr (st__e, st__o')
  ⊆ AM_live_roles prod_AM_strong_lr (st__e, st__o).
  Proof. 
    assert (Nat.odd M = false) as O.
    { rewrite -Nat.negb_even. by destruct (Nat.even M). } 
    apply elem_of_subseteq. intros ρ.
    setoid_rewrite <- (AM_live_roles_spec prod_AM_strong_lr).
    intros (a&st''&STEP').
    simpl in STEP'.

    destruct ρ as [ρ__e' | ρ__o'];
      revgoals. 
    { (* TODO: is it possible to unify these proofs in _sync and _priv? *)
      clear -STEP' LR__o Ns CUR__O CUR__O' O.
      
      inversion STEP'; subst.
      - (* role under consideration makes private step in new state *)
        assert (ρ__o' ∈ AM_live_roles ame_strong st__o) as IN.
        { apply LR__o.
          apply AM_live_roles_spec. eauto. }
        apply AM_live_roles_spec in IN as (ao_ & st_ & STEP_).
        destruct ao_ as [[k]| ].
        + (* in old state it could make a _public_ step *)
          eapply odd_sync_step_inv in STEP_ as [-> ?]; eauto.
          by rewrite O in H. 
        + do 2 eexists. eapply @pt_inner2; [| eauto].
          Unshelve. 2: exact (inr $ inr o). done.
      - destruct a2 as [[k]| ]. 
        2: { clear -LBL. destruct a; simpl in *; [set_solver| ].
             destruct s; set_solver. }
        eapply odd_sync_step_inv in STEP2 as [-> ?]; eauto.
        by rewrite O in H. }

    (* TODO: is it possible to unify these proofs in _sync and _priv? *)
    clear -STEP' Ns CUR__O CUR__E.
    inversion STEP'; subst.
    - do 2 eexists. eapply @pt_inner1; eauto.
    - destruct a1 as [[k]| ]. 
      2: { clear -LBL. destruct a; simpl in *; [set_solver| ].
           destruct s; set_solver. }
      pose proof STEP1 as XX. eapply even_sync_step_inv in XX as [EQ ?]; eauto. 
      edestruct (odd_syncable _ M st__o) as (st__o_ & STEP2_ & ?); eauto.
      do 2 eexists. eapply @pt_sync1. 
      2, 3: eauto.
      Unshelve. 2: exact (inl (step_sync M)). simpl. subst k. done.
  Qed.

  Lemma even_spec_use tid l (N : nat) ρ f (Hf: f > 40) :
    {{{ evenodd_inv l ∗ tid ↦M {[ inl ρ := f ]} ∗ even_at N ∗
        frag_free_roles_are ∅ }}}
      (even_prog even_impl) #l #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hf & Heo & FR) Hk".
    
    iApply (@even_spec even_impl the_fair_model _ _ _ evenThreadG fst inl 
             with "[$Hf $FR $Heo]"); [lia| simpl; lia | |done].
    rewrite /even_vs. iModIntro.
    iMod (inv_acc with "Hinv") as "[OPEN CLOS]".
    { apply top_subseteq. }
  
    iDestruct "OPEN" as (st__e st__o M) "(>Hmod & >%CUR__E & >%CUR__O & >Hn & Hauths)".
    rewrite if_arg2_comm. iDestruct "Hauths" as "[E O]".
    iModIntro. iExists _, _. iSplitL "Hmod Hn E".
    { rewrite /even_corr. simpl. iFrame.
      simpl. iFrame. destruct (Nat.even M); auto. }
    simpl. 
    destruct (Nat.even M) eqn:E.
    - iSplitL.
      2: { rewrite -Nat.negb_even E. by iIntros "%foo". }
      iIntros "_ %st__t' [%STEP %CUR__E']".
      pose proof CUR__O as foo. eapply @odd_syncable in foo as (st2' & STEP2 & CUR__O').
      2: { set_solver. }      
      iExists (st__t', st2'). iSplitR.
      { iPureIntro. repeat split; auto.
        - econstructor. simpl. econstructor; eauto.
          Unshelve. 2: exact (inl (step_sync M)). done.
        - simpl. intros LR__e. eapply lr_pres_even_sync; eauto. }
      iIntros "(?&?&?&?)". iMod ("CLOS" with "[-]") as "_"; [| done].
      iNext. iFrame. simpl.
      rewrite even_plus1_negb E. simpl. iFrame. done.
    - iSplitR.
      { iIntros "%g". done. }
      iIntros "%O" (st__e') "%a__e [%STEP %CUR__E']".
      iExists (st__e', st__o). iSplitR.
      { iPureIntro. repeat split; auto.
        { econstructor. simpl. econstructor; eauto.
          Unshelve. 2: exact (inr $ inl a__e). done. }
        simpl. intros.
        eapply lr_pres_even_priv; eauto. }
      iIntros "(?&?&?&?)". iMod ("CLOS" with "[-]") as "_"; [| done].
      iNext. iFrame. simpl. 
      rewrite E. iFrame. done. 
  Qed.
  
  Lemma odd_spec_use tid l (N : nat) ρ f (Hf: f > 40) :
    {{{ evenodd_inv l ∗ tid ↦M {[ inr ρ := f ]} ∗ odd_at N ∗
        frag_free_roles_are ∅ }}}
      (odd_prog odd_impl) #l #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof. 
    iIntros (Φ) "(#Hinv & Hf & Heo & FR) Hk".
    
    iApply (@odd_spec odd_impl the_fair_model _ _ _ oddThreadG snd inr
             with "[$Hf $FR $Heo]"); [lia| simpl; lia | |done].
    rewrite /odd_vs. iModIntro.
    iMod (inv_acc with "Hinv") as "[OPEN CLOS]".
    { apply top_subseteq. }
    iDestruct "OPEN" as (st__e st__o M) "(>Hmod & >%CUR__E & >%CUR__O & >Hn & Hauths)".
    rewrite if_arg2_comm. iDestruct "Hauths" as "[E O]".
    iModIntro. iExists _, _. iSplitL "Hmod Hn O".
    { rewrite /odd_corr. simpl. iFrame.
      simpl. rewrite -Nat.negb_odd. destruct (Nat.odd M); auto. }
    simpl.
    (* rewrite !odd_plus1_negb even_plus1_negb Nat.negb_even. *)
    rewrite -Nat.negb_odd.
    destruct (Nat.odd M) eqn:E.
    - iSplitL.
      2: { simpl. by iIntros "%foo". }
      iIntros "_ %st__t' [%STEP %CUR__O']".
      pose proof CUR__E as foo. eapply @even_syncable in foo as (st1' & STEP1 & CUR__E').
      2: { set_solver. }      
      iExists (st1', st__t'). iSplitR.
      { iPureIntro. repeat split; auto.
        - econstructor. simpl.
          eapply @pt_sync2; eauto. 
          Unshelve. 2: exact (inl (step_sync M)). done.
        - simpl. intros LR__e. eapply lr_pres_odd_sync; eauto. }
      iIntros "(?&?&?&?)". iMod ("CLOS" with "[-]") as "_"; [| done].
      (* rewrite !Nat.add_0_r. *)
      iNext. iFrame. simpl. rewrite !even_plus1_negb !odd_plus1_negb -!Nat.negb_odd E.  
      simpl. iFrame. done.
    - iSplitR.
      { iIntros "%g". done. }
      iIntros "_" (st__o') "%a__o [%STEP %CUR__O']".
      iExists (st__e, st__o'). iSplitR.
      { iPureIntro. repeat split; auto.
        { econstructor. simpl. econstructor; eauto.
          Unshelve. 2: exact (inr $ inr a__o). done. }
        simpl. intros.
        eapply lr_pres_odd_priv; eauto.
        rewrite -Nat.negb_odd. by rewrite E. }
      iIntros "(?&?&?&?)". iMod ("CLOS" with "[-]") as "_"; [| done].
      iNext. iFrame. simpl.
      rewrite -!Nat.negb_odd E. simpl. iFrame. done. 
  Qed. 

  Lemma incr_loop_spec (eo : EO') tid ρ__e ρ__o n (N : nat) f (Hf: f > 40) :
    {{{ evenodd_inv n ∗ tid ↦M {[ if eo then inl ρ__e else inr ρ__o := f ]} ∗ (eo_frag eo) N ∗
        frag_free_roles_are ∅ }}}
      (if eo then even_prog even_impl else odd_prog odd_impl) #n #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hf & Heo & FR) Hk".
    destruct eo; simpl in *. 
    - iApply (even_spec_use with "[$Hf $FR $Heo]"); [lia| ..]; done.
    - iApply (odd_spec_use with "[$Hf $FR $Heo]"); [lia| ..]; done.
  Qed. 

End proof.

Section proof_start.
  Context {even_impl: EvenModel} {odd_impl: OddModel}.
  Context `{!heapGS Σ (@the_model even_impl odd_impl), !evenoddG Σ}.
  Context {th_preG: threadPreG Σ}. 
  Let Ns := nroot .@ "even_odd".

  (* TODO: move *)
  Lemma frag_free_roles_are_sep: forall fr1 fr2 (DISJ: fr1 ## fr2), 
        frag_free_roles_are (fr1 ∪ fr2) ⊣⊢ frag_free_roles_are fr1 ∗ frag_free_roles_are fr2.
  Proof.
    intros. rewrite /frag_free_roles_are /frag_free_roles_are.    
    rewrite -gset.gset_op.
    rewrite -gset.gset_disj_union; auto. 
    rewrite -own_op. by rewrite -auth_frag_op.
  Qed. 

  Let ρEven: fmrole (@the_fair_model even_impl odd_impl) := inl (ρ__e even_impl).
  Let ρOdd: fmrole (@the_fair_model even_impl odd_impl) := inr (ρ__o odd_impl).

  Definition start : val :=
    λ: "l",
      let: "x" := !"l" in
      (Fork ((even_prog even_impl) "l" "x") ;;
       Fork ((odd_prog odd_impl) "l" ("x"+#1))).

  Existing Instance even_AME. 
  Existing Instance odd_AME.

  Lemma start_spec tid n N1 N2 f (Hf: f > 60) (EVEN: N1 < N2)
    :
    {{{ evenodd_inv n ∗ 
        tid ↦M {[ ρEven := f; ρOdd := f ]} ∗
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
    iInv Ns as (st__e st__o M) "(>Hmod & >%CUR__E & >%CUR__O & >Hn & Hauths)" "Hclose".
    iIntros "!>". wp_load. iIntros "!>".
    
    rewrite if_arg2_comm !if_arg_comm.
    iDestruct "Hauths" as "[Heven Hodd]".
    iDestruct (even_agree with "Heven_at Heven") as %<-.
    iDestruct (odd_agree with "Hodd_at Hodd") as %<-.
    destruct (Nat.even M) eqn:E; [| lia].     

    iMod ("Hclose" with "[-Hf Heven_at Hodd_at HΦ HFR1 HFR2]") as "_".
    { iIntros "!>". iExists _. iFrame. 
      rewrite E. iFrame; done. }
    iIntros "!>". wp_pures. wp_bind (Fork _).
    iApply (wp_role_fork _ tid _ _ _ {[ρOdd := _]} {[ρEven := _]}
             with "[Hf ] [Heven_at HFR1]"). 
    { apply map_disjoint_dom. rewrite !dom_singleton.
      destruct (Nat.even M); set_solver. }
    { intros Hempty%map_positive_l. set_solver. }
    { rewrite has_fuels_gt_1; last solve_fuel_positive.
      rewrite !fmap_insert fmap_empty //.      
      iApply has_fuels_proper; [..| by iFrame]; auto.
      rewrite !insert_union_singleton_l map_union_empty.
      rewrite map_union_comm; [reflexivity| ].
      rewrite map_disjoint_dom. set_solver. }
    { iIntros (tid') "!> Hf".
      iApply (even_spec_use with "[-]").
      2: { iFrame "#∗". }
      { lia. }
      intuition. }

    iIntros "!> Hf".
    iIntros "!>".
    wp_pures.
    iApply (wp_role_fork _ tid _ _ _ ∅ _ with "[Hf] [Hodd_at HFR2]").
    { apply map_disjoint_dom. apply map_disjoint_dom. apply map_disjoint_empty_l. }
    2: { rewrite has_fuels_gt_1; last solve_fuel_positive.
         rewrite !fmap_insert fmap_empty //.
         rewrite insert_union_singleton_l. 
         rewrite map_union_comm; [done|].
         apply map_disjoint_dom. set_solver. }
    { rewrite map_empty_union. set_solver. }
    { iIntros (tid') "!> Hf".
      wp_pures.
      replace (Z.of_nat M + 1)%Z with (Z.of_nat (M + 1)) by lia.
      iApply (odd_spec_use with "[-]").
      2: { iFrame "#∗". }
      { lia. }
      intuition. }

    iIntros "!> Hf". by iApply "HΦ".
  Qed. 

End proof_start.
