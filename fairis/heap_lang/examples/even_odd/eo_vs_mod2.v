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
From trillium.fairness.heap_lang.examples.even_odd Require Import action_model (* threads *) utils.


Import derived_laws_later.bi.

Open Scope nat.

Set Default Proof Using "Type".

Inductive PubA := step_sync (k: nat).

Global Instance PubA_EqDec: EqDecision PubA.
Proof.
  intros [x] [y]. destruct (decide (x = y)); [left | right]; set_solver.
Qed. 

Class threadG Σ := ThreadG {
  th_name: gname;
  th_n_G :> inG Σ (excl_authR natO);
}.

Class threadPreG Σ := {
  thread_PreG :> inG Σ (excl_authR natO);
}.

Section ThreadGLemmas.
  Context `{!threadG Σ}.

  Definition th_at (n: nat) := own th_name (◯E n).
  Definition auth_th_at (n: nat) := own th_name (●E n).
  
  Lemma th_agree γ (N M: nat) :
    own γ (◯E N) -∗ own γ (●E M) -∗ ⌜ M = N ⌝.
  Proof.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.
  
  Lemma th_update γ (N M P: nat) :
    own γ (●E N) ∗ own γ (◯E M) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.

End ThreadGLemmas.

Definition BuildSubModel (St Priv Role: Type) Trans := {|
   amSt := St;
   amA := PubA + Priv;
   amRole := Role;
   amTrans := Trans;
|}.


Record EvenModel := {
    eSt: Type;
    ePriv: Type;
    eRole: Type;
    eTrans;
    even_role_eqdec :> EqDecision eRole;
    even_role_cnt :> Countable eRole;
    even_st_eqdec :> EqDecision eSt;
    even_st_inh :> Inhabited eSt;
    even_role_inh :> Inhabited eRole;

    cur_even: eSt -> nat -> Prop;

    even_AM := BuildSubModel eSt ePriv eRole eTrans;
    even_AM_strong: AM_strong_lr even_AM;
    even_AM_fin_branch': AM_fin_branch' even_AM;
    even_AM_step_dec: AM_step_dec even_AM;

    even_syncable n st (EVEN: Nat.odd n) (CUR: cur_even st n):
      exists st', amTrans even_AM st (inl (step_sync n), None) st' /\ cur_even st' (n + 1);
    even_sync_step_inv st__e st__e' k N ρ
      (STEP: amTrans even_AM st__e (inl (step_sync k), Some ρ) st__e')
      (CUR: cur_even st__e N):
      k = N /\ Nat.even N;
    even_sync_lr_nonincr st__e st__e' M
      (STEP: amTrans even_AM st__e (inl (step_sync M), None) st__e'):
      AM_live_roles even_AM_strong st__e' ⊆ AM_live_roles even_AM_strong st__e;
}.

Record OddModel := {
    oSt: Type;
    oPriv: Type;
    oRole: Type;
    oTrans;
    odd_role_eqdec :> EqDecision oRole;
    odd_role_cnt :> Countable oRole;
    odd_st_eqdec :> EqDecision oSt;
    odd_st_inh :> Inhabited oSt;
    odd_role_inh :> Inhabited oRole;

    cur_odd: oSt -> nat -> Prop;

    odd_AM := BuildSubModel oSt oPriv oRole oTrans;
    odd_AM_strong: AM_strong_lr odd_AM;
    odd_AM_fin_branch': AM_fin_branch' odd_AM;
    odd_AM_step_dec: AM_step_dec odd_AM;

    odd_syncable n st (ODD: Nat.even n) (CUR: cur_odd st n):
      exists st', amTrans odd_AM st (inl (step_sync n), None) st' /\ cur_odd st' (n + 1);
    odd_sync_step_inv st__e st__e' k N ρ
      (STEP: amTrans odd_AM st__e (inl (step_sync k), Some ρ) st__e')
      (CUR: cur_odd st__e N):
      k = N /\ Nat.odd N;
    odd_sync_lr_nonincr st__e st__e' M
      (STEP: amTrans odd_AM st__e (inl (step_sync M), None) st__e'):
      AM_live_roles odd_AM_strong st__e' ⊆ AM_live_roles odd_AM_strong st__e;
}.

(* Arguments ePriv {_}. *)
(* Arguments oPriv {_}. *)


Section Models.
  
  Context (even_impl: EvenModel). 
  Context (odd_impl: OddModel).

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

  Lemma prod_AM_fin_branch': AM_fin_branch' prod_model.
  Proof. 
    unshelve eapply prod_AM_fin_branch'.
    3: apply odd_AM_fin_branch'. 
    2: apply even_AM_fin_branch'. 
    { exact (fun '(oa1, oa2) => 
               match oa1, oa2 with
               | Some (inl pa1), Some _ => inl pa1
               | Some (inr pa1), None => inr (inl pa1)
               | None, Some (inr pa2) => inr (inr pa2)
               | _, _ => inl (step_sync 0)
               end). }
    red. intros [?|[?|?]]; reflexivity.
  Qed.

  Local Instance prod_role_eqdec: EqDecision (amRole prod_model).
  Proof.
    unshelve eapply sum_eq_dec.
    - simpl. apply even_impl.
    - simpl. apply odd_impl.
  Defined. 
    
  Local Instance prod_role_cnt: Countable (amRole prod_model).
  Proof.
    unshelve eapply sum_countable.
    - simpl. apply even_impl.
    - simpl. apply odd_impl.
  Defined.

  (* TODO: how to get rid of this? *)
  Local Instance even_st_eqdec': EqDecision (amSt even_AM) := even_st_eqdec even_impl.
  Local Instance odd_st_eqdec': EqDecision (amSt odd_AM) := odd_st_eqdec odd_impl.
  Local Instance even_st_inh': Inhabited (amSt even_AM) := even_st_inh even_impl.
  Local Instance odd_st_inh': Inhabited (amSt odd_AM) := odd_st_inh odd_impl.
  Local Instance even_role_inh': Inhabited (amRole even_AM) := even_role_inh even_impl. 
  Local Instance odd_role_inh': Inhabited (amRole odd_AM) := odd_role_inh odd_impl.

  Lemma prod_AM_strong_lr: AM_strong_lr prod_model.
  Proof. 
    apply fin_branch_strong.
    - apply prod_AM_fin_branch'. 
    - unshelve eapply prod_AM_step_dec.
      + apply even_AM_step_dec.
      + apply odd_AM_step_dec.
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
  threadPre_G :> threadPreG Σ;
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
  Context (even_impl: EvenModel) (odd_impl: OddModel).
  Context `{!heapGS Σ (the_model even_impl odd_impl), !evenoddG Σ}.

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

  (* Lemma tfm_live_roles' N st__e st__o (CUR__e: cur_n 0 st__e N) (CUR__o: cur_n 1 st__o N):  *)
  (*   AM_live_roles prod_AM_strong_lr (st__e, st__o) = *)
  (*    set_map inl (AM_live_roles (thread_AM_strong 0) st__e) ∪ *)
  (*    set_map inr (AM_live_roles (thread_AM_strong 1) st__o). *)
  (* Proof. *)
  (*   apply set_eq. intros ρ. *)
  (*   rewrite elem_of_union. rewrite !elem_of_map.  *)
  (*   setoid_rewrite <- (AM_live_roles_spec prod_AM_strong_lr). *)
  (*   setoid_rewrite <- (AM_live_roles_spec (thread_AM_strong 0)). *)
  (*   setoid_rewrite <- (AM_live_roles_spec (thread_AM_strong 1)). *)
  (*   split. *)
  (*   - intros (?&?&STEP). inversion STEP; subst. *)
  (*     1, 3: by left; eexists; split; eauto.  *)
  (*     all: by right; eexists; split; eauto. *)
  (*   - intros [[ρ1 [-> (a1&?&STEP)]]| [ρ2 [-> (a2&?&STEP)]]]. *)
  (*     + simpl in a1. *)
  (*       destruct a1 as [[n]| ]. *)
  (*       * *)
  (*         (* inversion STEP; subst. *) *)
  (*         rewrite Nat.add_0_r in H3. *)
  (*         edestruct (odd_syncable n n) as [st2' STEP2]; eauto. *)
  (*         eexists _, (_, _). simpl.           *)
  (*         eapply (@pt_sync1 _ _ _ fact_TA); eauto. *)
  (*         2: { apply STEP2.  *)
  (*         Unshelve. 2: exact (inl (step_sync n)). done. *)
  (*       * do 2 eexists. simpl. econstructor; eauto. *)
  (*         Unshelve. 2: exact (inr $ inl p). done. *)
  (*     + simpl in a2. unfold TA in a2. *)
  (*       destruct a2 as [[n]| ]. *)
  (*       * inversion STEP; subst. rewrite Nat.add_1_r Nat.even_succ in H3. *)
  (*         edestruct (even_syncable n n) as [st1' STEP1]; eauto. *)
  (*         eexists _, (_, _). simpl.           *)
  (*         eapply (@pt_sync2 _ _ _ fact_TA); eauto. *)
  (*         Unshelve. 2: exact (inl (step_sync n)). done. *)
  (*       * do 2 eexists. simpl. econstructor; eauto. *)
  (*         Unshelve. 2: exact (inr $ inr p). done. *)
  (* Qed. *)

  (* (* TODO: require it from thread *) *)
  (* Lemma odd_syncable n (st: amSt odd_AM) *)
  (*   (EVEN: Nat.even n) (CUR: cur_n 1 st n): *)
  (*   exists st', amTrans odd_AM st (inl (step_sync n), None) st' /\ cur_n 1 st' (n + 1). *)
  (* Proof. Admitted.  *)
  (* (* TODO: require it from thread *) *)
  (* Lemma even_syncable n (st: amSt even_AM) *)
  (*   (EVEN: Nat.odd n) (CUR: cur_n 0 st n): *)
  (*   exists st', amTrans even_AM st (inl (step_sync n), None) st' /\ cur_n 0 st' (n + 1). *)
  (* Proof. Admitted.  *)

  (* Lemma even_sync_step_inv st__e st__e' k N ρ *)
  (*   (STEP: amTrans even_AM st__e (inl (step_sync k), Some ρ) st__e') *)
  (*   (CUR: cur_n 0 st__e N): *)
  (*   k = N /\ Nat.even N. *)
  (* Proof using. Admitted.      *)
  (* Lemma odd_sync_step_inv st__e st__e' k N ρ *)
  (*   (STEP: amTrans odd_AM st__e (inl (step_sync k), Some ρ) st__e') *)
  (*   (CUR: cur_n 1 st__e N): *)
  (*   k = N /\ Nat.odd N. *)
  (* Proof using. Admitted. *)

  (* Lemma odd_sync_lr_nonincr st__o st__o' M *)
  (*   (STEP: amTrans odd_AM st__o (inl (step_sync M), None) st__o'): *)
  (*   AM_live_roles (thread_AM_strong 1) st__o' ⊆ AM_live_roles (thread_AM_strong 1) st__o. *)
  (* Proof. Admitted.  *)
  (* Lemma even_sync_lr_nonincr st__e st__e' M *)
  (*   (STEP: amTrans even_AM st__e (inl (step_sync M), None) st__e'): *)
  (*   AM_live_roles (thread_AM_strong 0) st__e' ⊆ AM_live_roles (thread_AM_strong 0) st__e. *)
  (* Proof. Admitted.  *)
   
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
    (LR__e : AM_live_roles (even_AM_strong _) st__e'
          ⊆ AM_live_roles (even_AM_strong _) st__e):
  AM_live_roles (prod_AM_strong_lr _ _) (st__e', st__o')
  ⊆ AM_live_roles (prod_AM_strong_lr _ _) (st__e, st__o).
  Proof.
    apply elem_of_subseteq. intros ρ.
    setoid_rewrite <- (AM_live_roles_spec (prod_AM_strong_lr _ _)).
    intros (a&st''&STEP').
    simpl in STEP'.

    destruct ρ as [ρ__e' | ρ__o'].
    { (* TODO: is it possible to unify these proofs in _sync and _priv? *)
      clear -STEP' LR__e M Ns CUR__E STEP2 CUR__E' E. 

      inversion STEP'; subst.
      - (* role under consideration makes private step in new state *)        
        assert (ρ__e' ∈ AM_live_roles (even_AM_strong _) st__e) as IN.
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
 
    assert (ρ__o' ∈ AM_live_roles (odd_AM_strong _) st__o) as IN.
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
  (CUR__O : cur_odd _ st__o M)
  (O : Nat.odd M)
  (STEP : amTrans even_AM st__e (inr a__e, Some ρ__e) st__e')
  (CUR__E' : cur_even _ st__e' M)
  (LR__e : AM_live_roles (even_AM_strong _) st__e'
      ⊆ AM_live_roles (even_AM_strong _) st__e):
  AM_live_roles (prod_AM_strong_lr _ _) (st__e', st__o)
  ⊆ AM_live_roles (prod_AM_strong_lr _ odd_impl) (st__e, st__o).
  Proof. 
    assert (Nat.even M = false) as E.
    { rewrite -Nat.negb_odd. by destruct (Nat.odd M). } 
    apply elem_of_subseteq. intros ρ.
    setoid_rewrite <- (AM_live_roles_spec (prod_AM_strong_lr _ _)).
    intros (a&st''&STEP').
    simpl in STEP'.

    destruct ρ as [ρ__e' | ρ__o'].
    { (* TODO: is it possible to unify these proofs in _sync and _priv? *)
      clear -STEP' LR__e Ns CUR__E CUR__E' E. 
      
      inversion STEP'; subst.
      - (* role under consideration makes private step in new state *)
        assert (ρ__e' ∈ AM_live_roles (even_AM_strong _) st__e) as IN.
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
    (LR__o : AM_live_roles (odd_AM_strong _) st__o'
          ⊆ AM_live_roles (odd_AM_strong _) st__o):
  AM_live_roles (prod_AM_strong_lr _ _) (st__e', st__o')
  ⊆ AM_live_roles (prod_AM_strong_lr _ _) (st__e, st__o).
  Proof.
    apply elem_of_subseteq. intros ρ.
    setoid_rewrite <- (AM_live_roles_spec (prod_AM_strong_lr _ _)).
    intros (a&st''&STEP').
    simpl in STEP'.

    destruct ρ as [ρ__e' | ρ__o'];
      revgoals. 
    { (* TODO: is it possible to unify these proofs in _sync and _priv? *)
      clear -STEP' LR__o M Ns CUR__O STEP2 CUR__O' O. 

      inversion STEP'; subst.
      - (* role under consideration makes private step in new state *)        
        assert (ρ__o' ∈ AM_live_roles (odd_AM_strong _) st__o) as IN.
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
 
    assert (ρ__e' ∈ AM_live_roles (even_AM_strong _) st__e) as IN.
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
  (CUR__E : cur_even _ st__e M)
  (CUR__O : cur_odd _ st__o M)
  (E : Nat.even M)  
  (STEP : amTrans odd_AM st__o (inr a__o, Some ρ__o) st__o')
  (CUR__O' : cur_odd _ st__o' M)
  (LR__o : AM_live_roles (odd_AM_strong _) st__o'
      ⊆ AM_live_roles (odd_AM_strong _) st__o):
  AM_live_roles (prod_AM_strong_lr _ _) (st__e, st__o')
  ⊆ AM_live_roles (prod_AM_strong_lr even_impl _) (st__e, st__o).
  Proof. 
    assert (Nat.odd M = false) as O.
    { rewrite -Nat.negb_even. by destruct (Nat.even M). } 
    apply elem_of_subseteq. intros ρ.
    setoid_rewrite <- (AM_live_roles_spec (prod_AM_strong_lr _ _)).
    intros (a&st''&STEP').
    simpl in STEP'.

    destruct ρ as [ρ__e' | ρ__o'];
      revgoals. 
    { (* TODO: is it possible to unify these proofs in _sync and _priv? *)
      clear -STEP' LR__o Ns CUR__O CUR__O' O.
      
      inversion STEP'; subst.
      - (* role under consideration makes private step in new state *)
        assert (ρ__o' ∈ AM_live_roles (odd_AM_strong _) st__o) as IN.
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

  (* From trillium.fairness.heap_lang.examples.even_odd Require Import threads. *)
  (* eo_go_spec *)
  
  Definition even_corr
    {M__p : FairModel} {LM__p : LiveModel heap_lang M__p}
    {Σ : gFunctors} {heapGS0 : heapGS Σ LM__p}
    (threadG0 : threadG Σ) 
  (proj_st : M__p → amSt even_AM) (l : loc) (st : M__p) 
  (N : nat) :=
  let st__t := proj_st st in
  (frag_model_is st ∗ l ↦ #N ∗ ⌜cur_even _ st__t N⌝ ∗
   own th_name (●E (if Nat.even N then N else N + 1)))%I. 


  Definition glob_step_even {M__p : FairModel}
    (proj_st : fmstate M__p → amSt even_AM)
  (lift_role : amRole even_AM → fmrole M__p) 
  (st st' : M__p) (ρ__t : amRole even_AM) (N : amSt even_AM) := 
  proj_st st' = N
  ∧ fmtrans M__p st (Some (lift_role ρ__t)) st'
    ∧ (AM_live_roles (even_AM_strong _) (proj_st st')
       ⊆ AM_live_roles (even_AM_strong _) (proj_st st)
       → live_roles M__p st' ⊆ live_roles M__p st). 


  Definition even_vs (M__p : FairModel) (LM__p : LiveModel heap_lang M__p) 
  (Σ : gFunctors) (heapGS0 : heapGS Σ LM__p) (threadG0 : threadG Σ) 
  (proj_st : fmstate M__p → amSt even_AM) (lift_role : 
                                            amRole even_AM → 
                                            fmrole M__p) 
  (l : loc) (ι : namespace) (ρ__t : amRole even_AM) := 
  (□ (|={⊤,⊤ ∖ ↑ι}=>
        ∃ (st__p : M__p) (N : nat),
          let st__t := proj_st st__p in
          ▷ even_corr threadG0 proj_st l st__p N ∗
          (⌜Nat.even N⌝
           → ∀ st__t' : amSt even_AM,
               ⌜amTrans even_AM st__t (inl (step_sync N), Some ρ__t)
                  st__t'⌝ ∗ ⌜cur_even _ st__t' (N + 1)⌝
               → ∃ st__p' : M__p,
                   ⌜glob_step_even proj_st lift_role st__p st__p' ρ__t st__t'%nat⌝ ∗
                   (▷ even_corr threadG0 proj_st l st__p' (N + 1) ={⊤ ∖ ↑ι,⊤}=∗ True)) ∗
          (⌜Nat.odd N⌝
           → ∀ (st__t' : amSt even_AM) (a : ePriv even_impl),
               ⌜amTrans even_AM st__t (inr a, Some ρ__t) st__t'⌝ ∗
               ⌜cur_even _ st__t' N⌝
               → ∃ st__p' : M__p,
                   ⌜glob_step_even proj_st lift_role st__p st__p' ρ__t st__t'⌝ ∗
                   (▷ even_corr threadG0 proj_st l st__p' N ={⊤ ∖ ↑ι,⊤}=∗ True))))%I. 

  Variable (even_prog: val). 
  Lemma eo_go_spec :
∀ {M__p : FairModel} {LM__p : LiveModel heap_lang M__p} 
  {Σ : gFunctors} {heapGS0 : heapGS Σ LM__p} {threadG0 : threadG Σ} 
  (proj_st : M__p → amSt even_AM) (lift_role : 
                                            amRole even_AM → 
                                            fmrole M__p) 
  (tid : locale heap_lang) (n : loc) (ρ__t : amRole even_AM) 
  (N f : nat),
  f > 40
  → ∀ ι : namespace,
      (∀ st : M__p, lm_fl LM__p st ≥ 61)
      → {{{ even_vs proj_st lift_role n ι ρ__t ∗
        tid ↦M {[lift_role ρ__t := f]} ∗
        own th_name (◯E N) ∗
        frag_free_roles_are ∅ }}}
          even_prog #n #N@tid
        {{{ RET #(); tid ↦M ∅ }}}. 

  
  Lemma even_spec (tid: locale heap_lang) n ρ__t (N: nat) f (Hf: f > 40) ι
    (FL: forall st, lm_fl LM__p st >= 61):
    {{{  eo_vs n ι ρ__t ∗
         has_fuels tid {[ lift_role ρ__t := f ]} ∗ own th_name (◯E N) ∗
         frag_free_roles_are ∅
    }}}
      even_spec #n #N @ tid
    {{{ RET #(); has_fuels tid ∅ }}}.

  Lemma even_spec tid l (N : nat) ρ f (Hf: f > 40) :
    {{{ evenodd_inv l ∗ tid ↦M {[ inl ρ := f ]} ∗ even_at N ∗
        frag_free_roles_are ∅ }}}
      even_prog #l #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hf & Heo & FR) Hk".
    
    iApply (@eo_go_spec 0 the_fair_model _ _ _ evenThreadG fst inl 
             with "[$Hf $FR $Heo]"); [lia| simpl; lia | |done].
    rewrite /eo_vs. iModIntro.
    iMod (inv_acc with "Hinv") as "[OPEN CLOS]".
    { apply top_subseteq. }
    iDestruct "OPEN" as (st__e st__o M) "(>Hmod & >%CUR__E & >%CUR__O & >Hn & Hauths)".
    rewrite if_arg2_comm. iDestruct "Hauths" as "[E O]".
    iModIntro. iExists _, _. iSplitL "Hmod Hn E".
    { rewrite /eo_corr. simpl. iFrame.
      simpl. iFrame. rewrite Nat.add_0_r. destruct (Nat.even M); auto. }
    simpl. rewrite Nat.add_0_r.
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
      rewrite !Nat.add_0_r.
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
      rewrite !Nat.add_0_r. rewrite E. iFrame. done. 
  Qed.
  
  Lemma odd_spec tid l (N : nat) ρ f (Hf: f > 40) :
    {{{ evenodd_inv l ∗ tid ↦M {[ inr ρ := f ]} ∗ odd_at N ∗
        frag_free_roles_are ∅ }}}
      incr_loop #l #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof. 
    iIntros (Φ) "(#Hinv & Hf & Heo & FR) Hk".
    
    iApply (@eo_go_spec 1 the_fair_model _ _ _ oddThreadG snd inr
             with "[$Hf $FR $Heo]"); [lia| simpl; lia | |done].
    rewrite /eo_vs. iModIntro.
    iMod (inv_acc with "Hinv") as "[OPEN CLOS]".
    { apply top_subseteq. }
    iDestruct "OPEN" as (st__e st__o M) "(>Hmod & >%CUR__E & >%CUR__O & >Hn & Hauths)".
    rewrite if_arg2_comm. iDestruct "Hauths" as "[E O]".
    iModIntro. iExists _, _. iSplitL "Hmod Hn O".
    { rewrite /eo_corr. simpl. iFrame.
      simpl. rewrite even_plus1_negb. destruct (Nat.even M); auto. }
    simpl. rewrite !odd_plus1_negb even_plus1_negb Nat.negb_even.
    destruct (Nat.odd M) eqn:E.
    - iSplitL.
      2: { simpl. by iIntros "%foo". }
      iIntros "_ %st__t' [%STEP %CUR__O']".
      pose proof CUR__E as foo. eapply @even_syncable in foo as (st1' & STEP1 & CUR__E').
      2: { set_solver. }      
      iExists (st1', st__t'). iSplitR.
      { iPureIntro. repeat split; auto.
        - econstructor. simpl.
          eapply pt_sync2; eauto. 
          Unshelve. 2: exact (inl (step_sync M)). done.
        - simpl. intros LR__e. eapply lr_pres_odd_sync; eauto. }
      iIntros "(?&?&?&?)". iMod ("CLOS" with "[-]") as "_"; [| done].
      (* rewrite !Nat.add_0_r. *)
      iNext. iFrame. simpl. rewrite !even_plus1_negb -!Nat.negb_odd E.  
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
      rewrite -!Nat.negb_odd odd_plus1_negb E. simpl. iFrame. done. 
  Qed. 

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

  Definition start : val :=
    λ: "l",
      let: "x" := !"l" in
      (Fork (incr_loop "l" "x") ;;
       Fork (incr_loop "l" ("x"+#1))).


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
    iInv Ns as (st__e st__o M) "(>Hmod & >%CUR__E & >%CUR__O & >Hn & Hauths)" "Hclose".
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
      destruct (Nat.even M); iFrame; done. }
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
