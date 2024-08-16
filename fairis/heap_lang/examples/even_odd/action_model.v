From trillium.fairness Require Import fairness.
From trillium.fairness Require Import utils.
From stdpp Require Import namespaces coPset. 
From iris.proofmode Require Import proofmode.

Import derived_laws_later.bi.

Section Actions.
  (* Definition to_action `{Countable T}: T -> Action := encode.  *)
  (* Definition from_action `{Countable T}: Action -> option T := decode. *)
  Definition Action := positive.

  Definition pick_act `{Countable T} (pref: namespace) (t: T) :=
    coPpick $ ↑ (pref .@ encode t).
  Definition acts_at (pref: namespace): coPset := ↑ pref. 

  (* (* Set Default Proof Using "Type". *) *)
  (* Definition pub_prefix: namespace := nroot .@ "pub".  *)
  (* Definition pub_actions: coPset := ↑pub_prefix.  *)
  (* Definition pub_act `{Countable T} (t: T): Action := pick_act pub_prefix t. *)

  (* Definition priv_prefix: namespace := nroot .@ "priv".  *)
  (* Definition priv_actions: coPset := ↑priv_prefix.  *)
  (* Definition priv_act `{Countable T} (t: T): Action := pick_act priv_prefix t. *)

  Lemma pick_act_dom `{Countable T} ns (t: T):
    pick_act ns t ∈ (↑ns: coPset). 
  Proof.
    rewrite /pick_act.
    eapply elem_of_weaken; [apply coPpick_elem_of| ].
    { apply nclose_infinite. }
    apply nclose_subseteq.
  Qed.
    
  (* Lemma priv_act_private `{Countable T} (t: T): *)
  (*   priv_act t ∈ priv_actions. *)
  (* Proof. *)
  (*   rewrite /priv_act /priv_actions. *)
  (*   eapply elem_of_weaken; [apply coPpick_elem_of| ]. *)
  (*   { apply nclose_infinite. } *)
  (*   apply nclose_subseteq. *)
  (* Qed. *)

  Lemma pick_act_inj `{CNT: Countable T} pref: Inj eq eq (@pick_act _ _ CNT pref).
  Proof.
    red. rewrite /pick_act. intros ?? EQ.
    destruct (decide (x = y)) as [| NEQ]; auto.
    assert ((↑pref.@encode x: coPset) ## (↑pref.@encode y)) as D.
    { assert (encode x ≠ encode y); [| solve_ndisj].
      intros ?. destruct NEQ. eapply encode_inj; eauto. }
    opose proof * (coPpick_elem_of (↑pref.@encode x)) as IN1.
    { eapply nclose_infinite. }
    opose proof * (coPpick_elem_of (↑pref.@encode y)) as IN2.
    { eapply nclose_infinite. }
    rewrite EQ in IN1. set_solver.
  Qed.
    
  (* Lemma pub_priv_actions_disjoint: pub_actions ## priv_actions. *)
  (* Proof. solve_ndisj. Qed. *)

  Lemma pick_act_disj_neq `{Countable T1} `{Countable T2}
    ns1 ns2 (DISJ: ns1 ## ns2):
    forall (a: T1) (b: T2), 
      pick_act ns1 a ≠ pick_act ns2 b.
  Proof.
    intros.
    pose proof (pick_act_dom ns1 a). pose proof (pick_act_dom ns2 b) as DOM2.
    intros EQ. rewrite -EQ in DOM2.
    edestruct DISJ; eauto. 
  Qed. 

  Lemma pick_act_notin_disj_ns `{Countable T}
      ns ns' (DISJ: ns ## ns'):
    forall (t: T), pick_act ns t ∉ (↑ ns': coPset).
  Proof.
    intros. apply disjoint_singleton_l.
    symmetry. eapply disjoint_subseteq.
    - apply _.
    - reflexivity.
    - apply elem_of_subseteq_singleton, pick_act_dom.
    - done. 
  Qed.

  Lemma pick_act_ns_nth_disj_neq `{Countable T}
    ns C INF (DISJ: ↑ ns ## C):
    forall (a: T) n, pick_act ns a ≠ coPset_nth C INF n. 
  Proof.
    intros.
    pose proof (pick_act_dom ns a). pose proof (coPset_nth_in C INF n) as DOM2.
    intros EQ. rewrite -EQ in DOM2.
    edestruct DISJ; eauto. 
  Qed.  

End Actions.

Section ActionModel.

  Record ActionModel := {
      amSt: Type;
      (* amA: Type; *)
      amRole: Type;
      amTrans: amSt -> Action * option amRole -> amSt -> Prop;
  }.

  Arguments amTrans {_}. 

  (* similar to "live roles" of FairModel, but the roles are optional, 
     and the list cannot contain anything non-stepping *)
  Definition AM_strong_lr (AM: ActionModel) `{Countable (amRole AM)} :=
    {lr: amSt AM -> gset (option (amRole AM)) |
      forall st oρ, oρ ∈ lr st <-> exists a st', amTrans st (a, oρ) st'}.

  Definition AM_fin_branch (AM: ActionModel) := 
    {next_steps: amSt AM -> list (amSt AM * Action * option (amRole AM)) 
     | forall s1 s2 a oρ, amTrans s1 (a, oρ) s2 <-> (s2, a, oρ) ∈ next_steps s1}.

  (* a weaker version of AM_fin_branch that is easier to show *)
  Definition AM_fin_branch' (AM: ActionModel) := 
    {next_steps': amSt AM -> list (amSt AM * Action * option (amRole AM)) 
     | forall s1 s2 a oρ, amTrans s1 (a, oρ) s2 -> (s2, a, oρ) ∈ next_steps' s1}.

  Definition AM_step_dec (AM: ActionModel) :=
    forall s1 a oρ s2, Decision (@amTrans AM s1 (a, oρ) s2).

  (* derive the strong finite branching from weaker one
     by filtering possible transitions *)
  Lemma AM_fin_branch_dec (AM: ActionModel)
    (FIN: AM_fin_branch' AM) (DEC: AM_step_dec AM):
    AM_fin_branch AM.
  Proof. 
    destruct FIN as [ns' FIN]. 
    exists (fun s => filter (fun '(s2, a, oρ) => @bool_decide _ (DEC s a oρ s2)) (ns' s)).
    intros. rewrite elem_of_list_filter. rewrite bool_decide_spec.
    symmetry. apply iff_and_impl_helper. intuition.
  Qed.

  (* (optional) live roles can be obtained by checking all possible transitions,
     given that there is a finite number of them *)
  Lemma fin_branch_strong (AM: ActionModel) `{Countable (amRole AM)}
    (FIN: AM_fin_branch' AM) (DEC: AM_step_dec AM):
    AM_strong_lr AM.
  Proof.
    eapply AM_fin_branch_dec in FIN as [ns FIN]; auto.
    exists (fun s => list_to_set ((fun '(_, _, oρ) => oρ) <$> ns s)). 
    intros. rewrite elem_of_list_to_set. rewrite elem_of_list_fmap.
    do 2 rewrite ex_prod.
    setoid_rewrite ex_det_iff with (a := oρ); [| by intuition].
    rewrite ex2_comm. do 2 (apply exist_proper; intros).
    rewrite FIN. tauto.
  Qed. 

  (* useful for defining the set of _non-optional_ live_roles of AM *)
  (* TODO: move *)  
  Definition extract_Somes {A: Type} (l: list (option A)): list A :=
    flat_map (from_option (fun a => [a]) []) l.

  Lemma extract_Somes_spec {A: Type} (l: list (option A)):
    forall a, In (Some a) l <-> In a (extract_Somes l).
  Proof. 
    intros. rewrite /extract_Somes.
    rewrite in_flat_map_Exists.
    rewrite List.Exists_exists. simpl.
    erewrite ex_det_iff with (a := Some a). 
    2: { intros ? [? ?]. destruct a'; try done.
         simpl in H0. set_solver. }
    simpl. set_solver.
  Qed.

  Definition extract_Somes_gset `{Countable A} (s: gset (option A)): gset A :=
    list_to_set ∘ extract_Somes ∘ elements $ s. 
  
  Lemma extract_Somes_gset_spec `{Countable A} (s: gset (option A)):
    forall a, Some a ∈ s <-> a ∈ (extract_Somes_gset s).
  Proof. 
    intros. rewrite /extract_Somes_gset.
    rewrite elem_of_list_to_set. 
    rewrite elem_of_list_In. rewrite -extract_Somes_spec.
    rewrite -elem_of_list_In. rewrite elem_of_elements.
    done. 
  Qed.

  Lemma extract_Somes_gset_inv `{Countable A} (s: gset (option A)):
    set_map Some (extract_Somes_gset s) = s ∖ {[ None ]}.
  Proof. 
    apply set_eq. intros ?. rewrite elem_of_map.
    setoid_rewrite <- extract_Somes_gset_spec.
    rewrite elem_of_difference not_elem_of_singleton.
    split; [intros (?&->&?) | intros [??]]. 
    - set_solver.
    - destruct x; eauto. done.
  Qed. 

  (* the counterpart of FairModel's "live_roles" *)
  Definition AM_live_roles {AM: ActionModel} `{Countable (amRole AM)} (AM_S: AM_strong_lr AM):
    amSt AM -> gset (amRole AM) :=
    extract_Somes_gset ∘ proj1_sig AM_S.

  Lemma AM_live_roles_spec {AM: ActionModel} `{Countable (amRole AM)} (AM_S: AM_strong_lr AM):
    forall st ρ,
    (exists a st', amTrans st (a, Some ρ) st') <-> ρ ∈ AM_live_roles AM_S st.
  Proof. 
    intros. rewrite /AM_live_roles /compose.
    rewrite -extract_Somes_gset_spec.
    destruct AM_S as [f SPEC]. simpl. rewrite SPEC.
    done.
  Qed.

  Section ActionsOf.
    Context (AM: ActionModel). 

    Definition is_action_of (a: Action) := 
      exists st oρ st', @amTrans AM st (a, oρ) st'.

    Lemma action_of_step st a oρ st'
      (STEP: @amTrans AM st (a, oρ) st'):
      is_action_of a.
    Proof. red. eauto. Qed.  

  End ActionsOf.

  Section AMProduct.
    Context (AM1 AM2: ActionModel).
    
    Let PS: Type := @amSt AM1 * @amSt AM2.
    Let PR: Type := @amRole AM1 + @amRole AM2.

    Context
      {is_act1_dec: forall a, Decision (is_action_of AM1 a)}
      {is_act2_dec: forall a, Decision (is_action_of AM2 a)}.

    Inductive ProdTrans: PS -> Action * option PR -> PS -> Prop :=
    | pt_inner1 s1 s1' s2 a r1 
        (* (PRIV: a ∉ pub_actions) *)
        (NO2: ¬ is_action_of AM2 a)
        (STEP1: amTrans s1 (a, Some r1) s1'):
      ProdTrans (s1, s2) (a, Some (inl r1)) (s1', s2)
    | pt_inner2 s2 s2' s1 a r2
        (* (PRIV: a ∉ pub_actions) *)
        (NO1: ¬ is_action_of AM1 a)
        (STEP2: amTrans s2 (a, Some r2) s2'):
      ProdTrans (s1, s2) (a, Some (inr r2)) (s1, s2')
    | pt_sync1 s1 s1' s2 s2' a r1
        (STEP1: amTrans s1 (a, Some r1) s1')
        (STEP2: amTrans s2 (a, None) s2'):
      ProdTrans (s1, s2) (a, Some (inl r1)) (s1', s2')
    | pt_sync2 s1 s1' s2 s2' a r2
        (STEP1: amTrans s1 (a, None) s1')
        (STEP2: amTrans s2 (a, Some r2) s2'):
      ProdTrans (s1, s2) (a, Some (inr r2)) (s1', s2')
    | pt_sync_ext s1 s1' s2 s2' a
        (STEP1: amTrans s1 (a, None) s1')
        (STEP2: amTrans s2 (a, None) s2'):
      ProdTrans (s1, s2) (a, None) (s1', s2')
    .
    
    Definition ProdAM: ActionModel := {| amTrans := ProdTrans; |}.

    (* Global Instance prod_AM_act_of_dec: forall a, Decision (is_action_of ProdAM a). *)      

    Lemma prod_AM_step_dec {EQ1: EqDecision (amSt AM1)} {EQ2: EqDecision (amSt AM2)}
      (D1: AM_step_dec AM1) (D2: AM_step_dec AM2)
      :
      AM_step_dec ProdAM.
    Proof.
      red. intros [s1 s2] a oρ [s1' s2'].
      Ltac inv_step := right; intros S; inversion S; subst; congruence.
      destruct oρ as [ρ| ].
      2: { destruct (D1 s1 a None s1'), (D2 s2 a None s2').
           all: try inv_step.
           left. econstructor; eauto. }
      destruct ρ as [ρ1 | ρ2]. 
      - destruct (D1 s1 a (Some ρ1) s1'), (D2 s2 a None s2').
        all: try inv_step.
        + left. econstructor; eauto.
        + destruct (is_act2_dec a), (decide (s2' = s2)) as [-> | ?].
          all: try inv_step.
          repeat econstructor; eauto.
      - destruct (D1 s1 a None s1'), (D2 s2 a (Some ρ2) s2').
        all: try inv_step.
        + left. econstructor; eauto.
        + destruct (is_act1_dec a), (decide (s1' = s1)) as [-> | ?].
          all: try inv_step.
          repeat econstructor; eauto.
    Qed.

    Lemma prod_AM_fin_branch' (FIN1: AM_fin_branch' AM1) (FIN2: AM_fin_branch' AM2)
      :
      AM_fin_branch' ProdAM.
    Proof. 
      destruct FIN1 as [ns1 FIN1], FIN2 as [ns2 FIN2].
      set (dummy := xH). 
      exists (fun '(s1, s2) =>
           '(s1', a1, oρ1) ← (s1, dummy, None) :: ns1 s1;
           '(s2', a2, oρ2) ← (s2, dummy, None) :: ns2 s2;
           a ← [a1; a2];
           ρ' ← [from_option (Some ∘ inl) None oρ1; from_option (Some ∘ inr) None oρ2];
           mret ((s1', s2'), a, ρ')). 
           
      intros [s1 s2] [s1' s2'] a oρ STEP.
      rewrite elem_of_list_bind.
      rewrite !ex_prod.

      (* TODO: shorten the following proof, rewrite under binders? *)
      (* setoid_rewrite elem_of_list_bind.       *)

      (* do 3 (eapply exist_proper; intros). *)
      (* { pattern x1. match goal with |- ((fun y => ?F y <-> _) x1) => idtac "foo" end.  *)      

      inversion STEP; subst.
      { exists s1', a, (Some r1).
        split; [| set_solver]. 
        rewrite elem_of_list_bind.
        exists (s2', dummy, None). set_solver. }
      { exists s1', dummy, None. 
        split; [| set_solver]. 
        rewrite elem_of_list_bind.
        exists (s2', a, Some r2). set_solver. }
      { exists s1', a, (Some r1).
        split; [| set_solver]. 
        rewrite elem_of_list_bind.
        exists (s2', a, None). 
        rewrite elem_of_list_bind. set_solver. }
      { exists s1', a, None.
        split; [| set_solver]. 
        rewrite elem_of_list_bind.
        exists (s2', a, Some r2). set_solver. }
      { exists s1', a, None.
        split; [| set_solver].
        rewrite elem_of_list_bind.
        exists (s2', a, None). set_solver. }
    Qed.

    Section Independent.

      Definition models_independent :=
        forall a, is_action_of AM1 a -> is_action_of AM2 a -> False.

      Context (INDEP: models_independent). 

      Lemma prod_indep_live_roles
        `{Countable (amRole AM1)} `{Countable (amRole AM2)}
        {STR1 STR2 STR__p} (st1: amSt AM1) (st2: amSt AM2):
        AM_live_roles STR__p ((st1, st2): amSt ProdAM) = 
        set_map inl (AM_live_roles STR1 st1) ∪ 
        set_map inr (AM_live_roles STR2 st2).
      Proof using INDEP.
        simpl. rewrite set_eq. intros ?.
        rewrite elem_of_union !elem_of_map.
        rewrite -(AM_live_roles_spec STR__p).
        repeat setoid_rewrite <- AM_live_roles_spec.
        split.
        { intros (a & st' & STEP). inversion STEP; subst.
          all: set_solver. }
        intros [(?&->&?&?&STEP)|(?&->&?&?&STEP)].
        - do 2 eexists. apply pt_inner1; eauto.
          intros ?. eapply INDEP; eauto.
          eapply action_of_step; eauto. 
        - do 2 eexists. apply pt_inner2; eauto.
          intros ?. eapply INDEP; eauto.
          eapply action_of_step; eauto.
      Qed. 
        
    End Independent.

  End AMProduct.

  Section AM2FM.
    Context (AM: ActionModel).
    Context `{CNT_R: Countable (amRole AM)}. 
    Context {EQ_ST: EqDecision (amSt AM)}. 
    Context {INH_ST: Inhabited (amSt AM)} {INH_R: Inhabited (amRole AM)}.

    (* this requirement is not necessary, but allows to reuse the AM_strong_lr machinery *)
    Context (AM_S: AM_strong_lr AM). 

    Inductive am_fmtrans: amSt AM → option (amRole AM) → amSt AM → Prop :=
    | amfm_role_step s1 s2 a r (STEP: amTrans s1 (a, Some r) s2):
      am_fmtrans s1 (Some r) s2
    | amfm_env_step s1 s2 a (STEP: amTrans s1 (a, None) s2):
      am_fmtrans s1 None s2
    .

    Lemma am_fmtrans_action s1 oρ s2:
      am_fmtrans s1 oρ s2 <-> exists a, amTrans s1 (a, oρ) s2.
    Proof.
      split.
      - intros STEP. inversion STEP; eauto.
      - intros [a STEP]. destruct oρ; econstructor; eauto.
    Qed. 

    Definition AM2FM : FairModel.
      refine {| fmtrans := am_fmtrans; live_roles := AM_live_roles AM_S |}.
    Proof. 
      intros. apply AM_live_roles_spec.
      inversion H; eauto.
    Defined. 

  End AM2FM.

End ActionModel.
