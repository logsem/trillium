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
From trillium.fairness.heap_lang.examples.even_odd Require Import action_model.


  Lemma ex_and_comm {T: Type} (A: Prop) (B: T -> Prop):
    (exists t, A /\ B t) <-> A /\ exists t, B t.
  Proof. split; intros (?&?&?); eauto. Qed.

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


Section Models.

  Inductive PubA := step_sync (k: nat).

  Global Instance PubA_EqDec: EqDecision PubA.
  Proof.
    intros [x] [y]. destruct (decide (x = y)); [left | right]; set_solver.
  Qed. 

  Section ThreadModel.
    Context (d: nat).

    Definition PrivA := unit.
    Let step_loop: PrivA := (). 
    
    Definition TA: Type := PubA + PrivA. 
    Definition TR := unit.
    Definition ρT: TR := (). 
    
    Definition TS := nat. 
    
    Inductive thread_trans: TS -> TA * option TR -> TS -> Prop :=
    | thread_step n : Nat.even (n + d) → thread_trans n (inl (step_sync n), Some ρT) (S n)
    | thread_loop n : Nat.odd (n + d) → thread_trans n (inr step_loop, Some ρT) n
    | thread_env n : Nat.odd (n + d) → thread_trans n (inl (step_sync n), None) (S n)
    .
    
    Definition thread_model: ActionModel := {| amTrans := thread_trans |}.

    (* Global Instance TR_eqdec: EqDecision TR. *)
    (* apply _.  *)
    (* Qed.  *)

    Lemma thread_AM_fin_branch': AM_fin_branch' thread_model.
    Proof.
      red. exists (fun n => n' ← [n; S n]; 
                      a ← [inl $ step_sync n; inr step_loop];
                      ρ ← [Some ρT; None]; mret (n', a, ρ)).
      intros * STEP.
      repeat (setoid_rewrite elem_of_list_bind).
      setoid_rewrite elem_of_list_ret.
      eexists. apply and_comm. rewrite -ex_and_comm.
      eexists. apply and_comm. rewrite -!and_assoc. apply and_comm. rewrite -ex_and_comm.
      eexists. apply and_comm. rewrite -!and_assoc.
      split; [reflexivity| ].
      inversion STEP; subst; set_solver.
    Qed.

    Lemma thread_AM_step_dec: AM_step_dec thread_model.
    Proof.
      red. intros.
      Local Ltac contra := right; intros TRANS; inversion TRANS; subst; try tauto; try lia.
      destruct (decide (Nat.even (s1 + d))).
      - destruct (decide (s2 = S s1 /\ oρ = Some ρT /\ a = inl (step_sync s1))) as [(-> & -> & ->)|?].
        + left. by econstructor.
        + contra; rewrite -Nat.negb_even in H3; by apply negb_prop_elim in H3.
      - pose proof n as n'. 
        apply negb_prop_intro in n. rewrite Nat.negb_even in n.
        destruct (decide (s2 = s1 /\ oρ = Some ρT /\ a = inr step_loop)) as [(-> & -> & ->)|?].
        + left. by econstructor.
        + destruct (decide (s2 = S s1 /\ oρ = None /\ a = inl (step_sync s1))) as [(-> & -> & ->)|?].
          * left. by econstructor.
          * contra.
    Qed.

    Lemma thread_AM_strong: AM_strong_lr thread_model.
    Proof. 
      apply fin_branch_strong; auto using thread_AM_step_dec, thread_AM_fin_branch'.
    Qed.
    
    (* Opaque PrivA.  *)
    (* Opaque TR.  *)
      
  End ThreadModel.
  
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

  Lemma prod_AM_strong_lr: AM_strong_lr prod_model.
  Proof. 
    apply fin_branch_strong.
    - unshelve eapply prod_AM_fin_branch'.  
      2, 3: apply thread_AM_fin_branch'. 
      { exact (fun '(oa1, oa2) => 
                 match oa1, oa2 with
                 | Some (inl pa1), Some _ => inl pa1
                 | Some (inr pa1), None => inr (inl pa1)
                 | None, Some (inr pa2) => inr (inr pa2)
                 | _, _ => inl (step_sync 0)
                 end). }
      red. intros [?|[?|?]]; reflexivity.
    - apply prod_AM_step_dec; apply thread_AM_step_dec.
  Qed.

  Definition the_fair_model: FairModel.
    unshelve eapply (AM2FM prod_model). 
  Proof.
    apply prod_AM_strong_lr. 
  Defined.

  Lemma tfm_live_roles st: 
    live_roles the_fair_model st =
     set_map inl (AM_live_roles (thread_AM_strong 0) st.1) ∪
     set_map inr (AM_live_roles (thread_AM_strong 1) st.2).
  Proof.
    destruct st as [st1 st2]. simpl.
    apply set_eq. intros ρ.
    rewrite elem_of_union. rewrite !elem_of_map. 
    setoid_rewrite <- (AM_live_roles_spec prod_AM_strong_lr).
    setoid_rewrite <- (AM_live_roles_spec (thread_AM_strong 0)).
    setoid_rewrite <- (AM_live_roles_spec (thread_AM_strong 1)).
    split.
    - intros (?&?&STEP). inversion STEP; subst.
      1, 3: by left; eexists; split; eauto. 
      all: by right; eexists; split; eauto.
    - (* !!! relies on the definition of thread_model *)
      (* !!! only holds in s1 = s2 *)
      intros [[ρ1 [-> (a1&?&STEP)]]| [? [-> (?&?&STEP)]]].
      + simpl in a1. unfold TA in a1.
        destruct a1 as [[n]| ].
        * inversion STEP; subst. rewrite Nat.add_0_r in H3.
          eexists _, (_, _). simpl.
          eapply (@pt_sync1 _ _ _ fact_TA); eauto.
          2: { eapply thread_env.        
  Abort. 

  Definition the_model: LiveModel heap_lang the_fair_model :=
    {| lm_fl (x: fmstate the_fair_model) := 61%nat; |}.

End Models.  

(** The CMRAs we need. *)
Class evenoddG Σ := EvenoddG {
  even_name: gname;
  odd_name: gname;
  evenodd_n_G :> inG Σ (excl_authR natO);
 }.
Class evenoddPreG Σ := {
  evenodd_PreG :> inG Σ (excl_authR natO);
 }.

(* Definition evenoddΣ : gFunctors := *)
(*   #[ heapΣ the_fair_model; GFunctor (excl_authR natO) ; GFunctor (excl_authR boolO) ]. *)

(* Global Instance subG_evenoddΣ {Σ} : subG evenoddΣ Σ → evenoddPreG Σ. *)
(* Proof. solve_inG. Qed. *)

Section proof.
  Context `{!heapGS Σ the_model, !evenoddG Σ}.
  (* Context `{EM__G: ExecutionModel heap_lang M__G} `{@heapGS Σ _ EM__G, evenoddG Σ}. *)
  (* Context {ifG: fairnessGS the_model Σ}. *)

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
      frag_model_is (N, N) ∗ n ↦ #N ∗
      if Nat.even N
      then auth_even_at N ∗ auth_odd_at (N+1)
      else auth_even_at (N+1) ∗ auth_odd_at N.
  Definition evenodd_inv n := inv Ns (evenodd_inv_inner n).

  Definition eo_corr n (N: nat) (γ: gname) (d: nat): iProp Σ :=
    frag_model_is (N, N) ∗ n ↦ #N ∗
    own γ (●E (if Nat.even (N + d) then N else (N + 1))).
    
  Definition eo_vs n ι γ d: iProp Σ :=
    □ |={⊤, ⊤ ∖ ↑ι}=> ∃ (N: nat),
    (▷ eo_corr n N γ d) ∗
    (▷ (eo_corr n (if (Nat.even (N + d)) then (N + 1) else N) γ d) ={⊤ ∖ ↑ι, ⊤}=∗ True).

  (* TODO: move *)
  Lemma even_succ_negb n: Nat.even (S n) = negb $ Nat.even n.
  Proof. by rewrite Nat.even_succ Nat.negb_even. Qed. 

  Lemma eo_go_spec  (tid: locale heap_lang) n ρ (N: nat) f (Hf: f > 40) ι γ d
    (STEP: forall k,
        let k' := if (Nat.even (k + d)) then (k + 1) else k in
        fmtrans the_fair_model (k, k) (Some ρ) (k', k'))
        :
    {{{  eo_vs n ι γ d ∗
         has_fuels tid {[ ρ := f ]} ∗ own γ (◯E N) ∗
         frag_free_roles_are ∅
    }}}
      incr_loop #n #N @ tid
    {{{ RET #(); has_fuels tid ∅ }}}.
  Proof.
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ). iIntros "(#VS & Hf & Heven & HFR) Hk".

    rewrite /incr_loop.
    wp_lam.
    wp_pures. wp_bind (CmpXchg _ _ _). iApply wp_atomic.
    iPoseProof "VS" as "-#V". iMod "V" as "(%M & (>Hmod & >Hn & >Hauths) & CLOS)".

    destruct (Nat.even (M + d)) eqn:Heqn.
    - iDestruct (they_agree with "Heven Hauths") as "->".
      iModIntro.
      iApply (wp_step_model_singlerole with "Hmod Hf HFR").
      { specialize (STEP N). rewrite Heqn in STEP. apply STEP. }
      { set_solver. }
      iApply (wp_cmpxchg_suc with "Hn"); [by do 3 f_equiv|done|].
      iIntros "!> Hb Hmod Hf HFR".
      iMod (they_update _ _ _ (N + 2) with "[$]") as "[Hay Heven]".
      wp_pures.
      iModIntro.
      iMod ("CLOS" with "[Hmod Hay Hb]") as "_". 
      { iFrame. rewrite Nat.add_shuffle0.
        rewrite (Nat.add_1_r (N + d)). 
        subst.
        rewrite even_succ_negb Heqn. simpl.
        rewrite -Nat.add_assoc.
        rewrite Nat2Z.inj_add. iFrame. }
      iModIntro. simpl. wp_pures.
      replace (Z.of_nat N + 2)%Z with (Z.of_nat (N + 2)) by lia.
      iApply ("Hg" with "[] [Heven Hf HFR] [$]"); last first.
      { iFrame "∗#". }
      iPureIntro; lia.
    - iDestruct (they_agree with "Heven Hauths") as "%Heq". rewrite -> Heq in *.
      iModIntro.
      subst. 
      iApply (wp_step_model_singlerole with "Hmod Hf HFR").
      { specialize (STEP M). rewrite Heqn in STEP. apply STEP. }
      { set_solver. }
      iApply (wp_cmpxchg_fail with "Hn"); [intros Hne; simplify_eq; lia|done|].
      iIntros "!> Hb Hmod Hf HFR".
      wp_pures.
      iModIntro. 
      iMod ("CLOS" with "[Hmod Hb Hauths]").
      { iFrame.
        by rewrite Heqn. }  
      iModIntro. simpl. wp_pures.
      iApply ("Hg" with "[] [Heven Hf HFR] [$]"); last first.
      { iFrame "∗#". }
      iPureIntro; lia.
  Qed.

  Lemma even_go_spec tid n (N: nat) f (Hf: f > 40) ι:
    {{{  eo_vs n ι even_name 0 ∗
         tid ↦M {[ ρEven := f ]} ∗ own even_name (◯E N) ∗
         frag_free_roles_are ∅
    }}}
      incr_loop #n #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    apply eo_go_spec; auto.
    intros. rewrite Nat.add_0_r Nat.add_1_r.
    destruct (Nat.even k) eqn:?; econstructor; eauto.
    by rewrite -Nat.negb_even Heqb.  
  Qed.

  Lemma odd_go_spec tid n (N: nat) f (Hf: f > 40) ι:
    {{{  eo_vs n ι odd_name 1 ∗
         tid ↦M {[ ρOdd := f ]} ∗ odd_at N ∗
         frag_free_roles_are ∅
    }}}
      incr_loop #n #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    apply eo_go_spec; auto.
    intros. rewrite Nat.add_1_r.
    rewrite Nat.even_succ. 
    destruct (Nat.odd k) eqn:?; econstructor; eauto.
    by rewrite -Nat.negb_odd Heqb.  
  Qed.

  Definition role_frag (eo : EO) : nat → iProp Σ :=
    match eo with
    | ρEven => even_at
    | ρOdd => odd_at
    end.

  (* TODO: move *)
  Lemma if_sep_comm (b: bool) (P1 Q1 P2 Q2: iProp Σ):
     (if b then (P1 ∗ Q1) else (P2 ∗ Q2)) ⊣⊢ (if b then P1 else P2) ∗ (if b then Q1 else Q2).
  Proof. destruct b; set_solver. Qed. 

  Lemma if_arg_comm {A B: Type} (b: bool) (x y: A) (f: A -> B):
    (if b then f x else f y) = f (if b then x else y).
  Proof. by destruct b. Qed. 

  Lemma incr_loop_spec tid n (N : nat) f (Hf: f > 40) (eo : EO) :
    {{{ evenodd_inv n ∗ tid ↦M {[ eo := f ]} ∗ (role_frag eo) N ∗
        frag_free_roles_are ∅ }}}
      incr_loop #n #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hf & Heo & FR) Hk".    
    destruct eo.
    - iApply (even_go_spec with "[$Hf $FR $Heo]"); [lia| |done].
      rewrite /eo_vs. iModIntro.
      iMod (inv_acc with "Hinv") as "[OPEN CLOS]".
      { apply top_subseteq. }
      iDestruct "OPEN" as (M) "(>Hmod & >Hn & Hauths)".
      rewrite if_sep_comm. iDestruct "Hauths" as "[E O]".      
      iModIntro. iExists _. iSplitL "Hmod Hn E".
      { iFrame. rewrite Nat.add_0_r. destruct (Nat.even M); auto. }
      iIntros "(?&?&?)". iMod ("CLOS" with "[-]") as "_"; [| done].
      iNext. iFrame.
      rewrite !Nat.add_0_r.
      rewrite if_sep_comm. destruct (Nat.even M) eqn:e.
      + rewrite Nat.add_1_r. rewrite Nat.even_succ -Nat.negb_even.
        rewrite e. simpl. iFrame. 
      + rewrite e. iFrame.  
    - iApply (odd_go_spec with "[$Hf $FR $Heo]"); [lia| |done].
      rewrite /eo_vs. iModIntro.
      iMod (inv_acc with "Hinv") as "[OPEN CLOS]".
      { apply top_subseteq. }
      iDestruct "OPEN" as (M) "(>Hmod & >Hn & Hauths)".
      rewrite if_sep_comm. iDestruct "Hauths" as "[E O]".
      iModIntro. iExists M.
      rewrite /eo_corr. 
      rewrite !(Nat.add_1_r M) Nat.even_succ.  
      iSplitL "Hmod Hn O".
      { iFrame. rewrite -Nat.negb_even. destruct (Nat.even M); simpl; auto. }
      iIntros "(?&?&?)". iMod ("CLOS" with "[-]") as "_"; [| done].
      iNext. iFrame.
      rewrite if_sep_comm. destruct (Nat.odd M) eqn:e.
      + rewrite Nat.add_1_r. rewrite !Nat.even_succ.
        rewrite Nat.odd_succ -Nat.negb_odd.
        rewrite e. iFrame.  
      + rewrite Nat.add_1_r. rewrite !Nat.even_succ.
        rewrite -Nat.negb_odd.
        rewrite e. iFrame.  
  Qed.

End proof.

Section proof_start.
  Context `{!heapGS Σ the_model, !evenoddG Σ}.
  Let Ns := nroot .@ "even_odd".

  Lemma frag_free_roles_are_sep: forall fr1 fr2 (DISJ: fr1 ## fr2), 
        frag_free_roles_are (fr1 ∪ fr2) ⊣⊢ frag_free_roles_are fr1 ∗ frag_free_roles_are fr2.
  Proof.
    intros. rewrite /frag_free_roles_are /frag_free_roles_are.    
    rewrite -gset.gset_op.
    rewrite -gset.gset_disj_union; auto. 
    rewrite -own_op. by rewrite -auth_frag_op.
  Qed. 

  Lemma start_spec tid n N1 N2 f (Hf: f > 60) :
    {{{ evenodd_inv n ∗ tid ↦M {[ ρEven := f; ρOdd := f ]} ∗
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
    
    rewrite if_sep_comm !if_arg_comm.
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
      iApply (incr_loop_spec with "[-]"); [|iFrame "#∗"|]; [lia| ..].
      2: { iNext. by iIntros. }
      destruct (Nat.even M); iFrame. }

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
      iApply (incr_loop_spec with "[-]"); [|iFrame "#∗"|]; [lia| ..].
      2: { iNext. by iIntros. }
      destruct (Nat.even M); iFrame. }

    iIntros "!> Hf". by iApply "HΦ".
  Qed.

End proof_start.