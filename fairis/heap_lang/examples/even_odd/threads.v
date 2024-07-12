From stdpp Require Import decidable.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness.heap_lang.examples.even_odd Require Import action_model utils interface.

Close Scope Z. 

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
  
  Global Instance TR_inh: Inhabited TR. 
  apply _.
  Defined. 

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
  
  (* TODO: can we make it work with non-trivial set of roles? *)
  Local Lemma thread_roles_equal (ρ1 ρ2: amRole thread_model):
    ρ1 = ρ2.
  Proof. 
    by destruct ρ1, ρ2.
  Qed.

  Instance thread_extra: ActionModelExtra thread_model.
  Proof.
    unshelve esplit; try by apply _.
    - apply thread_AM_fin_branch'.
    - apply thread_AM_step_dec. 
  Qed. 

  Lemma thread_AM_lr_exact n: AM_live_roles ame_strong n = {[ ρT ]}.
  Proof.
    apply set_eq. intros ρ. rewrite elem_of_singleton. 
    rewrite -AM_live_roles_spec. pose proof (thread_roles_equal ρ ρT) as ->.
    split; auto. intros _.
    destruct (decide (Nat.even (n + d))).
    - do 2 eexists. econstructor. eauto.
    - apply negb_prop_intro in n0. rewrite Nat.negb_even in n0. 
      do 2 eexists. by eapply thread_loop.
  Qed. 

  Lemma thread_syncable n (EVEN: Nat.odd (n + d)):
    amTrans thread_model n (inl (step_sync n), None) (n + 1).
  Proof.
    rewrite Nat.add_1_r. by econstructor.
  Qed. 

  Lemma thread_sync_step_inv n n' k ρ
      (STEP: amTrans thread_model n (inl (step_sync k), Some ρ) n'):
      k = n /\ Nat.even (n + d).
  Proof. 
    inversion STEP; subst; eauto.
  Qed.

  Lemma thread_sync_lr_nonincr n n' M
      (STEP: amTrans thread_model n (inl (step_sync M), None) n'):
    AM_live_roles ame_strong n' ⊆ AM_live_roles ame_strong n.
  Proof. 
    rewrite !thread_AM_lr_exact. done.
  Qed. 

  Section Proofs. 
    Context `{LM__p: LiveModel heap_lang M__p}.
    Context `{!heapGS Σ LM__p}. 

    Context `{!threadG Σ}.

    Definition incr_loop : val :=
      rec: "incr_loop" "l" "n" :=
        (if: CAS "l" "n" ("n"+ #1)
         then "incr_loop" "l" ("n" + #2)
         else "incr_loop" "l" "n").

    Context (proj_st: fmstate M__p -> amSt thread_model).
    Context (lift_role: amRole thread_model -> fmrole M__p). 

    Definition cur_n (st: amSt thread_model) (n: nat) := st = n. 
    
    Definition eo_corr l (st: fmstate M__p) (N: nat): iProp Σ :=
      (* let st__t := proj_st st in *)
      frag_model_is st ∗ l ↦ #N ∗
      (* ⌜ cur_n st__t N ⌝ ∗ *)
      own th_name (●E (if Nat.even (N + d) then N else (N + 1))).

    (* Definition glob_step st st' ρ__t N := *)
    (*   proj_st st' = N /\ fmtrans M__p st (Some $ lift_role ρ__t) st' /\ *)
    (*   (AM_live_roles ame_strong (proj_st st') ⊆ AM_live_roles ame_strong (proj_st st) -> *)
    (*    live_roles M__p st' ⊆ live_roles M__p st). *)

    Definition eo_vs l ι ρ__t tid : iProp Σ :=
      □ |={⊤, ⊤ ∖ ↑ι}=> ∃ st__p N,
      let st__t := proj_st st__p in
      (▷ eo_corr l st__p N) ∗
      (∀ f, tid ↦M {[ lift_role ρ__t := f ]} -∗ frag_model_is st__p -∗ frag_free_roles_are ∅ -∗
             MU (⊤ ∖ ↑ι) tid (
               ∃ st__p' f', tid ↦M {[ lift_role ρ__t := f' ]}  ∗ frag_model_is st__p' ∗ frag_free_roles_are ∅ ∗ ⌜ f' > 43 ⌝ ∗
                 (∀ M, ▷ (eo_corr l st__p' M) ={⊤ ∖ ↑ι, ⊤}=∗ True))).
    
  Lemma eo_go_spec (tid: locale heap_lang) n ρ__t (N: nat) f (Hf: f > 40) ι
    (FL: forall st, lm_fl LM__p st >= 61):
    {{{  eo_vs n ι ρ__t tid ∗
         has_fuels tid {[ lift_role ρ__t := f ]} ∗ own th_name (◯E N) ∗
         frag_free_roles_are ∅
    }}}
      incr_loop #n #N @ tid
    {{{ RET #(); has_fuels tid ∅ }}}.
  Proof.
    rewrite !(thread_roles_equal ρ__t ρT). clear ρ__t.  
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ). iIntros "(#VS & Hf & Heven & HFR) Hk".

    rewrite /incr_loop.
    wp_lam.
    wp_pures. wp_bind (CmpXchg _ _ _). iApply wp_atomic.
    iPoseProof "VS" as "-#V". iMod "V" as "(%st & %M & (>Hmod & >Hn & >Hauths) & CLOS)".

    (* remember (proj_st st) as st__t.  *)

    destruct (Nat.even (M + d)) eqn:Heqn.
    - iDestruct (th_agree with "Heven Hauths") as "->".
      iModIntro.
      (* iDestruct "CLOS" as "[CLOS _]". iSpecialize ("CLOS" with "[]"); [done| ]. *)
      (* iSpecialize ("CLOS" with "[]"). *)
      (* { iPureIntro. split; [| split]; [| reflexivity | ].  *)
      (*   - rewrite Nat.add_1_r. simpl. econstructor. intuition. *)
      (*   - by rewrite !thread_AM_lr_exact. } *)

      iSpecialize ("CLOS" with "[$] [$] [$]"). 
      iApply sswp_MU_wp; [done| ].
      iApply (wp_cmpxchg_suc with "[$]"); try done.  
      iIntros "!> Hb".
      iApply (MU_wand with "[-CLOS] [$]"). 
      iIntros "(%st' & %f' & (Hf& Hmod& HFR & %FUEL' & CLOS))".

      iMod (th_update _ _ _ (N + 2) with "[$]") as "[Hay Heven]".
      wp_pures.
      iModIntro. 
      iMod ("CLOS" with "[Hmod Hay Hb]") as "_". 
      { replace (Z.of_nat N + 1)%Z with (Z.of_nat (N + 1)) by lia.
        (* rewrite -ST'. *)
        iFrame.
        rewrite Nat.add_shuffle0. rewrite Nat.even_add.
        rewrite Heqn. simpl.
        rewrite -Nat.add_assoc. done. }
      iModIntro. simpl.

      pose proof (FL st').
      do 3 wp_pure _.
      replace (Z.of_nat N + 2)%Z with (Z.of_nat (N + 2)) by lia.
      iApply ("Hg" with "[] [Heven Hf HFR] [$]"); last first.
      { iFrame "∗#". }
      iPureIntro; lia.
    - iDestruct (th_agree with "Heven Hauths") as "%Heq". rewrite -> Heq in *.
      iModIntro.
      subst.


      iSpecialize ("CLOS" with "[$] [$] [$]"). 
      iApply sswp_MU_wp; [done| ].
      iApply (wp_cmpxchg_fail with "[$]"); [| done| ].
      { assert (M ≠ M + 1) by lia. set_solver. }
      iIntros "!> Hb".
      iApply (MU_wand with "[-CLOS] [$]"). 
      iIntros "(%st' & %f' & (Hf& Hmod& HFR & %FUEL' & CLOS))".

      iMod (th_update _ _ _ (M + 1) with "[$]") as "[Hay Heven]".
      wp_pures.
      iModIntro. 
      iMod ("CLOS" $! M with "[Hmod Hay Hb]") as "_". 
      { iFrame. by rewrite Heqn. }
      iModIntro. simpl.

      pose proof (FL st').
      do 2 wp_pure _.
      iApply ("Hg" with "[] [Heven Hf HFR] [$]"); last first.
      { iFrame "∗#". }
      iPureIntro; lia.

      (* iDestruct "CLOS" as "[_ CLOS]". iSpecialize ("CLOS" with "[]"). *)
      (* { iPureIntro. by rewrite -Nat.negb_even Heqn. }  *)
      (* iSpecialize ("CLOS" with "[]"). *)
      (* { iPureIntro. simpl. split; [| reflexivity]. *)
      (*   econstructor. by rewrite -Nat.negb_even Heqn. } *)
      (* iDestruct "CLOS" as (st') "((%ST'&%STEP&%LR)&CLOS)". *)
 
      (* iApply (wp_step_model_singlerole with "Hmod Hf HFR"); eauto. *)
      (* { apply LR. simpl. by rewrite !thread_AM_lr_exact. }  *)

      (* iApply (wp_cmpxchg_fail with "Hn"); [intros Hne; simplify_eq; lia|done|]. *)
      (* iIntros "!> Hb Hmod Hf HFR". *)
      (* wp_pures. *)
      (* iModIntro.  *)
      (* iMod ("CLOS" with "[Hmod Hb Hauths]"). *)
      (* { rewrite -ST'. iFrame. iSplitR; [done| ].  *)
      (*   by rewrite ST' Heqn. }   *)
      (* iModIntro. simpl. *)
      (* (* wp_pures. *) *)
      (* pose proof (FL st'). *)
      (* do 2 wp_pure _.  *)
      (* iApply ("Hg" with "[] [Heven Hf HFR] [$]"); last first. *)
      (* { iFrame "∗#". } *)
      (* iPureIntro; lia. *)
  Qed.
    
  End Proofs.
  
End ThreadModel.

Definition thread_0_even: EvenModel.
  refine {| cur_even := cur_n 0 |}.
  - intros. red in CUR. subst st.
    rewrite (plus_n_O n) in ODD. 
    eapply thread_syncable in ODD.
    eexists. split; eauto. done.
  - intros. red in CUR. subst st__e.
    simpl in *.
    apply thread_sync_step_inv in STEP as [-> STEP]. 
    rewrite -plus_n_O in STEP. done.
  - intros. simpl.  
    eapply thread_sync_lr_nonincr; eauto.
  - iIntros "*" (????) "(#VS&MAP&FRAG&FREE) Post".
    iApply (eo_go_spec with "[MAP FRAG FREE]").
    1, 2: by eauto.
    2: done.
    simpl in *.
    iFrame. rewrite /eo_vs. iModIntro. simpl.
    iMod "VS" as (st__p M) "((ST&CUR&>%CORR&AUTH)&E&O)". red in CORR. 
    iModIntro. do 2 iExists _.
    admit. 
    (* rewrite !Nat.add_0_r. *)
    (* iSplitL "ST CUR AUTH". *)
    (* { iNext. rewrite /eo_corr. rewrite /cur_n. *)
    (*   rewrite Nat.add_0_r. iFrame. done. } *)
    (* iSplitL "E". *)
    (* + iIntros "%E" (st__t') "[%STEP %CUR']". iSpecialize ("E" with "[%//]"). *)
    (*   iDestruct ("E" $! _ with "[%//]") as "E". *)
    (*   iIntros "**". iSpecialize ("E" with "[] [$] [$] [$]"); auto. *)
    (*   iApply (MU_wand with "[] [$]"). *)
    (*   iIntros "(% & % & (?&?&?&%&%&CLOS))". *)
    (*   do 2 iExists _. iFrame. iApply bi.sep_assoc. iSplitR; [done| ]. *)
    (*   rewrite /eo_corr. iIntros "(?&?&?&?)". iApply "CLOS". iNext. *)
    (*   rewrite Nat.add_0_r. iFrame.  *)
    (* + iIntros "%O" (st__t' a) "[%STEP %CUR']". iSpecialize ("O" with "[%//]"). *)
    (*   iDestruct ("O" $! _ with "[%//]") as (?) "((%&%&%)&CLOS)". *)
    (*   red in CUR'. subst.  *)
    (*   iExists _. iSplitL ""; [done| ].  *)
    (*   iIntros "(?&?&?&?)". iApply "CLOS". *)
    (*   iNext. rewrite Nat.add_0_r. iFrame. *)
  - exact ρT.
(* Qed.  *)
Admitted. 

    
Definition thread_1_odd: OddModel.
  refine {| cur_odd := cur_n 1 |}.
  - intros. red in CUR. subst st.
    rewrite -Nat.negb_odd -odd_plus1_negb in ODD. 
    eapply thread_syncable in ODD.
    eexists. split; eauto. done.
  - intros. red in CUR. subst st__e.
    simpl in *.
    apply thread_sync_step_inv in STEP as [-> STEP]. 
    rewrite even_plus1_negb Nat.negb_even in STEP. done.
  - intros.
    eapply thread_sync_lr_nonincr; eauto.
  - iIntros "*" (????) "(#VS&MAP&FRAG&FREE) Post".
    iApply (eo_go_spec with "[MAP FRAG FREE]").
    1, 2: by eauto.
    2: done.
    simpl in *.
    iFrame. rewrite /eo_vs. iModIntro. simpl.
    iMod "VS" as (st__p M) "((ST&CUR&>%CORR&AUTH)&O&E)". red in CORR. 
    iModIntro. do 2 iExists _.
    rewrite !even_plus1_negb !Nat.negb_even !odd_plus1_negb. 
    iSplitL "ST CUR AUTH".
    { iNext. rewrite /eo_corr. rewrite /cur_n.
      rewrite even_plus1_negb. iFrame. done. }
    iSplitL "O".
    + iIntros "%O" (st__t') "[%STEP %CUR']". iSpecialize ("O" with "[%//]").
      (* iDestruct ("O" $! _ with "[%//]") as (?) "((%&%&%)&CLOS)". *)
      (* red in CUR'. subst.  *)
      (* iExists _. iSplitL ""; [done| ].  *)
      (* iIntros "(?&?&?&?)". iApply "CLOS". *)
      (* iNext. rewrite !even_plus1_negb negb_involutive. iFrame. *)
      admit. 
    + iIntros "%E" (st__t' a) "[%STEP %CUR']".
      rewrite Nat.negb_odd in E. 
      iSpecialize ("E" with "[%//]").
      iDestruct ("E" $! _ with "[%//]") as (?) "((%&%&%)&CLOS)".
      red in CUR'. subst. 
      iExists _. iSplitL ""; [done| ]. 
      iIntros "(?&?&?&?)". iApply "CLOS".
      iNext. rewrite !even_plus1_negb. iFrame.
  - exact ρT.
Admitted. 
