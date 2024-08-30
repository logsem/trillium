From iris.proofmode Require Import tactics.
From trillium.fairness.heap_lang Require Import iris_inst.
From trillium.fairness Require Import action_model fuel resources.
From trillium.fairness.heap_lang Require Export lang tactics notation.


Section SSWP.
  Context `{LM: LiveModel heap_lang M}.
  Context `{hG: !heapGS Σ LM}.

  
  Lemma sswp_pure_step s E e1 e2 (Φ : Prop) Ψ :
    PureExec Φ 1 e1 e2 → Φ → ▷ Ψ e2 -∗ sswp s E e1 Ψ%I.
  Proof.
    iIntros (Hpe HΦ) "HΨ".
    assert (pure_step e1 e2) as Hps.
    { specialize (Hpe HΦ). by apply nsteps_once_inv in Hpe. }
    rewrite /sswp /=.
    assert (to_val e1 = None) as ->.
    { destruct Hps as [Hred _]. specialize (Hred (Build_state ∅ ∅)).
      by eapply reducible_not_val. }
    iIntros (σ) "Hσ".
    iMod fupd_mask_subseteq as "Hclose"; last iModIntro; [by set_solver|].
    iSplit.
    { destruct s; [|done]. by destruct Hps as [Hred _]. }
    iIntros (e2' σ2 efs Hstep) "!>!>!>".
    iMod "Hclose". iModIntro. destruct Hps as [_ Hstep'].
    apply Hstep' in Hstep as [-> [-> ->]]. by iFrame.
  Qed.
  
  (** Heap *)
  (** The usable rules for [allocN] stated in terms of the [array] proposition
      are derived in te file [array]. *)
  Lemma heap_array_to_seq_meta l vs (n : nat) :
    length vs = n →
    ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
      [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
  Proof.
    iIntros (<-) "Hvs". iInduction vs as [|v vs] "IH" forall (l)=> //=.
    rewrite big_opM_union; last first.
    { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
      intros (j&?&Hjl&_)%heap_array_lookup.
      rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
    rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
    setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
    setoid_rewrite <-loc_add_assoc.
    rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
  Qed.

  Lemma heap_array_to_seq_mapsto l v (n : nat) :
    ([∗ map] l' ↦ v ∈ heap_array l (replicate n v), l' ↦ v) -∗
      [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v.
  Proof.
    iIntros "Hvs". iInduction n as [|n] "IH" forall (l); simpl.
    { done. }
    rewrite big_opM_union; last first.
    { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
      intros (j&?&Hjl&_)%heap_array_lookup.
      rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
    rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
    setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
    setoid_rewrite <-loc_add_assoc.
    rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
  Qed.

  Lemma wp_allocN_seq s E v n (Φ : expr → iProp Σ) :
    0 < n →
    ▷ (∀ (l:loc), ([∗ list] i ∈ seq 0 (Z.to_nat n),
                    (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤) -∗ Φ #l) -∗
      sswp s E (AllocN (Val $ LitV $ LitInt $ n) (Val v)) Φ (LM := LM).
  Proof.
    iIntros (HnO) "HΦ".
    rewrite /sswp. simpl.
    iIntros (σ) "Hσ".
    iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
    iSplit.
    { iPureIntro. destruct s; [|done]. apply head_prim_reducible. eauto. }
    iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
    iMod "Hclose".
    apply head_reducible_prim_step in Hstep; [|eauto].
    inv_head_step.
    iMod (gen_heap_alloc_big _ (heap_array l (replicate (Z.to_nat n) v)) with "Hσ")
      as "(Hσ & Hl & Hm)".
    { apply heap_array_map_disjoint.
      rewrite replicate_length Z2Nat.id ?Hexend; auto with lia. }
    iFrame.
    iModIntro.
    iSplit; [|done].
    iApply "HΦ".
    iApply big_sepL_sep. iSplitL "Hl".
    + by iApply heap_array_to_seq_mapsto.
    + iApply (heap_array_to_seq_meta with "Hm"). by rewrite replicate_length.
  Qed.

  Lemma wp_alloc s E v (Φ : expr → iProp Σ) :
    ▷ (∀ l, l ↦ v -∗ meta_token l ⊤ -∗ Φ (LitV (LitLoc l))) -∗
      sswp s E (Alloc v) Φ (LM := LM).
  Proof.
    iIntros "HΦ". iApply wp_allocN_seq; [lia|].
    iIntros "!>" (l) "[[Hl Hm] _]". rewrite loc_add_0.
    iApply ("HΦ" with "Hl Hm").
  Qed.
  
  Lemma wp_choose_nat s E (Φ : expr → iProp Σ) :
    ▷ (∀ (n:nat), Φ $ Val $ LitV (LitInt n)) -∗
      sswp s E ChooseNat Φ (LM := LM).
  Proof.
    iIntros "HΦ".
    rewrite /sswp. simpl.
    iIntros (σ) "Hσ".
    iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
    iSplit.
    { iPureIntro. destruct s; [|done]. apply head_prim_reducible. eauto. }
    iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
    iMod "Hclose".
    apply head_reducible_prim_step in Hstep; [|eauto].
    inv_head_step.
    iFrame.
    iModIntro.
    iSplit; [|done].
    iApply "HΦ".
    Unshelve. all: apply O.
  Qed.

  Lemma wp_load s E l q v (Φ : expr → iProp Σ) :
    ▷ l ↦{q} v -∗
      ▷ (l ↦{q} v -∗ Φ v) -∗
      sswp s E (Load (Val $ LitV $ LitLoc l)) Φ (LM := LM).
  Proof.
    iIntros ">Hl HΦ".
    rewrite /sswp. simpl.
    iIntros (σ) "Hσ".
    iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
    iDestruct (@gen_heap_valid with "Hσ Hl") as %Hheap.
    iSplit.
    { iPureIntro. destruct s; [|done]. apply head_prim_reducible. eauto. }
    iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
    iMod "Hclose".
    apply head_reducible_prim_step in Hstep; [|eauto].
    inv_head_step.
    iFrame.
    iModIntro.
    iSplit; [|done].
    by iApply "HΦ".
  Qed.

  Lemma wp_store s E l v' v (Φ : expr → iProp Σ) :
    ▷ l ↦ v' -∗
      ▷ (l ↦ v -∗ Φ $ LitV LitUnit) -∗
      sswp s E (Store (Val $ LitV (LitLoc l)) (Val v)) Φ (LM := LM).
  Proof.
    iIntros ">Hl HΦ". simpl.
    iIntros (σ1) "Hsi".
    iDestruct (gen_heap_valid with "Hsi Hl") as %Hheap.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit.
    { destruct s; [|done]. iPureIntro. apply head_prim_reducible. by eauto. }
    iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
    iMod "Hclose".
    iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
    iFrame.
    apply head_reducible_prim_step in Hstep; [|by eauto].
    inv_head_step. iFrame. iModIntro. iSplit; [|done]. by iApply "HΦ".
  Qed.

  Lemma wp_cmpxchg_fail s E l q v' v1 v2 (Φ : expr → iProp Σ) :
    v' ≠ v1 → vals_compare_safe v' v1 →
    ▷ l ↦{q} v' -∗
      ▷ (l ↦{q} v' -∗ Φ $ PairV v' (LitV $ LitBool false)) -∗
      sswp s E (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) Φ (LM := LM).
  Proof.
    iIntros (??) ">Hl HΦ". simpl.
    iIntros (σ1) "Hsi".
    iDestruct (gen_heap_valid with "Hsi Hl") as %Hheap.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit.
    { destruct s; [|done]. iPureIntro. apply head_prim_reducible. by eauto. }
    iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
    iMod "Hclose".
    iFrame.
    apply head_reducible_prim_step in Hstep; [|by eauto].
    inv_head_step.
    rewrite bool_decide_false //. iFrame. iModIntro.
    iSplit; [|done].
    by iApply "HΦ".
  Qed.
  
  Lemma wp_cmpxchg_suc s E l v' v1 v2 (Φ : expr → iProp Σ) :
    v' = v1 → vals_compare_safe v' v1 →
    ▷ l ↦ v' -∗
      ▷ (l ↦ v2 -∗ Φ $ PairV v' (LitV $ LitBool true)) -∗
      sswp s E (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) Φ (LM := LM).
  Proof.
    iIntros (??) ">Hl HΦ". simpl.
    iIntros (σ1) "Hsi".
    iDestruct (gen_heap_valid with "Hsi Hl") as %Hheap.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit.
    { destruct s; [|done]. iPureIntro. apply head_prim_reducible. by eauto. }
    iIntros (e2 σ2 efs Hstep). iIntros "!>!>!>".
    iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
    iMod "Hclose".
    iFrame.
    apply head_reducible_prim_step in Hstep; [|by eauto].
    inv_head_step.
    rewrite bool_decide_true //. iFrame. iModIntro.
    iSplit; [|done].
    by iApply "HΦ".
  Qed.

End SSWP.
