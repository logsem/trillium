From iris.algebra Require Import excl_auth.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import action_model resources fuel.
From trillium.fairness.heap_lang Require Import iris_inst. 


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
