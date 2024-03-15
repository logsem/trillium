From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From fairneris Require Import fairness fuel map_included_utils env_model.

Canonical Structure ModelO `{GoodLang Λ} (Mdl : UserModel Λ) := leibnizO Mdl.
Canonical Structure RoleO `{GoodLang Λ} (Mdl : UserModel Λ) := leibnizO (Mdl.(usr_role)).
Canonical Structure localeO (Λ : language) := leibnizO (locale Λ).

Class fairnessGpreS `{GoodLang Λ} `(LM: LiveModel Λ (joint_model M Net)) Σ := {
  fairnessGpreS_model :> inG Σ (authUR (optionUR (exclR (ModelO M))));
  fairnessGpreS_model_fuel_mapping :>
    inG Σ (authUR (gmapUR (localeO Λ)
                          (exclR $ gmapUR (RoleO M) natO)));
  fairnessGpreS_model_free_roles :> inG Σ (authUR (gset_disjUR (RoleO M)));
}.

Class fairnessGS `{GoodLang Λ} `(LM : LiveModel Λ (joint_model M Net)) Σ := FairnessGS {
  fairness_inG :> fairnessGpreS LM Σ;
  (** Underlying model *)
  fairness_model_name : gname;
  (** Mapping of threads to roles with fuel *)
  fairness_model_fuel_mapping_name : gname;
  (** Set of free/availble roles *)
  fairness_model_free_roles_name : gname;
}.

Global Arguments fairnessGS {_ _ _ _ _ _ _ _ _ _ _ _} LM Σ.
Global Arguments fairness_model_name {_ _ _ _ _ _ _ _ _ _ _ _ LM Σ} _.
Global Arguments fairness_model_fuel_mapping_name {Λ _ _ _ _ _ _ _ _ _ M Net LM Σ} _ : assert.
Global Arguments fairness_model_free_roles_name {Λ _ _ _ _ _ _ _ _ _ M Net LM Σ} _ : assert.

Definition fairnessΣ Λ `{GoodLang Λ} M : gFunctors := #[
   GFunctor (authUR (optionUR (exclR (ModelO M))));
   GFunctor (authUR (gmapUR (localeO Λ)
                            (exclR $ gmapUR (RoleO M) natO)));
   GFunctor (authUR (gset_disjUR (RoleO M)))
].

(* We need more parameters than the iris tactic supports... *)
Ltac solve_inG :=
  intros;
   lazymatch goal with
   | H:subG (?xΣ _ _ _ _ _ _ _ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _ _ _ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _ _ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _) _ |- _ => try unfold xΣ in H
   | H:subG ?xΣ _ |- _ => try unfold xΣ in H
   end;
  repeat match goal with
    | H:subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
  end;
  repeat match goal with
    | H:subG _ _ |- _ => move : (H) ; apply subG_inG in H || clear H
  end;
  intros; simpl in *; try assumption; split; assumption || by apply _.



Global Instance subG_fairnessGpreS {Σ} `{GoodLang Λ} `{LM : LiveModel Λ (joint_model M Net)}
       :
  subG (fairnessΣ Λ M) Σ -> fairnessGpreS LM Σ.
Proof. solve_inG. Qed.

Notation "f ⇂ R" := (filter (λ '(k,v), k ∈ R) f) (at level 30).

Lemma dom_domain_restrict `{Countable X} {A} (f: gmap X A) (R: gset X):
  R ⊆ dom f ->
  dom  (f ⇂ R) = R.
Proof.
  intros ?. apply dom_filter_L.
  intros i; split; [|set_solver].
  intros Hin. assert (Hin': i ∈ dom f) by set_solver.
  apply elem_of_dom in Hin' as [??]. set_solver.
Qed.

Lemma dom_domain_restrict_union_l `{Countable X} {A} (f: gmap X A) R1 R2:
  R1 ∪ R2 ⊆ dom f ->
  dom (f ⇂ R1) = R1.
Proof.
  intros ?. apply dom_domain_restrict. set_solver.
Qed.
Lemma dom_domain_restrict_union_r `{Countable X} {A} (f: gmap X A) R1 R2:
  R1 ∪ R2 ⊆ dom f ->
  dom (f ⇂ R2) = R2.
Proof.
  intros ?. apply dom_domain_restrict. set_solver.
Qed.

Section bigop_utils.
  Context `{Monoid M o}.
  Context `{Countable K}.

  Lemma big_opMS (g: gset K) (P: K -> M):
    ([^ o set] x ∈ g, P x) ≡ [^ o map] x ↦ y ∈ (mapset_car g), P x.
  Proof.
    rewrite big_opS_elements /elements /gset_elements /mapset_elements.
    rewrite big_opM_map_to_list.
    destruct g as [g]. simpl. rewrite big_opL_fmap.
    f_equiv.
  Qed.
End bigop_utils.

Section bigop_utils.
  Context `{Countable K} {A : cmra}.
  Implicit Types m : gmap K A.
  Implicit Types i : K.

  Lemma gset_to_gmap_singletons (a : A) (g : gset K):
    ([^op set] x ∈ g, {[x := a]}) ≡ gset_to_gmap a g.
  Proof.
    rewrite big_opMS.
    rewrite -(big_opM_singletons (gset_to_gmap a g)).
    rewrite /gset_to_gmap big_opM_fmap //.
  Qed.
End bigop_utils.

Section map_utils.
  Context `{Countable K, Countable V, EqDecision K}.

  Definition maps_inverse_match (m: gmap K V) (m': gmap V (gset K)) :=
    ∀ (k: K) (v: V), m !! k = Some v <-> ∃ (ks: gset K), m' !! v = Some ks ∧ k ∈ ks.

  Lemma no_locale_empty M M' ρ ζ:
    maps_inverse_match M M' ->
    M' !! ζ = Some ∅ ->
    M !! ρ ≠ Some ζ.
  Proof.
    intros Hinv Hem contra.
    destruct (Hinv ρ ζ) as [Hc _]. destruct (Hc contra) as (?&?&?).
    by simplify_eq.
  Qed.

  Lemma maps_inverse_bij M M' ρ X1 X2 ζ ζ':
    maps_inverse_match M M' ->
    M' !! ζ = Some X1 -> ρ ∈ X1 ->
    M' !! ζ' = Some X2 -> ρ ∈ X2 ->
    ζ = ζ'.
  Proof.
    intros Hinv Hζ Hρ Hζ' Hρ'.
    assert (M !! ρ = Some ζ); first by apply Hinv; eexists; done.
    assert (M !! ρ = Some ζ'); first by apply Hinv; eexists; done.
    congruence.
  Qed.

End map_utils.

Section fin_map_dom.
Context `{FinMapDom K M D}.
Lemma dom_empty_iff {A} (m : M A) : dom m ≡ ∅ ↔ m = ∅.
Proof.
  split; [|intros ->; by rewrite dom_empty].
  intros E. apply map_empty. intros. apply not_elem_of_dom.
  rewrite E. set_solver.
Qed.

Section leibniz.
  Context `{!LeibnizEquiv D}.
  Lemma dom_empty_iff_L {A} (m : M A) : dom m = ∅ ↔ m = ∅.
  Proof. unfold_leibniz. apply dom_empty_iff. Qed.
End leibniz.
End fin_map_dom.

Section map_imap.
  Context `{Countable K}.
  Lemma map_imap_dom_inclusion {A B} (f : K → A → option B) (m : gmap K A) :
    dom (map_imap f m) ⊆ dom m.
  Proof.
    intros i [k Hk]%elem_of_dom. rewrite map_lookup_imap in Hk.
    destruct (m !! i) eqn:?; last done.
    rewrite elem_of_dom. by eexists.
  Qed.
  Lemma map_imap_dom_eq {A B} (f : K → A → option B) (m : gmap K A) :
    (forall k a, k ∈ dom m -> is_Some (f k a)) ->
    dom (map_imap f m) = dom m.
  Proof.
    rewrite -leibniz_equiv_iff. intros HisSome i. split.
    - intros [x Hx]%elem_of_dom. rewrite map_lookup_imap in Hx.
      apply elem_of_dom. destruct (m !! i) eqn:Heq; eauto.
      by simpl in Hx.
    - intros [x Hx]%elem_of_dom.
      rewrite elem_of_dom map_lookup_imap Hx /=. apply HisSome, elem_of_dom. eauto.
  Qed.
End map_imap.

Section model_state_interp.
  Context `{GoodLang Λ}.
  Context `{LM: LiveModel Λ (joint_model M Net)}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.
  Context `{!invGS_gen HasNoLc Σ}.

  Notation Role := (usr_role M).

  Definition auth_fuel_mapping_is
             (m: gmap (locale Λ) (gmap Role nat)) : iProp Σ :=
    own (fairness_model_fuel_mapping_name fG)
        (● (fmap Excl m :
              ucmra_car (gmapUR _ (exclR $ gmapUR (RoleO M) natO)
        ))).

  Definition frag_fuel_mapping_is
             (m: gmap (locale Λ) (gmap Role nat)) : iProp Σ :=
    own (fairness_model_fuel_mapping_name fG)
        (◯ (fmap Excl m:
              ucmra_car (gmapUR _ (exclR $ gmapUR (RoleO M) natO)
        ))).

  Definition auth_model_is (fm: M): iProp Σ :=
    own (fairness_model_name fG) (● Excl' fm).

  Definition frag_model_is (fm: M): iProp Σ :=
    own (fairness_model_name fG) (◯ Excl' fm).

  Definition auth_free_roles_are (FR: gset Role): iProp Σ :=
    own (fairness_model_free_roles_name fG) (● (GSet FR)).

  Definition frag_free_roles_are (FR: gset Role): iProp Σ :=
    own (fairness_model_free_roles_name fG) (◯ (GSet FR)).

  Definition fuel_map_le_inner (m1 m2 : gmap (locale Λ) (gmap Role nat)) :=
    map_included (λ (fs1 fs2 : gmap Role nat),
                    map_included (≤) fs1 fs2) m1 m2.

  Definition fuel_map_le (m1 m2 : gmap (locale Λ) (gmap Role nat)) :=
    fuel_map_le_inner m1 m2 ∧
    (* OBS: This is a bit hacky, should instead change definition. *)
    dom m1 = dom m2.

  Definition fuel_map_preserve_dead
             (m : gmap (locale Λ) (gmap Role nat))
             (ρs : gset Role) :=
    ∀ ρ, ρ ∈ ρs → ∃ ζ fs, m !! ζ = Some fs ∧ ρ ∈ dom fs.

  Definition fuel_map_preserve_threadpool (tp: list $ expr Λ)
             (fuel_map : gmap (locale Λ) (gmap Role nat)) :=
     ∀ ζ, ζ ∉ locales_of_list tp → fuel_map !! ζ = None.

  Definition usr_state (δ : LiveStateData Λ (joint_model M Net)) : M := δ.(ls_under).1.
  Definition env_state (δ : LiveStateData Λ (joint_model M Net)) : Net := δ.(ls_under).2.

  Definition model_state_interp (c: cfg Λ) (δ: LiveStateData Λ (joint_model M Net)): iProp Σ :=
    ∃ fuel_map,
      ⌜ fuel_map_le fuel_map δ.(ls_map) ⌝ ∗
      ⌜ fuel_map_preserve_dead fuel_map (M.(usr_live_roles) (usr_state δ)) ⌝ ∗
      ⌜ fuel_map_preserve_threadpool c.1 fuel_map ⌝ ∗
      auth_model_is (usr_state δ) ∗ auth_fuel_mapping_is fuel_map ∗
      ⌜ env_states_match c (ls_under δ).2 ⌝.

  Lemma model_state_interp_tids_smaller (δ : LiveState _ _) c :
    model_state_interp c δ -∗ ⌜ tids_smaller c.1 δ ⌝.
  Proof.
    iIntros "(%m&[_ %Heq]&%&%Hbig&_)".
    iPureIntro.
    intros ζ Hin.
    assert (¬ (ζ ∉ locales_of_list c.1)).
    - intros contra.
      specialize (Hbig _ contra).
      rewrite -Heq elem_of_dom Hbig in Hin.
      inversion Hin. naive_solver.
    - destruct (decide (ζ ∈ locales_of_list c.1)) as [Hin'|] =>//.
      apply elem_of_list_fmap in Hin' as [[tp' e'] [-> Hin']].
      unfold from_locale. exists e'. by apply from_locale_from_Some.
  Qed.

End model_state_interp.

Lemma own_proper `{inG Σ X} γ (x y: X):
  x ≡ y ->
  own γ x -∗ own γ y.
Proof. intros ->. naive_solver. Qed.

Section model_state_lemmas.
  Context `{GoodLang Λ}.
  Context `{LM: LiveModel Λ (joint_model M Net)}.
  Context {Σ : gFunctors}.
  Context `{EqDecision (expr Λ)}.
  Context {fG: fairnessGS LM Σ}.

  Notation Role := (M.(usr_role)).

  Definition has_fuels (ζ: locale Λ) (fs: gmap Role nat) : iProp Σ :=
    frag_fuel_mapping_is {[ ζ := fs ]}.

  #[global] Instance has_fuels_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (has_fuels).
  Proof. solve_proper. Qed.

  #[global] Instance has_fuels_timeless (ζ: locale Λ) (fs: gmap Role nat):
    Timeless (has_fuels ζ fs).
  Proof. rewrite /has_fuels. apply _. Qed.

  Definition has_fuels_S (ζ: locale Λ) (fs: gmap Role nat): iProp Σ :=
    has_fuels ζ (S <$> fs).

  Definition has_fuels_plus (n: nat) (ζ: locale Λ) (fs: gmap Role nat): iProp Σ :=
    has_fuels ζ (fmap (fun m => n+m) fs).

  Lemma has_fuel_fuels_plus_1 (ζ: locale Λ) fs:
    has_fuels_plus 1 ζ fs ⊣⊢ has_fuels_S ζ fs.
  Proof.
    rewrite /has_fuels_plus /has_fuels_S. do 2 f_equiv.
    intros m m' ->. apply leibniz_equiv_iff. lia.
  Qed.

  Lemma has_fuel_fuels_plus_0 (ζ: locale Λ) fs:
    has_fuels_plus 0 ζ fs ⊣⊢ has_fuels ζ fs.
  Proof.
    rewrite /has_fuels_plus /=.  f_equiv. intros ?.
    rewrite lookup_fmap. apply leibniz_equiv_iff.
    destruct (fs !! i) eqn:Heq; rewrite Heq //.
  Qed.

  Lemma has_fuels_plus_split_S n (ζ: locale Λ) fs:
    has_fuels_plus (S n) ζ fs ⊣⊢ has_fuels_S ζ ((λ m, n + m) <$> fs).
  Proof.
    rewrite /has_fuels_plus /has_fuels_S. f_equiv.
    rewrite -map_fmap_compose /= => ρ.
    rewrite !lookup_fmap //.
  Qed.

End model_state_lemmas.

Notation "tid ↦M R" := (has_fuels tid R) (at level 20, format "tid  ↦M  R") : bi_scope.
Notation "tid ↦M++ R" := (has_fuels_S tid R) (at level 20, format "tid  ↦M++  R") : bi_scope.

Section adequacy.
  Context `{GoodLang Λ}.
  Context `{LM: LiveModel Λ (joint_model M Net)}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGpreS LM Σ}.

  Lemma model_state_init (s0: M) :
    ⊢ |==> ∃ γ,
        own (A := authUR (optionUR (exclR (ModelO M)))) γ
            (● (Excl' s0) ⋅ ◯ (Excl' s0)).
  Proof.
    iMod (own_alloc (● Excl' s0 ⋅ ◯ Excl' s0)) as (γ) "[Hfl Hfr]".
    { by apply auth_both_valid_2. }
    iExists _. by iSplitL "Hfl".
  Qed.

  Definition init_fuel_map (s0: M) (ζ0: locale Λ) :
    gmap (locale Λ) (exclR $ gmap (usr_role M) nat) :=
    {[ ζ0 := Excl (gset_to_gmap (usr_fl s0) (usr_live_roles s0)) ]}.

  Lemma model_fuel_mapping_init (s0: M) (ζ0: locale Λ) :
    ⊢ |==> ∃ γ,
      own γ (● (init_fuel_map s0 ζ0)) ∗
      own γ (◯ (init_fuel_map s0 ζ0)).
  Proof.
    iMod (own_alloc (● (init_fuel_map s0 ζ0) ⋅
                     ◯ (init_fuel_map s0 ζ0))) as (γ) "[Hfl Hfr]".
    { apply auth_both_valid_2; eauto. by apply singleton_valid. }
    iExists _. by iSplitL "Hfl".
  Qed.

  Lemma model_free_roles_init (s0: M) (FR: gset _):
    ⊢ |==> ∃ γ,
        own (A := authUR (gset_disjUR (RoleO M))) γ (● GSet FR  ⋅ ◯ GSet FR).
  Proof.
    iMod (own_alloc (● GSet FR  ⋅ ◯ GSet FR)) as (γ) "[H1 H2]".
    { apply auth_both_valid_2 =>//. }
    iExists _. by iSplitL "H1".
  Qed.
End adequacy.

Section model_state_lemmas.
  Context `{GoodLang Λ}.
  Context `{LM: LiveModel Λ (joint_model M Net)}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.
  Context `{!invGS_gen HasNoLc Σ}.
  Context `{EqDecision (expr Λ)}.

  Lemma update_model δ δ1 δ2:
    auth_model_is δ1 -∗ frag_model_is δ2 ==∗ auth_model_is δ ∗ frag_model_is δ.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    iMod (own_update with "H") as "[??]" ; eauto.
    - by apply auth_update, option_local_update, (exclusive_local_update _ (Excl δ)).
    - iModIntro. iFrame.
  Qed.

  Lemma model_agree s1 s2:
    auth_model_is s1 -∗ frag_model_is s2 -∗ ⌜ s1 = s2 ⌝.
  Proof.
    iIntros "Ha Hf".
      by iDestruct (own_valid_2 with "Ha Hf") as
          %[Heq%Excl_included%leibniz_equiv ?]%auth_both_valid_discrete.
  Qed.

  Lemma model_agree' δ1 s2 n:
    model_state_interp n δ1 -∗ frag_model_is s2 -∗ ⌜ (ls_under δ1).1 = s2 ⌝.
  Proof.
    iIntros "Hsi Hs2". iDestruct "Hsi" as "(%fm&?&_&_&Hs1&_)".
    iApply (model_agree with "Hs1 Hs2").
  Qed.

  Lemma has_fuels_agree (ζ : locale Λ) (fs : gmap (usr_role M) nat)
        (m : gmap (locale Λ) (gmap (usr_role M) nat)) :
    auth_fuel_mapping_is m -∗ has_fuels ζ fs -∗ ⌜m !! ζ = Some fs⌝.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
    iPureIntro.
    apply auth_both_valid_discrete in Hvalid as [Hincl Hvalid].
    rewrite fmap_insert fmap_empty in Hincl.
    rewrite lookup_included in Hincl.
    specialize (Hincl ζ).
    rewrite lookup_insert in Hincl.
    apply option_included in Hincl.
    destruct Hincl as [|Hincl]; [done|].
    destruct Hincl as (a&b&Ha&Hb&Hincl).
    simplify_eq.
    rewrite lookup_fmap_Some in Hb.
    destruct Hb as (b'&Heq&HSome).
    simplify_eq.
    rewrite HSome. f_equiv.
    destruct Hincl as [Hincl|Hincl].
    - naive_solver.
    - apply Some_included_mono in Hincl.
      rewrite Excl_included in Hincl.
      naive_solver.
  Qed.

  Lemma has_fuels_update fm ζ fs fs' :
    auth_fuel_mapping_is fm -∗ has_fuels ζ fs ==∗
    auth_fuel_mapping_is (<[ζ := fs']>fm) ∗ has_fuels ζ fs'.
  Proof.
    iIntros "Hfm Hfs".
    iDestruct (has_fuels_agree with "Hfm Hfs") as %Hagree.
    iMod (own_update_2 with "Hfm Hfs") as "[$ $]"; [|done].
    apply auth_update.
    rewrite !fmap_insert.
    rewrite !fmap_empty.
    rewrite -(insert_insert ∅ ζ (Excl fs') (Excl fs)).
    eapply insert_local_update; [| |].
    - rewrite lookup_fmap. rewrite Hagree. simpl. done.
    - simpl. rewrite lookup_insert. done.
    - eapply exclusive_local_update. done.
  Qed.

  Lemma has_fuels_decr (ζ : locale Λ) (fs : gmap (usr_role M) nat)
        (m : gmap (locale Λ) (gmap (usr_role M) nat)) :
    auth_fuel_mapping_is m -∗ has_fuels_S ζ fs ==∗
    auth_fuel_mapping_is (<[ζ := fs]>m) ∗ has_fuels ζ fs.
  Proof.
    iIntros "Hfm Hfs".
    iMod (has_fuels_update with "Hfm Hfs") as "[Hfm Hfs]".
    by iFrame.
  Qed.

  Lemma has_fuels_delete fs ζ ρs ρ :
    auth_fuel_mapping_is fs -∗ has_fuels ζ ρs ==∗
    auth_fuel_mapping_is (<[ζ := delete ρ ρs]>fs) ∗
    has_fuels ζ (delete ρ ρs).
  Proof.
    iIntros "Hfm Hfs".
    iMod (has_fuels_update with "Hfm Hfs") as "[Hfm Hfs]".
    by iFrame.
  Qed.

  Lemma model_state_interp_has_fuels_decr tp δ tid fs :
    model_state_interp tp δ -∗ has_fuels_S tid fs ==∗
    model_state_interp tp δ ∗ has_fuels tid fs.
  Proof.
    iDestruct 1 as "(%fm&[%Hfmle%Hdom]&%Hfmdead&%Htp&Hδ&Hfm&%Hsm)".
    iIntros "Hfs".
    iDestruct (has_fuels_agree with "Hfm Hfs") as %Hagree.
    iMod (has_fuels_decr with "Hfm Hfs") as "[Hfm Hfs]".
    iModIntro. iFrame "Hfs".
    iExists _. iFrame.
    iPureIntro. repeat split.
    - eapply map_included_transitivity; [|done].
      rewrite -{2}(insert_id fm tid (S <$> fs)); [|done].
      apply map_included_insert; [|apply map_included_refl].
      apply map_included_fmap. lia.
    - rewrite -Hdom. rewrite -{2}(insert_id fm tid (S <$> fs)); [set_solver|].
      done.
    - intros ρ Hin. apply Hfmdead in Hin as (ζ'&ρs&HSome&Hρ).
      destruct (decide (tid = ζ')) as [->|Hneq].
      + exists ζ', fs. rewrite lookup_insert.
        split; [done|]. set_solver.
      + exists ζ', ρs. rewrite lookup_insert_ne; [|done]. done.
    - intros ζ Hζ.
      specialize (Htp ζ Hζ).
      rewrite -(insert_id fm tid (S <$> fs)) in Htp; [|done].
      rewrite -not_elem_of_dom.
      rewrite -not_elem_of_dom in Htp.
      set_solver.
    - done.
  Qed.

  Lemma model_state_interp_has_fuels_dealloc tid fs ρ tp δ δ' :
    ρ ∉ usr_live_roles δ →
    model_state_interp tp δ' -∗
    frag_model_is δ -∗
    has_fuels tid fs ==∗
    model_state_interp tp δ' ∗ frag_model_is δ ∗ has_fuels tid (delete ρ fs).
  Proof.
    intros Hρ.
    destruct (decide (ρ ∈ dom fs)) as [Hin|Hnin]; last first.
    { assert (delete ρ fs = fs) as ->.
      { apply delete_notin. by rewrite -not_elem_of_dom. }
      by iIntros "$$$". }
    iDestruct 1 as "(%fm&[%Hfmle%Hdom]&%Hfmdead&%Htp&Hm&Hfm&%Hsm)".
    iIntros "Hst Hfs".
    iDestruct (model_agree with "Hm Hst") as %Heq. rewrite !Heq.
    assert (is_Some (fs !! ρ)) as [f HSome].
    { by rewrite -elem_of_dom. }
    iDestruct (has_fuels_agree with "Hfm Hfs") as %Hagree.
    iMod (has_fuels_delete with "Hfm Hfs") as "[Hfm Hfs]".
    iModIntro.
    iFrame "Hst". iFrame "Hfs".
    iExists _. iFrame. rewrite Heq. iFrame.
    iPureIntro.
    repeat split; try done.
    - rewrite /fuel_map_le.
      eapply map_included_transitivity; [|done].
      rewrite -{2}(insert_id fm tid fs); [|done].
      apply map_included_insert; [|apply map_included_refl].
      eapply map_included_subseteq; [|done].
      apply delete_subseteq.
    - rewrite dom_insert_L.
      assert (tid ∈ dom fm).
      { by apply elem_of_dom. }
      set_solver.
    - rewrite /fuel_map_preserve_dead.
      intros ρ' Hρ'.
      assert (ρ ≠ ρ') by set_solver.
      rewrite /fuel_map_preserve_dead in Hfmdead.
      rewrite Heq in Hfmdead.
      apply Hfmdead in Hρ' as (ζ&ρs&HSome'&Hρs).
      destruct (decide (tid = ζ)) as [->|Hneq].
      + exists ζ, (delete ρ fs).
        rewrite lookup_insert. set_solver.
      + exists ζ, ρs. rewrite lookup_insert_ne; [|done].
        set_solver.
    - intros ζ Hζ. specialize (Htp ζ Hζ).
      rewrite -not_elem_of_dom.
      rewrite -not_elem_of_dom in Htp.
      assert (ζ ≠ tid).
      { intros ->.
        assert (tid ∈ dom fm).
        { rewrite elem_of_dom. by set_solver. }
        set_solver. }
      set_solver.
  Qed.

  (* TODO: Move this *)
  Lemma silent_step_suff_data_weak act fl `(δ: LiveState Λ (joint_model M Net))
        (fs fs' : gmap _ nat) ζ:
    δ.(ls_map) !! ζ = Some fs →
    fs ≠ ∅ →
    map_included (<) fs' fs →
    (dom fs ∖ dom fs') ∩ usr_live_roles (usr_state δ) = ∅ →
    ∃ δ', δ'.(ls_data) =
          {| ls_under := δ;
            ls_map := <[ζ := fs']> δ.(ls_map) |} ∧
            ls_trans fl δ (Silent_step ζ act) δ'.
  Proof.
    intros.
    apply (silent_step_suff_data fl δ fs fs' ∅ ζ None); try done.
    - rewrite -> map_included_spec in *. done.
    - set_solver.
    - set_solver.
  Qed.

  (* TODO: Change original lemma to not existentially quantify new state *)
  Lemma silent_step_suff_data_weak_alt act fl (δ δ' : LiveState Λ (joint_model M Net))
        (fs fs' : gmap _ nat) ζ :
    δ.(ls_under) = δ'.(ls_under) →
    δ.(ls_map) !! ζ = Some fs →
    δ'.(ls_map) = <[ζ := fs']>δ.(ls_map) →
    fs ≠ ∅ →
    map_included (<) fs' fs →
    (dom fs ∖ dom fs') ∩ usr_live_roles (usr_state δ) = ∅ →
    ls_trans fl δ (Silent_step ζ act) δ'.
  Proof.
    rewrite map_included_spec. intros Hδ Hfs Hfs' Hne Hle Hlive.
    assert (∃ δ', δ'.(ls_data) =
          {| ls_under := δ;
            ls_map := <[ζ := fs']> δ.(ls_map) |} ∧
            ls_trans fl δ (Silent_step ζ act) δ') as (δ''&Heq&Htrans).
    { apply (silent_step_suff_data fl δ fs fs' ∅ ζ None); try set_solver. }
    rewrite Heq Hδ -Hfs' in Htrans. by destruct δ', ls_data.
  Qed.

  Definition model_can_fuel_step (δ1 : LM) (ζ : locale Λ) (δ2 : LM) : Prop :=
    ∃ fs1 fs2,
      δ1.(ls_under) = δ2.(ls_under) ∧
      δ1.(ls_map) !! ζ = Some fs1 ∧
      δ2.(ls_map) = <[ζ := fs2]>δ1.(ls_map) ∧
      fs1 ≠ ∅ ∧
      map_included (<) fs2 fs1 ∧
      (dom fs1 ∖ dom fs2) ∩ usr_live_roles (usr_state δ1) = ∅.

  Lemma model_can_fuel_step_trans act fl ζ (δ δ' : LiveState Λ _) :
    model_can_fuel_step δ ζ δ' → ls_trans fl δ (Silent_step ζ act) δ'.
  Proof.
    destruct 1 as (?&?&?&?&?&?&?&?). by eapply silent_step_suff_data_weak_alt.
  Qed.

  Definition decr_fuel_map (fs : gmap (usr_role M) nat) : gmap (usr_role M) nat :=
    (λ f, f - 1) <$> fs.

  Lemma decr_fuel_map_included fs : map_included (≤) (decr_fuel_map fs) fs.
  Proof.
    apply map_included_spec. intros k v1 Hm.
    apply lookup_fmap_Some in Hm as [v2 [Hv2 Hm]].
    exists v2. split; [done|lia].
  Qed.

  Definition filter_fuel_map
             (δ: LiveState Λ (joint_model M Net)) (ρs : gset (usr_role M)) (fs : gmap (usr_role M) nat) :
      gmap (usr_role M) nat :=
    (filter (λ ρf, ρf.1 ∈ usr_live_roles (usr_state δ) ∨ ρf.1 ∈ ρs)) fs.

  Lemma filter_fuel_map_included δ ρs fs :
    map_included (≤) (filter_fuel_map δ ρs fs) fs.
  Proof.
    apply map_included_spec.
    intros k v1 Hm.
    exists v1. split; [|lia].
    pose proof (map_filter_subseteq
                  (λ ρf : usr_role M * nat, ρf.1 ∈ usr_live_roles (usr_state δ) ∨ ρf.1 ∈ ρs) fs)
      as Hle.
    rewrite map_subseteq_spec in Hle.
    by apply Hle.
  Qed.

  Definition model_update_locale_role_map
          δ (ρs : gset (usr_role M)) : gmap (usr_role M) nat → gmap (usr_role M) nat :=
    decr_fuel_map ∘ filter_fuel_map δ ρs.

  Lemma model_update_locale_role_map_map_included δ ρs fs :
    map_included (≤) (model_update_locale_role_map δ ρs fs) fs.
  Proof.
    rewrite /model_update_locale_role_map.
    eapply map_included_transitivity;
      [eapply decr_fuel_map_included|eapply filter_fuel_map_included].
  Qed.

  Definition model_update_locale_fuel_map
          δ (ζ : locale Λ) (ρs : gset (usr_role M))
          (fm : gmap (locale Λ) (gmap (usr_role M) nat)) :
      gmap (locale Λ) (gmap (usr_role M) nat) :=
    <[ζ:= model_update_locale_role_map δ ρs (fm !!! ζ)]>fm.

  Program Definition model_update_decr (ζ : locale Λ) (δ : LM) : LM :=
    {|
      ls_data :=
        {| ls_under := δ.(ls_under);
           ls_map := alter (fmap (λ f, f - 1)) ζ δ.(ls_map); |};
    |}.
  Next Obligation.
    intros ζ δ ζ1 ζ2 fs1 fs2 Hneq HSome1 HSome2.
    simpl in *.
    pose proof δ.(ls_map_disj) as Hdisj.
    assert (∃ fs1', map_included (≤) fs1 fs1' ∧ ls_map δ !!! ζ1 = fs1')
      as (fs1' & Hle1 & Hfs1').
    { destruct (decide (ζ = ζ1)) as [<-|Hneq'].
      + rewrite lookup_alter in HSome1.
        rewrite -lookup_fmap in HSome1.
        apply lookup_fmap_Some in HSome1 as (fs1'&Hfs1'&HSome1').
        simplify_eq.
        exists fs1'. rewrite lookup_total_alt. simpl. rewrite HSome1'.
        split; [apply decr_fuel_map_included|done].
      + rewrite lookup_alter_ne in HSome1; [|done].
        rewrite lookup_total_alt. eexists _.
        split; [done|by rewrite HSome1]. }
    assert (∃ fs2', map_included (≤) fs2 fs2' ∧ ls_map δ !!! ζ2 = fs2')
      as (fs2' & Hle2 & Hfs2').
    { destruct (decide (ζ = ζ2)) as [<-|Hneq'].
      + rewrite lookup_alter in HSome2.
        rewrite -lookup_fmap in HSome2.
        apply lookup_fmap_Some in HSome2 as (fs2'&Hfs2'&HSome2').
        simplify_eq.
        exists fs2'. rewrite lookup_total_alt. simpl. rewrite HSome2'.
        split; [apply decr_fuel_map_included|done].
      + rewrite lookup_alter_ne in HSome2; [|done].
        rewrite lookup_total_alt. eexists _.
        split; [done|by rewrite HSome2]. }
    rewrite lookup_total_alt in Hfs1'.
    rewrite lookup_total_alt in Hfs2'.
    destruct (ls_map δ !! ζ1) as [fs1''|] eqn:Hfs1''; last first.
    { apply map_included_subseteq_inv in Hle1.
      apply map_disjoint_dom.
      rewrite Hfs1'' /= in Hfs1'. simplify_eq. set_solver. }
    destruct (ls_map δ !! ζ2) as [fs2''|] eqn:Hfs2''; last first.
    { apply map_included_subseteq_inv in Hle2.
      apply map_disjoint_dom. rewrite Hfs2'' in Hfs2'. set_solver. }
    simplify_eq; simpl in *.
    specialize (Hdisj ζ1 ζ2 fs1'' fs2'' Hneq Hfs1'' Hfs2'').
    apply map_disjoint_spec.
    rewrite map_disjoint_spec in Hdisj.
    intros i x y HSome1' HSome2'.
    rewrite map_included_spec in Hle1.
    apply Hle1 in HSome1' as (?&?&?).
    rewrite map_included_spec in Hle2.
    apply Hle2 in HSome2' as (?&?&?).
    rewrite -> Hfs1'', Hfs2'' in *.
    by eapply Hdisj.
  Qed.
  Next Obligation.
    intros ζ δ ρ Hlive.
    simpl in *.
    pose proof Hlive as Hlive'.
    apply (ls_map_live δ) in Hlive as (ζ' & fs & HSome & Hdom).
    destruct (decide (ζ = ζ')) as [<-|Hneq].
    - eexists ζ, _.
      rewrite lookup_alter. rewrite HSome. simpl.
      split; [done|].
      rewrite dom_fmap. done.
    - eexists ζ', fs. by rewrite lookup_alter_ne.
  Qed.

  Program Definition model_update_filter
          (ζ : locale Λ) (ρs : gset (usr_role M)) (δ : LM) : LM :=
    {|
      ls_data :=
        {| ls_under := δ.(ls_under);
           ls_map :=
             alter (filter
                       (λ ρf, ρf.1 ∈ usr_live_roles (usr_state δ) ∨ ρf.1 ∈ ρs))
                       ζ δ.(ls_map); |};
    |}.
  Next Obligation.
    intros ζ ρs δ ζ1 ζ2 fs1 fs2 Hneq HSome1 HSome2.
    simpl in *.
    pose proof δ.(ls_map_disj) as Hdisj.
    assert (∃ fs1', map_included (≤) fs1 fs1' ∧ ls_map δ !!! ζ1 = fs1')
      as (fs1' & Hle1 & Hfs1').
    { destruct (decide (ζ = ζ1)) as [<-|Hneq'].
      + rewrite lookup_alter in HSome1.
        rewrite -lookup_fmap in HSome1.
        apply lookup_fmap_Some in HSome1 as (fs1'&Hfs1'&HSome1').
        simplify_eq.
        exists fs1'. rewrite lookup_total_alt. simpl. rewrite HSome1'.
        split; [apply filter_fuel_map_included|done].
      + rewrite lookup_alter_ne in HSome1; [|done].
        rewrite lookup_total_alt. eexists _.
        split; [done|by rewrite HSome1]. }
    assert (∃ fs2', map_included (≤) fs2 fs2' ∧ ls_map δ !!! ζ2 = fs2')
      as (fs2' & Hle2 & Hfs2').
    { destruct (decide (ζ = ζ2)) as [<-|Hneq'].
      + rewrite lookup_alter in HSome2.
        rewrite -lookup_fmap in HSome2.
        apply lookup_fmap_Some in HSome2 as (fs2'&Hfs2'&HSome2').
        simplify_eq.
        exists fs2'. rewrite lookup_total_alt. simpl. rewrite HSome2'.
        split; [apply filter_fuel_map_included|done].
      + rewrite lookup_alter_ne in HSome2; [|done].
        rewrite lookup_total_alt. eexists _.
        split; [done|by rewrite HSome2]. }
    rewrite lookup_total_alt in Hfs1'.
    rewrite lookup_total_alt in Hfs2'.
    destruct (ls_map δ !! ζ1) as [fs1''|] eqn:Hfs1''; last first.
    { apply map_included_subseteq_inv in Hle1.
      apply map_disjoint_dom. rewrite Hfs1'' in Hfs1'. set_solver. }
    destruct (ls_map δ !! ζ2) as [fs2''|] eqn:Hfs2''; last first.
    { apply map_included_subseteq_inv in Hle2.
      apply map_disjoint_dom. rewrite Hfs2'' in Hfs2'. set_solver. }
    simplify_eq; simpl in *.
    specialize (Hdisj ζ1 ζ2 fs1'' fs2'' Hneq Hfs1'' Hfs2'').
    apply map_disjoint_spec.
    rewrite map_disjoint_spec in Hdisj.
    intros i x y HSome1' HSome2'.
    rewrite map_included_spec in Hle1.
    apply Hle1 in HSome1' as (?&?&?).
    rewrite map_included_spec in Hle2.
    apply Hle2 in HSome2' as (?&?&?).
    rewrite -> Hfs1'', Hfs2'' in *.
    by eapply Hdisj.
  Qed.
  Next Obligation.
    intros ζ ρs δ ρ Hlive.
    simpl in *.
    pose proof Hlive as Hlive'.
    apply (ls_map_live δ) in Hlive as (ζ' & fs & HSome & Hdom).
    destruct (decide (ζ = ζ')) as [<-|Hneq].
    - eexists ζ, _.
      rewrite lookup_alter. rewrite HSome. simpl.
      split; [done|].
      rewrite map_filter_or.
      rewrite dom_union_L.
      apply elem_of_union. left.
      apply elem_of_dom.
      apply elem_of_dom in Hdom as [f Heq]. exists f.
      by apply map_lookup_filter_Some_2.
    - eexists ζ', fs. by rewrite lookup_alter_ne.
  Qed.

  Definition model_update_locale_fuel
             (δ : LM) (ζ : locale Λ) (ρs : gset (usr_role M)) : LM :=
    model_update_decr ζ $ model_update_filter ζ ρs δ.

  Lemma model_update_locale_spec extr (auxtr : auxiliary_trace LM) ζ c2 ρs:
    valid_state_evolution_fairness extr auxtr →
    model_can_fuel_step (trace_last auxtr) ζ ((model_update_locale_fuel (trace_last auxtr) ζ) ρs) →
    tids_smaller c2.1 (model_update_locale_fuel (trace_last auxtr) ζ ρs) →
    locale_step (trace_last extr) (inl (ζ, None)) c2 →
    valid_state_evolution_fairness
      (extr :tr[inl (ζ, None)]: c2)
      (auxtr :tr[Silent_step ζ None]:
          (model_update_locale_fuel (trace_last auxtr) ζ) ρs).
  Proof.
    intros Hvse Hstep Htids Hexstep. destruct c2 as [tp σ].
    destruct Hvse as (?&?&?).
    split; [| split]=>//.
    econstructor=>//; first by apply model_can_fuel_step_trans.
  Qed.

  Definition map_disj (m : gmap (locale Λ) (gmap (usr_role M) nat)) :=
    ∀ ζ ζ' fs fs', ζ ≠ ζ' → m !! ζ = Some fs → m !! ζ' = Some fs' → fs ##ₘ fs'.

  Lemma decr_succ_compose_id : (λ f : nat, f - 1) ∘ S = id.
  Proof. apply FunExt. intros x. simpl. lia. Qed.

  Definition map_inner_disj `{Countable K1} `{Countable K2} {V}
             (m : gmap K1 (gmap K2 V)) :=
    ∀ (k1 k2 : K1) (vs1 vs2 : gmap K2 V),
      k1 ≠ k2 → m !! k1 = Some vs1 → m !! k2 = Some vs2 → vs1 ##ₘ vs2.

  Lemma fuel_map_le_disj ζ1 ζ2 fm fs1 fs2 ρ
        (fuel_map : gmap (locale Λ) (gmap (usr_role M) nat)) :
    fuel_map_le_inner fm fuel_map → map_inner_disj fuel_map →
    fm !! ζ1 = Some fs1 → fm !! ζ2 = Some fs2 →
    ρ ∈ dom fs1 → ρ ∈ dom fs2 →
    ζ1 = ζ2 ∧ fs1 = fs2.
  Proof.
    intros Hle Hdisj HSome1 HSome2 [f1 Hf1]%elem_of_dom [f2 Hf2]%elem_of_dom.
    destruct (decide (ζ1 = ζ2)) as [->|Hneq].
    { simplify_eq. set_solver. }
    rewrite /fuel_map_le_inner map_included_spec in Hle.
    apply Hle in HSome1 as (fs1'&Hfs1'&Hle1).
    apply Hle in HSome2 as (fs2'&Hfs2'&Hle2).
    assert (ρ ∈ dom fs1') as [??]%elem_of_dom.
    { apply elem_of_dom. rewrite map_included_spec in Hle1.
      by apply Hle1 in Hf1 as (?&?&?). }
    assert (ρ ∈ dom fs2') as [??]%elem_of_dom.
    { apply elem_of_dom. rewrite map_included_spec in Hle2.
      by apply Hle2 in Hf2 as (?&?&?). }
    exfalso. rewrite /map_inner_disj in Hdisj.
    specialize (Hdisj ζ1 ζ2 fs1' fs2' Hneq Hfs1' Hfs2').
    rewrite map_disjoint_spec in Hdisj. by eapply Hdisj.
  Qed.

  Lemma fuel_map_le_disj' ζ1 ζ2 fm fs1 fs2 fs1' fs2' ρ
        (fuel_map : gmap (locale Λ) (gmap (usr_role M) nat)) :
    fuel_map_le_inner fm fuel_map → map_inner_disj fuel_map →
    fm !! ζ1 = Some fs1 → fm !! ζ2 = Some fs2 →
    fuel_map !! ζ1 = Some fs1' → fuel_map !! ζ2 = Some fs2' →
    ρ ∈ dom fs1' → ρ ∈ dom fs2' →
    ζ1 = ζ2 ∧ fs1 = fs2.
  Proof.
    intros Hle Hdisj HSome1 HSome2 HSome1' HSome2'
           [f1 Hf1]%elem_of_dom [f2 Hf2]%elem_of_dom.
    destruct (decide (ζ1 = ζ2)) as [->|Hneq].
    { simplify_eq. set_solver. }
    rewrite /fuel_map_le_inner map_included_spec in Hle.
    exfalso. rewrite /map_inner_disj in Hdisj.
    specialize (Hdisj ζ1 ζ2 fs1' fs2' Hneq HSome1' HSome2').
    rewrite map_disjoint_spec in Hdisj. by eapply Hdisj.
  Qed.

  (* TODO: Clean up *)
  Lemma fuel_map_le_live_roles fm fm' (lρs : gset (usr_role M)) ζ ρs ρs' ρ :
    map_inner_disj fm' → fuel_map_le_inner fm fm' →
    fuel_map_preserve_dead fm lρs →
    fm !! ζ = Some ρs → fm' !! ζ = Some ρs' →
    ρ ∈ lρs → ρ ∈ dom ρs' →
    ρ ∈ dom ρs.
  Proof.
    intros Hdisj Hfmle Hfmdead Hρ Hρs' Hlive [f Hf]%elem_of_dom.
    rewrite /fuel_map_le_inner map_included_spec in Hfmle.
    apply Hfmdead in Hlive as (ζ'&fs'&Hfs'&Hv2').
    assert (dom ρs = dom fs') as Heq.
    { f_equiv. pose proof Hfs' as Hfs''. apply Hfmle in Hfs'' as (fs''&?&Hfs'').
      eapply (fuel_map_le_disj' ζ ζ' fm ρs fs' ρs' fs'' ρ
                                fm'); try done.
      - rewrite /fuel_map_le_inner map_included_spec. apply Hfmle.
      - by apply elem_of_dom.
      - rewrite map_included_spec in Hfs''.
        apply elem_of_dom in Hv2' as [? Hsome].
        apply Hfs'' in Hsome. destruct Hsome as (?&?&?).
        by apply elem_of_dom. }
    set_solver.
  Qed.

  Lemma model_state_interp_can_fuel_step es (δ : LiveState _ _) ζ fs :
    fs ≠ ∅ → model_state_interp es δ -∗ has_fuels_S ζ fs -∗
    ⌜model_can_fuel_step δ ζ ((model_update_locale_fuel δ ζ) (dom fs))⌝.
  Proof.
    iIntros (Hfs) "Hm Hfs".
    iDestruct "Hm" as "(%fm&[%Hfmle%Hdom]&%Hfmdead&%Htp&Hm&Hfm&%Hsm)".
    rewrite /model_can_fuel_step.
    iDestruct (has_fuels_agree with "Hfm Hfs") as %Hagree.
    rewrite /fuel_map_le /fuel_map_le_inner map_included_spec in Hfmle.
    pose proof Hagree as Hagree'.
    apply Hfmle in Hagree as [v2 [HSome Hle]].
    iPureIntro.
    exists v2. exists (model_update_locale_role_map δ (dom fs) v2).
    repeat split; try done.
    - simpl. rewrite -alter_compose.
      rewrite -alter_insert. f_equiv; [done|by rewrite insert_id].
    - assert (dom fs ⊆ dom v2).
      { erewrite <-dom_fmap_L. by eapply map_included_subseteq_inv. }
      rewrite -dom_empty_iff_L.
      rewrite -dom_empty_iff_L in Hfs.
      set_solver.
    - clear Htp Hfs. pose proof δ.(ls_map_disj) as Hdisj.
      apply map_included_spec.
      rewrite map_included_spec in Hle.
      intros k v1 Hv2.
      rewrite /model_update_locale_role_map lookup_fmap in Hv2.
      apply fmap_Some in Hv2 as [? [Hv2 ->]].
      pose proof Hv2 as Hv2'%map_lookup_filter_Some_1_2. simpl in *.
      apply map_lookup_filter_Some_1_1 in Hv2.
      assert (k ∈ dom fs) as Hv2''.
      { destruct Hv2' as [Hv2'|Hv2']; [|done].
        rewrite -(dom_fmap_L S fs).
        eapply (fuel_map_le_live_roles _ δ.(ls_map)); [| |done..|].
        - intros ???????. eapply Hdisj; try done.
        - rewrite /fuel_map_le_inner map_included_spec. apply Hfmle.
        - by apply elem_of_dom. }
      rewrite -(dom_fmap_L S) in Hv2''.
      apply elem_of_dom in Hv2'' as [f Heq].
      pose proof Heq as Heq'.
      apply lookup_fmap_Some in Heq' as [f' [<- ?]].
      apply Hle in Heq as [f'' [Heq Hle']].
      exists f''. split; [done|].
      destruct f''; [lia|].
      simplify_eq. lia.
    - rewrite /model_update_locale_role_map.
      simpl.
      rewrite dom_fmap_L.
      clear.
      induction v2 using map_ind.
      { set_solver. }
      rewrite /filter_fuel_map.
      rewrite map_filter_insert. simpl.
      case_decide.
      + set_solver.
      + rewrite -dom_difference_L.
        rewrite map_filter_delete.
        rewrite -insert_difference.
        set_solver.
  Qed.

  Lemma fuel_map_le_fuel_step fm ζ fs (δ:LM) :
    fm !! ζ = Some (S <$> fs) →
    fuel_map_le fm (ls_map δ) →
    fuel_map_le (<[ζ:=fs]> fm) (ls_map (model_update_locale_fuel δ ζ (dom fs))).
  Proof.
    intros Hagree [Hfmle Hfmdom].
    split; [|by apply elem_of_dom_2 in Hagree; set_solver].
    rewrite /model_update_locale_fuel=> /=.
    pose proof Hfmle as Hfmle'. rewrite /fuel_map_le_inner map_included_spec in Hfmle'.
    apply Hfmle' in Hagree as [ρs [HSome Hρs]].
    rewrite -(insert_id (ls_map δ) ζ ρs); [|done].
    rewrite -alter_compose alter_insert=> /=.
    apply map_included_insert; [|done].
    (* OBS: The remaining proof can likely be decomposed into library lemmas *)
    clear Hfmle Hfmle' HSome Hfmdom.
    apply map_included_spec.
    intros ρ f1 Hρ.
    rewrite map_included_spec in Hρs.
    assert ((S <$> fs) !! ρ = Some (S f1)) as Hρ'; [by rewrite lookup_fmap Hρ|].
    specialize (Hρs ρ (S f1) Hρ') as [v2 [Hv2 Hle]].
    destruct v2; [lia|]. exists v2. split; [|lia].
    rewrite !lookup_fmap map_lookup_filter Hv2=> /=.
    destruct (decide (ρ ∈ usr_live_roles (usr_state δ) ∨ ρ ∈ dom fs)) as [Hin|Hnin].
    + rewrite option_guard_True; [|done]. simpl. f_equiv. lia.
    + apply Decidable.not_or in Hnin. destruct Hnin as [Hnin1 Hnin2].
      apply not_elem_of_dom in Hnin2. set_solver.
  Qed.

  Lemma fuel_map_preserve_dead_fuel_step fm ζ fs (δ:LM) :
    fm !! ζ = Some (S <$> fs) →
    fuel_map_preserve_dead fm
      (usr_live_roles $ usr_state $ model_update_locale_fuel δ ζ (dom fs)) →
    fuel_map_preserve_dead (<[ζ:=fs]> fm)
      (usr_live_roles $ usr_state $ (model_update_locale_fuel δ ζ (dom fs))).
  Proof.
    intros Hagree Hfmdead ρ Hin. apply Hfmdead in Hin as (ζ'&ρs&HSome&Hρ).
    destruct (decide (ζ = ζ')) as [<-|Hneq].
    + exists ζ, fs. rewrite lookup_insert. by set_solver.
    + exists ζ', ρs. rewrite lookup_insert_ne; [by set_solver|done].
  Qed.

  Lemma fuel_map_preserve_threadpool_fuel_step
        act c1 ζ c2 (fm1 fm2 : gmap _ (gmap (usr_role M) nat)) :
    dom fm1 = dom fm2 → locale_step c1 (inl (ζ, act)) c2 →
    fuel_map_preserve_threadpool c1.1 fm1 →
    fuel_map_preserve_threadpool c2.1 fm2.
  Proof.
    rewrite /fuel_map_preserve_threadpool.
    intros Hdom Hstep Htp. intros ζ' Hζ'. destruct c1, c2.
    apply locales_of_list_step_incl in Hstep.
    assert (ζ' ∉ locales_of_list l) as Hζ'' by set_solver.
    apply Htp in Hζ''.
    rewrite -not_elem_of_dom. rewrite -not_elem_of_dom in Hζ''.
    set_solver.
  Qed.

  Lemma model_state_interp_fuel_update act c1 c2 (δ : LiveState _ (joint_model M Net)) ζ fs :
    locale_step c1 (inl (ζ, act)) c2 →
    env_states_match c2 (ls_under δ).2 →
    model_state_interp c1 δ -∗
    has_fuels_S ζ fs ==∗
    model_state_interp c2 (model_update_locale_fuel δ ζ (dom fs)) ∗
    has_fuels ζ fs.
  Proof.
    iIntros (Hstep Hm) "Hm Hfs".
    iDestruct "Hm" as "(%fm&[%Hfmle%Hdom]&%Hfmdead&%Htp&Hm&Hfm&%Hsm)".
    iDestruct (has_fuels_agree with "Hfm Hfs") as %Hagree.
    iMod (has_fuels_decr with "Hfm Hfs") as "[Hfm $]".
    iModIntro. iExists _. iFrame. iPureIntro.
    split; [|split; [|split; [|done]]].
    - by apply fuel_map_le_fuel_step.
    - by apply fuel_map_preserve_dead_fuel_step.
    - eapply fuel_map_preserve_threadpool_fuel_step; [|done..].
      apply elem_of_dom_2 in Hagree. by set_solver.
  Qed.

  Lemma model_interp_states_match c (δ : LiveState _ (joint_model M Net)) :
    model_state_interp c δ -∗ ⌜ env_states_match c (ls_under δ).2 ⌝.
  Proof.
    by iIntros "(%fm&[%Hfmle%Hdom]&%Hfmdead&%Htp&Hm&Hfm&%Hsm)"; iPureIntro.
  Qed.

  Lemma update_fuel_step extr (auxtr : auxiliary_trace LM) c2 fs ζ :
    fs ≠ ∅ →
    locale_step (trace_last extr) (inl (ζ, None)) c2 →
    has_fuels_S ζ fs -∗
    ⌜ valid_state_evolution_fairness extr auxtr ⌝ -∗
    model_state_interp (trace_last extr) (trace_last auxtr) ==∗
    ∃ δ2,
      ⌜ valid_state_evolution_fairness
        (extr :tr[inl (ζ, None)]: c2) (auxtr :tr[Silent_step ζ None]: δ2) ⌝ ∗
      has_fuels ζ fs ∗ model_state_interp c2 δ2.
  Proof.
    iIntros (Hdom Hstep) "Hfuel %Hvse Hm".
    iExists (model_update_locale_fuel (trace_last auxtr) ζ (dom fs)).
    iDestruct (model_state_interp_can_fuel_step with "Hm Hfuel") as %Hcan_step;
      [done|].
    iDestruct (model_interp_states_match _ _ with "Hm") as %?.
    iMod (model_state_interp_fuel_update with "Hm Hfuel") as "[Hm Hfuel]";
      [done.. | by eapply env_match_internal_step|].
    iDestruct (model_state_interp_tids_smaller with "Hm") as %Htids.
    iModIntro.
    iFrame "Hm Hfuel".
    iPureIntro. apply model_update_locale_spec=>//.
  Qed.

  (** Model step *)

  (* OBS: Maybe use fuel limit instead of generic [f] *)
  Program Definition model_update_set (ζ : locale Λ) (ρ : usr_role M) (f : nat) (δ : LM) : LM :=
    {|
      ls_data :=
        {| ls_under := δ.(ls_under);
           ls_map := alter (alter (λ _, f) ρ) ζ δ.(ls_map); |};
    |}.
  Next Obligation.
    intros ζ ρ f δ ζ1 ζ2 fs1 fs2 Hneq HSome1 HSome2. simpl in *.
    pose proof (δ.(ls_map_disj)) as Hdisj.
    apply lookup_alter_Some in HSome1.
    apply lookup_alter_Some in HSome2.
    destruct HSome1 as [[-> [fs1' [HSome1 ->]]]|[_ HSome1]],
               HSome2 as [[-> [fs2' [HSome2 ->]]]|[_ HSome2]];
               [done| | |].
    - specialize (Hdisj ζ1 ζ2 _ _ Hneq HSome1 HSome2).
      rewrite map_disjoint_dom dom_alter_L.
      rewrite map_disjoint_dom in Hdisj. set_solver.
    - specialize (Hdisj ζ1 ζ2 _ _ Hneq HSome1 HSome2).
      rewrite map_disjoint_dom dom_alter_L.
      rewrite map_disjoint_dom in Hdisj. set_solver.
    - by eapply Hdisj.
  Qed.
  Next Obligation.
    intros ζ ρ f δ ρ' Hρ'. simpl in *.
    pose proof (δ.(ls_map_live)) as Hlive.
    apply Hlive in Hρ' as (ζ'&fs'&HSome&Hρ').
    destruct (decide (ζ = ζ')) as [<-|Hneq].
    - eexists ζ, _. rewrite lookup_alter HSome. split; [done|].
      by rewrite dom_alter_L.
    - eexists ζ', _. by rewrite lookup_alter_ne.
  Qed.

  Definition model_update_state (δ2 : joint_model M Net) (δ1 : LiveStateData Λ (joint_model M Net)) :
    LiveStateData Λ _ :=
    {| ls_under := δ2;
      ls_map := δ1.(ls_map); |}.

  Lemma model_update_state_valid (δ2 : joint_model M Net) (δ1 : LM) :
    usr_live_roles δ2.1 ⊆ usr_live_roles (usr_state δ1) →
    ∃ δ, (ls_data δ) = model_update_state δ2 δ1.
  Proof.
    intros Hle.
    assert (∀ ζ ζ' fs fs',
              ζ ≠ ζ' → (model_update_state δ2 δ1).(ls_map) !! ζ = Some fs →
              (model_update_state δ2 δ1).(ls_map) !! ζ' = Some fs' → fs ##ₘ fs') as Hdisj'.
    { intros. by eapply (δ1.(ls_map_disj)). }
    assert (∀ ρ, ρ ∈ usr_live_roles $ usr_state (model_update_state δ2 δ1) →
                 ∃ ζ fs, (model_update_state δ2 δ1).(ls_map) !! ζ = Some fs ∧ ρ ∈ dom fs) as Hlive'.
    { pose proof (δ1.(ls_map_live)) as Hlive.
      intros.
      assert (ρ ∈ usr_live_roles (usr_state δ1)) as Hin by set_solver.
      apply Hlive in Hin as (?&?&?&?). eexists _, _. done. }
    exists
      {| ls_data := model_update_state δ2 δ1;
         ls_map_disj := Hdisj';
         ls_map_live := Hlive' |}.
    done.
  Qed.

  Definition model_update_model_step
          (ζ : locale Λ) (ρs : gset (usr_role M)) ρ δ2 (δ : LM) :=
    model_update_state δ2 $ model_update_set ζ ρ (fm_fl δ2) $ model_update_decr ζ $ model_update_filter ζ ρs δ.

  Lemma model_update_model_step_valid (ζ : locale Λ) (ρs : gset (usr_role M)) ρ s2 (δ1:LM) :
    usr_live_roles s2.1 ⊆ usr_live_roles (usr_state δ1) →
    ∃ δ, (ls_data δ) = model_update_model_step ζ ρs ρ s2 δ1.
  Proof. intros. by apply model_update_state_valid. Qed.

  Lemma model_update s1 s2 s3 :
    auth_model_is s1 -∗ frag_model_is s2 ==∗
    auth_model_is s3 ∗ frag_model_is s3.
  Proof.
    iIntros "Hauth Hfrag".
    iMod (own_update_2 with "Hauth Hfrag") as "[$ $]"; [|done].
    apply auth_update. apply option_local_update.
    by eapply exclusive_local_update.
  Qed.

  Lemma alter_insert_alt `{Countable K} {A} (m : gmap K A) i f x :
    m !! i = Some x → alter f i m = <[i := f x]> m.
  Proof.
    intros. rewrite -{1}(insert_id m i x); [|done]. apply alter_insert.
  Qed.

  (* OBS: Need to make frag model abstract *)
  Lemma model_state_interp_model_step_update (ρ : usr_role M)
        fmact act
        (fs : gmap (usr_role M) nat) tp1 tp2
        (δ δ2 : LM) ζ σ1 σ2 (f1 : nat) (s1 s2 : joint_model M Net) :
    ρ ∉ dom fs →
    usr_live_roles s2.1 ⊆ usr_live_roles s1.1 →
    locale_step (tp1, σ1) (inl (ζ, act)) (tp2, σ2) →
    env_states_match (tp2, σ2) (ls_under δ2).2 →
    fmtrans _ s1 (inl (ρ, fmact)) s2 →
    (ls_data δ2) = model_update_model_step ζ ({[ρ]} ∪ dom fs) ρ s2 δ →
    model_state_interp (tp1, σ1) δ -∗
    has_fuels ζ ({[ρ := f1]} ∪ (S <$> fs)) -∗
    frag_model_is s1.1 ==∗
    model_state_interp (tp2, σ2) δ2 ∗
    has_fuels ζ ({[ρ := fm_fl s2]} ∪ fs) ∗
    frag_model_is s2.1.
  Proof.
    iIntros (Hfs Hlive Hstep Hsm2 Hmstep Hδ2) "Hm Hf Hs".
    iDestruct "Hm" as "(%fm&%Hfmle&%Hfmdead&%Htp&Hm&Hfm&%Hsm1)".
    iDestruct (has_fuels_agree with "Hfm Hf") as %Hagree.
    iMod (has_fuels_update _ _ _ ({[ρ := fm_fl s2]} ∪ fs) with "Hfm Hf")
      as "[Hfm Hf]".
    iDestruct (model_agree with "Hm Hs") as %Heq.
    iMod (model_update _ _ s2.1 with "Hm Hs") as "[Hm Hs]".
    iModIntro. iFrame. iExists _. iFrame.
    rewrite Hδ2. iFrame.
    iPureIntro.
    split; [|split; [|split]].
    - split; last first.
      { simpl.
        destruct Hfmle as [Hfmle Hdom].
        pose proof Hfmle as Hfmle'.
        rewrite /fuel_map_le /fuel_map_le_inner map_included_spec in Hfmle.
        pose proof Hagree as Hagree'.
        apply Hfmle in Hagree' as (fs'&HSome&Hfs').
        rewrite -(insert_id (ls_map δ) ζ fs'); [|done].
        rewrite !alter_insert.
        set_solver. }
      simpl.
      destruct Hfmle as [Hfmle Hdom].
      pose proof Hfmle as Hfmle'.
      rewrite /fuel_map_le /fuel_map_le_inner map_included_spec in Hfmle.
      pose proof Hagree as Hagree'.
      apply Hfmle in Hagree' as (fs'&HSome&Hfs').
      rewrite -(insert_id (ls_map δ) ζ fs'); [|done].
      rewrite !alter_insert.
      apply map_included_insert; [|done].
      assert ({[ρ := usr_fl s2.1]} ∪ fs =
              (alter (λ _ : nat, fm_fl s2) ρ
                     ((λ f : nat, f - 1) <$>
                                         (filter
                                            (λ ρf : usr_role M * nat, ρf.1 ∈ usr_live_roles (usr_state δ) ∨ ρf.1 ∈ {[ρ]} ∪ dom fs)
                                            ({[ρ := f1]} ∪ (S <$> fs)))))) as ->.
      { rewrite -!insert_union_singleton_l.
        rewrite map_filter_insert. simpl.
        case_decide; [|set_solver].
        rewrite fmap_insert. rewrite alter_insert. f_equiv.
        rewrite map_filter_fmap.
        rewrite -map_fmap_compose.
        rewrite decr_succ_compose_id.
        rewrite map_fmap_id.
        rewrite map_filter_id; [done|].
        intros i x Hin. apply elem_of_dom_2 in Hin. set_solver. }
      apply map_included_mono_strong; [set_solver..| |].
      { intros k x1 x2 y1 y2 Hx1 Hx2 Hy1 Hy2 HR.
        destruct (decide (k = ρ)) as [->|Hneq].
        - erewrite alter_insert_alt in Hy1; [|done].
          erewrite alter_insert_alt in Hy2; [|done].
          rewrite lookup_insert in Hy1.
          rewrite lookup_insert in Hy2. by simplify_eq.
        - rewrite lookup_alter_ne in Hy1; [|done].
          rewrite lookup_alter_ne in Hy2; [|done].
          by simplify_eq. }
      apply map_included_mono_strong; [set_solver..| |].
      { intros k x1 x2 y1 y2 Hx1 Hx2 Hy1 Hy2 HR.
        apply lookup_fmap_Some in Hy1 as (y1'&Hy1'&Hy1).
        apply lookup_fmap_Some in Hy2 as (y2'&Hy2'&Hy2).
        simplify_eq. lia. }
      apply map_included_filter; [set_solver..|].
      done.
    - apply elem_of_subseteq in Hlive.
      intros ρ' Hin.
      apply Hlive in Hin.
      rewrite Heq in Hfmdead.
      apply Hfmdead in Hin as (ζ'&ρs&HSome&Hρ).
      destruct (decide (ζ = ζ')) as [<-|Hneq].
      + eexists ζ, _. rewrite lookup_insert. split; [done|]. by set_solver.
      + eexists ζ', _. rewrite lookup_insert_ne; [|done].
        split; [done|]. by set_solver.
    - rewrite /fuel_map_preserve_threadpool.
      intros ζ' Hζ'.
      apply locales_of_list_step_incl in Hstep.
      assert (ζ' ∉ locales_of_list tp1) as Hζ'' by set_solver.
      apply Htp in Hζ''.
      rewrite -not_elem_of_dom. rewrite -not_elem_of_dom in Hζ''.
      rewrite dom_insert_L.
      rewrite -(insert_id fm ζ ({[ρ := f1]} ∪ (S <$> fs))) in Hζ''; [|done].
      rewrite dom_insert_L in Hζ''.
      set_solver.
    - rewrite Hδ2 // in Hsm2.
  Qed.

  Lemma model_step_suff_data_weak_alt (δ1 δ2 : LiveState Λ (joint_model M Net)) ρ fmact act
        (fs fs': gmap _ nat) ζ :
    fmtrans _ δ1 (inl (ρ, fmact)) δ2 →
    usr_live_roles (usr_state δ2) ⊆ usr_live_roles (usr_state δ1) →
    δ1.(ls_map) !! ζ = Some fs →
    δ2.(ls_map) = <[ζ := fs']> δ1.(ls_map) →
    ρ ∈ dom fs →
    fs' !! ρ = Some (fm_fl (ls_under δ2)) →
    map_included (<) (delete ρ fs') fs →
    (dom fs ∖ dom fs' ∩ usr_live_roles (usr_state δ1) = ∅) →
    ls_trans fm_fl δ1 (Take_step ρ fmact ζ act) δ2.
  Proof.
    intros Hstep Hlive Hfs Hfs' Hρ Hρ' Hlt Hlive'.
    assert (∃ (δ'': LiveState Λ _), δ''.(ls_data) =
          {| ls_under := ls_under δ2;
            ls_map := <[ζ := fs']> δ1.(ls_map) |} ∧
            ls_trans fm_fl δ1 (Take_step ρ fmact ζ act) δ'') as (δ''&Heq&Htrans).
    { eapply (model_step_suff_data); try done.
      - rewrite map_included_spec in Hlt.
        intros ρ' f f' Hf' Hneq Hf.
        rewrite -(lookup_delete_ne _ ρ ρ') in Hf'; [|done].
        apply Hlt in Hf' as (?&?&?). by simplify_eq.
      - set_solver.
      - apply map_included_subseteq_inv in Hlt. set_solver.
      - apply map_included_subseteq_inv in Hlt. set_solver.
      - set_solver. }
    rewrite Heq -Hfs' in Htrans. by destruct δ2, ls_data.
  Qed.

  Definition model_can_model_step (δ1 : LM) (ζ : locale Λ) (ρ : usr_role M) (δ2 : LM) fmact : Prop :=
    ∃ (fs fs' : gmap (usr_role M) nat),
      fmtrans _ δ1 (inl (ρ, fmact)) δ2 ∧
      usr_live_roles (usr_state δ2) ⊆ usr_live_roles (usr_state δ1) ∧
      δ1.(ls_map) !! ζ = Some fs ∧
      δ2.(ls_map) = <[ζ := fs']> δ1.(ls_map) ∧
      ρ ∈ dom fs ∧
      fs' !! ρ = Some (fm_fl (ls_under δ2)) ∧
      map_included (<) (delete ρ fs') fs ∧
      (dom fs ∖ dom fs' ∩ usr_live_roles (usr_state δ1) = ∅).

  Lemma model_can_model_step_trans ζ (ρ : fmrole (joint_model M Net))
    (δ δ' : LiveState Λ (joint_model M Net)) fmact act:
    model_can_model_step δ ζ ρ δ' fmact → ls_trans fm_fl δ (Take_step ρ fmact ζ act) δ'.
  Proof.
    destruct 1 as (?&?&?&?&?&?&?&?&?&?).
    by eapply model_step_suff_data_weak_alt.
  Qed.

  Lemma model_state_interp_can_model_step es (δ δ2 : LM) ζ ρ f fmact
        (fs : gmap (usr_role M) nat) (s1 s2 : joint_model M Net) :
    fmtrans _ s1 (inl (ρ, fmact)) s2 →
    usr_live_roles s2.1 ⊆ usr_live_roles s1.1 →
    ρ ∉ dom fs →
    env_state δ = s1.2 →
    (ls_data δ2) = model_update_model_step ζ ({[ρ]} ∪ dom fs) ρ s2 δ →
    model_state_interp es δ -∗
    has_fuels ζ ({[ρ := f]} ∪ (S <$> fs)) -∗
    frag_model_is s1.1 -∗
    ⌜model_can_model_step δ ζ ρ δ2 fmact⌝.
  Proof.
    iIntros (Hstep Hle Hρ Henv Hδ2) "Hm Hf Hδ".
    iDestruct "Hm" as "(%fm&%Hfmle&%Hfmdead&%Htp&Hm&Hfm&%Hsm)".
    iDestruct (model_agree with "Hm Hδ") as %Heq.
    have Heq': δ.(ls_under) = s1.
    { destruct δ as [[[??] ?] ]. simpl in *.
      rewrite /usr_state /= in Heq. rewrite /env_state /= in Henv.
      rewrite Henv Heq. by destruct s1. }
    iDestruct (has_fuels_agree with "Hfm Hf") as %Hagree.
    iPureIntro.
    rewrite /fuel_map_le /fuel_map_le_inner map_included_spec in Hfmle.
    pose proof Hagree as Hagree'.
    apply Hfmle in Hagree as (fs'&Hζ&Hfs').
    assert (ρ ∈ dom fs') as Hρ'.
    { apply map_included_subseteq_inv in Hfs'. set_solver. }
    eexists _, _. repeat split; try done.
    - rewrite Hδ2 Heq' //.
    - rewrite !Heq Hδ2 //.
    - rewrite Hδ2. simpl. rewrite -!alter_compose.
      rewrite -{1}(insert_id (ls_map δ) ζ fs'); [|done].
      rewrite alter_insert.
      f_equiv.
      done.
    - rewrite Hδ2. simpl. rewrite lookup_alter. rewrite lookup_fmap.
      apply elem_of_dom in Hρ' as [f' Hlk].
      rewrite map_lookup_filter.
      rewrite Hlk. simpl.
      rewrite option_guard_True; [done|].
      set_solver.
    - rewrite map_included_spec.
      intros ρ' f' HSome.
      assert (ρ ≠ ρ').
      { intros Heqρ. rewrite Heqρ in HSome.
        by rewrite lookup_delete in HSome. }
      rewrite lookup_delete_ne in HSome; [|done].
      exists (f' + 1).
      split; [|lia].
      simpl in *.
      rewrite lookup_alter_ne in HSome; [|done].
      rewrite lookup_fmap in HSome.
      rewrite map_lookup_filter in HSome. simpl in *.
      destruct (fs' !! ρ') eqn:Heqn; [|done].
      simpl in *.
      destruct (decide (ρ' ∈ usr_live_roles (usr_state δ) ∨ ρ' ∈ {[ρ]} ∪ dom fs)) as [Hin|Hnin].
      + rewrite option_guard_True in HSome; [|done].
        simpl in *. simplify_eq. f_equiv.
        assert (ρ' ∈ dom ({[ρ := f]} ∪ (S <$> fs))) as Hin'.
        { destruct Hin as [Hin|Hin]; [|set_solver].
          eapply (fuel_map_le_live_roles _ δ.(ls_map)); [| |done..|].
          - intros ???????. by eapply δ.(ls_map_disj).
          - rewrite /fuel_map_le_inner map_included_spec. apply Hfmle.
          - by apply elem_of_dom. }
        rewrite dom_union_L in Hin'.
        apply elem_of_union in Hin' as [Hin'|Hin']; [set_solver|].
        apply elem_of_dom in Hin' as [v2 Hv2].
        rewrite map_included_spec in Hfs'.
        specialize (Hfs' ρ' v2).
        rewrite lookup_union_r in Hfs'; [|by rewrite lookup_insert_ne].
        destruct v2.
        { apply lookup_fmap_Some in Hv2 as (?&?&?). lia. }
        apply Hfs' in Hv2 as (n'&Hn'&Hn'').
        simplify_eq.
        lia.
      + by rewrite option_guard_False in HSome.
    - (* TODO: Make a lemma for this *)
      simpl.
      rewrite dom_alter_L.
      rewrite dom_fmap_L.
      clear.
      induction fs' using map_ind.
      { set_solver. }
      rewrite /filter_fuel_map.
      rewrite map_filter_insert. simpl.
      case_decide.
      + set_solver.
      + rewrite -dom_difference_L.
        rewrite map_filter_delete.
        rewrite -insert_difference.
        set_solver.
  Qed.

  Lemma model_update_locale_spec_model_step extr
        (auxtr : auxiliary_trace LM) ζ c2 ρs (ρ : fmrole (joint_model M Net)) δ2 s2 fmact act :
    (ls_data δ2) = model_update_model_step ζ ({[ρ]} ∪ ρs) ρ s2
                                           (trace_last auxtr) →
    model_can_model_step (trace_last auxtr) ζ ρ δ2 fmact →
    valid_state_evolution_fairness extr auxtr →
    tids_smaller c2.1 δ2 →
    valid_state_evolution_fairness
      (extr :tr[inl (ζ, act)]: c2)
      (auxtr :tr[Take_step ρ fmact ζ act]: δ2).
  Proof.
    intros Hstep Htids Hvse. destruct c2.
    destruct Hvse as (?&?&?).
    split; [| split]=>//.
    econstructor=>//; first by apply model_can_model_step_trans.
  Qed.

  (* Lemma update_model_step *)
  (*       (extr : execution_trace Λ) *)
  (*       (auxtr: auxiliary_trace LM) c2 (s1 s2 : joint_model M Net) fs ρ (δ1 : LM) ζ f fmact act : *)
  (*   usr_live_roles s2.1 ⊆ usr_live_roles s1.1 → *)
  (*   ρ ∉ dom fs → *)
  (*   trace_last auxtr = δ1 → *)
  (*   locale_step (trace_last extr) (inl (ζ, act)) c2 → *)
  (*   env_states_match c2  → *)
  (*   fmtrans _ s1 (inl (ρ, fmact)) s2 → *)
  (*   env_state δ1 = s1.2 → *)
  (*   has_fuels ζ ({[ρ := f]} ∪ (S <$> fs)) -∗ frag_model_is s1.1 -∗ *)
  (*   ⌜valid_state_evolution_fairness extr auxtr⌝ -∗ *)
  (*   model_state_interp (trace_last extr) δ1 ==∗ *)
  (*   ∃ (δ2: LM), *)
  (*     ⌜valid_state_evolution_fairness *)
  (*       (extr :tr[inl (ζ, act)]: c2) (auxtr :tr[Take_step ρ fmact ζ act]: δ2)⌝ ∗ *)
  (*     has_fuels ζ ({[ρ := fm_fl s2]} ∪ fs) ∗ *)
  (*     frag_model_is s2.1 ∗ model_state_interp c2 δ2. *)
  (* Proof. *)
  (*   iIntros (Hlive Hdom Hlast Hstep Htrans Henv) "Hfuel Hfrag %Hvse Hm". *)
  (*   iDestruct (model_agree' with "Hm Hfrag") as %Heq. *)
  (*   pose proof (model_update_model_step_valid *)
  (*                 ζ ({[ρ]} ∪ dom fs) ρ s2 δ1) as [δ2 Hδ2]. *)
  (*   { rewrite /usr_state Heq //. } *)
  (*   iExists δ2. *)
  (*   iDestruct (model_state_interp_can_model_step with "Hm Hfuel Hfrag") *)
  (*     as %Hcan_step; [try done..|]. *)
  (*   destruct (trace_last extr), c2. *)
  (*   iMod (model_state_interp_model_step_update with "Hm Hfuel Hfrag") *)
  (*     as "(Hm&Hf&Hfrag)"; [try done..|]. *)
  (*   { rewrite Hδ2 //=. } *)
  (*   iDestruct (model_state_interp_tids_smaller with "Hm") as %Htids. *)
  (*   iModIntro. *)
  (*   iFrame "Hm Hf Hfrag". *)
  (*   iPureIntro. subst. *)
  (*   by eapply model_update_locale_spec_model_step. *)
  (* Qed. *)

  (** Fork step *)

  Definition has_forked (tp1 tp2 : list (expr Λ)) e : Prop :=
    ∃ tp1', tp2 = tp1' ++ [e] ∧ locales_equiv tp1 tp1'.

  Definition model_update_split
             (ζ ζf : locale Λ) (ρs : gset (usr_role M))
             (δ : LiveStateData Λ (joint_model M Net)) : LiveStateData Λ _ :=
    {| ls_under := δ.(ls_under);
       ls_map := <[ζf := (filter (λ ρf, ρf.1 ∈ ρs)) (δ.(ls_map) !!! ζ)]>
                   (alter (filter (λ ρf, ρf.1 ∉ ρs)) ζ δ.(ls_map)); |}.

  Definition map_live (ρs : gset (usr_role M))
             (m : gmap (locale Λ) (gmap (usr_role M) nat)) : Prop :=
    ∀ ρ, ρ ∈ ρs → ∃ ζ fs, m !! ζ = Some fs ∧ ρ ∈ dom fs.

  Lemma disjoint_subseteq `{Countable A} (xs1 xs2 ys1 ys2 : gset A) :
    xs1 ⊆ xs2 → ys1 ⊆ ys2 → xs2 ## ys2 → xs1 ## ys1.
  Proof.
    intros Hle1 Hle2 Hdisj x Hxs Hys.
    eapply Hdisj; [by apply Hle1|by apply Hle2].
  Qed.

  Lemma disjoint_subseteq_l `{Countable A} (xs ys zs : gset A) :
    xs ⊆ ys → ys ## zs → xs ## zs.
  Proof. intros Hle Hdisj x Hxs Hzs. eapply Hdisj; [by apply Hle|done]. Qed.

  Lemma disjoint_subseteq_r `{Countable A} (xs ys zs : gset A) :
    zs ⊆ ys → xs ## ys → xs ## zs.
  Proof. intros Hle Hdisj x Hxs Hzs. eapply Hdisj; [done|by apply Hle]. Qed.

  Lemma model_update_split_valid ζ ζf ρs (δ1 : LM) :
    ζ ∈ dom δ1.(ls_map) → ζf ∉ dom δ1.(ls_map) →
    ∃ δ2, (ls_data δ2) = model_update_split ζ ζf ρs δ1.
  Proof.
    intros [ρs' HSome]%elem_of_dom Hnin.
    set δ2 := model_update_split ζ ζf ρs δ1.
    assert (ζ ≠ ζf) as Hneq.
    { intros ->. apply not_elem_of_dom in Hnin. set_solver. }
    assert (map_inner_disj δ2.(ls_map)) as Hdisj.
    { simpl.
      pose proof δ1.(ls_map_disj) as Hdisj.
      intros ζ1 ζ2 ρs1 ρs2 Hneq' HSome1 HSome2.
      destruct (decide (ζf = ζ1)) as [<-|Hneqf1].
      { rewrite lookup_insert in HSome1.
        rewrite lookup_insert_ne in HSome2; [|done].
        rewrite lookup_total_alt in HSome1.
        rewrite HSome in HSome1.
        simpl in *.
        destruct (decide (ζ = ζ2)) as [<-|Hneq2].
        { rewrite lookup_alter in HSome2.
          rewrite HSome in HSome2. simpl in *. simplify_eq.
          apply map_disjoint_dom.
          pose proof (disjoint_filter_complement
                        (λ ρ : usr_role M, ρ ∈ ρs) (dom ρs')) as Hcomp.
          by rewrite !filter_dom_L in Hcomp. }
        rewrite lookup_alter_ne in HSome2; [|done].
        simplify_eq.
        apply map_disjoint_dom.
        pose proof (Hdisj ζ ζ2 _ _ Hneq2 HSome HSome2) as Hdisj.
        apply map_disjoint_dom in Hdisj.
        eapply disjoint_subseteq_l; [|done].
        apply dom_filter_subseteq. }
      rewrite lookup_insert_ne in HSome1; [|done].
      destruct (decide (ζf = ζ2)) as [<-|Hneqf2].
      { rewrite lookup_insert in HSome2.
        destruct (decide (ζ = ζ1)) as [<-|Hneq2].
        { rewrite lookup_alter in HSome1.
          rewrite lookup_total_alt in HSome2.
          rewrite HSome in HSome1.
          rewrite HSome in HSome2.
          simpl in *. simplify_eq.
          apply map_disjoint_dom.
          pose proof (disjoint_filter_complement
                        (λ ρ : usr_role M, ρ ∈ ρs) (dom ρs')) as Hcomp.
          by rewrite !filter_dom_L in Hcomp. }
        rewrite lookup_alter_ne in HSome1; [|done].
        rewrite lookup_total_alt in HSome2.
        rewrite HSome in HSome2.
        simpl in *. simplify_eq.
        pose proof (Hdisj ζ ζ1 _ _ Hneq2 HSome HSome1) as Hdisj.
        apply map_disjoint_dom.
        apply map_disjoint_dom in Hdisj.
        eapply disjoint_subseteq_r; [|done].
        apply dom_filter_subseteq. }
      destruct (decide (ζ = ζ1)) as [<-|Hneq1].
      { rewrite lookup_alter in HSome1.
        rewrite lookup_insert_ne in HSome2; [|done].
        rewrite lookup_alter_ne in HSome2; [|done].
        rewrite HSome in HSome1.
        simpl in *. simplify_eq.
        pose proof (Hdisj ζ ζ2 _ _ Hneq' HSome HSome2) as Hdisj.
        apply map_disjoint_dom.
        apply map_disjoint_dom in Hdisj.
        eapply disjoint_subseteq_l; [|done].
        apply dom_filter_subseteq. }
      destruct (decide (ζ = ζ2)) as [<-|Hneq2].
      { rewrite lookup_alter_ne in HSome1; [|done].
        rewrite lookup_insert_ne in HSome2; [|done].
        rewrite lookup_alter in HSome2.
        rewrite HSome in HSome2.
        simpl in *. simplify_eq.
        pose proof (Hdisj ζ ζ1 _ _ Hneq1 HSome HSome1) as Hdisj.
        apply map_disjoint_dom.
        apply map_disjoint_dom in Hdisj.
        eapply disjoint_subseteq_r; [|done].
        apply dom_filter_subseteq. }
      rewrite lookup_alter_ne in HSome1; [|done].
      rewrite lookup_insert_ne in HSome2; [|done].
      rewrite lookup_alter_ne in HSome2; [|done].
      pose proof (Hdisj ζ1 ζ2 _ _ Hneq' HSome1 HSome2).
      done. }
    assert (map_live (usr_live_roles (usr_state δ2)) δ2.(ls_map)) as Hlive.
    { intros ρ Hin.
      pose proof (δ1.(ls_map_live)) as Hlive.
      apply Hlive in Hin as (ζ'&fs&HSome'&Hin').
      destruct (decide (ζ' = ζf)) as [->|Hneqf].
      { apply not_elem_of_dom in Hnin. set_solver. }
      destruct (decide (ζ' = ζ)) as [->|Hneq'].
      { rewrite HSome in HSome'. simplify_eq.
        simpl.
        destruct (decide (ρ ∈ ρs)) as [Hin|Hnin'].
        - exists ζf, (filter (λ ρf : usr_role M * nat, ρf.1 ∈ ρs) fs).
          rewrite lookup_insert. rewrite lookup_total_alt. rewrite HSome. simpl.
          split; [done|].
          apply elem_of_dom. rewrite /is_Some.
          apply elem_of_dom in Hin' as [??].
          eexists _. by apply map_lookup_filter_Some_2.
        - exists ζ, (filter (λ ρf : usr_role M * nat, ρf.1 ∉ ρs) fs).
          rewrite lookup_insert_ne; [|done].
          rewrite lookup_alter. rewrite HSome. simpl.
          split; [done|].
          apply elem_of_dom. rewrite /is_Some.
          apply elem_of_dom in Hin' as [??].
          eexists _. by apply map_lookup_filter_Some_2. }
      exists ζ', fs. split; [|done].
      simpl. rewrite !lookup_insert_ne; [|done].
      rewrite lookup_alter_ne; [|done].
      done. }
    by exists
      {| ls_data := δ2;
         ls_map_disj := Hdisj;
         ls_map_live := Hlive |}.
  Qed.

  Definition model_update_fork
          (ζ : locale Λ) (ζf : locale Λ)
          (ρs1 ρs2 : gset (usr_role M)) (δ : LM) :
      LiveStateData Λ _ :=
    model_update_split ζ ζf ρs2 $
    model_update_decr ζ $
    model_update_filter ζ ρs1 δ.

  Lemma model_update_fork_valid
        ζ ζf (ρs1 ρs2 : gset (usr_role M)) (δ1 : LM) :
    ζ ∈ dom δ1.(ls_map) → ζf ∉ dom δ1.(ls_map) →
    ∃ δ2, (ls_data δ2) = model_update_fork ζ ζf ρs1 ρs2 δ1.
  Proof. intros ??. by apply model_update_split_valid; set_solver. Qed.

  Lemma has_fuels_alloc fm ζ fs :
    ζ ∉ dom fm →
    auth_fuel_mapping_is fm ==∗
    auth_fuel_mapping_is (<[ζ := fs]>fm) ∗ has_fuels ζ fs.
  Proof.
    iIntros (Hnin) "Hfm".
    rewrite /has_fuels_S.
    iMod (own_update with "Hfm") as "[$ $]"; [|done].
    apply auth_update_alloc.
    rewrite !fmap_insert.
    rewrite !fmap_empty.
    eapply alloc_local_update; [|done].
    apply not_elem_of_dom in Hnin. by rewrite lookup_fmap Hnin.
  Qed.

  Lemma has_fuels_split fm ζ ζf fs1 fs2 :
    ζf ∉ dom fm → fs1 ##ₘ fs2 →
    auth_fuel_mapping_is fm -∗ has_fuels ζ (fs1 ∪ fs2) ==∗
    auth_fuel_mapping_is (<[ζf := fs2]>(<[ζ := fs1]>fm)) ∗
    has_fuels ζ fs1 ∗ has_fuels ζf fs2.
  Proof.
    iIntros (Hnin Hdisj) "Hfm Hfs".
    iDestruct (has_fuels_agree with "Hfm Hfs") as %HSome.
    assert (ζ ≠ ζf) as Hneq.
    { rewrite not_elem_of_dom in Hnin. set_solver. }
    iMod (has_fuels_update with "Hfm Hfs") as "[Hfm $]".
    iMod (has_fuels_alloc with "Hfm") as "[$$]"; set_solver.
  Qed.

  Lemma not_elem_of_locale_of_from_list (tp : list $ expr Λ) e :
    locale_of tp e ∉ locales_of_list tp.
  Proof.
    unfold locales_of_list_from.
    intros Habs.
    apply elem_of_list_fmap in Habs as ((tp1&e1) & Hlo & Hpf).
    apply (prefixes_from_spec [] tp e1 tp1) in Hpf as (tp2&tp3&He1&He2).
    simplify_eq.
    list_simplifier.

    have Hdone: (tp2 ++ e1 :: tp3, e) ∈ prefixes_from (tp2++[e1]) (tp3 ++ [e]).
    { apply prefixes_from_spec. eexists _, _. list_simplifier. naive_solver. }
    by apply locale_injective in Hdone.
  Qed.

  Lemma elem_of_locale_of_from_list (tp1 tp2 : list $ expr Λ) e :
    locales_equiv tp1 tp2 →
    locale_of tp1 e ∈ locales_of_list (tp2++[e]).
  Proof.
    intros Heq. rewrite (locale_equiv _ _ _ Heq) /locales_of_list_from.
    apply elem_of_list_fmap. exists (tp2, e). split=>//.
    apply prefixes_from_spec. eexists _, _. list_simplifier. naive_solver.
  Qed.

  Lemma model_state_interp_fork_update fs1 fs2 tp1 tp2
        (δ1 δ2 : LM) ζ efork σ1 σ2 :
    (ls_data δ2) = model_update_fork ζ (locale_of tp1 efork) (dom fs1 ∪ dom fs2) (dom fs2) δ1 →
    fs1 ∪ fs2 ≠ ∅ → fs1 ##ₘ fs2 →
    has_forked tp1 tp2 efork →
    locale_step (tp1, σ1) (inl (ζ, None)) (tp2, σ2) →
    model_state_interp (tp1, σ1) δ1 -∗
    has_fuels_S ζ (fs1 ∪ fs2) ==∗
    model_state_interp (tp2, σ2) δ2 ∗
    has_fuels ζ fs1 ∗
    has_fuels (locale_of tp1 efork) fs2.
  Proof.
    iIntros (Hδ2 Hfs Hdisj Hforked Hstep) "Hm Hf".
    iDestruct "Hm" as "(%fm&%Hfmle&%Hfmdead&%Htp&Hm&Hfm&%Hsm1)".
    iDestruct (has_fuels_agree with "Hfm Hf") as %Hagree.
    assert (locale_of tp1 efork ∉ dom fm) as Hnin.
    { pose proof (not_elem_of_locale_of_from_list tp1 efork) as Hes%Htp.
      apply not_elem_of_dom in Hes. set_solver. }
    assert (ζ ≠ locale_of tp1 efork) as Hneq.
    { rewrite not_elem_of_dom in Hnin. set_solver. }
    iMod (has_fuels_decr with "Hfm Hf") as "[Hfm Hf]".
    iMod (has_fuels_split _ _ (locale_of tp1 efork) with "Hfm Hf")
      as "[Hfm [Hf1 Hf2]]"; [|done|].
    { set_solver. }
    iModIntro. iFrame. iExists _. iFrame. rewrite Hδ2. iFrame.
    iPureIntro.
    split; [|split; [| split]].
    - split; last first.
      { simpl.
        destruct Hfmle as [Hfmle Hdom].
        pose proof Hfmle as Hfmle'.
        rewrite /fuel_map_le /fuel_map_le_inner map_included_spec in Hfmle.
        pose proof Hagree as Hagree'.
        apply Hfmle in Hagree' as (fs'&HSome&Hfs').
        rewrite -(insert_id (ls_map δ1) ζ fs'); [|done].
        rewrite !alter_insert.
        set_solver. }
      simpl.
      destruct Hfmle as [Hfmle Hdom].
      pose proof Hfmle as Hfmle'.
      rewrite /fuel_map_le /fuel_map_le_inner map_included_spec in Hfmle.
      pose proof Hagree as Hagree'.
      apply Hfmle in Hagree' as (fs'&HSome&Hfs').
      rewrite -(insert_id (ls_map δ1) ζ fs'); [|done].
      rewrite !alter_insert.
      rewrite insert_insert.

      apply map_included_map_agree_R in Hfs'
          as (fs12'&fsf'&->&Hdisj'&Hfs').
      pose proof Hfs' as Hfs''.
      apply map_agree_R_fmap_inv in Hfs'' as [fs1'' ->]; last first.
      { intros ?[]?; [lia|by eauto]. }
      apply map_agree_R_fmap in Hfs'; last first.
      { intros. lia. }
      apply map_agree_R_union_inv in Hfs'
          as (fs1'&fs2'&->&Hfs1'&Hfs2'); [|done].

      apply map_included_insert.
      { rewrite lookup_total_alt.
        rewrite lookup_insert.
        rewrite map_filter_fmap.
        rewrite map_filter_filter.
        rewrite map_fmap_union.
        rewrite map_filter_union; last first.
        { apply map_disjoint_dom. apply map_disjoint_dom in Hdisj'.
          set_solver. }
        rewrite map_filter_union; last first.
        { apply map_disjoint_dom. apply map_disjoint_dom in Hdisj.
          apply map_agree_R_dom in Hfs1'.
          apply map_agree_R_dom in Hfs2'.
          set_solver. }
        rewrite !map_fmap_union.
        eapply map_included_subseteq_r.
        { apply map_union_subseteq_l. }
        eapply map_included_subseteq_r.
        { apply map_union_subseteq_r.
          apply map_disjoint_dom.
          rewrite !map_filter_fmap. rewrite !dom_fmap_L.
          apply map_disjoint_dom in Hdisj.
          apply map_agree_R_dom in Hfs1'.
          apply map_agree_R_dom in Hfs2'.
          eapply disjoint_subseteq_l; [apply dom_filter_subseteq|].
          eapply disjoint_subseteq_r; [apply dom_filter_subseteq|].
          set_solver. }
        rewrite map_filter_id; last first.
        { simpl. intros ? ? Hlk. apply elem_of_dom_2 in Hlk.
          apply map_agree_R_dom in Hfs1'.
          apply map_agree_R_dom in Hfs2'.
          split; [set_solver|].
          set_solver. }
        rewrite -map_fmap_compose.
        rewrite decr_succ_compose_id. rewrite map_fmap_id.
        by apply map_agree_R_map_included. }

      apply map_included_insert; [|done].
      rewrite map_filter_fmap.
      rewrite map_filter_filter.

      rewrite !map_fmap_union.
      rewrite map_filter_union; last first.
      { apply map_disjoint_dom. apply map_disjoint_dom in Hdisj'.
        set_solver. }
      rewrite map_filter_union; last first.
      { apply map_disjoint_dom. apply map_disjoint_dom in Hdisj.
        apply map_agree_R_dom in Hfs1'.
        apply map_agree_R_dom in Hfs2'.
        set_solver. }
      rewrite !map_fmap_union.
      eapply map_included_subseteq_r.
      { apply map_union_subseteq_l. }
      eapply map_included_subseteq_r.
      { apply map_union_subseteq_l. }

      rewrite map_filter_id; last first.
      { simpl. intros ?? Hlk. apply elem_of_dom_2 in Hlk.
        apply map_agree_R_dom in Hfs1'.
        apply map_agree_R_dom in Hfs2'.
        rewrite dom_fmap in Hlk.
        apply map_disjoint_dom in Hdisj.
        split; [set_solver|].
        set_solver. }
      rewrite -map_fmap_compose.
      rewrite decr_succ_compose_id. rewrite map_fmap_id.
      by apply map_agree_R_map_included.
  - intros ρ' Hin.
      apply Hfmdead in Hin as (ζ'&ρs&HSome&Hρ).
      destruct (decide (ζ = ζ')) as [<-|Hneq'].
      + rewrite Hagree in HSome.
        simplify_eq.
        rewrite dom_fmap_L in Hρ.
        rewrite dom_union_L in Hρ.
        apply elem_of_union in Hρ.
        destruct Hρ as [Hρ|Hρ].
        * eexists ζ, _. rewrite insert_insert.
          rewrite insert_commute; [|done].
          rewrite lookup_insert. done.
        * eexists (locale_of tp1 efork), _. rewrite insert_insert.
          rewrite lookup_insert. done.
      + assert (ζ' ≠ locale_of tp1 efork) as Hneq''.
        { intros ->. apply not_elem_of_dom in Hnin. set_solver. }
        eexists ζ', _.
        rewrite lookup_insert_ne; [|done].
        rewrite insert_insert.
        rewrite lookup_insert_ne; [|done].
        split; [done|]. by set_solver.
    - rewrite /fuel_map_preserve_threadpool.
      intros ζ' Hζ'.
      apply locales_of_list_step_incl in Hstep.
      assert (ζ' ∉ locales_of_list tp1) as Hζ'' by set_solver.
      apply Htp in Hζ''.
      rewrite insert_insert.
      assert (ζ ≠ ζ') as Hneq'.
      { set_solver. }
      assert (locale_of tp1 efork ≠ ζ') as Hneq''.
      { assert (locale_of tp1 efork ∈ locales_of_list tp2).
        { destruct Hforked as [tp2' [-> Hequiv]].
          by apply elem_of_locale_of_from_list. }
        set_solver. }
      rewrite lookup_insert_ne; [|done].
      rewrite lookup_insert_ne; [|done].
      done.
    - simpl. by eapply env_match_internal_step.
  Qed.

  Definition model_can_fork_step (δ1 : LM) (ζ ζf : locale Λ) (δ2 : LM) : Prop :=
    ∃ fs fs1 fs2,
      δ1.(ls_under) = δ2.(ls_under) ∧
      δ1.(ls_map) !! ζ = Some fs ∧ fs ≠ ∅ ∧
      δ2.(ls_map) = <[ζ := fs1]>(<[ζf := fs2]> δ1.(ls_map)) ∧
      map_included (<) fs1 fs ∧
      map_included (<) fs2 fs ∧
      (dom fs ∖ (dom fs1 ∪ dom fs2) ∩ usr_live_roles (usr_state δ1) = ∅) ∧
      (dom fs1 ∩ dom fs2 = ∅) ∧
      ζf ∉ dom δ1.(ls_map).

  Lemma silent_step_suff_data_fork_weak act fl `(δ: LiveState Λ (joint_model M Net))
        (fs fs1 fs2 : gmap _ nat) ζ ζf :
    δ.(ls_map) !! ζ = Some fs →
    fs ≠ ∅ →
    map_included (<) fs1 fs →
    map_included (<) fs2 fs →
    (dom fs ∖ (dom fs1 ∪ dom fs2)) ∩ usr_live_roles (usr_state δ) = ∅ →
    (dom fs1 ∩ dom fs2 = ∅) →
    ζf ∉ dom δ.(ls_map) →
    ∃ δ', δ'.(ls_data) =
          {| ls_under := δ;
            ls_map := <[ζ := fs1]>(<[ζf := fs2]> δ.(ls_map)) |} ∧
            ls_trans fl δ (Silent_step ζ act) δ'.
  Proof.
    intros ?? Hincl1 Hincl2 **.
    apply (silent_step_suff_data fl δ fs fs1 fs2 ζ (Some ζf)); try done.
    - rewrite map_included_spec in Hincl1. done.
    - rewrite map_included_spec in Hincl2. done.
    - set_solver.
  Qed.

  (* TODO: Change original lemma to not existentially quantify new state *)
  Lemma silent_step_suff_data_fork_weak_alt act fl (δ δ': LiveState Λ (joint_model M Net))
        (fs fs1 fs2 : gmap _ nat) ζ ζf :
    δ.(ls_under) = δ'.(ls_under) →
    δ.(ls_map) !! ζ = Some fs →
    δ'.(ls_map) = <[ζ := fs1]>(<[ζf := fs2]> δ.(ls_map)) →
    fs ≠ ∅ →
    map_included (<) fs1 fs →
    map_included (<) fs2 fs →
    (dom fs ∖ (dom fs1 ∪ dom fs2)) ∩ usr_live_roles (usr_state δ) = ∅ →
    (dom fs1 ∩ dom fs2 = ∅) →
    ζf ∉ dom δ.(ls_map) →
    ls_trans fl δ (Silent_step ζ act) δ'.
  Proof.
    rewrite !map_included_spec.
    intros Hδ Hfs Hfs12 Hne Hle1 Hle2 Hlive Hdisj Hnin.
    assert (∃ δ', δ'.(ls_data) =
          {| ls_under := δ;
            ls_map := <[ζ := fs1]> (<[ζf := fs2]>δ.(ls_map)) |} ∧
            ls_trans fl δ (Silent_step ζ act) δ') as (δ''&Heq&Htrans).
    { apply (silent_step_suff_data fl δ fs fs1 fs2 ζ (Some ζf));
        try set_solver. }
    rewrite Heq Hδ -Hfs12 in Htrans. by destruct δ', ls_data.
  Qed.

  Lemma model_can_fork_step_trans act fl ζ ζf (δ δ' : LiveState Λ (joint_model M Net)) :
    model_can_fork_step δ ζ ζf δ' → ls_trans fl δ (Silent_step ζ act) δ'.
  Proof.
    destruct 1 as (?&?&?&?&?&?&?&?&?&?&?&?).
    by eapply silent_step_suff_data_fork_weak_alt.
  Qed.

  Lemma model_state_interp_can_fork_step σ es (δ1 δ2 : LM) ζ
        (fs1 fs2 : gmap (usr_role M) nat) e :
    (ls_data δ2) = model_update_fork ζ (locale_of es e) (dom fs1 ∪ dom fs2) (dom fs2) δ1 →
    (fs1 ∪ fs2) ≠ ∅ → fs1 ##ₘ fs2 →
    model_state_interp (es, σ) δ1 -∗ has_fuels_S ζ (fs1 ∪ fs2) -∗
    ⌜model_can_fork_step δ1 ζ (locale_of es e) δ2⌝.
  Proof.
    iIntros (Hδ2 Hne Hdisj) "Hm Hf".
    iDestruct "Hm" as "(%fm&[%Hfmle %Hdom]&%Hfmdead&%Htp&Hm&Hfm&%Hsm)".
    iDestruct (has_fuels_agree with "Hfm Hf") as %Hagree.
    pose proof Hagree as Hagree'.
    rewrite /fuel_map_le_inner map_included_spec in Hfmle.
    apply Hfmle in Hagree as (fs'&HSome&Hle).
    iPureIntro.
    apply map_included_map_agree_R in Hle as (fs12'&fsf'&->&Hdisj'&Hle).
    pose proof Hle as Hle'.
    apply map_agree_R_fmap_inv in Hle' as (fs12''&->); last first.
    { intros. destruct v2; [lia|by eauto]. }
    apply map_agree_R_fmap in Hle; last first.
    { intros. lia. }
    apply map_agree_R_union_inv in Hle as (fs1'&fs2'&->&Hle1&Hle2);
      [|done].
    eexists _, fs1', fs2'.
    repeat split.
    - rewrite Hδ2. done.
    - done.
    - apply map_agree_R_dom in Hle1.
      apply map_agree_R_dom in Hle2.
      intros Heq. apply Hne.
      apply dom_empty_iff_L in Heq.
      apply dom_empty_iff_L.
      set_solver.
    - rewrite Hδ2. simpl.
      rewrite insert_commute; last first.
      { assert (locale_of es e ∉ locales_of_list es) as Hes%Htp.
        apply not_elem_of_locale_of_from_list.
        set_solver. }
      f_equiv.
      { rewrite lookup_total_alt. simpl.
        rewrite !lookup_alter. rewrite HSome.
        simpl.
        rewrite map_filter_fmap. simpl.
        rewrite map_filter_filter. simpl.
        rewrite !map_fmap_union.
        apply map_agree_R_dom in Hle1.
        apply map_agree_R_dom in Hle2.
        apply map_disjoint_dom in Hdisj.
        apply map_disjoint_dom in Hdisj'.
        rewrite map_filter_union; [|apply map_disjoint_dom; set_solver].
        rewrite map_filter_union; [|apply map_disjoint_dom; set_solver].
        assert (filter
                  (λ '(i, _),
                     i ∈ dom fs2 ∧ (i ∈ usr_live_roles (usr_state δ1) ∨ i ∈ dom fs1 ∪ dom fs2))
                  (S <$> fs1') = ∅) as Hfs1'.
        { apply map_filter_empty_iff.
          intros ρ f Hρ [HP1 HP2].
          apply elem_of_dom_2 in Hρ.
          rewrite dom_fmap_L in Hρ. set_solver. }
        assert (filter
                  (λ '(i, _),
                     i ∈ dom fs2 ∧ (i ∈ usr_live_roles (usr_state δ1) ∨ i ∈ dom fs1 ∪ dom fs2))
                  fsf' = ∅) as Hfsf'.
        { apply map_filter_empty_iff.
          intros ρ f Hρ [HP1 HP2].
          apply elem_of_dom_2 in Hρ. set_solver. }
        rewrite Hfs1' Hfsf'.
        rewrite left_id right_id.
        rewrite map_filter_id; last first.
        { intros ?? Hlk. split.
          - apply elem_of_dom_2 in Hlk. set_solver.
          - right.
            apply elem_of_dom_2 in Hlk. set_solver. }
        rewrite -map_fmap_compose.
        rewrite decr_succ_compose_id.
        rewrite map_fmap_id.
        done. }
      rewrite -!alter_compose.
      erewrite alter_insert_alt; [|done].
      f_equiv.
      simpl.
      rewrite map_filter_fmap. simpl.
      rewrite map_filter_filter. simpl.
      apply map_agree_R_dom in Hle1.
      apply map_agree_R_dom in Hle2.
      apply map_disjoint_dom in Hdisj.
      apply map_disjoint_dom in Hdisj'.
      rewrite !map_fmap_union.
      rewrite map_filter_union; [|apply map_disjoint_dom; set_solver].
      rewrite map_filter_union; [|apply map_disjoint_dom; set_solver].
      assert (filter
             (λ '(i, _),
                (i ∉ dom fs2) ∧ (i ∈ usr_live_roles (usr_state δ1) ∨ i ∈ dom fs1 ∪ dom fs2))
             (S <$> fs2') = ∅) as Hfs2'.
      { apply map_filter_empty_iff.
        intros ρ f Hρ [HP1 HP2].
        apply elem_of_dom_2 in Hρ.
        rewrite dom_fmap_L in Hρ. set_solver. }
      assert (filter
                (λ '(i, _),
                   (i ∉ dom fs2) ∧ (i ∈ usr_live_roles (usr_state δ1) ∨ i ∈ dom fs1 ∪ dom fs2))
                fsf' = ∅) as Hfsf'.
      { apply map_filter_empty_iff.
        intros ρ f Hρ [HP1 HP2].
        apply elem_of_dom_2 in Hρ.
        rewrite Hle2 in HP1.
        clear HP1.
        assert (ρ ∈ (dom fs1 ∪ dom fs2)).
        { destruct HP2 as [HP2|?]; [|done].
          rewrite -dom_union_L.
          rewrite -(dom_fmap_L S).
          eapply fuel_map_le_live_roles; [| | |apply Hagree'|..].
          - intros ????. by apply δ1.(ls_map_disj).
            (* TODO: Fix this by unifying defs *)
          - rewrite /fuel_map_le_inner map_included_spec.
            eapply Hfmle.
          - done.
          - done.
          - done.
          - set_solver. }
        set_solver. }
      rewrite Hfs2' Hfsf'.
      rewrite right_id right_id.
      rewrite map_filter_id; last first.
      { intros ?? Hlk. split.
        - apply elem_of_dom_2 in Hlk. set_solver.
        - right.
          apply elem_of_dom_2 in Hlk. set_solver. }
      rewrite -map_fmap_compose.
      rewrite decr_succ_compose_id.
      rewrite map_fmap_id.
      done.
    - eapply (map_included_subseteq_r _ _ (S <$> fs1')).
      { rewrite map_fmap_union.
        etransitivity; apply map_union_subseteq_l. }
      apply map_included_spec.
      intros k v1 Hv1. exists (S v1).  split; [|lia].
      by rewrite lookup_fmap Hv1.
    - eapply (map_included_subseteq_r _ _ (S <$> fs2')).
      { rewrite map_fmap_union.
        rewrite (map_union_comm (S <$> fs1') (S <$> fs2')).
        - etransitivity; apply map_union_subseteq_l.
        - apply map_disjoint_dom. rewrite !dom_fmap_L.
          apply map_disjoint_dom in Hdisj.
          apply map_agree_R_dom in Hle1.
          apply map_agree_R_dom in Hle2.
          set_solver. }
      apply map_included_spec.
      intros k v1 Hv1. exists (S v1). split; [|lia].
      by rewrite lookup_fmap Hv1.
    - rewrite -dom_empty_iff_L in Hne.
      apply map_agree_R_dom in Hle1.
      apply map_agree_R_dom in Hle2.
      apply disjoint_intersection_L.
      apply map_disjoint_dom in Hdisj.
      apply map_disjoint_dom in Hdisj'.
      rewrite dom_union_L.
      rewrite dom_fmap_L.
      rewrite -dom_union_L.
      replace (dom (fs1' ∪ fs2' ∪ fsf') ∖ (dom fs1' ∪ dom fs2'))
        with (dom fsf') by set_solver.
      intros ρ Hin1 Hin2.
      assert (ρ ∈ (dom fs1 ∪ dom fs2)).
      { rewrite -dom_union_L.
        rewrite -(dom_fmap_L S).
        eapply fuel_map_le_live_roles; [| | |apply Hagree'|..].
        - intros ????. by apply δ1.(ls_map_disj).
        - rewrite /fuel_map_le_inner map_included_spec.
          eapply Hfmle.
        - done.
        - done.
        - done.
        - set_solver. }
      set_solver.
    - apply map_agree_R_dom in Hle1.
      apply map_agree_R_dom in Hle2.
      apply disjoint_intersection_L.
      apply map_disjoint_dom in Hdisj.
      set_solver.
    - pose proof (not_elem_of_locale_of_from_list es e)
        as Hes%Htp.
      apply not_elem_of_dom in Hes. set_solver.
  Qed.

  Lemma model_update_locale_spec_fork extr
        (auxtr : auxiliary_trace LM) ζ ζf c2 ρs1 ρs2 δ2 :
    valid_state_evolution_fairness extr auxtr →
    δ2.(ls_data) = model_update_fork ζ ζf ρs1 ρs2 (trace_last auxtr) →
    model_can_fork_step (trace_last auxtr) ζ ζf δ2 →
    tids_smaller c2.1 δ2 →
    valid_state_evolution_fairness
      (extr :tr[inl (ζ, None)]: c2)
      (auxtr :tr[Silent_step ζ None]: δ2).
  Proof.
    intros Hvse Hstep Htids. destruct c2.
    destruct Hvse as (?&?&?).
    split; [| split]=>//.
    econstructor=>//; first by eapply model_can_fork_step_trans.
  Qed.

  Lemma model_state_interp_has_fuels_agree es δ ζ (fs : gmap (usr_role M) nat) :
    model_state_interp es δ -∗ has_fuels ζ fs -∗
    ⌜∃ fs', δ.(ls_map) !! ζ = Some fs' ∧ map_included (≤) fs fs'⌝.
  Proof.
    iIntros "Hm Hf".
    iDestruct "Hm" as "(%fm&[%Hfmle %Hdom]&%Hfmdead&%Htp&Hm&Hfm&%Hsm)".
    iDestruct (has_fuels_agree with "Hfm Hf") as %Hagree.
    rewrite /fuel_map_le_inner map_included_spec in Hfmle.
    apply Hfmle in Hagree as (fs'&HSome&Hfs').
    iPureIntro. by eexists _.
  Qed.

  (* Lemma update_fork_step fs1 fs2 tp1 tp2 (extr : execution_trace Λ) *)
  (*       (auxtr: auxiliary_trace LM) ζ efork σ1 σ2 : *)
  (*   fs1 ∪ fs2 ≠ ∅ → fs1 ##ₘ fs2 → *)
  (*   trace_last extr = (tp1, σ1) → *)
  (*   locale_step (tp1, σ1) (inl (ζ, None)) (tp2, σ2) → *)
  (*   valid_state_evolution_fairness extr auxtr → *)
  (*   has_forked tp1 tp2 efork → *)
  (*   has_fuels_S ζ (fs1 ∪ fs2) -∗ *)
  (*   model_state_interp (tp1, σ1) (trace_last auxtr) ==∗ *)
  (*   ∃ δ2, *)
  (*     ⌜valid_state_evolution_fairness *)
  (*       (extr :tr[inl (ζ, None)]: (tp2, σ2)) (auxtr :tr[Silent_step ζ None]: δ2)⌝ ∗ *)
  (*     has_fuels ζ fs1 ∗ has_fuels (locale_of tp1 efork) fs2 ∗ *)
  (*     model_state_interp tp2 δ2. *)
  (* Proof. *)
  (*   iIntros (Hdom Hdisj Hlast Hstep Hvse Hforked) "Hfuel Hm". *)
  (*   iDestruct (model_state_interp_has_fuels_agree with "Hm Hfuel") *)
  (*     as %(fs'&HSome&Hfs'). *)
  (*   iAssert (⌜(locale_of tp1 efork) ∉ dom (ls_map (trace_last auxtr))⌝)%I as %Hnin. *)
  (*   { destruct Hforked as (?&?&?). *)
  (*     iDestruct "Hm" as "(%fm&[%Hfmle %Hdom']&%Hfmdead&%Htp&Hm&Hfm)". *)
  (*     rewrite -Hdom'. *)
  (*     iPureIntro. apply not_elem_of_dom. apply Htp. *)
  (*     apply locale_step_equiv in Hstep. simpl in *. *)
  (*     apply not_elem_of_locale_of_from_list. } *)
  (*   opose proof (model_update_fork_valid _ _ _ _ _) as [δ2 Hδ]; *)
  (*     [by apply elem_of_dom|done|]. *)
  (*   iDestruct (model_state_interp_can_fork_step with "Hm Hfuel") as %Hcan_step; *)
  (*     [done..|]. *)
  (*   iMod (model_state_interp_fork_update with "Hm Hfuel") as "(Hm&Hf1&Hf2)"; *)
  (*     [done..|]. *)
  (*   iDestruct (model_state_interp_tids_smaller with "Hm") as %Htids. *)
  (*   iModIntro. *)
  (*   iExists δ2. *)
  (*   iFrame "Hm Hf1 Hf2". *)
  (*   iPureIntro. *)
  (*   by eapply model_update_locale_spec_fork. *)
  (* Qed. *)

  Lemma free_roles_inclusion FR fr:
    auth_free_roles_are FR -∗
    frag_free_roles_are fr -∗
    ⌜fr ⊆ FR⌝.
  Proof.
    iIntros "HFR Hfr".
    iDestruct (own_valid_2 with "HFR Hfr") as %Hval. iPureIntro.
    apply auth_both_valid_discrete in Hval as [??].
    by apply gset_disj_included.
  Qed.

  Lemma update_free_roles rem FR fr1:
    rem ⊆ fr1 ->
    auth_free_roles_are FR -∗
    frag_free_roles_are fr1 ==∗
    auth_free_roles_are (FR ∖ rem) ∗
    frag_free_roles_are (fr1 ∖ rem).
  Proof.
    iIntros (?) "HFR Hfr1".
    iDestruct (free_roles_inclusion with "HFR Hfr1") as %Hincl.
    replace FR with ((FR ∖ rem) ∪ rem); last first.
    { rewrite difference_union_L. set_solver. }
    replace fr1 with ((fr1 ∖ rem) ∪ rem); last first.
    { rewrite difference_union_L. set_solver. }
    iAssert (frag_free_roles_are (fr1 ∖ rem) ∗ frag_free_roles_are rem)%I with "[Hfr1]" as "[Hfr2 Hrem]".
    { rewrite /frag_free_roles_are -own_op -auth_frag_op gset_disj_union //. set_solver. }
    iCombine "HFR Hrem" as "H".
    iMod (own_update with "H") as "[??]" ; eauto.
    - apply auth_update, gset_disj_dealloc_local_update.
    - iModIntro. iFrame. iApply (own_proper with "Hfr2").
      do 2 f_equiv. set_solver.
  Qed.

  (* Lemma update_model_state_interp_config (δ : LiveState _ _) cl fl tp m2 : *)
  (*   LM.(lm_cfg_action) δ cl = (fl, m2) → *)
  (*   ⊢ model_state_interp tp δ ==∗ model_state_interp tp {| ls_under := m2; ls_map := ls_map δ |}. *)
  (* Proof. *)
  (*   iIntros (Heq) "Hmod". unfold model_state_interp. *)
  (*   iDestruct "Hmod" as (fm) "(#? & #? & #? & Hmod & Hfuel)". *)
  (*   erewrite (lm_cfg_spec_live_roles) =>//. *)
  (*   iExists fm. simpl. iFrame "Hfuel #". *)
  (*   iMod (model_update _ _ m2 with "Hmod") as "[? ?]". *)

End model_state_lemmas.
