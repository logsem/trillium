From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fuel.

Canonical Structure ModelO (Mdl : FairModel) := leibnizO Mdl.
Canonical Structure RoleO (Mdl : FairModel) := leibnizO (Mdl.(fmrole)).
Canonical Structure localeO (Λ : language) := leibnizO (locale Λ).

Class fairnessGpreS `(LM: LiveModel Λ M) Σ `{Countable (locale Λ)} := {
  fairnessGpreS_model :> inG Σ (authUR (optionUR (exclR (ModelO M))));
  fairnessGpreS_model_mapping :> inG Σ (authUR (gmapUR (localeO Λ) (exclR (gsetR (RoleO M)))));
  fairnessGpreS_model_fuel :> inG Σ (authUR (gmapUR (RoleO M) (exclR natO)));
  fairnessGpreS_model_free_roles :> inG Σ (authUR (gset_disjUR (RoleO M)));
}.

Class fairnessGS `(LM : LiveModel Λ M) Σ `{Countable (locale Λ)} := FairnessGS {
  fairness_inG :> fairnessGpreS LM Σ;
  (** Underlying model *)
  fairness_model_name : gname;
  (** Mapping of threads to sets of roles *)
  fairness_model_mapping_name : gname;
  (** Mapping of roles to fuel *)
  fairness_model_fuel_name : gname;
  (** Set of free/availble roles *)
  fairness_model_free_roles_name : gname;
}.

Global Arguments fairnessGS {_ _} LM Σ {_ _}.
Global Arguments FairnessGS {_ _} LM Σ {_ _ _} _ _ _.
Global Arguments fairness_model_name {_ _ LM Σ _ _} _.
Global Arguments fairness_model_mapping_name {Λ M LM Σ _ _} _ : assert.
Global Arguments fairness_model_fuel_name {Λ M LM Σ _ _} _ : assert.
Global Arguments fairness_model_free_roles_name {Λ M LM Σ _ _} _ : assert.

Definition fairnessΣ Λ M `{Countable (locale Λ)} : gFunctors := #[
   GFunctor (authUR (optionUR (exclR (ModelO M))));
   GFunctor (authUR (gmapUR (localeO Λ) (exclR (gsetR (RoleO M)))));
   GFunctor (authUR (gmapUR (RoleO M) (exclR natO)));
   GFunctor (authUR (gset_disjUR (RoleO M)))
].

Global Instance subG_fairnessGpreS {Σ} `{LM : LiveModel Λ M}
       `{Countable (locale Λ)} :
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
  Context `{LM: LiveModel Λ M}.
  Context `{Countable (locale Λ)}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.

  Notation Role := (M.(fmrole)).

  Definition auth_fuel_is (F: gmap Role nat): iProp Σ :=
    own (fairness_model_fuel_name fG)
        (● (fmap (λ f, Excl f) F : ucmra_car (gmapUR (RoleO M) (exclR natO)))).

  Definition frag_fuel_is (F: gmap Role nat): iProp Σ :=
    own (fairness_model_fuel_name fG)
        (◯ (fmap (λ f, Excl f) F : ucmra_car (gmapUR (RoleO M) (exclR natO)))).

  Definition auth_mapping_is (m: gmap (locale Λ) (gset Role)): iProp Σ :=
    own (fairness_model_mapping_name fG)
        (● ( (fmap (λ (f: gset M.(fmrole)), Excl f) m) :
              ucmra_car (gmapUR _ (exclR (gsetR (RoleO M))))
        )).

  Definition frag_mapping_is (m: gmap (locale Λ) (gset Role)): iProp Σ :=
    own (fairness_model_mapping_name fG)
        (◯ ( (fmap (λ (f: gset M.(fmrole)), Excl f) m) :
              ucmra_car (gmapUR _ (exclR (gsetR (RoleO M))))
        )).

  Definition auth_model_is (fm: M): iProp Σ :=
    own (fairness_model_name fG) (● Excl' fm).

  Definition frag_model_is (fm: M): iProp Σ :=
    own (fairness_model_name fG) (◯ Excl' fm).

  Definition auth_free_roles_are (FR: gset Role): iProp Σ :=
    own (fairness_model_free_roles_name fG) (● (GSet FR)).

  Definition frag_free_roles_are (FR: gset Role): iProp Σ :=
    own (fairness_model_free_roles_name fG) (◯ (GSet FR)).

  Definition fuel_map_le (m1 m2 : gmap Role nat) :=
    map_included (≤) m1 m2.

  (* Definition maps_inverse_match_le `{Countable K} `{Countable V} *)
  (*            (m: gmap K V) (m': gmap V (gset K)) := *)
  (*   ∀ (k: K) (v: V), m !! k = Some v ↔ ∃ (ks: gset K), m' !! v = Some ks ∧ k ∈ ks. *)

  (* Definition role_map_le (m1 m2 : gmap Role nat) := *)
  (*   map_included (=) m1 m2. *)

  (* Definition fuel_map_le (m1 m2 : gmap Role nat) := *)
  (*   ∀ ρ f1, m1 !! ρ = Some f1 → ∃ f2, m2 !! ρ = Some f2 ∧ f1 ≤ f2. *)
  (* Definition role_map_le *)
  (*            (m1 : gmap (locale Λ) (gset Role)) *)
  (*            (m2 : gmap Role (locale Λ)) := *)
  (*   map_Forall (λ ζ ρs, set_Forall (λ ρ, ) ρs) *)
  (* . *)

  Definition fuel_map_preserve_dead (m : gmap Role nat) (δ : LiveState Λ M) :=
    ∀ ρ, ρ ∉ dom m → ρ ∉ M.(live_roles) δ.

  Definition model_state_interp (tp: list $ expr Λ) (δ: LiveState Λ M): iProp Σ :=
    ∃ fuel_map role_map FR,
      ⌜ fuel_map_le fuel_map δ.(ls_fuel) ⌝ ∗
      ⌜ fuel_map_preserve_dead fuel_map δ ⌝ ∗
      ⌜ maps_inverse_match δ.(ls_mapping) role_map ⌝ ∗
      ⌜ ∀ ζ, ζ ∉ locales_of_list tp → role_map !! ζ = None ⌝ ∗
      ⌜ FR ∩ dom δ.(ls_fuel) = ∅ ⌝ ∗
      auth_fuel_is fuel_map ∗ auth_mapping_is role_map ∗
      auth_free_roles_are FR ∗ auth_model_is δ.

  (* Definition model_state_interp (tp: list $ expr Λ) (δ: LiveState Λ M): iProp Σ := *)
  (*   ∃ M FR, auth_fuel_is δ.(ls_fuel) ∗ auth_mapping_is M ∗ auth_free_roles_are FR ∗ *)
  (*     ⌜maps_inverse_match δ.(ls_mapping) M⌝ ∗ *)
  (*     ⌜ ∀ ζ, ζ ∉ locales_of_list tp → M !! ζ = None ⌝ ∗ *)
  (*     auth_model_is δ ∗ ⌜ FR ∩ dom δ.(ls_fuel) = ∅ ⌝. *)

  (* Lemma model_state_interp_tids_smaller δ tp : *)
  (*   model_state_interp tp δ -∗ ⌜ tids_smaller tp δ ⌝. *)
  (* Proof. *)
  (*   iDestruct 1 as (fm rm FR ?? Hminv ?) "_". iPureIntro. done. *)
  (* Qed. *)

  Lemma model_state_interp_tids_smaller δ tp :
    model_state_interp tp δ -∗ ⌜ tids_smaller tp δ ⌝.
  Proof.
    iDestruct 1 as (fm rm FR ?? Hminv Hbig ?) "_". iPureIntro.
    intros ρ ζ Hin.
    assert (¬ (ζ ∉ locales_of_list tp)).
    - intros contra.
      apply Hminv in Hin as [? [Hsome _]].
      specialize (Hbig _ contra).
      by rewrite Hbig in Hsome.
    - destruct (decide (ζ ∈ locales_of_list tp)) as [Hin'|] =>//.
      apply elem_of_list_fmap in Hin' as [[tp' e'] [-> Hin']].
      unfold from_locale. exists e'. by apply from_locale_from_Some.
  Qed.

End model_state_interp.

Lemma own_proper `{inG Σ X} γ (x y: X):
  x ≡ y ->
  own γ x -∗ own γ y.
Proof. by intros ->. Qed.

Lemma auth_fuel_is_proper `{fairnessGS (LM:=LM) Σ}
      (x y : gmap (fmrole M) nat):
  x = y ->
  auth_fuel_is x -∗ auth_fuel_is y.
Proof. by intros ->. Qed.

Notation "tid ↦M R" := (frag_mapping_is {[ tid := R ]}) (at level 33).
Notation "tid ↦m ρ" := (frag_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
(* Notation "ρ ↦F fs" := (frag_fuel_is fs) (at level 33). *)
(* Notation "ρ ↦f f" := (frag_fuel_is {[ ρ := f ]}) (at level 33). *)
Notation "ρ ↦F f" := (frag_fuel_is {[ ρ := f ]}) (at level 33).

Section model_state_lemmas.
  Context `{LM: LiveModel Λ M}.
  Context `{Countable (locale Λ)}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.

  Notation Role := (M.(fmrole)).

  (* Definition has_fuels (ζ: locale Λ) (fs: gmap Role nat): iProp Σ := *)
  (*   ζ ↦M dom fs ∗ [∗ set] ρ ∈ dom fs, ∃ f, ⌜fs !! ρ = Some f⌝ ∧ ρ ↦F f. *)

  (* Definition has_fuels (ζ: locale Λ) (fs: gmap Role nat): iProp Σ := *)
  (*   ∃ fs', ⌜dom fs ⊆ fs'⌝ ∗ ζ ↦M fs' ∗ ρ ↦F fs. *)

  (* Definition has_fuels (ζ: locale Λ) (fs: gmap Role nat): iProp Σ := *)
  (*   ∃ fs', ⌜set_Forall (λ ρ, ρ ∉ live_roles) fs⌝ ∗ *)
  (*          ⌜set_Forall (λ ρ, ρ ∈ live_roles) fs⌝ ∗ *)
  (*          ζ ↦M (fs ∪ fs') ∗ [∗ map] ρ ↦ f ∈ fs, ρ ↦F f. *)

  Definition has_fuels (ζ: locale Λ) (fs: gmap Role nat): iProp Σ :=
    ∃ fs', ⌜dom fs ⊆ fs'⌝ ∗ ζ ↦M fs' ∗ [∗ map] ρ ↦ f ∈ fs, ρ ↦F f.

  Definition has_fuel (ζ: locale Λ) (ρ: Role) (f: nat): iProp Σ :=
    has_fuels ζ {[ρ:=f]}.

  #[global] Instance has_fuels_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (has_fuels).
  Proof. solve_proper. Qed.

  #[global] Instance has_fuels_timeless (ζ: locale Λ) (fs: gmap Role nat):
    Timeless (has_fuels ζ fs).
  Proof. rewrite /has_fuels. apply _. Qed.


  Lemma has_fuel_fuels (ζ: locale Λ) (ρ: Role) (f: nat):
    has_fuel ζ ρ f ⊣⊢ has_fuels ζ {[ ρ := f ]}.
  Proof. rewrite /has_fuel /has_fuels. done. Qed.

  (* Lemma has_fuel_fuels (ζ: locale Λ) (ρ: Role) (f: nat): *)
  (*   has_fuel ζ ρ f ⊣⊢ has_fuels ζ {[ ρ := f ]}. *)
  (* Proof. *)
  (*   rewrite /has_fuel /has_fuels. iSplit. *)
  (*   - iIntros "[Hζ Hρ]". iExists {[ρ := f]}. iSplit; [done|]. *)
  (*     rewrite dom_singleton_L big_sepS_singleton. iFrame. *)
  (*     iExists f. iFrame. iPureIntro. by rewrite lookup_singleton. *)
  (*   - iDestruct 1 as (fs' Hfs) "(?&H)". *)
  (*     rewrite dom_singleton_L big_sepS_singleton. iFrame. *)
  (*     iDestruct "H" as (?) "H". rewrite lookup_singleton. *)
  (*     iDestruct "H" as "[% ?]". by simplify_eq. *)
  (* Qed. *)

  Definition has_fuels_S (ζ: locale Λ) (fs: gmap Role nat): iProp Σ :=
    has_fuels ζ (fmap S fs).

  Definition has_fuels_plus (n: nat) (ζ: locale Λ) (fs: gmap Role nat): iProp Σ :=
    has_fuels ζ (fmap (fun m => n+m) fs).

  Lemma has_fuel_fuels_S (ζ: locale Λ) (ρ: Role) (f: nat):
    has_fuel ζ ρ (S f) ⊣⊢ has_fuels_S ζ {[ ρ := f ]}.
  Proof.
    rewrite has_fuel_fuels /has_fuels_S map_fmap_singleton //.
  Qed.

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

  Lemma frag_mapping_same ζ m R:
    auth_mapping_is m -∗ ζ ↦M R -∗ ⌜ m !! ζ = Some R ⌝.
  Proof.
    iIntros "Ha Hf". iCombine "Ha Hf" as "H". rewrite own_valid.
    iDestruct "H" as "%Hval". iPureIntro.
    apply auth_both_valid in Hval as [HA HB].
    rewrite map_fmap_singleton in HA.
    specialize (HA 0%nat).
    apply cmra_discrete_included_iff in HA.
    apply -> (@singleton_included_l (locale Λ)) in HA. destruct HA as (R' & HA & Hsub).
    assert (✓ Some R'). by rewrite -HA.
    destruct R' as [R'|]; last done.
    apply Excl_included in Hsub. apply leibniz_equiv in Hsub.
    rewrite Hsub.
    apply leibniz_equiv in HA. rewrite -> lookup_fmap_Some in HA.
    destruct HA as (?&?&?). congruence.
  Qed.

End model_state_lemmas.

Section adequacy.
  Context `{LM: LiveModel Λ M}.
  Context `{Countable (locale Λ)}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGpreS LM Σ}.

  Lemma model_state_init (s0: M):
    ⊢ |==> ∃ γ,
        own (A := authUR (optionUR (exclR (ModelO M)))) γ
            (● (Excl' s0) ⋅ ◯ (Excl' s0)).
  Proof.
    iMod (own_alloc (● Excl' s0 ⋅ ◯ Excl' s0)) as (γ) "[Hfl Hfr]".
    { by apply auth_both_valid_2. }
    iExists _. by iSplitL "Hfl".
  Qed.

  Lemma model_mapping_init (s0: M) (ζ0: locale Λ):
    ⊢ |==> ∃ γ,
        own (A := authUR (gmapUR _ (exclR (gsetR (RoleO M))))) γ
            (● ({[ ζ0 :=  Excl (M.(live_roles) s0) ]}) ⋅
               ◯ ({[ ζ0 :=  Excl (M.(live_roles) s0) ]})).
  Proof.
    iMod (own_alloc (● ({[ ζ0 :=  Excl (M.(live_roles) s0) ]}) ⋅
                       ◯ ({[ ζ0 :=  Excl (M.(live_roles) s0) ]}))) as (γ) "[Hfl Hfr]".
    { apply auth_both_valid_2; eauto. by apply singleton_valid. }
    iExists _. by iSplitL "Hfl".
  Qed.

  Lemma model_fuel_init (s0: M):
    ⊢ |==> ∃ γ,
        own (A := authUR (gmapUR (RoleO M) (exclR natO))) γ
            (● gset_to_gmap (Excl (LM.(lm_fl) s0)) (M.(live_roles) s0)  ⋅
               (◯ gset_to_gmap (Excl (LM.(lm_fl) s0)) (M.(live_roles) s0))).
  Proof.
    iMod (own_alloc
            (● gset_to_gmap (Excl (LM.(lm_fl) s0)) (M.(live_roles) s0)  ⋅
               (◯ gset_to_gmap (Excl (LM.(lm_fl) s0)) (M.(live_roles) s0)))) as (γ) "[H1 H2]".
    { apply auth_both_valid_2;eauto. intros ρ.
      destruct (gset_to_gmap (Excl (LM.(lm_fl) s0)) (live_roles M s0) !! ρ) eqn:Heq;
        rewrite Heq; last done.
      apply lookup_gset_to_gmap_Some in Heq.
      destruct Heq as [?<-]. done. }
    iExists _. by iSplitL "H1".
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
  Context `{LM: LiveModel Λ M}.
  Context `{Countable (locale Λ)}.
  Context `{EqDecision (expr Λ)}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.

  Lemma update_model δ δ1 δ2:
    auth_model_is δ1 -∗ frag_model_is δ2 ==∗ auth_model_is δ ∗ frag_model_is δ.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    iMod (own_update with "H") as "[??]" ; eauto.
    - by apply auth_update, option_local_update, (exclusive_local_update _ (Excl δ)).
    - iModIntro. iFrame.
  Qed.

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

  Lemma model_agree s1 s2:
    auth_model_is s1 -∗ frag_model_is s2 -∗ ⌜ s1 = s2 ⌝.
  Proof.
    iIntros "Ha Hf".
      by iDestruct (own_valid_2 with "Ha Hf") as
          %[Heq%Excl_included%leibniz_equiv ?]%auth_both_valid_discrete.
  Qed.

  Lemma model_agree' δ1 s2 n:
    model_state_interp n δ1 -∗ frag_model_is s2 -∗ ⌜ ls_under δ1 = s2 ⌝.
  Proof.
    iDestruct 1 as (????????) "(_&_&_&Hs1)". iIntros "Hs2".
    iApply (model_agree with "Hs1 Hs2").
  Qed.

  Lemma update_fuel_delete ρ f F:
    auth_fuel_is F -∗ ρ ↦F f ==∗ auth_fuel_is (delete ρ F).
  Proof.
    iIntros "Hafuel Hfuel".
    iCombine "Hafuel Hfuel" as "H".
    iMod (own_update with "H") as "H"; last first.
    { iModIntro. iFrame. }
    rewrite map_fmap_singleton fmap_delete.
    eapply auth_update_dealloc.
    apply delete_singleton_local_update.
    typeclasses eauto.
  Qed.

  Definition fuel_apply (fs' F:  gmap (fmrole M) nat) (LR: gset (fmrole M)):
    gmap (fmrole M) nat :=
    map_imap
      (λ (ρ: fmrole M ) (fold : nat),
       match decide (ρ ∈ dom fs') with
       | left x => fs' !! ρ
       | right _ => F !! ρ
       end) (gset_to_gmap (0%nat) LR).

  Definition update_fuel_resource (δ1: LiveState Λ M) (fs1 fs2: gmap (fmrole M) nat) (s2: M):
    gmap (fmrole M) nat :=
    fuel_apply fs2 (δ1.(ls_fuel (Λ := Λ))) (((dom $ ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2)).

  Lemma elem_of_frame_excl_map
        (fs F: gmap (fmrole M) nat)
        (mf: gmap (fmrole M) (excl nat))
        (ρ: fmrole M)
        (f: excl nat):
    ✓ ((λ f : nat, Excl f) <$> F) ->
    ((λ f : nat, Excl f) <$> F ≡ ((Excl <$> fs) ⋅? (Some mf))) ->
    mf !! ρ = Some f ->
    ρ ∈ dom F ∖ dom fs.
  Proof.
    intros Hval Heq Hlk. simpl in Heq.
    specialize (Heq ρ). rewrite lookup_op Hlk !lookup_fmap in Heq.
    destruct (decide (ρ ∈ dom F)) as [HF|HF]; last first.
    { exfalso. apply not_elem_of_dom in HF. rewrite HF //= in Heq.
      destruct (fs !! ρ) eqn:Hfs; inversion Heq as [A S D G Habs|A Habs];
        setoid_rewrite -> Hfs in Habs; by compute in Habs. }
    destruct (decide (ρ ∈ dom fs)) as [Hfs|Hfs].
    { exfalso. apply elem_of_dom in Hfs as [f' Hlk'].
      rewrite Hlk' /= in Heq.
      suffices: Some f = None by eauto.
      eapply exclusive_Some_l; last first.
      - specialize (Hval ρ). rewrite -> lookup_fmap, Heq in Hval.
        apply Hval.
      - typeclasses eauto. }
    set_solver.
  Qed.

  Lemma update_fuel fs fs' F:
    let LR := (dom F ∪ dom fs') ∖ (dom fs ∖ dom fs') in
    (fs ≠ ∅) ->
    (dom fs' ∖ dom fs ∩ dom F = ∅) ->
    auth_fuel_is F -∗
    ([∗ map] ρ ↦ f ∈ fs, ρ ↦F f) ==∗
      auth_fuel_is (fuel_apply fs' F LR) ∗
      ([∗ map] ρ ↦ f ∈ fs', ρ ↦F f).
  Proof.
    iIntros (? Hnotemp Hdisj) "Hafuel Hfuel".
    rewrite {1}/frag_fuel_is -big_opM_own //.
    setoid_rewrite map_fmap_singleton.
    rewrite -big_opM_auth_frag.
    iCombine "Hafuel Hfuel" as "H".
    iMod (own_update with "H") as "[A B]"; last first.
    { iModIntro.
      destruct (decide (fs' = ∅)) as [Heq|]; last first.
      -  rewrite {1}/frag_fuel_is -big_opM_own //.
         iSplitL "A"; done.
      - rewrite Heq. iSplitL "A"; first done. done. }

    simpl.
    setoid_rewrite map_fmap_singleton.
    rewrite -big_opM_auth_frag.

    simpl.
    apply auth_update.

    apply local_update_discrete.

    intros mf Hval Heq.
    split.
    { intros ρ. rewrite /fuel_apply lookup_fmap map_lookup_imap.
      rewrite lookup_gset_to_gmap.
      destruct (decide (ρ ∈ LR)).
      - rewrite option_guard_True //=.
        destruct (decide (ρ ∈ dom fs')) as [Hd|Hd].
        + rewrite decide_True //=. apply elem_of_dom in Hd as [? Hsome].
          rewrite Hsome //.
        + rewrite decide_False //= -lookup_fmap. apply (Hval ρ).
      - rewrite option_guard_False //=. }

    intros ρ. rewrite /fuel_apply lookup_fmap map_lookup_imap.
    rewrite lookup_gset_to_gmap.
    rewrite -big_opM_fmap big_opM_singletons.
    rewrite <-big_opM_fmap in Heq. setoid_rewrite big_opM_singletons in Heq.
    destruct (decide (ρ ∈ LR)).
    - rewrite option_guard_True //=.
      destruct (decide (ρ ∈ dom fs')) as [Hd'|Hd'].
      + rewrite decide_True //=. apply elem_of_dom in Hd' as [? Hsome].
        rewrite Hsome //= lookup_opM.
        rewrite lookup_fmap Hsome.
        destruct mf as [mf|]; simpl; last done.
        destruct (mf !! ρ) as [f|] eqn:Hlk; rewrite Hlk //.

        assert (ρ ∈ dom F ∖ dom fs).
        { eauto using elem_of_frame_excl_map. }
        assert (ρ ∈ dom fs').
        { apply elem_of_dom. eauto. }
        set_solver.
      + rewrite decide_False //= -lookup_fmap.
        rewrite Heq.
        destruct (decide (ρ ∈ dom fs)) as [Hd|Hd];
          first set_solver.
        pose proof Hd as Hd2. pose proof Hd' as Hd'2.
        apply not_elem_of_dom in Hd2, Hd'2. rewrite !lookup_opM !lookup_fmap Hd2 Hd'2 //.
    - rewrite option_guard_False //=.
      rewrite lookup_opM lookup_fmap.
      destruct mf as [mf|]; simpl.
      + destruct (mf !! ρ) as [f|] eqn:Hlk; rewrite Hlk //.
        * assert (ρ ∈ dom F ∖ dom fs).
          { eauto using elem_of_frame_excl_map. }
          set_solver.
        * assert (Hnotin: ρ ∉ dom fs') by set_solver.
          apply not_elem_of_dom in Hnotin. rewrite Hnotin //.
      + assert (Hnotin: ρ ∉ dom fs') by set_solver.
        apply not_elem_of_dom in Hnotin. rewrite Hnotin //.
  Qed.

  Lemma update_mapping ζ (R' : gset $ fmrole M) (R: gset (fmrole M)) m :
    auth_mapping_is m -∗ ζ ↦M R ==∗ auth_mapping_is (<[ ζ := R' ]> m) ∗ ζ ↦M R'.
  Proof.
    iIntros "Hamap Hmap".
    iCombine "Hamap Hmap" as "H".
    iMod (own_update with "H") as "[A B]"; last first.
    { iModIntro. iSplitL "A"; iFrame. }
    rewrite !map_fmap_singleton fmap_insert.
    eapply auth_update, singleton_local_update_any.
    intros. by apply exclusive_local_update.
  Qed.

  Lemma mapping_lookup ζ m R:
    auth_mapping_is m -∗ ζ ↦M R -∗ ⌜ ζ ∈ dom m ⌝.
  Proof.
    unfold auth_mapping_is, frag_mapping_is.
    iIntros "Ham Hm".
    iCombine "Ham Hm" as "H".
    iDestruct (own_valid with "H") as %Hval. iPureIntro.
    apply auth_both_valid_discrete in Hval as [Hval ?].
    rewrite map_fmap_singleton in Hval.
    apply singleton_included_exclusive_l in Hval =>//; last by typeclasses eauto.
    rewrite -> lookup_fmap, leibniz_equiv_iff in Hval.
    apply fmap_Some_1 in Hval as (f'&Hfuelρ&?). simplify_eq.
    apply elem_of_dom. eauto.
  Qed.

  Lemma update_mapping_new_locale ζ ζ' (R R1 R2 : gset $ fmrole M) m :
    ζ' ∉ dom m ->
    auth_mapping_is m -∗
    ζ ↦M R ==∗
    auth_mapping_is (<[ ζ' := R2]> (<[ ζ := R1 ]> m)) ∗
    ζ ↦M R1 ∗ ζ' ↦M R2.
  Proof.
    iIntros (Hnotin) "Hamap Hmap".
    iDestruct (mapping_lookup with "Hamap Hmap") as %Hin.
    iCombine "Hamap Hmap" as "H".
    iMod (own_update (A := (authUR (gmapUR _ (exclR (gsetR (RoleO M)))))) _ _ (
                       ● ((λ f : gset (fmrole M), Excl f) <$> ((<[ ζ := R1 ]> m)))
                         ⋅ ◯ ((λ f : gset (fmrole M), Excl f) <$> {[ζ := R1]})
                     ) with "H") as "[A B]".
    { rewrite !map_fmap_singleton fmap_insert.
      eapply auth_update. eapply singleton_local_update_any.
      intros. by apply exclusive_local_update. }
    iCombine "A B" as "H".
    iMod (own_update (A := (authUR (gmapUR _ (exclR (gsetR (RoleO M)))))) _ _ (
                       ● ((λ f : gset (fmrole M), Excl f) <$> (<[ ζ' := R2]> (<[ ζ := R1 ]> m)))
                         ⋅ ◯ ((λ f : gset (fmrole M), Excl f) <$> {[ζ := R1 ; ζ' := R2]})
                     ) with "H") as "[A B]"; last first.
    { iModIntro. iSplitL "A"; first iFrame. rewrite !fmap_insert fmap_empty insert_empty.
      replace (◯ {[ζ := Excl R1; ζ' := Excl R2]}) with (◯ {[ζ := Excl R1]} ⋅ ◯ {[ζ' := Excl R2]}).
      - iDestruct "B" as "[A B]". iSplitL "A"; rewrite /frag_mapping_is map_fmap_singleton //.
      - rewrite -auth_frag_op insert_singleton_op //. rewrite lookup_singleton_ne //. set_solver. }
    rewrite !map_fmap_singleton fmap_insert !fmap_insert.
    rewrite (insert_commute _ _ _ (Excl R1) (Excl R2)); last set_solver.
    eapply auth_update. rewrite fmap_empty. eapply alloc_local_update; eauto.
    - rewrite lookup_insert_ne; last set_solver. apply not_elem_of_dom. set_solver.
    - done.
  Qed.

  Lemma update_mapping_delete ζ (Rrem : gset $ fmrole M) (R: gset (fmrole M)) m :
    auth_mapping_is m -∗ ζ ↦M R ==∗ auth_mapping_is (<[ ζ := R ∖ Rrem ]> m) ∗ ζ ↦M (R ∖ Rrem).
  Proof.
    eauto using update_mapping.
  Qed.

  Lemma update_mapping_add ζ (Radd : gset $ fmrole M) (R: gset (fmrole M)) m :
    auth_mapping_is m -∗ ζ ↦M R ==∗ auth_mapping_is (<[ ζ := R ∪ Radd ]> m) ∗ ζ ↦M (R ∪ Radd).
  Proof.
    eauto using update_mapping.
  Qed.

  Lemma has_fuels_equiv fs ζ:
    has_fuels ζ fs ⊣⊢
    ∃ fs', ⌜dom fs ⊆ fs'⌝ ∗ ζ ↦M fs' ∗ ([∗ map] ρ ↦ f ∈ fs, ρ ↦F f).
  Proof. done. Qed.

  (* TODO: Move *)
  (* TODO: Generalise to map_included instead of subseteq? *)
  Lemma map_included_subseteq `{∀ A, Lookup K A (MAP A)} {A}
        (R : relation A) (m1 m2 m3 : MAP A) :
    m1 ⊆ m2 → map_included R m2 m3 → map_included R m1 m3.
  Proof.
    intros Hle Hincluded.
  Admitted.

  (* TODO: Move *)
  Lemma map_included_transitivity `{∀ A, Lookup K A (MAP A)} {A}
        (R : relation A) (m1 m2 m3 : MAP A) :
    map_included R m1 m2 → map_included R m2 m3 → map_included R m1 m3.
  Proof.
    intros Hle Hincluded.
  Admitted.

  Notation Role := (M.(fmrole)).

  (* TODO: Generalize types *)
  Lemma map_included_fmap `{Countable K} {A}
        (R : relation A) (m : gmap K A) (f : A → A) :
    (∀ x:A, R x (f x)) → map_included R m (f <$> m).
  Proof.
    intros Hf. intros k. rewrite lookup_fmap.
    destruct (m !! k); [by apply Hf|done].
  Qed.

  Lemma has_fuels_decr tid fs fs' :
    fs ##ₘ fs' →
    auth_fuel_is ((S <$> fs) ∪ fs') -∗ has_fuels_S tid fs ==∗
    auth_fuel_is (fs ∪ fs') ∗ has_fuels tid fs.
  Proof.
  Admitted.

  Lemma model_state_interp_has_fuels_decr tp δ tid fs :
    model_state_interp tp δ -∗ has_fuels_S tid fs ==∗
    model_state_interp tp δ ∗ has_fuels tid fs.
  Proof.
    iDestruct 1 as
      (fm rm FR Hfmle Hfmdead Hmapinv Htp Hfr) "(Hfm & Hrm & HFR & Hm)".
    iDestruct 1 as (fs' Hfs) "[Htid Hfs]".
    iInduction fs as [|f fs Hnin] "IHfs" using map_ind.
    { iModIntro.
      iSplitR "Htid Hfs".
      { iExists _, _, _. iFrame. done. }
      iExists _. iSplit; [done|]. rewrite fmap_empty. iFrame. }
    rewrite fmap_insert.
    rewrite big_sepM_insert; [|rewrite lookup_fmap]; last first.
    { rewrite H0. done. }
    iDestruct "Hfs" as "[Hf Hfs]".
    rewrite /frag_fuel_is.
    rewrite /auth_fuel_is.
    admit.
  Admitted.

  Lemma model_state_interp_has_fuels_dealloc tid fs ρ tp δ δ' :
    ρ ∉ live_roles _ δ →
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
    iDestruct 1 as
      (fm rm FR Hfmle Hfmdead Hmapinv Htp Hfr) "(Hfm & Hrm & HFR & Hm)".
    iIntros "Hst".
    iDestruct 1 as (fs' Hfs) "[Htid Hfs]".
    iDestruct (model_agree with "Hm Hst") as %Heq. rewrite !Heq.
    assert (is_Some (fs !! ρ)) as [f HSome].
    { by rewrite -elem_of_dom. }
    rewrite big_sepM_delete; [|done].
    iDestruct "Hfs" as "[Hf Hfs]".
    (* iDestruct "Hf" as (f Hf) "Hf". *)
    iMod (update_fuel_delete with "Hfm Hf") as "Hfm".
    iModIntro.
    (* iDestruct (thing _ _ (dom (delete ρ fs)) with "Htid") as "Htid". *)
    (* { rewrite dom_delete_L. set_solver. } *)
    iFrame "Hst".
    iSplitR "Htid Hfs"; last first.
    { rewrite /has_fuels. iExists _. iFrame.
      rewrite dom_delete_L. iPureIntro.
      set_solver. }
    iExists _, _, _. iFrame. rewrite Heq. iFrame.
    iPureIntro.
    repeat split; try done.
    - rewrite /fuel_map_le.
      eapply map_included_transitivity; [|done].
      eapply map_included_subseteq; [|done].
      apply delete_subseteq.
    - rewrite /fuel_map_preserve_dead.
      intros ρ' Hρ' Hlive.
      assert (ρ ≠ ρ') by set_solver.
      rewrite /fuel_map_preserve_dead in Hfmdead.
      rewrite not_elem_of_dom in Hρ'.
      rewrite lookup_delete_ne in Hρ'; [|done].
      specialize (Hfmdead ρ').
      rewrite not_elem_of_dom in Hfmdead.
      specialize (Hfmdead Hρ'). done.
    - intros ?. apply Hmapinv. done.
    - intros ?. apply Hmapinv. done.
  Qed.

  (* Lemma has_fuels_equiv fs ζ: *)
  (*   has_fuels ζ fs ⊣⊢ ζ ↦M (dom fs) ∗ ([∗ map] ρ ↦ f ∈ fs, ρ ↦F f). *)
  (* Proof. *)
  (*   rewrite /has_fuels -big_opM_dom. iSplit. *)
  (*   - iIntros "($ & H)". iApply (big_sepM_impl with "H"). *)
  (*     iIntros "!#" (ρ f Hin) "(%f' & %Hin' & ?)". *)
  (*       by simplify_eq. *)
  (*   - iIntros "($&H)". *)
  (*     iApply (big_sepM_impl with "H"). *)
  (*     iIntros "!#" (ρ f Hin)  "?". iExists f. iSplit; done. *)
  (* Qed. *)

  (* Lemma update_has_fuels ζ fs fs' F m : *)
  (*   let LR := (dom F ∪ dom fs') ∖ (dom fs ∖ dom fs') in *)
  (*   (fs ≠ ∅) -> *)
  (*   (dom fs' ∖ dom fs ∩ dom F = ∅) -> *)
  (*   has_fuels ζ fs -∗ *)
  (*   auth_fuel_is F -∗ *)
  (*   auth_mapping_is m ==∗ *)
  (*   auth_fuel_is (fuel_apply fs' F LR) ∗ *)
  (*   has_fuels ζ fs' ∗ *)
  (*   auth_mapping_is (<[ ζ := dom fs' ]> m). *)
  (* Proof. *)
  (*   iIntros (LR Hfs Hdom) "Hfuels Hafuels Hamapping". *)
  (*   rewrite !has_fuels_equiv. iDestruct "Hfuels" as "[Hmapping Hfuels]". *)
  (*   iMod (update_fuel with "Hafuels Hfuels") as "[Hafuels Hfuels]" =>//. *)
  (*   iMod (update_mapping with "Hamapping Hmapping") as "[Hamapping Hmapping]". *)
  (*   iModIntro. *)
  (*   iFrame. *)
  (* Qed. *)

  (* Lemma update_has_fuels_no_step ζ fs fs' F m : *)
  (*   let LR := (dom F ∪ dom fs') ∖ (dom fs ∖ dom fs') in *)
  (*   (fs ≠ ∅) -> *)
  (*   (dom fs' ⊆ dom fs) -> *)
  (*   has_fuels ζ fs -∗ *)
  (*   auth_fuel_is F -∗ *)
  (*   auth_mapping_is m ==∗ *)
  (*   auth_fuel_is (fuel_apply fs' F LR) ∗ *)
  (*   has_fuels ζ fs' ∗ *)
  (*   auth_mapping_is (<[ ζ := dom fs' ]> m). *)
  (* Proof. *)
  (*   iIntros (LR Hfs Hdom) "Hfuels Hafuels Hamapping". *)
  (*   rewrite !has_fuels_equiv. iDestruct "Hfuels" as "[Hmapping Hfuels]". *)
  (*   iMod (update_fuel fs fs' with "Hafuels Hfuels") as "[Hafuels Hfuels]"; [done|set_solver|]. *)
  (*   iMod (update_mapping with "Hamapping Hmapping") as "[Hamapping Hmapping]". *)
  (*   iModIntro. iFrame. *)
  (* Qed. *)

  (* Lemma update_has_fuels_no_step_no_change ζ fs fs' F m : *)
  (*   let LR := (dom F ∪ dom fs') ∖ (dom fs ∖ dom fs') in *)
  (*   (fs ≠ ∅) -> *)
  (*   (dom fs' = dom fs) -> *)
  (*   has_fuels ζ fs -∗ *)
  (*   auth_fuel_is F -∗ *)
  (*   auth_mapping_is m ==∗ *)
  (*   auth_fuel_is (fuel_apply fs' F LR) ∗ *)
  (*   has_fuels ζ fs' ∗ *)
  (*   auth_mapping_is m. *)
  (* Proof. *)
  (*   iIntros (LR Hfs Hdom) "Hfuels Hafuels Hamapping". *)
  (*   rewrite !has_fuels_equiv. iDestruct "Hfuels" as "[Hmapping Hfuels]". *)
  (*   iMod (update_fuel fs fs' with "Hafuels Hfuels") as "[Hafuels Hfuels]" =>//. *)
  (*   { rewrite Hdom. set_solver. } *)
  (*   iModIntro. *)
  (*   iFrame. rewrite Hdom //. *)
  (* Qed. *)

  Lemma has_fuel_in ζ δ fs n:
    has_fuels ζ fs -∗ model_state_interp n δ -∗
    ⌜ ∀ ρ, ρ ∈ dom fs → ls_mapping δ !! ρ = Some ζ ⌝.
  Proof. Admitted.
  (* done. *)
  (* assert (ρ ∈ dom (ls_fuel (trace_last auxtr))) as Hρ'. *)
  (* { admit.  (* by Hle' *) } *)
  (* rewrite -(trace_last auxtr).(ls_same_doms) in Hρ'. *)
  (* eexists ρ. *)
  (* rewrite elem_of_dom in Hρ'. *)
  (* set_solver. *)

  (* Lemma has_fuel_in ζ δ fs n: *)
  (*   has_fuels ζ fs -∗ model_state_interp n δ -∗ ⌜ ∀ ρ, ls_mapping δ !! ρ = Some ζ <-> ρ ∈ dom fs ⌝. *)
  (* Proof. *)
  (*   unfold model_state_interp, has_fuels, auth_mapping_is, frag_mapping_is. *)
  (*   iDestruct 1 as (fs' ) "[Hζ Hfuels]". *)
  (*   iDestruct 1 as *)
  (*     (fm rm FR Hfmle Hfmdead Hmapinv Htp Hfr) "(Hfm & Hrm & HFR & Hm)". *)
  (*   iIntros (ρ). *)
  (*   iCombine "Hrm Hζ" as "H". *)
  (*   iDestruct (own_valid with "H") as %Hval. iPureIntro. *)
  (*   apply auth_both_valid_discrete in Hval as [Hval ?]. *)
  (*   rewrite map_fmap_singleton in Hval. *)
  (*   apply singleton_included_exclusive_l in Hval =>//; last by typeclasses eauto. *)
  (*   rewrite -> lookup_fmap, leibniz_equiv_iff in Hval. *)
  (*   apply fmap_Some_1 in Hval as (R'&HMζ&?). simplify_eq. *)
  (*   rewrite (Hmapinv ρ ζ) HMζ. split. *)
  (*   - intros (?&?&?). by simplify_eq. *)
  (*   - intros ?. eexists. split; eauto. *)
  (* Qed. *)

  Lemma has_fuel_fuel ζ δ fs n:
    has_fuels ζ fs -∗ model_state_interp n δ -∗
    ⌜ map_included (≤) fs δ.(ls_fuel) ⌝.
    (* ⌜ ∀ ρ, ρ ∈ dom fs -> ls_fuel δ !! ρ = fs !! ρ ⌝. *)
  Proof.
    unfold has_fuels, model_state_interp, auth_fuel_is.
    iDestruct 1 as (fs' Hfs) "[Hζ Hfuels]".
    iDestruct 1 as
      (fm rm FR Hfmle Hfmdead Hmapinv Htp Hfr) "(Hfm & Hrm & HFR & Hm)".
    iAssert (⌜fs ⊆ fm⌝)%I as %Hle.
    {
      iClear "Hζ Hrm HFR Hm".
      iInduction fs as [|ρ f fs Hnin] "IHfs" using map_ind forall (fs' Hfs).
      { iPureIntro. apply map_empty_subseteq. }
      (* rewrite dom_insert_L. *)
      rewrite big_sepM_insert; [|done].
      iDestruct "Hfuels" as "[Hf Hfuels]".
      (* iDestruct "Hf" as (f' Hf') "Hf". *)

      iDestruct (own_valid_2 with "Hfm Hf") as %Hvalid.
      apply auth_both_valid_discrete in Hvalid as [Hvalid ?].
      rewrite map_fmap_singleton in Hvalid.
      apply singleton_included_exclusive_l in Hvalid =>//; last by typeclasses eauto.
      rewrite -> lookup_fmap, leibniz_equiv_iff in Hvalid.
      apply fmap_Some_1 in Hvalid as (f''&Hfuelρ&?). simplify_eq.
      iDestruct ("IHfs" with "[//] Hfuels Hfm") as %Hle'.
      iPureIntro.
      apply insert_subseteq_l; [|done]. done. }
    iPureIntro.
    eapply map_included_subseteq; done.
  Qed.

  Definition map_relation_alt `{∀ A, Lookup K A (MAP A)} {A B}
             (R : A → B → Prop) (m1 : MAP A) (m2 : MAP B) :=
    map_relation R (λ _, False) (λ _, False) m1 m2.

  Lemma map_relation_alt_fmap `{Countable K} {A}
        (R : relation A) (m1 m2: gmap K A) (f : A → A) :
    (∀ x y:A, R x y → R (f x) (f y)) →
    map_relation_alt R m1 m2 →
    map_relation_alt R (f <$> m1) (f <$> m2).
  Proof.
    intros Hf HR. intros k. specialize (HR k).
    rewrite !lookup_fmap.
    destruct (m1 !! k); destruct (m2 !! k); [by apply Hf|done..].
  Qed.

  Lemma map_relation_alt_fmap_inv `{Countable K} {A}
        (R : relation A) (m1 m2: gmap K A) (f : A → A) :
    (∀ x y:A, R (f x) (f y) → R x y) →
    map_relation_alt R (f <$> m1) (f <$> m2) →
    map_relation_alt R m1 m2.
  Proof.
    intros Hf HR. intros k. specialize (HR k).
    rewrite !lookup_fmap in HR.
    destruct (m1 !! k); destruct (m2 !! k); [by apply Hf|done..].
  Qed.

  (* Lemma map_included_split `{∀ A, Lookup K A (MAP A)} {A} (R : A → A → Prop) *)
  (*       m1 m2 : *)
  (*   map_included R m1 m2 → *)
  (*   ∃ m21 m22, map_relation_alt R m1 m21 ∧ m21 ##ₘ m22. *)

  Lemma map_subseteq_disjoint_union_L `{Countable K} `{Countable V}
        (X Y : gmap K V) :
    X ⊆ Y ↔ (∃ (Z : gmap K V), Y = X ∪ Z ∧ X ##ₘ Z).
  Proof. Admitted.

  (* Lemma map_included_disjoint_union_L `{Countable K} `{Countable V} R *)
  (*       (X Y : gmap K V) : *)
  (*   map_included R X Y ↔ *)
  (*   (∃ (Y1 Y2 : gmap K V), Y = Y1 ∪ Y2 ∧ Y1 ##ₘ Y2 ∧ map_relation_alt R X Y1). *)
  (* Proof. Admitted. *)

  Lemma map_included_map_relation_alt `{∀ A, Lookup K A (MAP A)} {A}
        `{Union (MAP A)} (R : relation A) (m1 m2 : MAP A) :
    map_included R m1 m2 →
    ∃ m21 m22,
      m2 = m21 ∪ m22 ∧
      m21 ##ₘ m22 ∧
      map_relation_alt R m1 m21.
  Proof. Admitted.

  Lemma map_relation_alt_union_inv_l_L `{∀ A, Lookup K A (MAP A)} {A}
        `{Union (MAP A)} (R : relation A) (X1 X2 Y : MAP A) :
    X1 ##ₘ X2 →
    map_relation_alt R (X1 ∪ X2) Y ↔
    ∃ (Y1 Y2 : MAP A), Y = Y1 ∪ Y2 ∧
                          map_relation_alt R X1 Y1 ∧
                          map_relation_alt R X2 Y2.
  Proof. Admitted.

  (* Lemma map_subseteq_disjoint_union_L `{Countable K} `{Countable V} R *)
  (*       (X Y : gmap K V) : *)
  (*   map_included R X Y ↔ *)
  (*   (∃ (Z : gmap K V), map_relation_alt R X (Y ∪ Z) ∧ dom X = dom Y ∧ Y ##ₘ Z). *)
  (* Proof. Admitted. *)

  (* Lemma map_subseteq_disjoint_union_L `{Countable K} `{Countable V} R *)
  (*       (X Y : gmap K V) : *)
  (*   map_included R X Y ↔ *)
  (*   (∃ (Z : gmap K V), map_relation_alt R X Y ∧ *)
  (*                      Y ##ₘ Z). *)
  (* Proof. Admitted. *)


  Lemma auth_fuel_subseteq gfm fs :
    auth_fuel_is gfm -∗ ([∗ map] ρ↦f ∈ fs, ρ ↦F f) -∗ ⌜fs ⊆ gfm⌝.
  Proof. Admitted.

  Lemma map_disjoint_fmap_l `{Countable K} `{Countable V}
        (f : V → V) (m1 m2 : gmap K V) :
    (f <$> m1) ##ₘ m2 ↔ m1 ##ₘ m2.
  Proof.
    rewrite !map_disjoint_spec. setoid_rewrite lookup_fmap_Some. naive_solver.
  Qed.

  Lemma map_disjoint_fmap_r `{Countable K} `{Countable V}
        (f : V → V) (m1 m2 : gmap K V) :
    m1 ##ₘ (f <$> m2) ↔ m1 ##ₘ m2.
  Proof.
    rewrite !map_disjoint_spec. setoid_rewrite lookup_fmap_Some. naive_solver.
  Qed.

  (* Lemma map_subseteq_disjoint_union_L `{∀ A, Lookup K A (MAP A)} {A} *)
  (*       (X Y : MAP A) : *)
  (*  X ⊆ Y ↔ (∃ (Z : MAP A), Y = X ∪ Z ∧ X ##ₘ Z). *)

  (* Lemma map_included_fmap_l `{Countable K} {A} *)
  (*       (R : relation A) (m1 m2: gmap K A) (f : A → A) : *)
  (*   (∀ (x y :A), R (f x) y → R x y) → map_included R (f <$> m1) m2. *)
  (* Proof. *)
  (*   intros Hf. intros k. rewrite lookup_fmap. *)
  (* Admitted. *)

  Lemma map_relation_alt_fmap_l `{Countable K} `{Countable A} `{LeibnizEquiv (gmap K A)}
        (R : relation A) (m1 m2: gmap K A) (f : A → A) :
    (∀ (x y :A), R (f x) y → R (f x) (f y)) →
    map_relation_alt R (f <$> m1) m2 →
    ∃ m2', m2 = (f <$> m2').
  Proof. Admitted.

  Lemma map_relation_alt_dom `{Countable K} `{Countable A}
        (R : relation A) (m1 m2: gmap K A) :
    map_relation_alt R m1 m2 → dom m1 = dom m2.
  Proof. Admitted.

  Lemma map_included_relation_alt `{Countable K} `{Countable A}
        (R : relation A) (m1 m2: gmap K A) :
    dom m1 = dom m2 → map_relation_alt R m1 m2 → map_included R m1 m2.
  Proof. Admitted.

  Lemma map_relation_alt_union `{Countable K} `{Countable A}
        (R : relation A) (m11 m12 m21 m22 : gmap K A) :
    map_relation_alt R m11 m21 →
    map_relation_alt R m12 m22 →
    map_relation_alt R (m11 ∪ m12) (m21 ∪ m22).
  Proof. Admitted.

  Lemma map_relation_alt_refl `{Countable K} `{Countable A}
        (R : relation A) `{!Reflexive R} (m : gmap K A) :
    map_relation_alt R m m.
  Proof.
    rewrite /map_relation_alt /map_relation. intros.
    rewrite /option_relation. by destruct lookup.
  Qed.

  (* Lemma map_relation_alt_test `{Countable K} (m : gmap K nat) : *)
  (*   map_relation_alt le (S <$> m) m. *)
  (* Proof. apply map_relation_alt_refl. Admitted. *)

  (* TODO: Move *)
  Lemma locales_of_list_from_locale_from
        `{EqDecision (locale Λ)} tp0 tp1 ζ :
    is_Some (from_locale_from tp0 tp1 ζ) ↔
    ζ ∈ locales_of_list_from tp0 tp1.
  Proof.
    split; [apply locales_of_list_from_locale_from|].
    revert tp0; induction tp1 as [|e1 tp1 IH]; intros tp0.
    { simpl. intros Hin. inversion Hin. }
    intros Hin. rewrite /locales_of_list_from /=.
    destruct (decide (locale_of tp0 e1 = ζ)); simplify_eq; first set_solver.
    set_solver.
  Qed.

  Lemma oleq_map_relation_alt `{Countable K} (m1 m2: gmap K nat) k :
    k ∈ dom m1 → map_relation_alt (≤) m1 m2 → oleq (m1 !! k) (m2 !! k).
  Proof.
    rewrite /map_relation_alt /map_relation /option_relation.
    rewrite /oleq elem_of_dom. intros [v Heq] Hle.
    specialize (Hle k).
    rewrite Heq.
    rewrite Heq in Hle. done.
  Qed.

  Lemma auth_fuel_is_agree fm ζ fs :
    auth_fuel_is fm -∗ has_fuels ζ fs -∗
    ∃ fs', ⌜fm = fs ∪ fs'⌝ ∗ ⌜fs ##ₘ fs'⌝.
  Proof.
    iIntros "Hfm Hfuel".
    iDestruct "Hfuel" as (fs' Hle) "[Hζ Hfs]".
    iDestruct (auth_fuel_subseteq with "Hfm Hfs") as %Hle'.
    assert (∃ fs'', fm = fs ∪ fs'' ∧ fs ##ₘ fs'') as [fs'' [-> Hdisj]].
    { by apply map_subseteq_disjoint_union_L in Hle'. }
    iExists fs''.
    iSplit; [done|]. set_solver.
  Qed.


  Definition maps_inverse_match_alt `{Countable K} `{Countable V1}
             `{Countable V2}
             (m: gmap K V1) (m': gmap V2 (gset K)) :=
    ∀ k, is_Some (m !! k) ↔
         (∃ v (ks: gset K), m' !! v = Some ks ∧ k ∈ ks).

  Lemma has_fuels_agree fm rm ζ fs :
    auth_fuel_is fm -∗ auth_mapping_is rm -∗ has_fuels ζ fs -∗
    ∃ fs' fs'' rm',
      ⌜fm = fs ∪ fs''⌝ ∗
      ⌜rm = {[ζ := dom (fs ∪ fs')]} ∪ rm'⌝ ∗
      ⌜fs ##ₘ fs''⌝ ∗ ⌜fs' ##ₘ fs''⌝ ∗ ⌜fs ##ₘ fs'⌝ ∗ ⌜ζ ∉ dom rm'⌝ ∗
      ⌜maps_inverse_match_alt fs'' rm'⌝.
  Proof. Admitted.

  (* Lemma ghost_map_model_map_agree fs fs' : *)
  (*   auth_fuel_is ((S <$> fs) ∪ fs') -∗ *)
  (*   ⌜∃ fs1 fs2 fs3, *)
  (*     ls_fuel (trace_last auxtr) = (S <$> fs1) ∪ fs2 ∪ fs3 ∧ *)
  (*     fs1 ##ₘ fs2 ∧ fs2 ##ₘ fs3 ∧ fs1 ##ₘ fs3 ∧ *)
  (*     map_relation_alt (≤) (S <$> fs) (S <$> fs1) ∧ *)
  (*     map_relation_alt (≤) fs' fs2 ∧ *)
  (*     (* fuel_map_le (S <$> fs) (S <$> fs1) ∧ *) *)
  (*     map_Forall (λ r f, r ∉ M.(live_roles) (trace_last auxtr)) fs3⌝. *)

  Lemma fuel_map_preserve_dead_disjoint (δ : LM) m1 m2 m3 :
    ls_fuel δ = m2 ∪ m3 →
    map_relation_alt le m1 m2 →
    m2 ##ₘ m3 →
    fuel_map_preserve_dead m1 δ →
    map_Forall (λ r _, r ∉ M.(live_roles) δ) m3.
  Proof.
    intros Heq Hle Hdisj Hfmdead.
    intros ρ ? Hin'.
    intros Hlive.
    assert (ρ ∈ live_roles M δ → ρ ∈ dom m1) as Hfmdead'.
    { intros Hin''. eapply contrapositive. apply Hfmdead. done. }
    assert (ρ ∈ dom m1).
    { apply Hfmdead'. done. }
    assert (ρ ∈ dom m3).
    { apply elem_of_dom. done. }
    pose proof Hle as Hdisj'%map_relation_alt_dom.
    apply map_disjoint_dom_1 in Hdisj.
    set_solver.
  Qed.

  Lemma foo ζ m1 m2 m3 (δ1 δ2 : LiveState Λ M) :
    ls_fuel δ1 = (S <$> m1) ∪ m2 ∪ m3 →
    ls_fuel δ2 = m1 ∪ m2 →
    (∀ ρ, ρ ∈ dom m2 → δ1.(ls_mapping) !! ρ ≠ Some ζ) →
    ls_mapping δ2 ⊆ ls_mapping δ1 →
    m1 ##ₘ m2 → m2 ##ₘ m3 → m1 ##ₘ m3 →
    fuel_decr (Some ζ) None δ1 δ2.
  Proof.
    intros Hδ1 Hδ2 Hζ Hle Hdisj12 Hdisj23 Hdisj13 .
    rewrite /fuel_decr=> /=.
    intros ρ Hin1 Hin2 Hdecr.
    assert (ρ ∉ dom m3).
    { rewrite Hδ2 in Hin2.
      apply map_disjoint_dom in Hdisj12.
      apply map_disjoint_dom in Hdisj23.
      apply map_disjoint_dom in Hdisj13.
      set_solver. }
    inversion Hdecr; simplify_eq.
    - rewrite Hδ1 Hδ2.
      rewrite /oless.
      destruct (decide (ρ ∈ dom m2)) as [Hin|Hnin].
      { apply Hζ in Hin. rewrite Hsametid in Hin. done. }
      { rewrite (lookup_union_l); [|by apply not_elem_of_dom].
        rewrite (lookup_union_l); [|by apply not_elem_of_dom].
        rewrite (lookup_union_l); [|by apply not_elem_of_dom].
        assert (ρ ∈ dom m1).
        { rewrite Hδ2 in Hin2.
          apply map_disjoint_dom in Hdisj12.
          apply map_disjoint_dom in Hdisj23.
          apply map_disjoint_dom in Hdisj13.
          set_solver. }
        rewrite lookup_fmap.
        apply elem_of_dom in H1 as [? ->]=> /=. lia. }
    - destruct Hissome as [? Heq].
      rewrite Heq in Hneqtid.
      specialize (Hle ρ).
      destruct (ls_mapping δ2 !! ρ); [|done].
      destruct (ls_mapping δ1 !! ρ); [naive_solver|].
      simpl in *. done.
  Qed.
  
  (* OBS: Might need requirement that nothing is forked *)
  Lemma update_fuel_step extr (auxtr : auxiliary_trace LM) c2 fs ζ :
    (dom fs ≠ ∅) →
    locale_step (trace_last extr) (Some ζ) c2 →
    has_fuels_S ζ fs -∗
    model_state_interp (trace_last extr).1 (trace_last auxtr) ==∗
    ∃ δ2,
      ⌜ valid_state_evolution_fairness
        (extr :tr[Some ζ]: c2) (auxtr :tr[Silent_step ζ]: δ2) ⌝ ∗
      has_fuels ζ fs ∗ model_state_interp c2.1 δ2.
  Proof.
    iIntros (Hdom Hstep) "Hfuel Hm".
    iDestruct (has_fuel_in with "Hfuel Hm") as %Hin.

    iDestruct "Hm" as
      (gfm rm FR Hfmle Hfmdead Hmapinv Htp Hfr)
        "(Hfm & Hrm & HFR & Hm)".

    (* Compute ghost map *)
    iDestruct (has_fuels_agree with "Hfm Hrm Hfuel")
      as %(fs'' & fs' & rm' & -> & -> & Hdisj & Hdisj23' & Hdisj13' & Hζ &
          Hmapinv'').
    assert (fs ##ₘ fs') as Hdisj_alt by by apply map_disjoint_fmap_l in Hdisj.

    (* Compute original model map *)
    pose proof (map_included_map_relation_alt _ _ _ Hfmle)
      as (mfs & mfs3 & Heq & Hdisj3 & Hle).
    pose proof Hle
      as (mfs1 & mfs2 & -> & Hle1 & Hle2)%map_relation_alt_union_inv_l_L.

    (* Eaw.. *)
    pose proof Hle1 as [mfs1' ->]%map_relation_alt_fmap_l.
    2: by lia.
    2: by done.
    rename mfs1' into mfs1.

    (* TODO: Make lemma? *)
    assert (mfs1 ##ₘ mfs2) as Hdisj12.
    { pose proof Hle1 as Hdisj1%map_relation_alt_dom.
      pose proof Hle2 as Hdisj2%map_relation_alt_dom.
      apply map_disjoint_dom.
      apply map_disjoint_dom in Hdisj_alt.
      set_solver. }

    assert (mfs2 ##ₘ mfs3) as Hdisj23.
    { apply map_disjoint_dom in Hdisj3.
      apply map_disjoint_dom. set_solver. }

    assert (mfs1 ##ₘ mfs3) as Hdisj13.
    { apply map_disjoint_dom in Hdisj3.
      apply map_disjoint_dom. set_solver. }

    (* TODO: Make lemma? *)
    assert (map_Forall (λ r _, r ∉ M.(live_roles) (trace_last auxtr)) mfs3)
      as Hlive.
    { by eapply fuel_map_preserve_dead_disjoint. }

    (* TODO: Make lemma *)
    assert (∀ ρ, ρ ∈ dom mfs2 → (trace_last auxtr).(ls_mapping) !! ρ ≠ Some ζ).
    { intros ρ Hin'.
      assert (ρ ∈ dom fs') as Hin''.
      { by erewrite map_relation_alt_dom. }
      intros HSome.
      apply Hmapinv in HSome as [ks Heq'].
      assert (ρ ∈ dom ((S <$> fs) ∪ fs'')).
      { destruct Heq' as [Heq1' Heq2'].
        rewrite lookup_union_l' in Heq1'.
        - rewrite lookup_insert in Heq1'. set_solver.
        - rewrite lookup_insert. set_solver. }
      apply map_disjoint_dom in Hdisj.
      apply map_disjoint_dom in Hdisj23'.
      set_solver. }

    assert (M.(live_roles) (trace_last auxtr).(ls_under) ⊆ dom (mfs1 ∪ mfs2))
           as Hfueldom.
    { pose proof ((trace_last auxtr).(ls_fuel_dom)) as Hdom'.
      rewrite Heq in Hdom'.
      assert (live_roles M (trace_last auxtr) ## dom mfs3) as Hdisj'.
      { apply elem_of_disjoint. 
        intros ρ Hin1 Hin2.
        apply elem_of_dom in Hin2 as [f Heq'].
        specialize (Hlive ρ f Heq'). apply Hlive. done. }
      (* Do this manually to make it more robust. *)
      clear -Hdom' Hdisj'. set_solver. }

    assert (∃ mrm, maps_inverse_match mrm
              ({[ζ := dom (S <$> fs)]} ∪ rm')) as [mrm Hmapinv'].
    { exists (filter (λ kv, kv.1 ∉ dom fs'') (ls_mapping (trace_last auxtr))).
      split.
      - intros Hsome.
        destruct (decide (k ∈ dom fs'')) as [Hin'|Hnin].
        + apply map_filter_lookup_Some_1_2 in Hsome. 
          done.
        + apply map_filter_lookup_Some_1_1 in Hsome.
          apply Hmapinv in Hsome as [ks [Hks1 Hks2]].
          apply lookup_union_Some in Hks1; last first.
          { apply map_disjoint_dom. set_solver. }
          destruct Hks1 as [Hks1 | Hks1].
          * apply lookup_singleton_Some in Hks1 as [-> Hζ'].
            exists (dom (S <$> fs)).
            rewrite -Hζ' in Hks2.
            split; [|set_solver].
            rewrite lookup_union_l. 
            -- rewrite lookup_insert. done.
            -- by apply not_elem_of_dom.
          * exists ks.
            rewrite lookup_union_r. 
            -- set_solver.
            -- destruct (decide (ζ = v)) as [->|Hneq].
               ++ apply not_elem_of_dom in Hζ. set_solver.
               ++ by rewrite lookup_insert_ne.
      - intros [ks [Hks Hin']].
        destruct (decide (k ∈ dom fs'')) as [Hin''|Hnin].
        + apply lookup_union_Some in Hks; last first.
          { apply map_disjoint_dom. set_solver. }
          destruct Hks as [Hks | Hks].
          * destruct (decide (v = ζ)) as [->|Hneq].
            -- rewrite lookup_insert in Hks.
               apply map_disjoint_dom in Hdisj13'.
               set_solver.
            -- by rewrite lookup_insert_ne in Hks.
          * destruct (decide (v = ζ)) as [Heq'|Hneq].
            { rewrite Heq' in Hks.
              apply not_elem_of_dom in Hζ.
              set_solver. }
            assert (({[ζ := dom ((S <$> fs) ∪ fs'')]} ∪ rm') !! v = Some ks).
            { rewrite lookup_union_r. done. by rewrite lookup_insert_ne. }
            assert (({[ζ := dom ((S <$> fs) ∪ fs'')]} ∪ rm') !! ζ = Some $ dom ((S <$> fs) ∪ fs'')).
            { rewrite lookup_union_l; [|by apply not_elem_of_dom].
              rewrite lookup_insert. set_solver. }
            assert (v = ζ) as Heq'.
            { eapply maps_inverse_bij; try done. set_solver. }
            rewrite Heq' in Hks.
            apply not_elem_of_dom in Hζ.
            set_solver.
        + apply map_filter_lookup_Some_2; [|done].
          apply Hmapinv.
          apply lookup_union_Some in Hks; last first.
          { apply map_disjoint_dom. set_solver. }
          destruct Hks as [Hks | Hks].
          * apply lookup_singleton_Some in Hks as [-> Hζ'].
            exists (dom ((S <$> fs) ∪ fs'')).
            split; [|set_solver].
            rewrite lookup_union_l. 
            -- rewrite lookup_insert. done.
            -- by apply not_elem_of_dom.
          * exists ks.
            rewrite lookup_union_r. 
            -- set_solver.
            -- destruct (decide (ζ = v)) as [->|Hneq].
               ++ apply not_elem_of_dom in Hζ. set_solver.
               ++ by rewrite lookup_insert_ne.
    }

    (* TODO: Need to prove this. *)
    assert (dom mrm = dom (mfs1 ∪ mfs2)) as Hsamedoms.
    { apply set_eq.
      intros ρ.
      split.
      - intros [ζ' Hζ']%elem_of_dom.
        apply Hmapinv' in Hζ' as [ks [Hks Hin'']].
        rewrite dom_union.
        apply map_relation_alt_fmap_inv in Hle1; [|lia].
        apply map_relation_alt_dom in Hle1.
        apply map_relation_alt_dom in Hle2.
        rewrite -Hle1.
        rewrite -Hle2.
        rewrite elem_of_union.
        apply lookup_union_Some in Hks as [Hks | Hks];
          [| |by apply map_disjoint_dom; set_solver].
        { rewrite lookup_insert_Some in Hks.
          destruct Hks as [[-> Heq']|?]; [|set_solver].
          left. set_solver. }
        right.
        apply elem_of_dom.
        apply Hmapinv''. set_solver.
      - rewrite dom_union.
        apply map_relation_alt_fmap_inv in Hle1; [|lia].
        apply map_relation_alt_dom in Hle1.
        apply map_relation_alt_dom in Hle2.
        rewrite -Hle1.
        rewrite -Hle2.
        rewrite elem_of_dom.
        rewrite elem_of_union.
        rewrite !elem_of_dom.
        intros [[f Hf]|[f Hf]].
        + exists ζ.
          apply Hmapinv'.
          exists (dom (S <$> fs)).
          rewrite lookup_union_l; last first.
          { by apply not_elem_of_dom in Hζ. }
          rewrite lookup_insert. split; [done|].
          apply elem_of_dom. rewrite lookup_fmap. exists (S f).
          rewrite Hf. done.
        + assert (is_Some (fs' !! ρ)) as Hf' by eauto.
          apply Hmapinv'' in Hf' as [v [ks [Hks Hin'']]].
          exists v.
          apply Hmapinv'.
          exists ks.
          rewrite lookup_union_r; [set_solver|].
          assert (v ≠ ζ).
          { intros Heq'. rewrite -Heq' in Hζ. 
            apply not_elem_of_dom in Hζ.
            set_solver. }
          by rewrite lookup_insert_ne. }

    iExists {|
      ls_under := (trace_last auxtr).(ls_under);
      ls_fuel := mfs1 ∪ mfs2;
      ls_mapping := mrm;
      ls_fuel_dom := Hfueldom;
      ls_same_doms := Hsamedoms;
      |}.

    iMod (has_fuels_decr with "Hfm Hfuel") as "[Hfm Hfuel]"; [done|].
    (* Need lemma. *)
    iAssert (|==> auth_mapping_is ({[ζ := dom (S <$> fs)]} ∪ rm') ∗
             has_fuels ζ fs)%I with "[Hrm Hfuel]" as ">[Hrm Hfuel]".
    { 
      iDestruct "Hfuel" as (fsf Hfsf) "[Hf1 Hf2]".
      rewrite dom_union_L.
      rewrite !dom_fmap_L.
      rewrite -dom_union_L.
      apply subseteq_disjoint_union_L in Hfsf as [fsf' [-> Hdisj']].
      iDestruct (frag_mapping_same with "Hrm Hf1") as %Hsame.
      rewrite lookup_union_l in Hsame; [|by apply not_elem_of_dom in Hζ].
      rewrite lookup_insert in Hsame.
      simplify_eq.
      assert (dom fs'' = fsf') as Heq'.
      { rewrite dom_union_L in Hsame.
        apply map_disjoint_dom in Hdisj13'.
        set_solver. }
      rewrite !dom_union_L. rewrite Heq'.
      iMod (update_mapping_delete _ fsf' with "Hrm Hf1") as "[Hrm Hf1]".
      iModIntro. iFrame.
      rewrite -!insert_union_singleton_l.
      rewrite insert_insert.
      rewrite difference_union_distr_l_L.
      rewrite difference_diag_L.
      rewrite union_empty_r_L.
      rewrite difference_disjoint_L; [|done].
      iFrame.
      iExists _. iFrame. iPureIntro. done. }
      
    iModIntro.
    iSplitR.
    { iPureIntro.
      destruct c2.
      rewrite /valid_state_evolution_fairness=> /=.
      repeat split.
      - assert (∃ ρ, ρ ∈ dom fs) as [ρ Hρ].
        { assert ((∃ ρ, ρ ∈ dom fs) ∨ ¬ (∃ ρ, ρ ∈ dom fs)) as [?|?]
            by apply ExcludedMiddle; [done|set_solver]. }
        exists ρ. apply Hin. set_solver.
      - eapply foo; try done.
        intros ρ.
        simpl.
        destruct (mrm !! ρ) as [ζ'|] eqn:Heqn; last first.
        { simpl. by destruct lookup; destruct lookup. (* ??? *) }
        simpl.
        apply Hmapinv' in Heqn as [ks [HSome Hks]].
        assert (ls_mapping (trace_last auxtr) !! ρ = Some ζ').
        { apply Hmapinv.
          destruct (decide (ζ = ζ')) as [->|Hneq].
          { assert (ks = dom (S <$> fs)) as ->.
            { rewrite lookup_union_l' in HSome; [|by rewrite lookup_insert].
              rewrite lookup_insert in HSome. set_solver. }
            exists (dom ((S <$> fs) ∪ fs'')).
            split; [|set_solver].
            rewrite lookup_union_l'.
            rewrite lookup_insert. done.
            by rewrite lookup_insert. }
          rewrite lookup_union_r in HSome; [|by rewrite lookup_insert_ne].
          exists ks.
          split; [|done].
          rewrite lookup_union_r ; [|by rewrite lookup_insert_ne].
          done. }
        by rewrite H1.
      - intros ρ Hin' HSome.
        simpl.
        destruct (decide (ρ ∈ dom mfs3)) as [Hin''|Hnin].
        + right.
          split.
          * intros Hin'''.
            rewrite dom_union in Hin'''.
            apply elem_of_union in Hin'''.
            apply map_disjoint_dom in Hdisj13.
            apply map_disjoint_dom in Hdisj23.
            destruct Hin'''; set_solver.
          * rewrite elem_of_dom in Hin''.
            destruct Hin'' as [? ?].
            by eapply Hlive.
        + (* TODO: Improve this proof *)
          left. rewrite Heq.
          rewrite not_elem_of_dom in Hnin.
          (* Needs new lookup-union-none lemma *)
          rewrite /oleq.
          rewrite (lookup_union_l _ mfs3); [|done].
          rewrite !lookup_union.
          rewrite lookup_fmap.
          destruct (mfs1 !! ρ) eqn:Heqn1;
          destruct (mfs2 !! ρ) eqn:Heqn2=> /=; try lia.
          rewrite Heq in Hin'. rewrite elem_of_dom in Hin'.
          rewrite !lookup_union in Hin'.
          rewrite Hnin in Hin'.
          rewrite lookup_fmap in Hin'.
          rewrite Heqn1 in Hin'.
          rewrite Heqn2 in Hin'.
          simpl in *.
          by inversion Hin'.
      - rewrite Heq. set_solver.
      - rewrite /tids_smaller=> /=.
        intros ρ' ζ' Hmap.
        destruct (trace_last extr) eqn:Heqn.
        eapply from_locale_step; [eapply Hstep|].
        simpl in *.
        (* mrm is a subset of last mapping *)
        assert ((trace_last auxtr).(ls_mapping) !! ρ' = Some ζ') as Hmap'.
        { apply Hmapinv. apply Hmapinv' in Hmap as [ks [HSome Hks]].
          destruct (decide (ζ = ζ')) as [->|Hneq].
          { assert (ks = dom (S <$> fs)) as ->.
            { rewrite lookup_union_l' in HSome; [|by rewrite lookup_insert].
              rewrite lookup_insert in HSome. set_solver. }
            exists (dom ((S <$> fs) ∪ fs'')).
            split; [|set_solver].
            rewrite lookup_union_l'.
            rewrite lookup_insert. done.
            by rewrite lookup_insert. }
          rewrite lookup_union_r in HSome; [|by rewrite lookup_insert_ne].
          exists ks.
          split; [|done].
          rewrite lookup_union_r ; [|by rewrite lookup_insert_ne].
          done. }
        apply Hmapinv in Hmap'.
        destruct Hmap' as [ks [HSome Hks]].
        assert (∀ ζ' : locale Λ, ζ' ∉ locales_of_list l0 → ζ' ∉ dom ({[ζ := dom ((S <$> fs) ∪ fs'')]} ∪ rm')) as Htp''.
        { intros. rewrite not_elem_of_dom. by apply Htp. }
        assert (ζ' ∈ locales_of_list l0).
        { eapply contrapositive. eapply Htp''.
          rewrite elem_of_dom. done. }
        by apply locales_of_list_from_locale_from. }
    iFrame "Hfuel".
    iExists _, _, _. iFrame. iPureIntro.
    repeat split.
    - simpl.
      rewrite /fuel_map_le.
      apply map_included_relation_alt.
      { rewrite dom_union_L.
        rewrite dom_union_L.
        f_equiv.
        - rewrite -(dom_fmap_L S fs).
          rewrite -(dom_fmap_L S mfs1).
          by eapply map_relation_alt_dom.
        - by eapply map_relation_alt_dom. }
      apply map_relation_alt_union.
      + eapply map_relation_alt_fmap_inv; [|done]. intros. lia.
      + done.
    - intros ρ Hin'. apply Hfmdead. set_solver.
    - simpl. apply Hmapinv'.
    - simpl. apply Hmapinv'.
    - intros ζ' Hζ'.
      assert (ζ' ∉ locales_of_list (trace_last extr).1) as Hζ''.
      { destruct (trace_last extr), c2.
        eapply locales_of_list_step_incl in Hstep. set_solver. }
      apply Htp in Hζ''.
      apply not_elem_of_dom in Hζ''.
      apply not_elem_of_dom. set_solver.
    - simpl. rewrite Heq in Hfr. set_solver.
  Qed.

  Lemma update_model_step
        (extr : execution_trace Λ)
        (auxtr: auxiliary_trace LM) c2 s1 s2 fs ρ (δ1 : LM) ζ f :
    ρ ∉ dom fs →
    trace_last auxtr = δ1 →
    locale_step (trace_last extr) (Some ζ) c2 →
    fmtrans _ s1 (Some ρ) s2 →
    has_fuels ζ ({[ρ := f]} ∪ fmap S fs) -∗ frag_model_is s1 -∗
    model_state_interp (trace_last extr).1 δ1 ==∗
    ∃ (δ2: LM),
      ⌜valid_state_evolution_fairness
        (extr :tr[Some ζ]: c2) (auxtr :tr[Take_step ρ ζ]: δ2)⌝ ∗
      has_fuels ζ ({[ρ := LM.(lm_fl) s2]} ∪ fs) ∗
      frag_model_is s2 ∗ model_state_interp c2.1 δ2.
  Proof. Admitted.

  Lemma update_fork_step R1 R2 tp1 tp2 (extr : execution_trace Λ)
        (auxtr: auxiliary_trace LM) ζ efork σ1 σ2 (Hdisj: R1 ##ₘ R2) :
    R1 ∪ R2 ≠ ∅ →
    trace_last extr = (tp1, σ1) →
    locale_step (tp1, σ1) (Some ζ) (tp2, σ2) →
    (∃ tp1', tp2 = tp1' ++ [efork] ∧ length tp1' = length tp1) →
    has_fuels_S ζ (R1 ∪ R2) -∗
    model_state_interp (trace_last extr).1 (trace_last auxtr) ==∗
    ∃ δ2,
      ⌜valid_state_evolution_fairness
        (extr :tr[Some ζ]: (tp2, σ2)) (auxtr :tr[Silent_step ζ]: δ2)⌝ ∗
      has_fuels (locale_of tp1 efork) R2 ∗
      has_fuels ζ R1 ∗
      model_state_interp tp2 δ2.
  Proof. Admitted.

End model_state_lemmas.
