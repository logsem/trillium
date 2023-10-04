From Coq Require Import ssreflect.
From stdpp Require Import gmap.

(* TODO: Make context, and generalise lemmas to canonical representation *)
Lemma map_included_spec `{∀ A, Lookup K A (MAP A)} {A}
      (R : relation A) (m1 m2 : MAP A) :
  map_included R m1 m2 ↔
  (∀ k v1, m1 !! k = Some v1 → ∃ v2, m2 !! k = Some v2 ∧ R v1 v2).
Proof.
  split.
  - rewrite /map_included /map_relation /option_relation.
    intros HR.
    intros k v1 Hv1.
    specialize (HR k). rewrite Hv1 in HR.
    destruct (m2 !! k) eqn:Heqn; [|done].
    exists a. done.
  - intros HR.
    rewrite /map_included /map_relation /option_relation.
    intros k.
    destruct (m1 !! k) eqn:Heqn.
    + apply HR in Heqn as [v2 [Hv2 HR']].
      rewrite Hv2. done.
    + by destruct (m2 !! k).
Qed.

Lemma map_included_insert `{Countable K} {A}
      (R : relation A) (m1 m2 : gmap K A) i x y :
  R x y →
  map_included R m1 m2 →
  map_included R (<[i:=x]>m1) (<[i:=y]>m2).
Proof.
  intros HR Hle.
  rewrite /map_included /map_relation /option_relation.
  intros k.
  destruct (decide (i=k)) as [<-|Hneq].
  - rewrite !lookup_insert. done.
  - rewrite lookup_insert_ne; [done|].
    rewrite lookup_insert_ne; [done|].
    apply Hle.
Qed.


Lemma map_included_refl `{∀ A, Lookup K A (MAP A)} {A}
      `{!Reflexive R} (m : MAP A) :
  map_included R m m.
Proof. rewrite map_included_spec. intros. by eauto. Qed.

(* TODO: Move *)
(* TODO: Generalise to map_included instead of subseteq? *)
Lemma map_included_subseteq `{∀ A, Lookup K A (MAP A)} {A}
      (R : relation A) (m1 m2 m3 : MAP A) :
  m1 ⊆ m2 → map_included R m2 m3 → map_included R m1 m3.
Proof.
  rewrite /subseteq /map_subseteq !map_included_spec.
  intros Hle1 Hle2.
  intros k v1 HSome.
  apply Hle1 in HSome as [v2 [HSome HR]].
  apply Hle2 in HSome as [v3 [HSome HR']].
  exists v3. split; [done|].
  by subst.
Qed.

(* TODO: Generalise to better typeclasses *)
Lemma map_included_subseteq_inv `{Countable K} {V}
      (R : relation V) (m1 m2 : gmap K V) :
  map_included R m1 m2 → (dom m1) ⊆ (dom m2).
Proof.
  rewrite /map_included /map_relation /option_relation.
  intros Hle k. rewrite !elem_of_dom. specialize (Hle k).
  intros [? Heq]. rewrite Heq in Hle.
  by destruct (m2 !! k).
Qed.

Lemma map_included_transitivity `{∀ A, Lookup K A (MAP A)} {A}
      `{!Transitive R} (m1 m2 m3 : MAP A) :
  map_included R m1 m2 → map_included R m2 m3 → map_included R m1 m3.
Proof.
  rewrite !map_included_spec.
  intros Hle1 Hle2.
  intros k v1 HSome.
  apply Hle1 in HSome as [v2 [HSome HR]].
  apply Hle2 in HSome as [v3 [HSome HR']].
  exists v3. split; [done|].
  by etransitivity.
Qed.

(* TODO: Generalize types *)
Lemma map_included_fmap `{Countable K} {A}
      (R : relation A) (m : gmap K A) (f : A → A) :
  (∀ x:A, R x (f x)) → map_included R m (f <$> m).
Proof.
  intros Hf. intros k. rewrite lookup_fmap.
  destruct (m !! k); [by apply Hf|done].
Qed.

Lemma map_included_mono `{Countable K} {A}
      (R : relation A) (m1 m2 : gmap K A) (f : A → A) :
  (∀ x1 x2 : A, R x1 x2 → R (f x1) (f x2)) →
  map_included R m1 m2 →
  map_included R (f <$> m1) (f <$> m2).
Proof.
  rewrite !map_included_spec.
  intros Hf Hle. intros k v1.  
  intros HSome.
  apply lookup_fmap_Some in HSome as (v1'&HSome&Hv1').
  apply Hle in Hv1' as (v2'&HSome2&Hv2).
  exists (f v2'). simplify_eq.
  rewrite lookup_fmap. rewrite HSome2.
  split; [done|]. by apply Hf.
Qed.

Lemma map_included_mono_strong `{Countable K} {A}
      (R : relation A) (m1 m2 : gmap K A) (f1 f2 : gmap K A → gmap K A) :
  dom (f1 m1) ⊆ dom m1 → dom m2 ⊆ dom (f2 m2) →
  (∀ k x1 x2 y1 y2,
     m1 !! k = Some x1 → m2 !! k = Some x2 →
     (f1 m1) !! k = Some y1 → (f2 m2) !! k = Some y2 →
     R x1 x2 → R y1 y2) →
  map_included R m1 m2 →
  map_included R (f1 m1) (f2 m2).
Proof.
  rewrite !map_included_spec.
  intros Hle1 Hle2 Hf HR. intros k v1.  
  intros HSome1.
  assert (∃ v1', m1 !! k = Some v1') as [v1' HSome1'].
  { apply elem_of_dom_2 in HSome1. apply Hle1 in HSome1.
    apply elem_of_dom in HSome1 as [? ->]. by eauto. }
  pose proof HSome1' as HSome1''.
  apply HR in HSome1'' as (v2'&HSome2'&Hv2').
  assert (∃ v2, f2 m2 !! k = Some v2) as [v2 HSome2].
  { apply elem_of_dom_2 in HSome2'. apply Hle2 in HSome2'.
    apply elem_of_dom in HSome2' as [? ->]. by eauto. }
  exists v2. split; [done|].
  by eapply Hf.
Qed.

Lemma map_included_filter `{Countable K} {A}
      (R : relation A) (m1 m2 : gmap K A) (P : (K * A) → Prop)
      `{∀ x, Decision (P x)} :
  (∀ k x1 x2,
     m1 !! k = Some x1 → m2 !! k = Some x2 → P (k,x1) → P (k,x2)) →
  map_included R m1 m2 →
  map_included R (filter P m1) (filter P m2).
Proof.
  rewrite !map_included_spec.
  intros HP Hle k v1 HSome1.
  pose proof HSome1 as HP'.
  apply map_filter_lookup_Some_1_1 in HSome1.
  apply map_filter_lookup_Some_1_2 in HP'.
  pose proof HSome1 as HSome2.
  apply Hle in HSome2 as [v2 [HSome2 HR]].
  specialize (HP k v1 v2 HSome1 HSome2 HP').
  exists v2. split; [|done].
  by apply map_filter_lookup_Some_2.
Qed.

Lemma map_included_subseteq_r `{∀ A, Lookup K A (MAP A)} {A}
      (R : relation A) (m1 m2 m3 : MAP A) :
  m2 ⊆ m3 → map_included R m1 m2 → map_included R m1 m3.
Proof.
  rewrite /subseteq /map_subseteq !map_included_spec.
  intros Hle1 Hle2.
  intros k v1 HSome.
  apply Hle2 in HSome as [v2 [HSome HR]].
  apply Hle1 in HSome as [v3 [HSome HR']].
  exists v3. split; [done|].
  by subst.
Qed.

Definition map_agree_R `{∀ A, Lookup K A (MAP A)} {A B}
           (R : A → B → Prop) (m1 : MAP A) (m2 : MAP B) :=
  map_relation R (λ _, False) (λ _, False) m1 m2.

Lemma map_agree_R_spec `{∀ A, Lookup K A (MAP A)} {A}
      (R : relation A) (m1 m2 : MAP A) :
  map_agree_R R m1 m2 ↔
  (∀ k v1, m1 !! k = Some v1 → ∃ v2, m2 !! k = Some v2 ∧ R v1 v2) ∧
  (∀ k v2, m2 !! k = Some v2 → ∃ v1, m1 !! k = Some v1 ∧ R v1 v2).
Proof.
  rewrite /map_agree_R /map_relation /option_relation. split.
  - intros HR. split.
    + intros k v HSome. specialize (HR k). rewrite HSome in HR.
      destruct (m2 !! k); [by eauto|done].
    + intros k v HSome. specialize (HR k). rewrite HSome in HR.
      destruct (m1 !! k); [by eauto|done].
  - intros [HR1 HR2] k.
    destruct (m1 !! k) as [v1|] eqn:Heqn1.
    { by apply HR1 in Heqn1 as [? [-> ?]]. }
    destruct (m2 !! k) as [v2|] eqn:Heqn2.
    { apply HR2 in Heqn2 as [? [? ?]]. by simplify_eq. }
    done.
Qed.

Lemma map_included_delete `{Countable K} {V}
      (R : relation V) (m1 m2 : gmap K V) k :
  map_included R m1 m2 →
  map_included R (delete k m1) (delete k m2).
Proof.
  rewrite !map_included_spec.
  intros Hle k' v HSome.
  apply lookup_delete_Some in HSome as [HK HSome].
  apply Hle in HSome as (?&?&?).
  exists x. by rewrite lookup_delete_ne.
Qed.

Lemma map_agree_R_dom `{Countable K} {V}
      (R : relation V) (m1 m2 : gmap K V) :
  map_agree_R R m1 m2 → dom m1 = dom m2.
Proof.
  rewrite map_agree_R_spec. intros [Hle1 Hle2]. apply set_eq.
  intros k. split.
  - intros [v1 HSome1]%elem_of_dom.
    apply Hle1 in HSome1 as (?&?&?).
    by apply elem_of_dom.
  - intros [v2 HSome2]%elem_of_dom.
    apply Hle2 in HSome2 as (?&?&?).
    by apply elem_of_dom.
Qed.

Lemma map_agree_R_insert `{Countable K} {V}
      (R : relation V) (m1 m2 : gmap K V) k v1 v2 :
  R v1 v2 →
  map_agree_R R m1 m2 →
  map_agree_R R (<[k:=v1]>m1) (<[k:=v2]>m2).
Proof.
  rewrite !map_agree_R_spec.
  intros HR [Hle1 Hle2].
  split.
  - intros k' v1' HSome1.
    destruct (decide (k = k')) as [->|Hneq].
    + rewrite lookup_insert in HSome1. simplify_eq.
      exists v2. rewrite lookup_insert. done.
    + rewrite lookup_insert_ne in HSome1; [done|].
      apply Hle1 in HSome1 as (v2'&HSome2&HR2).
      exists v2'. rewrite lookup_insert_ne; [|done]. done.
  - intros k' v2' HSome2.
    destruct (decide (k = k')) as [->|Hneq].
    + rewrite lookup_insert in HSome2. simplify_eq.
      exists v1. rewrite lookup_insert. done.
    + rewrite lookup_insert_ne in HSome2; [done|].
      apply Hle2 in HSome2 as (v1'&HSome1&HR1).
      exists v1'. rewrite lookup_insert_ne; [|done]. done.
Qed.

Lemma map_agree_R_insert_inv `{Countable K} {V}
      (R : relation V) (m1 m2 : gmap K V) k v1 v2 :
  k ∉ dom m1 → k ∉ dom m2 →
  map_agree_R R (<[k:=v1]>m1) (<[k:=v2]>m2) →
  map_agree_R R m1 m2.
Proof.
  intros Hnin1 Hnin2.
  rewrite !map_agree_R_spec.
  intros [Hle1 Hle2].
  split.
  - intros k' v1' HSome1.
    destruct (decide (k = k')) as [->|Hneq].
    { apply not_elem_of_dom in Hnin1. set_solver. }
    assert (<[k:=v1]>m1 !! k' = Some v1') as HSome1'.
    { by rewrite lookup_insert_ne. }
    apply Hle1 in HSome1' as (v2'&HSome2&HR).
    rewrite lookup_insert_ne in HSome2; [done|].
    by eauto.
  - intros k' v2' HSome2.
    destruct (decide (k = k')) as [->|Hneq].
    { apply not_elem_of_dom in Hnin2. set_solver. }
    assert (<[k:=v2]>m2 !! k' = Some v2') as HSome2'.
    { by rewrite lookup_insert_ne. }
    apply Hle2 in HSome2' as (v1'&HSome1&HR).
    rewrite lookup_insert_ne in HSome1; [done|].
    by eauto.
Qed.

Lemma map_agree_R_agree `{Countable K} {V}
      (R : relation V) (m1 m2 : gmap K V) k v1 v2 :
  m1 !! k = Some v1 → m2 !! k = Some v2 →
  map_agree_R R m1 m2 →
  R v1 v2.
Proof.
  rewrite map_agree_R_spec.
  intros HSome1 HSome2 Hle.
  apply Hle in HSome1 as (v2'&HSome2'&HR).
  rewrite HSome2' in HSome2. by simplify_eq.
Qed.

Lemma map_included_R_agree `{Countable K} {V}
      (R : relation V) (m1 m2 : gmap K V) k v1 v2 :
  m1 !! k = Some v1 → m2 !! k = Some v2 →
  map_included R m1 m2 →
  R v1 v2.
Proof.
  rewrite map_included_spec.
  intros HSome1 HSome2 Hle.
  apply Hle in HSome1 as (v2'&HSome2'&HR).
  rewrite HSome2' in HSome2. by simplify_eq.
Qed.

Lemma map_included_map_agree_R `{Countable K} {V}
      (R : relation V) (m1 m2 : gmap K V) :
  map_included R m1 m2 →
  ∃ m21 m22,
    m2 = m21 ∪ m22 ∧
    m21 ##ₘ m22 ∧
    map_agree_R R m1 m21.
Proof.
  revert m1.
  induction m2 as [|k v2 m2 Hnin IHm2] using map_ind; intros m1 Hle.
  { by exists ∅, ∅. }
  destruct (decide (k ∈ dom m1)) as [Hin|Hnin']; last first.
  { apply (map_included_delete _ _ _ k) in Hle.
    rewrite delete_insert in Hle; [done|].
    apply IHm2 in Hle as (m21&m22&->&Hdisj&HR).
    exists m21, (<[k:=v2]>m22).
    assert (dom m1 = dom m21) as Hdom.
    { eapply map_agree_R_dom. apply not_elem_of_dom in Hnin'.
      by rewrite delete_notin in HR. }
    apply map_disjoint_dom in Hdisj.
    rewrite insert_union_r; [by apply not_elem_of_dom; set_solver|].
    split; [done|].
    apply not_elem_of_dom in Hnin'.
    rewrite delete_notin in HR; [done|].
    split; [|done].
    apply map_disjoint_dom.
    apply not_elem_of_dom in Hnin'.
    set_solver. }
  apply elem_of_dom in Hin as [v1 HSome].
  assert (R v1 v2).
  { eapply map_included_R_agree; [| |done].
    - done.
    - by rewrite lookup_insert. }
  apply (map_included_delete _ _ _ k) in Hle.
  rewrite delete_insert in Hle; [done|].
  apply IHm2 in Hle as (m21&m22&->&Hdisj&HR).
  exists (<[k:=v2]>m21), m22.
  assert (dom (delete k m1) = dom m21) as Hdom.
  { eapply map_agree_R_dom. done. }
  apply map_disjoint_dom in Hdisj.
  rewrite insert_union_l.
  split; [done|].
  apply (map_agree_R_insert _ _ _ k v1 v2) in HR; [|done].
  rewrite insert_delete in HR; [done|].
  split; [|done].
  apply map_disjoint_dom.
  rewrite dom_insert_L.
  apply not_elem_of_dom in Hnin.
  set_solver.
Qed.

Lemma map_agree_R_map_included `{Countable K} {V}
      (R : relation V) (m1 m2 : gmap K V) :
  map_agree_R R m1 m2 → map_included R m1 m2.
Proof.
  rewrite map_included_spec map_agree_R_spec.
  by intros [Hle _].
Qed.

Lemma map_agree_R_union_inv `{Countable K} {V}
      (R : relation V) (m11 m12 m2 : gmap K V) :
  m11 ##ₘ m12 →
  map_agree_R R (m11 ∪ m12) m2 →
  ∃ m21 m22, m2 = m21 ∪ m22 ∧ map_agree_R R m11 m21 ∧
             map_agree_R R m12 m22.
Proof.
  intros Hdisj%map_disjoint_dom Hle.
  pose proof Hle as Hdom%map_agree_R_dom.
  rewrite comm in Hdom.
  rewrite dom_union_L in Hdom.
  apply dom_union_inv_L in Hdom as (m21&m22&->&Hdosj&Hdom1&Hdom2);
    [|done].
  exists m21, m22.
  split; [done|].
  split.
  - apply map_agree_R_spec.
    split.
    + intros k v1 HSome1.
      apply map_agree_R_spec in Hle as [Hle1 Hle2].
      assert ((m11 ∪ m12) !! k = Some v1) as HSome1'.
      { rewrite lookup_union_l; [|done].
        apply not_elem_of_dom.
        apply elem_of_dom_2 in HSome1. set_solver. }
      apply Hle1 in HSome1' as (v2&HSome2'&HR).
      assert (m21 !! k = Some v2) as HSome2.
      { rewrite lookup_union_l in HSome2'; [|done].
        apply not_elem_of_dom. apply elem_of_dom_2 in HSome1.
        set_solver. }
      eauto.
    + intros k v2 HSome2.
      apply map_agree_R_spec in Hle as [Hle1 Hle2].
      assert ((m21 ∪ m22) !! k = Some v2) as HSome2'.
      { rewrite lookup_union_l; [|done].
        apply not_elem_of_dom.
        apply elem_of_dom_2 in HSome2. set_solver. }
      apply Hle2 in HSome2' as (v1&HSome1'&HR).
      assert (m11 !! k = Some v1) as HSome1.
      { rewrite lookup_union_l in HSome1'; [|done].
        apply not_elem_of_dom. apply elem_of_dom_2 in HSome2.
        set_solver. }
      eauto.
  - apply map_agree_R_spec.
    split.
    + intros k v1 HSome1.
      apply map_agree_R_spec in Hle as [Hle1 Hle2].
      assert ((m11 ∪ m12) !! k = Some v1) as HSome1'.
      { rewrite lookup_union_r; [|done].
        apply not_elem_of_dom.
        apply elem_of_dom_2 in HSome1. set_solver. }
      apply Hle1 in HSome1' as (v2&HSome2'&HR).
      assert (m22 !! k = Some v2) as HSome2.
      { rewrite lookup_union_r in HSome2'; [|done].
        apply not_elem_of_dom. apply elem_of_dom_2 in HSome1.
        set_solver. }
      eauto.
    + intros k v2 HSome2.
      apply map_agree_R_spec in Hle as [Hle1 Hle2].
      assert ((m21 ∪ m22) !! k = Some v2) as HSome2'.
      { rewrite lookup_union_r; [|done].
        apply not_elem_of_dom.
        apply elem_of_dom_2 in HSome2. set_solver. }
      apply Hle2 in HSome2' as (v1&HSome1'&HR).
      assert (m12 !! k = Some v1) as HSome1.
      { rewrite lookup_union_r in HSome1'; [|done].
        apply not_elem_of_dom. apply elem_of_dom_2 in HSome2.
        set_solver. }
      eauto.
Qed.

(* OBS: Need restrictions on f *)
Lemma map_agree_R_fmap_inv `{Countable K} {V}
      (R : relation V) (m1 m2 : gmap K V) f :
  (* OBS: Is this a general relation/function property? *)
  (∀ v1 v2, R (f v1) v2 → ∃ v2', v2 = f v2') →
  map_agree_R R (f <$> m1) m2 →
  ∃ m2', m2 = f <$> m2'.
Proof.
  revert m1.
  induction m2 as [|k v2 m2 Hnin IHm2] using map_ind; intros m1 Hf Hle.
  { exists ∅. rewrite fmap_empty. done. }
  pose proof Hle as Hle'.
  apply map_agree_R_spec in Hle.
  assert (<[k:=v2]> m2 !! k = Some v2) as HSome2
                                            by by rewrite lookup_insert.
  apply Hle in HSome2 as (v1&HSome1&HR).
  apply lookup_fmap_Some in HSome1 as (v1'&<-&HSome1').
  assert (∃ v2', v2 = f v2') as [v2' Heq].
  { by eapply Hf. }
  rewrite Heq in HR.
  assert (map_agree_R R (f <$> (delete k m1)) m2) as Hle''.
  { rewrite -(insert_id m1 k v1') in Hle'; [done|].
    rewrite -insert_delete_insert in Hle'.
    rewrite fmap_insert in Hle'.
    eapply map_agree_R_insert_inv; [| |apply Hle'].
    - set_solver.
    - apply not_elem_of_dom. set_solver.
  }
  apply IHm2 in Hle'' as [m2' Heq']; [|done].
  exists (<[k:=v2']>m2').
  rewrite fmap_insert. rewrite Heq. f_equiv. done.
Qed.

(* OBS: Need restrictions on f *)
Lemma map_agree_R_fmap `{Countable K} {V}
      (R : relation V) (m1 m2 : gmap K V) f :
  (∀ v1 v2, R (f v1) (f v2) → R v1 v2) →
  map_agree_R R (f <$> m1) (f <$> m2) →
  map_agree_R R m1 m2.
Proof.
  intros Hf.
  rewrite !map_agree_R_spec.
  intros [Hle1 Hle2].
  split.
  - intros k v1 HSome1.
    assert ((f <$> m1) !! k = Some (f v1)) as HSome1'.
    { rewrite lookup_fmap. destruct (m1 !! k); [by simplify_eq|done]. }
    apply Hle1 in HSome1' as (v2'&HSome2'&HR).
    apply lookup_fmap_Some in HSome2' as (v2&<-&HSome2).
    apply Hf in HR.
    by eauto.
  - intros k v2 HSome2.
    assert ((f <$> m2) !! k = Some (f v2)) as HSome2'.
    { rewrite lookup_fmap. destruct (m2 !! k); [by simplify_eq|done]. }
    apply Hle2 in HSome2' as (v1'&HSome1'&HR).
    apply lookup_fmap_Some in HSome1' as (v1&<-&HSome1).
    apply Hf in HR.
    by eauto.
Qed.

