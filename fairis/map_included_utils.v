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
