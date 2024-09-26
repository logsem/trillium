From trillium.fairness Require Import fuel resources.
From trillium.fairness.heap_lang.examples.yesno Require Import yesno yesno_mus yesno_threads.
From trillium.fairness.heap_lang.examples.even_odd Require Import eo_vs_mod model_updates thread_progs.


Close Scope Z. 


Definition combined: val :=
  λ: "N" "l",
     Fork (yesno.start "N") ;;
     Fork (eo_vs_mod.start incr_loop_even_prog incr_loop_odd_prog "l")
.


Section CombinedProof.
  Context `{LM: LiveModel heap_lang M}.
  Context `{!heapGS Σ LM, !yesnoPreG Σ, !evenoddPreG Σ}. 
  
  Context (st_res even_at odd_at: nat -> iProp Σ). 
  Context
    (st_res_SR_even: @StateRes _ Nat.even st_res even_at)
    (st_res_SR_odd: @StateRes _ Nat.odd st_res odd_at). 

  Lemma combined_spec tid (N: nat) l f 
    (Hf: f > 70) N1 N2
    (EVEN: N1 < N2)
    Ns ρ__eo1 ρ__eo2 ρ__yn1 ρ__yn2
    (* (NEQ: ρ1 ≠ ρ2) *)
    (DISJ: NoDup [ρ__eo1; ρ__eo2; ρ__yn1; ρ__yn2])
    (FLM: lm_flm LM >= 70):
    {{{
        (∀ l, l ↦ #true ==∗ ∃ (_: yesnoG Σ),
                yes_vs l Ns ρ__yn1 ∗ no_vs l Ns ρ__yn2 ∗ yes_at N ∗ no_at N) ∗
        (* tid ↦M {[  ρ__yn1 := f; ρ__yn2 := f ]} *)
        has_fuels tid (gset_to_gmap f {[ ρ__eo1; ρ__eo2; ρ__yn1; ρ__yn2 ]} ) ∗
        ⌜N > 0⌝ ∗ 
        even_vs st_res_SR_even l Ns__eo ρ__eo1 ∗
        odd_vs st_res_SR_odd l Ns__eo ρ__eo2 ∗
        main_vs st_res l Ns__eo ∗
        even_at N1 ∗ odd_at N2}}}
      combined #N #l @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using All.
    iIntros (Φ) "(VS_YN & Hf & %HN & VS_E & VS_O & VS_M & E & O) Hkont". rewrite /combined.
    rewrite -!union_assoc_L. 
    rewrite !gset_to_gmap_union_singleton utils.gset_to_gmap_singleton.
    wp_pures.

    wp_bind (Fork _).
    iApply (wp_role_fork _ tid _ _ _ _ {[ρ__yn1 := _; ρ__yn2 := _]}  with "[Hf ] [VS_YN]").
    3: { rewrite has_fuels_gt_1; [| solve_fuel_positive].
         rewrite !fmap_insert fmap_empty insert_empty.
         iApply (has_fuels_proper with "[$]"); [done| ].
         f_equiv. 
         rewrite !insert_union_singleton_l.
         rewrite !map_union_assoc. reflexivity. }
    { admit. }
    { clear. intros ?%dom_empty_iff_L. set_solver. }
    { iIntros (τ') "!> Hf". iApply (yesno.start_spec with "[VS_YN Hf]").
      5: set_solver.
      4: by iFrame.
      3: lia.
      2: { admit. }
      lia. }

    iIntros "!> Hf". iModIntro.
    rewrite -insert_union_singleton_l. wp_pures.

    iApply (wp_role_fork _ tid _ _ _ with "[Hf] [-Hkont]").
    { apply map_disjoint_empty_l. }
    2: { rewrite map_empty_union.
         rewrite has_fuels_gt_1; [| solve_fuel_positive].
         rewrite !fmap_insert fmap_empty insert_empty. iFrame. }
    { clear. intros ?%dom_empty_iff_L. set_solver. }
    2: { iNext. iIntros "?". iModIntro. by iApply "Hkont". }
    iIntros (τ') "!> Hf".
    iApply (eo_vs_mod.start_spec with "[-]").
    6: set_solver.
    5: { iFrame "VS_E VS_O VS_M E O Hf".
         admit. }
    4: lia.
    3: { admit. }
    2: lia.
    lia.
    Unshelve. admit.
  Admitted.
    

End CombinedProof.
