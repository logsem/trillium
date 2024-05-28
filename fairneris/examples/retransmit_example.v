From stdpp Require Import list fin_maps.
From iris.algebra Require Import excl_auth.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From trillium.program_logic Require Import ectx_lifting.
From fairneris Require Import fairness fair_resources fuel.
From fairneris.examples Require Import retransmit_model.
From fairneris.aneris_lang Require Import proofmode.
From fairneris.aneris_lang.state_interp Require Import state_interp state_interp_events.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.

(*Temporary*)
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.

Definition Aprog (saA saB : socket_address) : expr :=
  let: "shA" := NewSocket #() in
  SocketBind "shA" #saA;;
  let: "f" := (rec: "go" <> := SendTo "shA" #"Hello" #saB;; "go" #()) in
  "f" #().

Definition wait_receive : val :=
  (λ: "sh",
    SetReceiveTimeout "sh" #1 #1 ;;
    let: "go" := rec: "go" <> :=
     let: "r" := ReceiveFrom "sh" in
     if: "r" = NONEV then "go" #() else #()%V
    in "go" #()
  ).
(* Definition wait_receive := wait_receive_def. *)
(* Lemma wait_receive_eq : wait_receive = wait_receive_def. *)
(* Proof. done. Qed. *)
(* Opaque wait_receive. *)

Definition Bprog saA saB : expr :=
  let: "shB" := NewSocket #() in
  SocketBind "shB" #saB;;
  wait_receive "shB" ;;
  SendTo "shB" #"Done" #saA.

Canonical Structure retransmitO := leibnizO retransmit_state.

Class retransmitG Σ := RetransmitG {
  retransmit_name: gname;
  retransmit_done_G :> inG Σ (excl_authR retransmitO);
 }.
Class retransmitPreG Σ := {
  retransmit_done_PreG :> inG Σ (excl_authR retransmitO);
 }.
Definition retransmitΣ : gFunctors :=
  #[ anerisΣ (live_model_of_user retransmit_model net_model);
     GFunctor (excl_authR retransmitO) ].

Global Instance subG_retransmitΣ {Σ} : subG retransmitΣ Σ → retransmitPreG Σ.
Proof. solve_inG. Qed.

Section with_Σ.
  Context `{anerisG _ _ (live_model_of_user retransmit_model net_model) Σ}.
  Context `{!retransmitG Σ}.
  Let Ns := nroot .@ "retransmit".

  Definition ipA := "0.0.0.0".
  Definition saA := SocketAddressInet ipA 80.

  Definition ipB := "0.0.0.1".
  Definition saB := SocketAddressInet ipB 80.

  Definition mAB := mkMessage saA saB "Hello".

  Definition retinv : iProp Σ := frag_free_roles_are ∅ ∗ ∃ st, frag_model_is st ∗ own retransmit_name (●E st).

  Lemma token_update γ (st st' st'' : retransmit_state) :
    own γ (●E st) ∗ own γ (◯E st'') ==∗ own γ (●E st') ∗ own γ (◯E st').
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.

  Lemma token_agree γ (st st' : retransmit_state) :
    own γ (●E st) -∗ own γ (◯E st') -∗ ⌜ st = st' ⌝.
  Proof.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.

  Lemma wp_A tid f (Hf: f > 9) :
    {{{ inv Ns retinv ∗ is_node ipA ∗ saB ⤇ (λ msg, ⌜ msg = mAB ⌝) ∗
          (ipA, tid) ↦M {[ Arole := f ]} ∗ saA ⤳ (∅, ∅) ∗
          free_ports (ip_of_address saA) {[port_of_address saA]} }}}
      (mkExpr (ip_of_address saA) (Aprog saA saB)) @ (ipA, tid); ⊤
    {{{ v, RET v; (ipA, tid) ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & #Hisn & #Hmsg & HA & Hrt & Hfp) HΦ".

    rewrite /Aprog.
    wp_bind (NewSocket _).

    iApply sswp_MU_wp. iApply wp_new_socket=>//.
    iIntros (sh) "Hsh'".

    mu_fuel.
    iApply wp_value'.

    do 2 wp_pure _.

    wp_bind (SocketBind _ _).
    iApply sswp_MU_wp.
    iApply (wp_socketbind with "[Hfp] [Hsh']")=>//=; first done.
    iIntros "Hsh".
    mu_fuel.
    iApply wp_value'.
    do 5 wp_pure _.

    iAssert (∃ R T, saA ⤳ (R, T) ∗
            [∗ set] m ∈ R, socket_address_group_own {[m_sender m]})%I
      with "[Hrt]" as (R T) "[HRT HR]"; [by eauto|].
    iAssert (∃ f, ⌜ f > 0 ⌝ ∗ ("0.0.0.0", tid) ↦M <[Arole:=f]> ∅)%I
      with "[HA]" as (f') "[Hf HA]".
    { iExists _. iSplit; last iFrame. iPureIntro. lia. }

    clear Hf.
    iLöb as "IH" forall (f' R T) "Hf".
    iDestruct "Hf" as %Hf.
    wp_pure _.

    wp_bind (SendTo _ _ _).
    iApply sswp_MU_wp_fupd.

    iInv Ns as "(Hfr & %st & Hst & Hrest)" "Hclose".
    iModIntro.

    iApply (wp_send _ _ false with "[Hsh] [HRT] [Hmsg]")=>//=>//=>//.
    iNext. iIntros "Hsh HRT".

    iApply (mu_step_model _ _ _ _ ∅ ∅ _ st with "Hst [HA] [Hfr //]").
    { constructor. }
    { set_solver. }
    { set_solver. }
    { rewrite fmap_empty map_union_empty //. }
    iIntros "Hst HA Hfr".

    iMod ("Hclose" with "[Hst Hrest Hfr]").
    { iNext. iFrame. iExists st. iFrame. }
    iModIntro.
    simpl.
    rewrite /= ?map_union_empty //.

    iApply wp_value'.
    do 2 wp_pure _.
    iApply ("IH" with "[$] [$] [$] [$] [$] []").
    iPureIntro; lia.
  Qed.

  Lemma wp_wait tid f (Hf: f > 9) sh b T1:
    {{{ inv Ns retinv ∗ own retransmit_name (◯E retransmit_model.Start) ∗
          is_node ipB ∗ saB ⤇ (λ msg, ⌜ msg = mAB ⌝) ∗
          (ipB, tid) ↦M {[ Brole := f ]} ∗ saB ⤳ (∅, T1) ∗
          sh ↪[ipB] {| saddress := Some saB; sblock := b |} }}}
      (mkExpr (ip_of_address saB) (wait_receive #(LitSocket sh))) @ (ipB, tid); ⊤
    {{{ v, RET v; ⌜ v.(val_n) = ipB ⌝ ∗ ∃ f' R2 T2, (ipB, tid) ↦M {[ Brole := f' ]} ∗ ⌜ f' > 8 ⌝ ∗
        own retransmit_name (◯E retransmit_model.Received) ∗
        saB ⤳ (R2, T2) ∗ sh ↪[ipB] {| saddress := Some saB; sblock := false |}
    }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Htok & Hin & #HsockB & HB & Hrt & Hsh) HΦ".
    rewrite /wait_receive.
    wp_pure _.

    wp_bind (SetReceiveTimeout _ _ _).

    iApply sswp_MU_wp.
    iApply (wp_rcvtimeo_ublock NotStuck ⊤ (ipB, tid) sh _ saB 1 1 with "[Hsh]").
    3: { auto. }
    { done. }
    { lia. }
    iIntros "Hsh".
    mu_fuel.
    iApply wp_value'.
    do 5 wp_pure _.

    iAssert (∃ f, ⌜ f > 2 ⌝ ∗ (ipB, tid) ↦M <[Brole:=f]> ∅)%I
      with "[HB]" as (f') "[Hf HB]".
    { iExists _. iSplit; last iFrame. iPureIntro. lia. }

    clear f Hf.
    iLöb as "IH" forall (f' T1) "Hf".
    iDestruct "Hf" as %Hf.

    wp_pure _.
    wp_bind (ReceiveFrom _).

    iApply sswp_MU_wp_fupd.

    iInv Ns as "(Hfr & %st & Hst & Hrest)" "Hclose".
    iModIntro.

    iApply (wp_recv with "[Hsh] [Hrt] [HsockB]")=>//=>//=>//.
    iNext.

    iDestruct (token_agree with "Hrest Htok") as %->.

    iIntros (om r) "H".
    iDestruct "H" as "[(%Hr&%Hom&Hsh&Hrt)|(%msg & %Hr & %Hom & %Hdest & Hsh & Hrt & %Hin')]".
    - simplify_eq.
      iApply (mu_step_model _ _ _ _ ∅ ∅ _ (retransmit_model.Start : retransmit_model) with "Hst [HB] [Hfr //]").
      { constructor. }
      { set_solver. }
      { set_solver. }
      { rewrite fmap_empty map_union_empty //. }
      iIntros "Hst HB Hfr'".

      iMod ("Hclose" with "[Hst Hrest Hfr']").
      { iNext. iFrame. iExists _. iFrame. }
      iModIntro.
      iApply wp_value'.
      simpl.
      rewrite !map_union_empty //.
      do 4 wp_pure _.
      iApply ("IH" with "[$] [$] [$] [$] [$] [$]").
      { iPureIntro; lia. }
    - simplify_eq.
      iApply (mu_step_model _ _ _ _ ∅ ∅ _ (Received : retransmit_model) with "Hst [HB] [Hfr //]").
      { rewrite Hin'. constructor. set_solver. }
      { set_solver. }
      { set_solver. }
      { rewrite fmap_empty map_union_empty //. }
      iIntros "Hst HB Hfr'".

      iMod (token_update with "[$]") as "[Hrest Htok]".
      iMod ("Hclose" with "[Hst Hrest Hfr']").
      { iNext. iFrame. iExists Received. iFrame. }
      iModIntro.
      iApply wp_value'.
      simpl.
      rewrite !map_union_empty //.
      do 4 wp_pure _.
      iApply wp_value.
      iApply "HΦ". iFrame. iSplit=>//.
      iExists _, _, _. iFrame. iPureIntro; lia.
  Qed.

  Lemma wp_B tid f (Hf: f > 20):
    {{{ inv Ns retinv ∗ own retransmit_name (◯E retransmit_model.Start) ∗
          is_node ipB ∗ saA ⤇ (λ _, True) ∗ saB ⤇ (λ msg, ⌜ msg = mAB ⌝) ∗
          (ipB, tid) ↦M {[ Brole := f ]} ∗ saB ⤳ (∅, ∅) ∗
          free_ports (ip_of_address saB) {[port_of_address saB]} }}}
      (mkExpr (ip_of_address saB) (Bprog saA saB)) @ (ipB, tid); ⊤
    {{{ v, RET v; (ipB, tid) ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Htok & #Hin & #HsockB & #HsockA & HB & Hrt & Hfp) HΦ".

    rewrite /Bprog.
    wp_bind (NewSocket _).

    iApply sswp_MU_wp. iApply wp_new_socket=>//.
    iIntros (sh) "Hsh'".

    mu_fuel.
    iApply wp_value'.

    do 2 wp_pure _.

    wp_bind (SocketBind _ _).
    iApply sswp_MU_wp.
    iApply (wp_socketbind with "[Hfp] [Hsh']")=>//=; first done.
    iIntros "Hsh".
    mu_fuel.
    iApply wp_value'.
    do 2 wp_pure _.

    wp_bind (wait_receive _).

    iApply (wp_wait _ _ with "[Hinv Hsh Hrt HB Htok]").
    2: { iFrame "#∗". }
    { lia. }
    iNext.
    iIntros (vv) "(%Heq & %f' & %R & %T & HB & %Hf' & Htok & Hrt & Hsh)".

    do 2 wp_pure _.

    iApply sswp_MU_wp_fupd.
    iInv Ns as "(Hfr & %st & Hst & Hrest)" "Hclose".
    iModIntro.


    iApply (wp_send _ _ false with "[Hsh] [Hrt] [HsockA]")=>//=>//=>//.
    iNext. iIntros "Hsh HRT".

    iDestruct (token_agree with "Hrest Htok") as %->.

    iApply (mu_step_model _ _ _ _ ∅ ∅ _ (Done : lts_state retransmit_model) with "Hst [HB] [Hfr //]").
    { constructor. }
    { set_solver. }
    { set_solver. }
    { rewrite fmap_empty map_union_empty //. }
    iIntros "Hst HB Hfr'".

    iMod (token_update with "[Hrest Htok]") as "[Hrest Htok]".
    { iFrame. }

    iMod ("Hclose" with "[Hst Hrest Hfr']").
    { iNext. iFrame. iExists Done. iFrame. }
    iModIntro.
    simpl.

    iApply wp_atomic.
    { intros ????? Hs. apply val_stuck in Hs. done. }

    iInv Ns as "(Hfr & %st & Hst & Hrest)" "Hclose".
    iModIntro.

    iPoseProof (timeless with "Hst") as "Hst".
    iPoseProof (timeless with "Hrest") as "Hrest".
    iMod "Hst". iMod "Hrest".

    iDestruct (token_agree with "Hrest Htok") as %->.

    iMod (has_fuels_dealloc _ _ _ (Brole: usr_role retransmit_model) Done
           with "Hst HB") as "[Hst HB]".
    { set_solver. }

    iApply wp_value'.

    iMod ("Hclose" with "[Hst Hrest Hfr]").
    { iNext. iFrame. iExists Done. iFrame. }
    iModIntro. iApply ("HΦ"). rewrite map_union_empty delete_insert //.
  Qed.

End with_Σ.
