From stdpp Require Import list fin_maps.
From iris.algebra Require Import excl_auth.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From trillium.program_logic Require Import ectx_lifting.
From fairneris Require Import fairness fair_resources fuel.
From fairneris.examples Require Import stenning_model.
From fairneris.aneris_lang Require Import proofmode.
From fairneris.aneris_lang.state_interp Require Import state_interp state_interp_events.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.

Definition client (sa_clt sa_srv : socket_address) : val :=
  λ: <>,
     let: "sh_clt" := NewSocket #() in
     SocketBind "sh_clt" #sa_clt;;
     SetReceiveTimeout "sh_clt" #1 #1;;
     let: "go" := (rec: "f" "i" :=
        SendTo "sh_clt" "sa_srv" (i2s "i");;
        match: (ReceiveFrom "sh_clt") with
          NONE     => "f" "i"
        | SOME "m" => if: Snd "m" = "sa_srv"
                      then
                        let: "j" := s2i (Fst "m") in
                        if: "i" = "j"
                        then "f" ("i" + #1)
                        else "f" "i"
                      else
                        "f" "i"
        end)
     in "go" #0.

Definition server (sa_clt sa_srv : socket_address) : val :=
  λ: <>,
     let: "sh_srv" := NewSocket #() in
     SocketBind "sh_srv" #sa_srv;;
     SetReceiveTimeout "sh_srv" #1 #1;;
     let: "go" := (rec: "f" "j" :=
        match: (ReceiveFrom "sh_srv") with
          NONE     => "f" "j"
        | SOME "m" => if: Snd "m" = "sa_clt"
                      then
                        let: "i" := s2i (Fst "m") in
                        if: "j"+#1 = "i"
                        then SendTo "sh_srv" "sa_clt" "i";; "f" "i"
                        else SendTo "sh_srv" "sa_clt" "j";; "f" "j"
                      else
                        "f" "j"
        end)
     in "go" #-1.

Canonical Structure stenning_A_stateO := leibnizO stenning_A_state.
Canonical Structure stenning_B_stateO := leibnizO stenning_B_state.

Class stenningG Σ := StenningG {
  stenning_A_name: gname;
  stenning_B_name: gname;
  stenning_A_G :> inG Σ (excl_authR stenning_A_stateO);
  stenning_B_G :> inG Σ (excl_authR stenning_B_stateO);
 }.
Class stenningPreG Σ := {
  stenning_A_PreG :> inG Σ (excl_authR stenning_A_stateO);
  stenning_B_PreG :> inG Σ (excl_authR stenning_B_stateO);
 }.
Definition stenningΣ : gFunctors :=
  #[ anerisΣ (live_model_of_user stenning_model);
     GFunctor (excl_authR stenning_A_stateO);
     GFunctor (excl_authR stenning_B_stateO) ].

Global Instance subG_stenningΣ {Σ} : subG stenningΣ Σ → stenningPreG Σ.
Proof. solve_inG. Qed.

Section with_Σ.
  Context `{anerisG _ _ (live_model_of_user stenning_model) Σ}.
  Context `{!stenningG Σ}.
  Let Ns := nroot .@ "stenning".

  Definition retinv : iProp Σ := frag_free_roles_are ∅ ∗
    ∃ stA stB, frag_model_is (stA, stB) ∗ own stenning_A_name (●E stA) ∗ own stenning_B_name (●E stB).

  Lemma token_update γ {A: ofe} {_: inG Σ (excl_authR A)} (st st' st'' : A) :
    own γ (●E st) ∗ own γ (◯E st'') ==∗ own γ (●E st') ∗ own γ (◯E st').
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.

                                               (*  TODO:   can we do better?     *)
  Lemma token_agree γ {A: ofe} `{OfeDiscrete A, @LeibnizEquiv A (ofe_equiv A)} {_: inG Σ (excl_authR A)} (st st' : A) :
    own γ (●E st) -∗ own γ (◯E st') -∗ ⌜ st = st' ⌝.
  Proof.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.

  Definition ipA := ip_of_address saA.
  Definition ipB := ip_of_address saB.

  Lemma wp_client tid (f : nat) (Hf: f > 40) :
    {{{ inv Ns retinv ∗ is_node ipA ∗ saA ⤇ (λ msg, ⌜ msg = msg⌝) ∗ saB ⤇ (λ msg, ⌜ msg = msg⌝) ∗
          own stenning_A_name (◯E (AReceiving 0)) ∗
          (ipA, tid) ↦M {[ Arole := f ]} ∗ saA ⤳ (∅, ∅) ∗
          free_ports (ip_of_address saA) {[port_of_address saA]} }}}
      (mkExpr (ip_of_address saA) (client saA saB #())) @ (ipA, tid); ⊤
    {{{ v, RET v; (ipA, tid) ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(Hinv&#Hin&HsA&HsB&Hst&Hf&HRT&Hfp) HΦ".
    rewrite /client.
    wp_pure _.

    wp_bind (NewSocket _).
    iApply sswp_MU_wp. iApply wp_new_socket=>//.
    iIntros (sh) "Hsh".
    mu_fuel.

    iApply wp_value'. do 2 wp_pure _.

    wp_bind (SocketBind _ _).
    iApply sswp_MU_wp. iApply (wp_socketbind with "[Hfp] [Hsh]") =>//=; first done.
    iIntros "Hsh".
    mu_fuel.
    iApply wp_value'.
    do 2 wp_pure _.

    wp_bind (SetReceiveTimeout _ _ _).
    iApply sswp_MU_wp. iApply (wp_rcvtimeo_ublock NotStuck ⊤ (ipA, tid) sh _ saA 1 1 with "[Hsh]").
    3: { auto. }
    { done. }
    { lia. }
    iIntros "Hsh". mu_fuel. iApply wp_value'. do 5 wp_pure _.

    iAssert (∃ (f : nat), ⌜ f > 25 ⌝ ∗ (ipA, tid) ↦M <[Arole:=f]> ∅)%I
      with "[Hf]" as (f') "[Hf' Hf]".
    { iExists _. iFrame. iPureIntro. lia. }
    clear f Hf.

    iAssert (∃ R T, saA ⤳ (R, T))%I with "[HRT]" as (R T) "HRT".
    { iExists _, _. iFrame. }

    (* TODO: generalize 0 *)
    iLöb as "IH" forall (f' R T) "Hf".
  Admitted.

  Lemma wp_sever tid (f : nat) (Hf: f > 40) :
    {{{ inv Ns retinv ∗ is_node ipA ∗ saA ⤇ (λ msg, ⌜ msg = msg⌝) ∗ saB ⤇ (λ msg, ⌜ msg = msg⌝) ∗
          own stenning_B_name (◯E (BReceiving 0)) ∗
          (ipB, tid) ↦M {[ Brole := f ]} ∗ saB ⤳ (∅, ∅) ∗
          free_ports (ip_of_address saA) {[port_of_address saA]} }}}
      (mkExpr (ip_of_address saA) (server saA saB)) @ (ipA, tid); ⊤
    {{{ v, RET v; (ipA, tid) ↦M ∅ }}}.
  Proof.
  Admitted.

End with_Σ.
