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
        SendTo "sh_clt" (i2s "i") #sa_srv ;;
        match: (ReceiveFrom "sh_clt") with
          NONE     => "f" "i"
        | SOME "m" => if: Snd "m" = #sa_srv
                      then
                        let: "j" := s2i (Fst "m") in
                        if: InjR "i" = "j"
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
        | SOME "m" => if: Snd "m" = #sa_clt
                      then
                        let: "i" := s2i (Fst "m") in
                        if: InjR ("j"+#1) = "i"
                        then SendTo "sh_srv" (i2s (#1 + "j")) #sa_clt ;; "f" (#1 + "j")
                        else SendTo "sh_srv" (i2s "j") #sa_clt ;; "f" "j"
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
  #[ anerisΣ (live_model_of_user stenning_model net_model);
     GFunctor (excl_authR stenning_A_stateO);
     GFunctor (excl_authR stenning_B_stateO) ].

Global Instance subG_stenningΣ {Σ} : subG stenningΣ Σ → stenningPreG Σ.
Proof. solve_inG. Qed.

Section with_Σ.
  Context `{anerisG _ _ (live_model_of_user stenning_model net_model) Σ}.
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
          own stenning_A_name (◯E (ASending 0)) ∗
          (ipA, tid) ↦M {[ Arole := f ]} ∗ saA ⤳ (∅, ∅) ∗
          free_ports (ip_of_address saA) {[port_of_address saA]} }}}
      (mkExpr (ip_of_address saA) (client saA saB #())) @ (ipA, tid); ⊤
    {{{ v, RET v; (ipA, tid) ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv&#Hin&#HsA&#HsB&Hst&Hf&HRT&Hfp) HΦ".
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

    remember 0 as n eqn:Heq.
    replace (ASending 0) with (ASending n); last naive_solver.

    assert (n >= 0) as Hn; first lia. clear Heq.
    iLöb as "IH" forall (f' n Hn R T) "Hf". iDestruct "Hf'" as %Hf.

    wp_pure _.
    wp_pure _.

    wp_bind (SendTo _ _ _).
    iApply sswp_MU_wp_fupd.

    iInv Ns as "Hi" "Hclose". iModIntro.
    iApply (wp_send _ _ false with "[Hsh] [HRT] [HsA]")=>//=>//=>//.
    iNext. iIntros "Hsh HRT".
    iDestruct "Hi" as "(Hfr & %stA & %stB & Hmod & HstA & HstB)".
    iDestruct (token_agree with "HstA Hst") as %->.

    iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((AReceiving n, stB) : stenning_model) with "Hmod [Hf] [Hfr //]").
    { simpl. constructor. }
    { set_solver. }
    { set_solver. }
    { rewrite fmap_empty map_union_empty. done. }
    iIntros "Hmod Hf Hfr".

    iMod (token_update with "[$HstA $Hst]") as "[HstA Hst]".
    iMod ("Hclose" with "[Hfr Hmod HstA HstB]").
    { iNext. rewrite /retinv. iFrame. iExists (AReceiving n), _. iFrame. }
    rewrite map_union_empty /usr_fl /=. iModIntro. iApply wp_value'. do 2 wp_pure _.

    wp_bind (ReceiveFrom _).
    iApply sswp_MU_wp_fupd.
    iInv Ns as "Hi" "Hclose". iModIntro.

    iApply (wp_recv with "[Hsh] [HRT] [HsB]")=>//=>//=>//.
    iNext. clear stB. iDestruct "Hi" as "(Hfr & %stA & %stB & Hmod & HstA & HstB)".
    iDestruct (token_agree with "HstA Hst") as %->.

    iIntros (om r) "Hmsg".

    iAssert (⌜ ∃ omsg, om = Recv saA omsg ⌝)%I as %[omsg ->].
    { iDestruct "Hmsg" as "[(-> & -> & Hsh & HRT)|(%msg & -> & -> & %Heqdest & Hsh & HRT & Hnew)]";
      iPureIntro; naive_solver. }
    destruct (decide (good_message false n omsg)) as [[msg Hgood]|Hbad].
    - iDestruct "Hmsg" as "[(-> & %Heq & Hsh & HRT)|(%msg' & -> & %Heq & %Heqdest & Hsh & HRT & Hnew)]".
      { simplify_eq. naive_solver. }
      destruct Hgood as (?&Hbody&?&?). simplify_eq.
      iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((ASending (1+n), stB) : stenning_model) with "Hmod [Hf] [Hfr //]").
      { constructor. exists msg'. naive_solver. }
      { set_solver. }
      { set_solver. }
      { rewrite fmap_empty map_union_empty. done. }
      iIntros "Hmod Hf Hfr".
      rewrite map_union_empty /usr_fl /=.
      iMod (token_update with "[$HstA $Hst]") as "[HstA Hst]".
      iMod ("Hclose" with "[Hfr Hmod HstA HstB]").
      { iNext. rewrite /retinv. iFrame. iExists (ASending (1+n)), _. iFrame. }
      iModIntro. iApply wp_value'. do 5 wp_pure _.
      rewrite bool_decide_true; last by do 2 f_equal.
      do 3 wp_pure _.
      { simpl. rewrite Hbody //. }
      do 4 wp_pure _. rewrite bool_decide_true //. do 2 wp_pure _.
      iApply ("IH" with "[] [Hst] [$] [$] [] [$HRT] [$]").
      { iPureIntro; lia. }
      { rewrite Z.add_comm //. }
      { iPureIntro; lia. }
    - iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((ASending n, stB) : stenning_model) with "Hmod [Hf] [Hfr //]").
      { simpl. by apply A_RecvFail. }
      { set_solver. }
      { set_solver. }
      { rewrite fmap_empty map_union_empty. done. }
      iIntros "Hmod Hf Hfr".
      rewrite map_union_empty /usr_fl /=.
      iMod (token_update with "[$HstA $Hst]") as "[HstA Hst]".
      iMod ("Hclose" with "[Hfr Hmod HstA HstB]").
      { iNext. rewrite /retinv. iFrame. iExists (ASending n), _. iFrame. }
      iModIntro. iApply wp_value'. simpl.
      iDestruct "Hmsg" as "[(-> & %Heq & Hsh & HRT)|(%msg & -> & %Heq & %Heqdest & Hsh & HRT & Hnew)]".
      + do 3 wp_pure _. iApply ("IH" with "[] [Hst] [$] [$] [] [$HRT] [$]")=>//.
      + do 5 wp_pure _. destruct (decide (m_sender msg = saB)); last first.
        { rewrite bool_decide_false; last naive_solver. wp_pure _.
          iApply ("IH" with "[] [Hst] [$] [$] [] [$HRT] [$]")=>//. }
        rewrite bool_decide_true //; last by do 2 f_equal. do 2 wp_pure _.
        destruct (ZOfString (m_body msg)) as [msg_n|] eqn:Heqmsg; last first.
        { wp_pure _. rewrite /= Heqmsg //. do 5 wp_pure _.
          iApply ("IH" with "[] [Hst] [$] [$] [] [$HRT] [$]")=>//. }
        wp_pure _. rewrite /= Heqmsg //. do 4 wp_pure _.
        rewrite bool_decide_false; last first.
        { intros Hc. simplify_eq. apply Hbad. eexists; split=>//. }
        wp_pure _. iApply ("IH" with "[] [Hst] [$] [$] [] [$HRT] [$]")=>//.
  Qed.

  Lemma wp_sever tid (f : nat) (Hf: f > 40) :
    {{{ inv Ns retinv ∗ is_node ipB ∗ saA ⤇ (λ msg, ⌜ msg = msg⌝) ∗ saB ⤇ (λ msg, ⌜ msg = msg⌝) ∗
          own stenning_B_name (◯E (BReceiving 0)) ∗
          (ipB, tid) ↦M {[ Brole := f ]} ∗ saB ⤳ (∅, ∅) ∗
          free_ports (ip_of_address saB) {[port_of_address saB]} }}}
      (mkExpr (ip_of_address saB) (server saA saB #())) @ (ipB, tid); ⊤
    {{{ v, RET v; (ipB, tid) ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv&#Hin&#HsA&#HsB&Hst&Hf&HRT&Hfp) HΦ".
    rewrite /server.
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
    iApply sswp_MU_wp. iApply (wp_rcvtimeo_ublock NotStuck ⊤ (ipB, tid) sh _ saB 1 1 with "[Hsh]").
    3: { auto. }
    { done. }
    { lia. }
    iIntros "Hsh". mu_fuel. iApply wp_value'. do 5 wp_pure _.

    iAssert (∃ (f : nat), ⌜ f > 25 ⌝ ∗ (ipB, tid) ↦M <[Brole:=f]> ∅)%I
      with "[Hf]" as (f') "[Hf' Hf]".
    { iExists _. iFrame. iPureIntro. lia. }
    clear f Hf.

    iAssert (∃ R T, saB ⤳ (R, T))%I with "[HRT]" as (R T) "HRT".
    { iExists _, _. iFrame. }

    remember (-1) as n eqn:Heq.
    replace (BReceiving 0) with (BReceiving (1+n)); last naive_solver.

    assert (n >= -1) as Hn; first lia. clear Heq.
    iLöb as "IH" forall (f' n Hn R T) "Hf". iDestruct "Hf'" as %Hf.

    wp_pure _.

    wp_bind (ReceiveFrom _).
    iApply sswp_MU_wp_fupd.
    iInv Ns as "Hi" "Hclose". iModIntro.

    iApply (wp_recv with "[Hsh] [HRT] [HsA]")=>//=>//=>//.
    iNext. iDestruct "Hi" as "(Hfr & %stA & %stB & Hmod & HstA & HstB)".
    iDestruct (token_agree with "HstB Hst") as %->.

    iIntros (om r) "Hmsg".

    iAssert (⌜ ∃ omsg, om = Recv saB omsg ⌝)%I as %[omsg ->].
    { iDestruct "Hmsg" as "[(-> & -> & Hsh & HRT)|(%msg & -> & -> & %Heqdest & Hsh & HRT & Hnew)]";
      iPureIntro; naive_solver. }
    destruct (decide (good_message true (1+n) omsg)) as [[msg Hgood]|Hbad];
    [|destruct (decide (omsg = None ∨ (∃ msg, omsg = Some msg ∧ m_sender msg ≠ saA))) as [Hempty|Hwrong]].
    - iDestruct "Hmsg" as "[(-> & %Heq & Hsh & HRT)|(%msg' & -> & %Heq & %Heqdest & Hsh & HRT & Hnew)]".
      { simplify_eq. naive_solver. }
      destruct Hgood as (?&Hbody&?&?). simplify_eq.
      iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((stA, BSending (1 + (1 + n))) : stenning_model) with "Hmod [Hf] [Hfr //]").
      { constructor. exists msg'. naive_solver. }
      { set_solver. }
      { set_solver. }
      { rewrite fmap_empty map_union_empty. done. }
      iIntros "Hmod Hf Hfr".
      rewrite map_union_empty /usr_fl /=.
      iMod (token_update with "[$HstB $Hst]") as "[HstB Hst]".
      iMod ("Hclose" with "[Hfr Hmod HstA HstB]").
      { iNext. rewrite /retinv. iFrame. iExists _, _. iFrame. }
      iModIntro. iApply wp_value'. do 5 wp_pure _.
      rewrite bool_decide_true; last by do 2 f_equal.
      do 3 wp_pure _.
      { simpl. rewrite Hbody //. }
      do 5 wp_pure _. rewrite bool_decide_true //. do 3 wp_pure _.

      wp_bind (SendTo _ _ _).
      iApply sswp_MU_wp_fupd.

      iInv Ns as "Hi" "Hclose". iModIntro.
      iApply (wp_send _ _ false with "[Hsh] [HRT] [HsB]")=>//=>//=>//.
      iNext. iIntros "Hsh HRT". clear stA.
      iDestruct "Hi" as "(Hfr & %stA & %stB & Hmod & HstA & HstB)".
      iDestruct (token_agree with "HstB Hst") as %->.

      iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((stA, (BReceiving (1+(1+n)))) : stenning_model) with "Hmod [Hf] [Hfr //]").
      { simpl. replace (Send _) with (Send (mBA $ (1 + (1 + n)) - 1)). constructor. f_equal.
        rewrite /mBA //=. do 2 f_equal. lia. }
      { set_solver. }
      { set_solver. }
      { rewrite fmap_empty map_union_empty. done. }
      iIntros "Hmod Hf Hfr".

      iMod (token_update with "[$HstB $Hst]") as "[HstB Hst]".
      iMod ("Hclose" with "[Hfr Hmod HstA HstB]").
      { iNext. rewrite /retinv. iFrame. iExists _, _. iFrame. }
      rewrite map_union_empty /usr_fl /=. iModIntro. iApply wp_value'. do 3 wp_pure _.
      iApply ("IH" with "[] [Hst] [$] [$] [] [$HRT] [$]")=>//.
      { iPureIntro; lia. }
      { rewrite Z.add_comm //. }
    - iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((stA, BReceiving (1+n)) : stenning_model) with "Hmod [Hf] [Hfr //]").
      { simpl. by apply B_RecvFailEmpty. }
      { set_solver. }
      { set_solver. }
      { rewrite fmap_empty map_union_empty. done. }
      iIntros "Hmod Hf Hfr".
      rewrite map_union_empty /usr_fl /=.
      iMod ("Hclose" with "[Hfr Hmod HstA HstB]").
      { iNext. rewrite /retinv. iFrame. iExists _, _. iFrame. }
      iModIntro. iApply wp_value'.
      iDestruct "Hmsg" as "[(-> & %Heq & Hsh & HRT)|(%msg' & -> & %Heq & %Heqdest & Hsh & HRT & Hnew)]".
      + do 3 wp_pure _. iApply ("IH" with "[] [Hst] [$] [$] [] [$HRT] [$]")=>//.
      + do 5 wp_pure _. rewrite bool_decide_false; last naive_solver.
        wp_pure _. iApply ("IH" with "[] [Hst] [$] [$] [] [$HRT] [$]")=>//.
    - iDestruct "Hmsg" as "[(-> & %Heq & Hsh & HRT)|(%msg' & -> & %Heq & %Heqdest & Hsh & HRT & Hnew)]".
      { simplify_eq. naive_solver. }
      simplify_eq. have ?: m_sender msg' = saA by apply NNP_P; naive_solver.
      iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((stA, BSending (1 + n)) : stenning_model) with "Hmod [Hf] [Hfr //]").
      { constructor=>//. }
      { set_solver. }
      { set_solver. }
      { rewrite fmap_empty map_union_empty. done. }
      iIntros "Hmod Hf Hfr".
      rewrite map_union_empty /usr_fl /=.
      iMod (token_update with "[$HstB $Hst]") as "[HstB Hst]".
      iMod ("Hclose" with "[Hfr Hmod HstA HstB]").
      { iNext. rewrite /retinv. iFrame. iExists _, _. iFrame. }
      iModIntro. iApply wp_value'. do 5 wp_pure _. rewrite bool_decide_true; last by do 2 f_equal.
      destruct (ZOfString (m_body msg')) as [?|] eqn:Heq.
      + do 3 wp_pure _; first by rewrite /= Heq. do 5 wp_pure _. rewrite bool_decide_false; last first.
        { intros ?; simplify_eq. apply Hbad. rewrite /good_message Z.add_comm //. naive_solver. }
        do 2 wp_pure _. wp_bind (SendTo _ _ _).
        iApply sswp_MU_wp_fupd. iInv Ns as "Hi" "Hclose". iModIntro.
        iApply (wp_send _ _ false with "[Hsh] [HRT] [HsB]")=>//=>//=>//.
        iNext. iIntros "Hsh HRT". clear stA.
        iDestruct "Hi" as "(Hfr & %stA & %stB & Hmod & HstA & HstB)".
        iDestruct (token_agree with "HstB Hst") as %->.
        iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((stA, (BReceiving (1+n))) : stenning_model) with "Hmod [Hf] [Hfr //]").
        { simpl. replace (Send _) with (Send (mBA $ (1 + n) - 1)). constructor. f_equal.
          rewrite /mBA //=. do 2 f_equal. lia. }
        { set_solver. }
        { set_solver. }
        { rewrite fmap_empty map_union_empty. done. }
        iIntros "Hmod Hf Hfr".
        iMod (token_update with "[$HstB $Hst]") as "[HstB Hst]".
        iMod ("Hclose" with "[Hfr Hmod HstA HstB]").
        { iNext. rewrite /retinv. iFrame. iExists _, _. iFrame. }
        rewrite map_union_empty /usr_fl /=. iModIntro. iApply wp_value'. do 2 wp_pure _.
        iApply ("IH" with "[] [Hst] [$] [$] [] [$HRT] [$]")=>//.
      + do 3 wp_pure _; first by rewrite /= Heq. do 7 wp_pure _.
        wp_bind (SendTo _ _ _).
        iApply sswp_MU_wp_fupd. iInv Ns as "Hi" "Hclose". iModIntro.
        iApply (wp_send _ _ false with "[Hsh] [HRT] [HsB]")=>//=>//=>//.
        iNext. iIntros "Hsh HRT". clear stA.
        iDestruct "Hi" as "(Hfr & %stA & %stB & Hmod & HstA & HstB)".
        iDestruct (token_agree with "HstB Hst") as %->.
        iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((stA, (BReceiving (1+n))) : stenning_model) with "Hmod [Hf] [Hfr //]").
        { simpl. replace (Send _) with (Send (mBA $ (1 + n) - 1)). constructor. f_equal.
          rewrite /mBA //=. do 2 f_equal. lia. }
        { set_solver. }
        { set_solver. }
        { rewrite fmap_empty map_union_empty. done. }
        iIntros "Hmod Hf Hfr".
        iMod (token_update with "[$HstB $Hst]") as "[HstB Hst]".
        iMod ("Hclose" with "[Hfr Hmod HstA HstB]").
        { iNext. rewrite /retinv. iFrame. iExists _, _. iFrame. }
        rewrite map_union_empty /usr_fl /=. iModIntro. iApply wp_value'. do 2 wp_pure _.
        iApply ("IH" with "[] [Hst] [$] [$] [] [$HRT] [$]")=>//.
  Qed.
End with_Σ.
