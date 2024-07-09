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
From fairneris.lib Require Import gen_heap_light.

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
  stenning_cnt_name: gname;
  stenning_A_G :> inG Σ (excl_authR stenning_A_stateO);
  stenning_B_G :> inG Σ (excl_authR stenning_B_stateO);
  stenning_cnt_G :> inG Σ (authR (gen_heapUR socket_address Z));
 }.
Class stenningPreG Σ := {
  stenning_A_PreG :> inG Σ (excl_authR stenning_A_stateO);
  stenning_B_PreG :> inG Σ (excl_authR stenning_B_stateO);
  stenning_cnt_PreG :> inG Σ (authR (gen_heapUR socket_address Z));
 }.
Definition stenningΣ : gFunctors :=
  #[ anerisΣ (live_model_of_user stenning_model net_model);
     GFunctor (excl_authR stenning_A_stateO);
     GFunctor (excl_authR stenning_B_stateO);
     GFunctor (authR (gen_heapUR socket_address Z))
  ].

Global Instance subG_stenningΣ {Σ} : subG stenningΣ Σ → stenningPreG Σ.
Proof. solve_inG. Qed.

Definition mAB_in (n : Z) (S: gset message) : Prop :=
  ∃ msg, msg ∈ S ∧ good_message true n (Some msg).
Definition mBA_in (n : Z) (S: gset message) : Prop :=
  ∃ msg, msg ∈ S ∧ good_message false n (Some msg).

Definition client_RT (n : Z) (R T : gset message) : Prop :=
  (∀ m, mBA_in m R → (m >= 0)%Z → mAB_in m T) ∧
  (∀ m, m >= n → ¬ mBA_in m R)%Z.

Definition server_RT (n : Z) (R T : gset message) : Prop :=
  (∀ m, 0 <= m → mBA_in m T → mAB_in m R)%Z ∧
  (∀ m, 0 <= m → m ≤ n → (mBA m) ∈ T)%Z ∧
  (∀ m, m > n → ¬ mAB_in m R)%Z.

Definition garbage_message b msg := ∀ m, (m >= 0)%Z → ¬ good_message b m (Some msg).

Lemma client_RT_good msg n R T :
  (n >= 0)%Z →
  good_message false n (Some msg) →
  client_RT n R T →
  client_RT (n + 1) ({[msg]} ∪ R) ({[ mAB n ]} ∪ T).
Proof.
  intros Hn Hg (HRT & Hnin). split_and!.
  - intros m [msgm [[Hin%elem_of_singleton | Hin]%elem_of_union Hgoodm]] Hm.
    + simplify_eq.
      have -> : n = m by eapply good_message_inj.
      exists (mAB m). split; [set_solver|]. exists (mAB m). split_and!; try naive_solver. simpl.
      rewrite ZOfString_inv //.
    + have [x [??]] : mAB_in m T.
      * apply HRT =>//. by exists msgm.
      * exists x. naive_solver set_solver.
  - intros m Hm [msg' [[Hin%elem_of_singleton | Hin]%elem_of_union ?]].
    + simplify_eq. have ? : n = m by eapply good_message_inj. lia.
    + ospecialize (Hnin m _). lia. apply Hnin. exists msg'. naive_solver.
Qed.

Lemma client_RT_garbage n G R T :
  (n >= 0)%Z →
  (∀ msg, msg ∈ G → garbage_message false msg) →
  client_RT n R T →
  client_RT n (G ∪ R) ({[ mAB n ]} ∪ T).
Proof.
  intros Hn Hgar (HRT & Hnin). split_and!.
  - intros m [msgm [[Hin | Hin]%elem_of_union Hgoodm]] Hm.
    + exfalso. unshelve eapply (Hgar msgm Hin m _ Hgoodm). lia.
    + have [x [??]] : mAB_in m T.
      * apply HRT=>//. by exists msgm.
      * exists x. naive_solver set_solver.
  - intros m Hm [msgm [[Hin | Hin]%elem_of_union Hgoodm]].
    + unshelve eapply (Hgar msgm Hin m _ Hgoodm). lia.
    + ospecialize (Hnin m _). lia. apply Hnin. exists msgm. naive_solver.
Qed.

Lemma client_RT_garbage_emp n R T :
  (n >= 0)%Z →
  client_RT n R T →
  client_RT n R ({[ mAB n ]} ∪ T).
Proof.
  pose proof (client_RT_garbage n ∅ R T) as Hccl.
  replace (∅ ∪ R) with R in Hccl by set_solver.
  intros ??. apply Hccl=>//.
Qed.

Lemma client_RT_garbage_singleton n msg R T :
  (n >= 0)%Z →
  (garbage_message false msg) →
  client_RT n R T →
  client_RT n ({[ msg ]} ∪ R) ({[ mAB n ]} ∪ T).
Proof.
  intros **. eapply client_RT_garbage=>//. naive_solver set_solver.
Qed.

Lemma server_RT_good msg n R T :
  good_message true n (Some msg) →
  server_RT (n-1)%Z R T →
  server_RT n ({[msg]} ∪ R) ({[ mBA n ]} ∪ T).
Proof.
  intros Hgood HRT. split_and!.
  - intros m Hm0 [msgm [[-> % elem_of_singleton | Hin]%elem_of_union Hgoodm]] .
    + have ?: n = m.
      { destruct Hgoodm as (?&Ha&Hb&Hc). simplify_eq. rewrite /mBA /= ZOfString_inv in Hb. naive_solver. }
      simplify_eq. exists msg. naive_solver set_solver.
    + have [x [??]] : mAB_in m R.
      * apply HRT =>//. by exists msgm.
      * exists x. naive_solver set_solver.
  - intros m Hm0 Hmn. destruct (decide (m = n)).
    + simplify_eq. by apply elem_of_union; left; apply elem_of_singleton.
    + apply elem_of_union; right. apply HRT; lia.
  - intros m Hmn (msg'&Hin&Hgood'). apply elem_of_union in Hin; destruct Hin as [Hin|Hin].
    + apply elem_of_singleton in Hin; simplify_eq. have: m = n; last lia.
      eapply good_message_inj=>//.
    + destruct HRT as (?&?&Hnin). unshelve eapply (Hnin m _). lia. by exists msg'.
Qed.

Lemma server_RT_garbage_1 msg n R T :
  (n >= -1)%Z →
  (garbage_message true msg) →
  server_RT n R T →
  server_RT n ({[msg]} ∪ R) ({[ mBA n ]} ∪ T).
Proof.
  intros Nn0 Hgar HRT. destruct HRT as (Hincl&Hin'&Hnin). split_and!.
  - intros m Hm0 [msgm [[Hin%elem_of_singleton | Hin]%elem_of_union Hgoodm]].
    + simplify_eq. have ?: n = m.
      { destruct Hgoodm as (?&Ha&Hb&Hc). simplify_eq. rewrite /mBA /= ZOfString_inv in Hb. naive_solver. }
      simplify_eq. have ? := Hm0. apply (Hin' m) in Hm0 =>//.
      have [msgin ?] : mAB_in m R.
      { apply Hincl=>//. exists (mBA m). naive_solver. }
      exists msgin. naive_solver set_solver.
    + have Hinp: mBA_in m T.
      { exists msgm. naive_solver. }
      apply Hincl in Hinp as [msgin ?]=>//. exists msgin. naive_solver set_solver.
  - intros m Hm0 Hmn. destruct (decide (m = n)).
    + simplify_eq. by apply elem_of_union; left; apply elem_of_singleton.
    + apply elem_of_union; right. apply Hin'; lia.
  - intros m Hmn (msg'&Hin&Hgood'). apply elem_of_union in Hin; destruct Hin as [Hin|Hin].
    + apply elem_of_singleton in Hin; simplify_eq. apply (Hgar m). lia. done.
    + unshelve eapply (Hnin m _). lia. by exists msg'.
Qed.

Lemma server_RT_garbage_2 msg n R T :
  (n >= -1)%Z →
  (garbage_message true msg) →
  server_RT n R T →
  server_RT n ({[msg]} ∪ R) T.
Proof.
  intros Nn0 Hgar HRT. destruct HRT as (Hincl&Hin'&Hnin). split_and!.
  - intros m Hm0 [msgm [Hin Hgood]].
    + have Hinp: mBA_in m T.
      { exists msgm. naive_solver. }
      apply Hincl in Hinp as [msgin ?]=>//. exists msgin. naive_solver set_solver.
  - intros m Hm0 Hmn. apply Hin'=>//.
  - intros m Hmn (msg'&Hin&Hgood'). apply elem_of_union in Hin; destruct Hin as [Hin|Hin].
    + apply elem_of_singleton in Hin; simplify_eq. apply (Hgar m). lia. done.
    + unshelve eapply (Hnin m _). lia. by exists msg'.
Qed.

Lemma server_RT_garbage_3 msg n R T :
  (n >= -1)%Z →
  (garbage_message false msg) →
  server_RT n R T →
  server_RT n R ({[msg]} ∪ T).
Proof.
  intros Nn0 Hgar HRT. destruct HRT as (Hincl&Hin'&Hnin). split_and!.
  - intros m Hm0 [msgm [[Hin%elem_of_singleton | Hin]%elem_of_union Hgoodm]].
    + simplify_eq. exfalso. apply (Hgar m)=>//. lia.
    + have Hinp: mBA_in m T.
      { exists msgm. naive_solver. }
      apply Hincl in Hinp as [msgin ?]=>//. exists msgin. naive_solver set_solver.
  - intros m Hm0 Hmn. apply elem_of_union; right. apply Hin'=>//.
  - intros m Hmn (msg'&Hin&Hgood'). unshelve eapply (Hnin m _). lia. by exists msg'.
Qed.

Section with_Σ.
  Context `{anerisG _ _ (live_model_of_user stenning_model net_model) Σ}.
  Context `{!stenningG Σ}.
  Let Ns := nroot .@ "stenning".
  Let Nc := nroot .@ "counter".
  Definition counter_inv :=
    inv Nc (∃ w, gen_heap_light_ctx (L:=socket_address) (V:=Z) stenning_cnt_name w)%I.

  Notation "a ↦c{ q } s" := (lmapsto (L:=socket_address) (V:=Z) stenning_cnt_name a q s)
    (at level 20, q at level 50, format "a  ↦c{ q }  s") : bi_scope.

  Notation "a ↦c s" := (lmapsto (L:=socket_address) (V:=Z) stenning_cnt_name a 1%Qp s)
    (at level 20, format "a  ↦c  s") : bi_scope.

  Definition retinv : iProp Σ := frag_free_roles_are ∅ ∗
     ∃ stA stB, frag_model_is (stA, stB) ∗ own stenning_A_name (●E stA) ∗ own stenning_B_name (●E stB) ∗
      let (n, m) := stenning_get_n (stA, stB) in ⌜ (n = m ∨ m = n + 1)%Z ⌝ ∗ saA ↦c{1/4} n ∗ saB ↦c{1/4} (m-1)%Z.

  Lemma token_update γ {A: ofe} {_: inG Σ (excl_authR A)} (st st' st'' : A) :
    own γ (●E st) ∗ own γ (◯E st'') ==∗ own γ (●E st') ∗ own γ (◯E st').
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.

  Lemma token_agree γ {A: ofe} `{OfeDiscrete A, @LeibnizEquiv A (ofe_equiv A)} {_: inG Σ (excl_authR A)} (st st' : A) :
    own γ (●E st) -∗ own γ (◯E st') -∗ ⌜ st = st' ⌝.
  Proof.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.

  Definition ipA := ip_of_address saA.
  Definition ipB := ip_of_address saB.

  Definition client_si (m : message) : iProp Σ :=
    ∃ (n : Z), ⌜ m_body m = StringOfZ n ⌝ ∗
         (⌜ n >= 0 ⌝%Z → saA ↦c{1/4} n ∗ saB ↦c{1/4} n).

  Definition server_si (m : message) : iProp Σ :=
    ∃ (n : Z), ⌜ m_body m = StringOfZ n ⌝ ∗
         saA ↦c{1/4} n ∗
         saB ↦c{1/4} (n - 1)%Z.

  Lemma wp_client tid (f : nat) (Hf: f > 40) :
    {{{ inv Ns retinv ∗ counter_inv ∗ is_node ipA ∗ saA ⤇ client_si ∗ saB ⤇ server_si ∗
          own stenning_A_name (◯E (ASending 0)) ∗ saA ↦c{1/2} 0%Z ∗ saA ↦c{1/4} 0%Z ∗ saB ↦c{1/4} (-1)%Z ∗
          (ipA, tid) ↦M {[ Arole := f ]} ∗ saA ⤳ (∅, ∅) ∗
          free_ports (ip_of_address saA) {[port_of_address saA]} }}}
      (mkExpr (ip_of_address saA) (client saA saB #())) @ (ipA, tid); ⊤
    {{{ v, RET v; (ipA, tid) ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv&#Hcinv&#Hin&#HsA&#HsB&Hst&Hcc&Hccm&Hcs&Hf&HRT&Hfp) HΦ".
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

    remember (0%Z) as n eqn:Heq.
    replace 0%Z with n by naive_solver.
    replace (ASending 0) with (ASending n) by naive_solver.
    replace (-1)%Z with (n-1)%Z by naive_solver.

    iDestruct "Hcc" as "[Hcc Hcc']".
    iAssert (∃ R T, saA ⤳ (R, T) ∗ ⌜ client_RT n R T ⌝ ∗ (⌜ mAB n ∉ T ⌝ -∗ saA ↦c{1/4} n ∗ saB ↦c{1/4} (n-1)%Z))%I
      with "[HRT Hccm Hcs]" as (R T) "(HRT & HinvRT & Hccm)".
    { iExists _, _. iFrame. iSplit; last naive_solver. rewrite /client_RT. iPureIntro.
      split_and!; try naive_solver set_solver. }

    iCombine "Hcc Hcc'" as "Hcc".

    assert (n >= 0)%Z as Hn; first lia. clear Heq.
    iLöb as "IH" forall (f' n Hn R T) "Hf". iDestruct "Hf'" as %Hf.

    iDestruct "HinvRT" as %HinvRT.

    wp_pure _.
    wp_pure _.

    wp_bind (SendTo _ _ _).
    iApply sswp_MU_wp_fupd.

    iInv Ns as "Hi" "Hclose". iModIntro.
    iApply (wp_send _ _ (if decide (mAB n ∈ T) then true else false) with "[Hsh] [HRT] [] [HsA Hccm]")=>//=>//=>//.
    { destruct (decide _); first naive_solver.
      iSpecialize ("Hccm" with "[//]"). rewrite /server_si //. iNext. iExists n. iSplit=>//.  }

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
    iInv Ns as "Hi" "Hclose". iInv Nc as "Hw" "Hclose'". iModIntro.

    iApply (wp_recv with "[Hsh] [HRT] [HsB]")=>//=>//=>//.
    iNext. clear stB. iDestruct "Hi" as "(Hfr & %stA & %stB & Hmod & HstA & HstB & Hcounters)".
    rewrite /stenning_get_n /=. iDestruct "Hcounters" as "(%Hcrel & Hcci & Hcsi)".
    iDestruct "Hw" as (w) "Hw".

    iDestruct (token_agree with "HstA Hst") as %->.

    iIntros (om r) "Hmsg".

    iAssert (⌜ ∃ omsg, om = Recv saA omsg ⌝)%I as %[omsg ->].
    { iDestruct "Hmsg" as "[(-> & -> & Hsh & HRT)|(%msg & -> & -> & %Heqdest & Hsh & HRT & Hnew)]";
      iPureIntro; naive_solver. }
    destruct (decide (good_message false n omsg)) as [[msg Hgood]|Hbad].
    - iDestruct "Hmsg" as "[(-> & %Heq & Hsh & HRT)|(%msg' & -> & %Heq & %Heqdest & Hsh & HRT & Hnew)]".
      { simplify_eq. naive_solver. }

      iAssert (⌜ msg ∉ R ⌝)%I as %HnR.
      { iPureIntro. destruct HinvRT as (?&Hnin). intros Hc. apply (Hnin n). lia.
        exists msg. split=>//. simplify_eq. eexists. naive_solver. }
      simplify_eq.

      iSpecialize ("Hnew" with "[]").
      { naive_solver. }
      iDestruct "Hnew" as (j) "(%Hbody' & Hnew)".
      iDestruct ("Hnew" with "[]") as "(Hcc' & Hcs)".
      { destruct Hgood as (?&Hcount&?). simplify_eq. rewrite Hbody' ZOfString_inv in Hcount.
        simplify_eq. iPureIntro; lia. }

      iDestruct (lmapsto_agree with "Hcc' Hcc") as %->.
      iDestruct (lmapsto_agree with "Hcs Hcsi") as %Hcseq.

      iCombine "Hcc Hcci Hcc'" as "Hcc".
      replace (1/2 + (1/4 + 1/4))%Qp with 1%Qp by compute_done.
      iDestruct (gen_heap_light_update (L:=socket_address) _ _ _ _ (n+1)%Z
             with "Hw Hcc") as ">[Hw [Hcc [Hccm Hcci]]]".

      destruct Hgood as (?&Hbody&?&?).
      iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((ASending (1+n), stB) : stenning_model) with "Hmod [Hf] [Hfr //]").
      { constructor. exists msg. naive_solver. }
      { set_solver. }
      { set_solver. }
      { rewrite fmap_empty map_union_empty. done. }
      iIntros "Hmod Hf Hfr".
      rewrite map_union_empty /usr_fl /=.
      iMod (token_update with "[$HstA $Hst]") as "[HstA Hst]".
      iMod ("Hclose'" with "[Hw]"); first naive_solver.
      iMod ("Hclose" with "[Hfr Hmod HstA HstB Hcci Hcsi]").
      { iNext. rewrite /retinv. iFrame. iExists (ASending (1+n)), _. iFrame.
        rewrite /stenning_get_n /=. iSplit.
        * iPureIntro. simplify_eq. left. lia.
        * rewrite Z.add_comm. replace (1/2/2)%Qp with (1/4)%Qp by compute_done. iFrame. }
      iModIntro. iApply wp_value'. do 5 wp_pure _.
      clear Hcseq.
      simplify_eq. rewrite bool_decide_true; last by do 2 f_equal.
      do 3 wp_pure _.
      { simpl. rewrite Hbody //. }
      do 4 wp_pure _. rewrite bool_decide_true //. do 2 wp_pure _.
      iApply ("IH" with "[] [Hst] [$] [$Hsh] [] [$HRT] [] [Hccm Hcs] [$Hcc] [$Hf]").
      { iPureIntro; lia. }
      { rewrite Z.add_comm //. }
      { iPureIntro; lia. }
      { iPureIntro. apply client_RT_good=>//. exists msg. naive_solver. }
      { iIntros. replace (n + 1 - 1)%Z with n by lia. iFrame.
        replace (1/2/2)%Qp with (1/4)%Qp by compute_done. iFrame. }
    - iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((ASending n, stB) : stenning_model) with "Hmod [Hf] [Hfr //]").
      { simpl. by apply A_RecvFail. }
      { set_solver. }
      { set_solver. }
      { rewrite fmap_empty map_union_empty. done. }
      iIntros "Hmod Hf Hfr".
      rewrite map_union_empty /usr_fl /=.

      iMod (token_update with "[$HstA $Hst]") as "[HstA Hst]".
      iMod ("Hclose'" with "[Hw]"); first naive_solver.
      iMod ("Hclose" with "[Hfr Hmod HstA HstB Hcci Hcsi]").
      { iNext. rewrite /retinv. iFrame. iExists (ASending n), _. iFrame. simpl. iPureIntro. naive_solver. }
      iModIntro. iApply wp_value'. simpl.
      iDestruct "Hmsg" as "[(-> & %Heq & Hsh & HRT)|(%msg & -> & %Heq & %Heqdest & Hsh & HRT & Hnew)]".
      + do 3 wp_pure _. iApply ("IH" with "[] [$Hst] [$] [$Hsh] [] [$HRT] [] [] [$Hcc] [$Hf]").
        { iPureIntro; lia. }
        { iPureIntro; lia. }
        { iPureIntro. by apply client_RT_garbage_emp. }
        { iIntros (Hnin). exfalso. apply Hnin. set_solver. }
      + do 5 wp_pure _. destruct (decide (m_sender msg = saB)); last first.
        { rewrite bool_decide_false; last naive_solver. wp_pure _.
          iApply ("IH" with "[] [$Hst] [$] [$Hsh] [] [$HRT] [] [] [$Hcc] [$Hf]").
          { iPureIntro; lia. }
          { iPureIntro; lia. }
          { iPureIntro. apply client_RT_garbage_singleton=>//.
            intros m. rewrite /good_message. naive_solver. }
          { iIntros (Hnin). exfalso. apply Hnin. set_solver. } }
        rewrite bool_decide_true //; last by do 2 f_equal. do 2 wp_pure _.
        destruct (ZOfString (m_body msg)) as [msg_n|] eqn:Heqmsg; last first.
        { wp_pure _. rewrite /= Heqmsg //. do 5 wp_pure _.
          iApply ("IH" with "[] [$Hst] [$] [$Hsh] [] [$HRT] [] [] [$Hcc] [$Hf]").
          { iPureIntro; lia. }
          { iPureIntro; lia. }
          { iPureIntro. apply client_RT_garbage_singleton=>//.
            intros m. rewrite /good_message. naive_solver. }
          { iIntros (Hnin). exfalso. apply Hnin. set_solver. } }
        wp_pure _. rewrite /= Heqmsg //. do 4 wp_pure _.
        have Hwrongn : msg_n ≠ n.
        { intros Hc. simplify_eq. apply Hbad. eexists; split=>//. }
        rewrite bool_decide_false //; last naive_solver. wp_pure _.

        destruct (decide (msg_n >= 0)%Z).

        * iAssert (⌜ msg ∈ R ⌝)%I with "[Hnew Hcc]" as %Hin.
          { destruct (decide (msg ∈ R)) as [|Hnin]=>//. iSpecialize ("Hnew" $! Hnin).
            rewrite /client_si.
            iDestruct "Hnew" as (j) "(%Hbody' & Hnew)".
            iDestruct ("Hnew" with "[]") as "(Hcc' & Hcs)".
            { simplify_eq. rewrite Hbody' ZOfString_inv in Heqmsg. simplify_eq. iPureIntro; lia. }
                iDestruct (lmapsto_agree with "Hcc' Hcc") as %->.
            rewrite Hbody' ZOfString_inv in Heqmsg. simplify_eq. }

          iApply ("IH" with "[] [$Hst] [$] [$Hsh] [] [$HRT] [] [] [$Hcc] [$Hf]").
          { iPureIntro; lia. }
          { iPureIntro; lia. }
          { iPureIntro. replace ({[msg]} ∪ R) with R by set_solver.
            apply client_RT_garbage_emp=>//. }
          { iIntros (Hnin). exfalso. apply Hnin. set_solver. }
        * iApply ("IH" with "[] [$Hst] [$] [$Hsh] [] [$HRT] [] [] [$Hcc] [$Hf]").
          { iPureIntro; lia. }
          { iPureIntro; lia. }
          { iPureIntro. apply client_RT_garbage_singleton=>//. intros ??.
            intros (?&?&?&?&?). simplify_eq. }
          { iIntros. exfalso. set_solver. }
  Qed.

  Lemma wp_server tid (f : nat) (Hf: f > 40) :
    {{{ inv Ns retinv ∗ counter_inv ∗ is_node ipB ∗ saA ⤇ client_si ∗ saB ⤇ server_si ∗
          own stenning_B_name (◯E (BReceiving 0)) ∗ saB ↦c{1/2} (-1)%Z ∗
          (ipB, tid) ↦M {[ Brole := f ]} ∗ saB ⤳ (∅, ∅) ∗
          free_ports (ip_of_address saB) {[port_of_address saB]} }}}
      (mkExpr (ip_of_address saB) (server saA saB #())) @ (ipB, tid); ⊤
    {{{ v, RET v; (ipB, tid) ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv&#Hcinv&#Hin&#HsA&#HsB&Hst&Hcs&Hf&HRT&Hfp) HΦ".
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

    remember (-1)%Z as n eqn:Heq.
    replace (BReceiving 0) with (BReceiving (1+n)); last naive_solver.

    iAssert (∃ R T, saB ⤳ (R, T) ∗ ⌜ server_RT n R T ⌝)%I
      with "[HRT]" as (R T) "(HRT & HinvRT)".
    { iExists _, _. iFrame. rewrite /server_RT. iPureIntro.
      split_and!; naive_solver (set_solver || lia). }

    assert (n >= -1)%Z as Hn; first lia. clear Heq.
    iLöb as "IH" forall (f' n Hn R T) "Hf". iDestruct "Hf'" as %Hf. iDestruct "HinvRT" as %HinvRT.

    wp_pure _.

    wp_bind (ReceiveFrom _).
    iApply sswp_MU_wp_fupd.
    iInv Ns as "Hi" "Hclose". iInv Nc as "Hw" "Hclose'". iModIntro.

    iApply (wp_recv with "[Hsh] [HRT] [HsA]")=>//=>//=>//.
    iNext. iDestruct "Hi" as "(Hfr & %stA & %stB & Hmod & HstA & HstB & Hcounters)".
    iDestruct (token_agree with "HstB Hst") as %->.

    rewrite /stenning_get_n /=. iDestruct "Hcounters" as "(%Hcrel & Hcci & Hcsi)".
    iDestruct "Hw" as (w) "Hw".

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

      iDestruct (lmapsto_agree with "Hcsi Hcs") as %->.

      iDestruct ("Hnew" with "[]") as (msg_n Hmsgbody) "[Hccm Hcsm]".
      { iPureIntro. destruct HinvRT as (?&?&Hnin). intros Hc.
        eapply (Hnin (1+n)%Z). lia. eexists. split=>//. exists msg'. naive_solver. }

      iDestruct (lmapsto_agree with "Hcs Hcsm") as %Hcseq. simplify_eq.
      replace (1 + (msg_n - 1))%Z with msg_n by lia.
      iDestruct (lmapsto_agree with "Hcci Hccm") as %Hcseq.

      iCombine "Hcs Hcsi Hcsm" as "Hcs".
      replace (1/2 + (1/4 + 1/4))%Qp with 1%Qp by compute_done.
      iDestruct (gen_heap_light_update (L:=socket_address) _ _ _ _ msg_n
             with "Hw Hcs") as ">[Hw [Hcs [Hcsm Hcsi]]]".

      iMod (token_update with "[$HstB $Hst]") as "[HstB Hst]".
      iMod ("Hclose'" with "[Hw]"); first naive_solver.
      iMod ("Hclose" with "[Hfr Hmod HstA HstB Hcsi Hcci]").
      { iNext. rewrite /retinv. iFrame. iExists _, _. cbn. iFrame. cbn.
        replace (1 + msg_n - 1)%Z with msg_n by lia; cbn.
        replace (1 / 2 / 2)%Qp with (1/4)%Qp by compute_done. iFrame.
        iPureIntro. rewrite !Hcseq. lia. }

      iModIntro. iApply wp_value'. do 5 wp_pure _.
      rewrite bool_decide_true; last by do 2 f_equal.
      do 3 wp_pure _.
      { simpl. rewrite Hbody //. }
      do 5 wp_pure _. rewrite bool_decide_true //; last by (do 3 f_equal; lia). do 3 wp_pure _.

      wp_bind (SendTo _ _ _).
      iApply sswp_MU_wp_fupd.

      iInv Ns as "Hi" "Hclose". iModIntro.
      iApply (wp_send _ _ false with "[Hsh] [HRT] [HsB] [Hcsm Hccm]")=>//=>//=>//.
      { iNext. iExists msg_n. iFrame.
        replace (1 / 2 / 2)%Qp with (1/4)%Qp by compute_done. iFrame. iPureIntro. cbn.
        split. f_equal; lia. lia. }

      iNext. iIntros "Hsh HRT". clear Hcrel Hcseq stA.
      iDestruct "Hi" as "(Hfr & %stA & %stB & Hmod & HstA & HstB & Hcounters)".
      iDestruct (token_agree with "HstB Hst") as %->.
      rewrite /stenning_get_n /=. iDestruct "Hcounters" as "(%Hcrel & Hcci & Hcsi)".
      iDestruct (lmapsto_agree with "Hcsi Hcs") as %->.

      iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((stA, (BReceiving (1 + msg_n)))%Z : stenning_model) with "Hmod [Hf] [Hfr //]").
      { simpl.
        replace (Send _) with (Send (mBA ((1 + msg_n) - 1)))%Z. constructor. f_equal.
        rewrite /mBA //=. do 2 f_equal. lia. }
      { set_solver. }
      { set_solver. }
      { rewrite fmap_empty map_union_empty. done. }
      iIntros "Hmod Hf Hfr".

      iMod (token_update with "[$HstB $Hst]") as "[HstB Hst]".
      iMod ("Hclose" with "[Hfr Hmod HstA HstB Hcci Hcsi]").
      { iNext. rewrite /retinv. iFrame. iExists _, _. iFrame. cbn.
        replace (1 + msg_n - 1)%Z with msg_n by lia. iFrame. iPureIntro. naive_solver. }
      rewrite map_union_empty /usr_fl /=. iModIntro. iApply wp_value'. do 3 wp_pure _.
      iApply ("IH" with "[] [Hst] [Hcs] [$HΦ] [$Hsh] [] [$HRT] [] [$Hf]")=>//.
      { iPureIntro; lia. }
      { replace (1 + (1 + (msg_n - 1)))%Z with (1 + msg_n)%Z by lia. iFrame. }
      { replace (1 + (msg_n - 1))%Z with msg_n by lia. iFrame. }
      { iPureIntro. lia. }
      { iPureIntro. replace (1 + (msg_n - 1))%Z with msg_n by lia.
        apply server_RT_good=>//. exists msg'. rewrite Hmsgbody ZOfString_inv. naive_solver. }
    - iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((stA, BReceiving (1+n)) : stenning_model) with "Hmod [Hf] [Hfr //]").
      { simpl. by apply B_RecvFailEmpty. }
      { set_solver. }
      { set_solver. }
      { rewrite fmap_empty map_union_empty. done. }
      iIntros "Hmod Hf Hfr".
      rewrite map_union_empty /usr_fl /=.
      iMod ("Hclose'" with "[Hw]"); first by naive_solver.
      iDestruct (lmapsto_agree with "Hcsi Hcs") as %Heq.
      iMod ("Hclose" with "[Hfr Hmod HstA HstB Hcsi Hcci]").
      { iNext. rewrite /retinv. iFrame. iExists _, _. iFrame. cbn. iFrame. iPureIntro. naive_solver. }
      iModIntro. iApply wp_value'.
      iDestruct "Hmsg" as "[(-> & %Heq' & Hsh & HRT)|(%msg' & -> & %Heq' & %Heqdest & Hsh & HRT & Hnew)]".
      + do 3 wp_pure _.
        iApply ("IH" with "[] [Hst] [Hcs] [$HΦ] [$Hsh] [] [$HRT] [] [$Hf]")=>//.
        { iPureIntro; lia. }
      + do 5 wp_pure _. rewrite bool_decide_false; last naive_solver.
        wp_pure _. iApply ("IH" with "[] [Hst] [Hcs] [$HΦ] [$Hsh] [] [$HRT] [] [$Hf]")=>//.
        { iPureIntro; lia. }
        { iPureIntro. apply server_RT_garbage_2=>//. intros ??(?&?&?&?&?). naive_solver. }
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
      iMod ("Hclose'" with "[Hw]"); first by naive_solver.
      iDestruct (lmapsto_agree with "Hcsi Hcs") as %Heq.
      iMod ("Hclose" with "[Hfr Hmod HstA HstB Hcsi Hcci]").
      { iNext. rewrite /retinv. iFrame. iExists _, _. iFrame. cbn. iFrame. iPureIntro. naive_solver. }
      iModIntro. iApply wp_value'. do 5 wp_pure _. rewrite bool_decide_true; last by do 2 f_equal.
      destruct (ZOfString (m_body msg')) as [msg_n|] eqn:Heq'.
      + do 3 wp_pure _; first by rewrite /= Heq'. do 5 wp_pure _. rewrite bool_decide_false; last first.
        { intros ?; simplify_eq. apply Hbad. rewrite /good_message Z.add_comm //. naive_solver. }
        do 2 wp_pure _. wp_bind (SendTo _ _ _).
        iApply sswp_MU_wp_fupd. iInv Ns as "Hi" "Hclose". iModIntro.
        iApply (wp_send _ _ (if decide (n >= 0)%Z then true else false) with "[Hsh] [HRT] [HsB]")=>//=>//=>//.
        { destruct (decide _).
          - iPureIntro. destruct HinvRT as (?&HT&?). ospecialize (HT n _ _). lia. lia. naive_solver.
          - iNext. iExists n. cbn. iSplit=>//. by iIntros. }
        iNext. iIntros "Hsh HRT". clear Hcrel stA.
        iDestruct "Hi" as "(Hfr & %stA & %stB & Hmod & HstA & HstB & Hcounters)".
        rewrite /stenning_get_n /=. iDestruct "Hcounters" as "(%Hcrel & Hcci & Hcsi)".
        iDestruct (lmapsto_agree with "Hcsi Hcs") as %->.
        iDestruct (token_agree with "HstB Hst") as %->.
        iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((stA, (BReceiving (1+n))) : stenning_model)
                 with "Hmod [Hf] [Hfr //]").
        { simpl. replace (Send _) with (Send (mBA $ (1 + n) - 1))%Z. constructor. f_equal.
          rewrite /mBA //=. do 2 f_equal. lia. }
        { set_solver. }
        { set_solver. }
        { rewrite fmap_empty map_union_empty. done. }
        iIntros "Hmod Hf Hfr".
        iMod (token_update with "[$HstB $Hst]") as "[HstB Hst]".
        iMod ("Hclose" with "[Hfr Hmod HstA HstB Hcci Hcsi]").
        { iNext. rewrite /retinv. iFrame. iExists _, _. iFrame. cbn.
          replace (1 + n - 1)%Z with n. iFrame. iPureIntro. naive_solver. }
        rewrite map_union_empty /usr_fl /=. iModIntro. iApply wp_value'. do 2 wp_pure _.

        destruct (decide (msg' ∈ R)) as [|Hnin].
        * iApply ("IH" with "[] [Hst] [Hcs] [$HΦ] [$Hsh] [] [$HRT] [] [$Hf]")=>//.
          { iPureIntro; lia. }
          { iPureIntro. destruct HinvRT as (?&HR&?).
            replace ({[msg']} ∪ R) with R by set_solver.
            destruct (decide (n < 0)%Z).
            + apply server_RT_garbage_3=>//. intros ??(?&?&?&?&?). simpl in *. simplify_eq. simpl in *.
              rewrite ->ZOfString_inv in *. simplify_eq. naive_solver.
            + opose proof (HR n _ _); try lia. replace (_ ∪ T) with T by set_solver. split_and!=>//. }
        * iSpecialize ("Hnew" $! Hnin).
          rewrite /server_si.
          iDestruct "Hnew" as (j) "(%Hbody' & Hccm & Hcsm)".
          iDestruct (lmapsto_agree with "Hcs Hcsm") as %->.
          rewrite Hbody' ZOfString_inv in Heq'. simplify_eq.
          exfalso. apply Hbad. exists msg'. split_and!=>//. rewrite Hbody' ZOfString_inv. f_equal. lia.
      + do 3 wp_pure _; first by rewrite /= Heq'. do 7 wp_pure _.
        wp_bind (SendTo _ _ _).
        iApply sswp_MU_wp_fupd. iInv Ns as "Hi" "Hclose". iModIntro.
        iApply (wp_send _ _ (if decide (n >= 0)%Z then true else false) with "[Hsh] [HRT] [HsB]")=>//=>//=>//.
        { destruct (decide _).
          - iPureIntro. destruct HinvRT as (?&HT&?). ospecialize (HT n _ _). lia. lia. naive_solver.
          - iNext. iExists n. cbn. iSplit=>//. by iIntros. }
        iNext. iIntros "Hsh HRT". clear Hcrel stA.
        iDestruct "Hi" as "(Hfr & %stA & %stB & Hmod & HstA & HstB & Hcounters)".
        rewrite /stenning_get_n /=. iDestruct "Hcounters" as "(%Hcrel & Hcci & Hcsi)".
        iDestruct (lmapsto_agree with "Hcsi Hcs") as %->.
        iDestruct (token_agree with "HstB Hst") as %->.
        iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((stA, (BReceiving (1+n))) : stenning_model) with "Hmod [Hf] [Hfr //]").
        { simpl. replace (Send _) with (Send (mBA $ (1 + n) - 1))%Z. constructor. f_equal.
          rewrite /mBA //=. do 2 f_equal. lia. }
        { set_solver. }
        { set_solver. }
        { rewrite fmap_empty map_union_empty. done. }
        iIntros "Hmod Hf Hfr".
        iMod (token_update with "[$HstB $Hst]") as "[HstB Hst]".
        iMod ("Hclose" with "[Hfr Hmod HstA HstB Hcci Hcsi]").
        { iNext. rewrite /retinv. iFrame. iExists _, _. iFrame. cbn.
          replace (1 + n - 1)%Z with n. iFrame. iPureIntro. naive_solver. }
        rewrite map_union_empty /usr_fl /=. iModIntro. iApply wp_value'. do 2 wp_pure _.
        iApply ("IH" with "[] [Hst] [Hcs] [$HΦ] [$Hsh] [] [$HRT] [] [$Hf]")=>//.
        { iPureIntro; lia. }
        { iPureIntro. apply server_RT_garbage_1=>//. intros ??(?&?&?&?). naive_solver. }
  Qed.
End with_Σ.
