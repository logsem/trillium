From stdpp Require Import list fin_maps.
From iris.algebra Require Import excl_auth.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From trillium.program_logic Require Import ectx_lifting.
From fairneris Require Import fairness fair_resources fuel.
From fairneris.aneris_lang Require Import proofmode.
From fairneris.examples Require Import stenning_model_ho foo.
From fairneris.aneris_lang.state_interp Require Import state_interp state_interp_events.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From fairneris.aneris_lang.lib Require Import serialization_code serialization_proof.
From fairneris.lib Require Import gen_heap_light.

Definition client (sa_clt sa_srv : socket_address) : val :=
  λ: "f" "h",
     let: "sh_clt" := NewSocket #() in
     SocketBind "sh_clt" #sa_clt;;
     SetReceiveTimeout "sh_clt" #1 #1;;
     let: "go" := (rec: "rec" "i" "v" :=
       SendTo "sh_clt" (prod_ser int_ser int_ser ("i","v")) #sa_srv ;;
       match: (ReceiveFrom "sh_clt") with
         NONE     => "rec" "i" "v"
       | SOME "m" => let: "jw" := prod_deser int_deser int_deser (Fst "m") in
                     let: "j" := (Fst "jw") in
                     if: "i" = "j"
                     then "h" (Snd "jw");; "rec" ("i" + #1) ("f" #())
                     else "rec" "i" "v"
       end)
     in "go" #0 ("f" #()).

Definition server (sa_clt sa_srv : socket_address) : val :=
  λ: "g",
     let: "sh_srv" := NewSocket #() in
     SocketBind "sh_srv" #sa_srv;;
     SetReceiveTimeout "sh_srv" #1 #1;;
     let: "go" := (rec: "rec" "j" "v" :=
        match: (ReceiveFrom "sh_srv") with
          NONE     => "rec" "j" "v"
        | SOME "m" => let: "iw" := prod_deser int_deser int_deser (Fst "m") in
                      let: "i" := Fst "iw" in
                      if: ("j"+#1) = "i"
                      then 
                        let: "w" := "g" (Snd "iw") in
                        SendTo "sh_srv" (prod_ser int_ser int_ser ("i", "w")) #sa_clt;;
                        "rec" "i" "w"
                      else SendTo "sh_srv" (prod_ser int_ser int_ser ("j", "v")) #sa_clt ;;
                             "rec" "j" "v"                      
        end)
     in "go" #(-1) #(-2).

Definition is_even : val :=
  λ: "x", "x" `rem` #2 = #0.

Definition double_if_even : val :=
  λ: "x", if: is_even "x" then "x" * #2 else assert: #().

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
  (∀ n', mBA_in n' R → (n' >= 0)%Z → mAB_in n' T) ∧
  (∀ n', n' >= n → ¬ mBA_in n' R)%Z ∧
  (∀ msg, msg ∈ R → ∃ n' m, msg = mBA n' m). (*  ∧ *)
  (* (∀ n' m m', mAB n' m ∈ T -> mAB n' m' ∈ T -> m = m'). *)
  (* (∀ n' m m', mAB n' m ∉ T -> mAB n' m' ∉ T). *)

Definition server_RT (n : Z) (R T : gset message) : Prop :=
  (∀ n', 0 <= n' → mBA_in n' T → mAB_in n' R)%Z ∧
  (∀ n', 0 <= n' → n' ≤ n → ∃ m, (mBA n' m) ∈ T)%Z ∧
  (∀ n', n' > n → ¬ mAB_in n' R)%Z ∧
  (∀ msg, msg ∈ R → ∃ n' m, msg = mAB n' m).

Definition garbage_message b msg := ∀ n, (n >= 0)%Z → ¬ good_message b n (Some msg).

Lemma StringOfZ_inv x y : StringOfZ x = StringOfZ y → x = y.
Proof. naive_solver. Qed.

Lemma prod_ser_str_inv s1 s2 s3 s4 :
  prod_ser_str s1 s2 = prod_ser_str s3 s4 → s1 = s3 ∧ s2 = s4.
Proof. 
  rewrite /prod_ser_str.
  intros Heq.
  assert (String.length s1 = String.length s3).
  { apply not_elem_of_string_app_cons_inv_l in Heq; [naive_solver| |].
    - intros H. by apply StringOfZ_not_sep in H.
    - intros H. by apply StringOfZ_not_sep in H. }
  rewrite H in Heq.
  apply append_eq_length_inv in Heq as [_ Heq]; [|done].
  apply append_eq_length_inv in Heq as [_ Heq]; [|done].
  by apply append_eq_length_inv.
Qed.

Lemma client_RT_good msg n m R T :
  (n >= 0)%Z →
  good_message false n (Some msg) →
  (* (∀ m, mAB n m ∉ T) → *)
  client_RT n R T →
  client_RT (n + 1) ({[msg]} ∪ R) ({[ mAB n m ]} ∪ T).
Proof.
  intros Hn Hg (* Hnin'' *) (HRT & Hnin & Hin' (* & Hnin' *)). split_and!.
  - intros n' [msgm [[Hin%elem_of_singleton | Hin]%elem_of_union Hgoodm]] Hn'.
    + simplify_eq.
      have -> : n = n' by eapply good_message_inj.
      exists (mAB n' m). split; [set_solver|]. exists m, (mAB n' m). split_and!; try naive_solver.
    + have [x [??]] : mAB_in n' T.
      * apply HRT =>//. by exists msgm.
      * exists x. naive_solver set_solver.
  - intros n' Hn' [msg' [[Hin%elem_of_singleton | Hin]%elem_of_union ?]].
    + simplify_eq. have ? : n = n' by eapply good_message_inj. lia.
    + ospecialize (Hnin n' _). lia. apply Hnin. exists msg'. naive_solver.
  - intros msg' Hin. rewrite elem_of_union in Hin. destruct Hin.
    + rewrite elem_of_singleton in H. subst. 
      destruct Hg as (m'&msg''&Hmsg''&H). simplify_eq.
      eexists _, _. done.
    + by apply Hin'.
Qed.

Lemma client_RT_garbage n m G R T :
  (n >= 0)%Z →
  (∀ msg, msg ∈ G → garbage_message false msg) →
  (∀ msg, msg ∈ G → ∃ n' m, msg = mBA n' m) →
  client_RT n R T →
  client_RT n (G ∪ R) ({[ mAB n m ]} ∪ T).
Proof.
  intros Hn Hgar HmBA (HRT & Hnin & Hin'). split_and!.
  - intros n' [msgm [[Hin | Hin]%elem_of_union Hgoodm]] Hn'.
    + exfalso. unshelve eapply (Hgar msgm Hin n' _ Hgoodm). lia.
    + have [x [??]] : mAB_in n' T.
      * apply HRT=>//. by exists msgm.
      * exists x. naive_solver set_solver.
  - intros n' Hn' [msgm [[Hin | Hin]%elem_of_union Hgoodm]].
    + unshelve eapply (Hgar msgm Hin n' _ Hgoodm). lia.
    + ospecialize (Hnin n' _). lia. apply Hnin. exists msgm. naive_solver.
  - intros msg' Hin. rewrite elem_of_union in Hin. destruct Hin.
    + by apply HmBA.
    + by apply Hin'.
Qed.

Lemma client_RT_garbage_emp n m R T :
  (n >= 0)%Z →
  client_RT n R T →
  client_RT n R ({[ mAB n m ]} ∪ T).
Proof.
  pose proof (client_RT_garbage n m ∅ R T) as Hccl.
  replace (∅ ∪ R) with R in Hccl by set_solver.
  intros ??. apply Hccl=>//.
Qed.

Lemma client_RT_garbage_singleton n m msg R T :
  (n >= 0)%Z →
  (garbage_message false msg) →
  (∃ n' m, msg = mBA n' m) →
  client_RT n R T →
  client_RT n ({[ msg ]} ∪ R) ({[ mAB n m ]} ∪ T).
Proof.
  intros **. eapply client_RT_garbage=>//;naive_solver set_solver.
Qed.

Lemma server_RT_good msg n m R T :
  good_message true n (Some msg) →
  server_RT (n-1)%Z R T →
  server_RT n ({[msg]} ∪ R) ({[ mBA n m ]} ∪ T).
Proof.
  intros Hgood HRT. split_and!.
  - intros n' Hm0 [msgm [[-> % elem_of_singleton | Hin]%elem_of_union Hgoodm]] .
    + have ?: n = n'.
      { destruct Hgoodm as (?&Ha&Hb&Hc). simplify_eq. 
        apply prod_ser_str_inv in Hb as [H1 _]. by apply StringOfZ_inv in H1. }
      simplify_eq. exists msg. naive_solver set_solver.
    + have [x [??]] : mAB_in n' R.
      * apply HRT =>//. by exists msgm.
      * exists x. naive_solver set_solver.
  - intros n' Hm0 Hmn. destruct (decide (n' = n)).
    + simplify_eq. exists m. by apply elem_of_union; left; apply elem_of_singleton.
    + apply HRT in Hm0 as [m' Hm0]; [|lia]. exists m'. apply elem_of_union; right. done.
  - intros n' Hmn (msg'&Hin&Hgood'). apply elem_of_union in Hin; destruct Hin as [Hin|Hin].
    + apply elem_of_singleton in Hin; simplify_eq. have: n' = n; last lia.
      eapply good_message_inj=>//.
    + destruct HRT as (?&?&Hnin&?). unshelve eapply (Hnin n' _). lia. by exists msg'.
  - destruct HRT as (?&?&Hnin&HmAB).
    intros msg' Hin. rewrite elem_of_union in Hin. destruct Hin.
    + rewrite elem_of_singleton in H1. subst. 
      destruct Hgood as (m'&msg''&Hmsg''&H'). simplify_eq.
      eexists _, _. done.
    + by apply HmAB.
Qed.

Lemma server_RT_garbage_1 msg n m R T :
  (n >= -1)%Z →
  (garbage_message true msg) →
  (∃ n' m, msg = mAB n' m) →
  server_RT n R T →
  server_RT n ({[msg]} ∪ R) ({[ mBA n m ]} ∪ T).
Proof.
  intros Nn0 Hgar HmAB' HRT. destruct HRT as (Hincl&Hin'&Hnin&HmAB). split_and!.
  - intros n' Hm0 [msgm [[Hin%elem_of_singleton | Hin]%elem_of_union Hgoodm]].
    + simplify_eq. have ?: n = n'.
      { destruct Hgoodm as (?&Ha&Hb&Hc). simplify_eq.
        apply prod_ser_str_inv in Hb as [H1 _]. by apply StringOfZ_inv in H1. }
      simplify_eq. have ? := Hm0. apply (Hin' n') in Hm0 =>//.
      have [msgin ?] : mAB_in n' R.
      { apply Hincl=>//.
        destruct Hm0 as [m' Hm0].
        exists (mBA n' m'). 
        split; [naive_solver|].
        eexists _, _. split; [done|].
        done. }
      exists msgin. naive_solver set_solver.
    + have Hinp: mBA_in n' T.
      { exists msgm. naive_solver. }
      apply Hincl in Hinp as [msgin ?]=>//. exists msgin. naive_solver set_solver.
  - intros n' Hm0 Hmn. destruct (decide (n' = n)).
    + exists m. simplify_eq. apply elem_of_union; left; apply elem_of_singleton. done.
    + apply Hin' in Hm0; [|lia]. destruct Hm0 as [m' Hm0].
      exists m'. apply elem_of_union; right. done.
  - intros n' Hmn (msg'&Hin&Hgood'). apply elem_of_union in Hin; destruct Hin as [Hin|Hin].
    + apply elem_of_singleton in Hin; simplify_eq. apply (Hgar n'). lia. done.
    + unshelve eapply (Hnin n' _). lia. by exists msg'.
  - intros msg' Hin. rewrite elem_of_union in Hin. destruct Hin.
    + rewrite elem_of_singleton in H. subst. by apply HmAB'.
    + by apply HmAB.
Qed.

Lemma server_RT_garbage_2 msg n R T :
  (n >= -1)%Z →
  (garbage_message true msg) →
  (∃ n' m, msg = mAB n' m) →
  server_RT n R T →
  server_RT n ({[msg]} ∪ R) T.
Proof.
  intros Nn0 Hgar HmAB' HRT. destruct HRT as (Hincl&Hin'&Hnin&HmAB). split_and!.
  - intros m Hm0 [msgm [Hin Hgood]].
    + have Hinp: mBA_in m T.
      { exists msgm. naive_solver. }
      apply Hincl in Hinp as [msgin ?]=>//. exists msgin. naive_solver set_solver.
  - intros m Hm0 Hmn. apply Hin'=>//.
  - intros m Hmn (msg'&Hin&Hgood'). apply elem_of_union in Hin; destruct Hin as [Hin|Hin].
    + apply elem_of_singleton in Hin; simplify_eq. apply (Hgar m). lia. done.
    + unshelve eapply (Hnin m _). lia. by exists msg'.
  - intros msg' Hin. rewrite elem_of_union in Hin. destruct Hin.
    + rewrite elem_of_singleton in H. subst. by apply HmAB'.
    + by apply HmAB.
Qed.

Lemma server_RT_garbage_3 msg n R T :
  (n >= -1)%Z →
  (garbage_message false msg) →
  server_RT n R T →
  server_RT n R ({[msg]} ∪ T).
Proof.
  intros Nn0 Hgar HRT. destruct HRT as (Hincl&Hin'&Hnin&HmAB). split_and!.
  - intros m Hm0 [msgm [[Hin%elem_of_singleton | Hin]%elem_of_union Hgoodm]].
    + simplify_eq. exfalso. apply (Hgar m)=>//. lia.
    + have Hinp: mBA_in m T.
      { exists msgm. naive_solver. }
      apply Hincl in Hinp as [msgin ?]=>//. exists msgin. naive_solver set_solver.
  - intros m Hm0 Hmn.
    apply Hin' in Hm0; [|done]. destruct Hm0 as [m' Hm0]. exists m'.
    apply elem_of_union; right. done.
  - intros m Hmn (msg'&Hin&Hgood'). unshelve eapply (Hnin m _). lia. by exists msg'.
  - intros msg' Hin. by apply HmAB.
Qed.

Lemma server_RT_garbage_4 n m R T :
  (n >= -1)%Z →
  server_RT n R T →
  server_RT n R ({[ mBA n m ]} ∪ T).
Proof.
  intros Nn0 HRT. destruct HRT as (Hincl&Hin'&Hnin&HmAB). split_and!.
  - intros n' Hm0 [msgm [[Hin%elem_of_singleton | Hin]%elem_of_union Hgoodm]].
    + simplify_eq. have ?: n = n'.
      { destruct Hgoodm as (?&Ha&Hb&Hc). simplify_eq.
        apply prod_ser_str_inv in Hb as [H1 _]. by apply StringOfZ_inv in H1. }
      simplify_eq. have ? := Hm0. apply (Hin' n') in Hm0 =>//.
      have [msgin ?] : mAB_in n' R.
      { apply Hincl=>//.
        destruct Hm0 as [m' Hm0].
        exists (mBA n' m'). 
        split; [naive_solver|].
        eexists _, _. split; [done|].
        done. }
      exists msgin. naive_solver set_solver.
    + have Hinp: mBA_in n' T.
      { exists msgm. naive_solver. }
      apply Hincl in Hinp as [msgin ?]=>//. exists msgin. naive_solver set_solver.
  - intros n' Hm0 Hmn. destruct (decide (n' = n)).
    + exists m. simplify_eq. apply elem_of_union; left; apply elem_of_singleton. done.
    + apply Hin' in Hm0; [|lia]. destruct Hm0 as [m' Hm0].
      exists m'. apply elem_of_union; right. done.
  - intros m' Hmn (msg'&Hin&Hgood'). unshelve eapply (Hnin m' _). lia. by exists msg'.
  - intros msg' Hin. by apply HmAB.
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

  Definition client_si (Ψ : Z → iProp Σ) (msg : message) : iProp Σ :=
    ∃ (n m : Z), ⌜ msg = mBA n m ⌝ ∗
         (⌜ n >= 0 ⌝%Z → saA ↦c{1/4} n ∗ saB ↦c{1/4} n ∗ Ψ m).

  Definition server_si (Φ : Z → iProp Σ) (msg : message) : iProp Σ :=
    ∃ (n m : Z), ⌜ msg = mAB n m ⌝ ∗
         saA ↦c{1/4} n ∗
         saB ↦c{1/4} (n - 1)%Z ∗
         Φ m.

  #[global] Instance stenning_A_state_inhabited : Inhabited stenning_A_state.
  Proof. exact (populate (ASending 0)). Qed.
  #[global] Instance stenning_B_state_inhabited : Inhabited stenning_B_state.
  Proof. exact (populate (BSending 0)). Qed.

  Definition int_to_val_pred (Φ : Z → iProp Σ) : val → iProp Σ := 
    (λ v, ∃ (x:Z), ⌜v = #x⌝ ∗ Φ x)%I.

  Lemma wp_client Φ Ψ tid (fl : nat) (Hf: fl > 100) (f h : val) gc :
    let st := ((inhabitant stenning_state):stenning_model) in
    gc < usr_fl st / 10 →
    (∃ c, ⌜c < usr_fl st / 10⌝ ∗
          ∀ fl v , ⌜ fl > c ⌝ -∗
       {{{ (ipA, tid) ↦M {[ Arole := fl ]} ∗ int_to_val_pred Ψ v }}}
            mkExpr ipA (h v) @ (ipA,tid)
          {{{ w, RET mkVal ipA w; (ipA, tid) ↦M {[ Arole := fl - c ]} }}}) -∗
    {{{ inv Ns retinv ∗ counter_inv ∗ is_node ipA ∗ saA ⤇ client_si Ψ ∗ saB ⤇ server_si Φ ∗
          own stenning_A_name (◯E (ASending 0)) ∗ saA ↦c{1/2} 0%Z ∗ saA ↦c{1/4} 0%Z ∗ saB ↦c{1/4} (-1)%Z ∗
          (ipA, tid) ↦M {[ Arole := fl ]} ∗ saA ⤳ (∅, ∅) ∗
          free_ports (ip_of_address saA) {[port_of_address saA]} ∗
          is_gen ipA tid gc f (int_to_val_pred Φ) }}}
      (mkExpr (ip_of_address saA) (client saA saB f h)) @ (ipA, tid); ⊤
    {{{ v, RET v; (ipA, tid) ↦M ∅  }}}.
  Proof.
    simpl.
    intros Hgc.
    iIntros "(%c&%Hc'&#Hh)" (Φ')"!> (#Hinv&#Hcinv&#Hin&#HsA&#HsB&Hst&Hcc&Hccm&Hcs&Hf&HRT&Hfp&Hvs) HΦ".
    rewrite /client.
    wp_pures.

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

    remember (0%Z) as n eqn:Heq.
    replace 0%Z with n by naive_solver.
    replace (ASending 0) with (ASending n) by naive_solver.
    replace (-1)%Z with (n-1)%Z by naive_solver.

    iDestruct "Hcc" as "[Hcc Hcc']".
    wp_bind (f _).
    iApply (is_gen_spec with "[$Hvs $Hf]"); [lia|].
    iIntros "!>" (w) "(HΦ'&Hgen&Hf)".

    iAssert (∃ (f : nat), ⌜ f > 20 ⌝ ∗ (ipA, tid) ↦M <[Arole:=f]> ∅)%I
      with "[Hf]" as (f') "[%Hf' Hf]".
    { iExists _. iFrame. iPureIntro. lia. }
    clear Hf.

    iAssert (∃ x : Z, ⌜w = #x⌝)%I with "[HΦ']" as %[x ->].
    { iDestruct "HΦ'" as (x ->) "HΦ'". iExists _. done. }

    iAssert (∃ R T, saA ⤳ (R, T) ∗ ⌜ client_RT n R T ⌝ ∗ ((⌜ mAB n x ∉ T ⌝) -∗ saA ↦c{1/4} n ∗ saB ↦c{1/4} (n-1)%Z))%I
      with "[HRT Hccm Hcs]" as (R T) "(HRT & HinvRT & Hccm)".
    { iExists _, _. iFrame. iSplit.
      - rewrite /client_RT. iPureIntro.
        split_and!; try naive_solver set_solver.
      - done. }

    iCombine "Hcc Hcc'" as "Hcc".

    assert (n >= 0)%Z as Hn; first lia. clear Heq.
    (* iLöb as "IH" forall (f' n Hn R T) "Hf". iDestruct "Hf'" as %Hf. *)

    iAssert (⌜mAB n x ∉ T⌝ -∗ Φ x)%I with "[HΦ']" as "HΦ'".
    { iDestruct "HΦ'" as (y Hy) "HΦ". inversion Hy. subst. iFrame. done. }

    iLöb as "IH" forall (f' Hf' n Hn R T x) "Hf". rename Hf' into Hf.

    iDestruct "HinvRT" as %HinvRT.

    wp_pures.
    wp_bind (prod_ser _ _ _).
    (* iDestruct "HΦ'" as (x ->) "HΦ'".  *)
    iApply (prod_ser_spec int_serialization int_serialization with "[$Hf]"); [try done..|].
    { rewrite /prod_valid_val. eexists _, _. split; [done|]. simpl.
      split; eexists _; done. }
    { simpl. lia. }
    iIntros "!>" (s) "[%Hser Hf]".

    destruct Hser as (v1&v2&s1&s2&Hv&Hv1&Hv2&->).

    assert (mAB n x = {| m_sender := saA; m_destination := saB; m_body := prod_ser_str s1 s2 |}) as Hmsg.
    { rewrite /mAB. f_equiv.
      destruct Hv1 as [z1 [-> ->]].
      destruct Hv2 as [z2 [-> ->]].
      f_equiv; by simplify_eq. }

    wp_pures.

    wp_bind (SendTo _ _ _).
    iApply sswp_MU_wp_fupd.
    
    iInv Ns as "Hi" "Hclose". iModIntro.
    iApply (wp_send _ _ (if decide (mAB n x ∈ T) then true else false) with "[Hsh] [HRT] [] [HsA Hccm HΦ']")=>//=>//=>//.
    { destruct (decide _).
      { iPureIntro. rewrite -Hmsg. done. }
      iDestruct ("Hccm" with "[]") as "[HsaA HsaB]".
      { iIntros (y). iPureIntro. set_solver. (* Stuck *) }
      (*  *)
      rewrite /server_si //. iNext. iExists n, x.
      iFrame. rewrite -Hmsg. iSplit; [done|]. by iApply "HΦ'". }

    iNext. iIntros "Hsh HRT".
    iDestruct "Hi" as "(Hfr & %stA & %stB & Hmod & HstA & HstB)".
    iDestruct (token_agree with "HstA Hst") as %->.

    iApply (mu_step_model _ (Arole:usr_role stenning_model) _ _ ∅ ∅ _ ((AReceiving n, stB) : stenning_model) with "Hmod [Hf] [Hfr //]").
    { simpl. rewrite -Hmsg. constructor. }
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
    destruct (decide (good_message false n omsg)) as [[m [msg Hgood]]|Hbad].
    - iDestruct "Hmsg" as "[(-> & %Heq & Hsh & HRT)|(%msg' & -> & %Heq & %Heqdest & Hsh & HRT & Hnew)]".
      { simplify_eq. naive_solver. }

      iAssert (⌜ msg ∉ R ⌝)%I as %HnR.
      { iPureIntro. destruct HinvRT as (?&Hnin&?). intros Hc. apply (Hnin n). lia.
        exists msg. split=>//. simplify_eq. eexists. naive_solver. }
      simplify_eq.

      iSpecialize ("Hnew" with "[]").
      { naive_solver. }
      iDestruct "Hnew" as (j w') "(%Hbody' & Hnew)".
      iDestruct ("Hnew" with "[]") as "(Hcc' & Hcs & HΨ)".
      { destruct Hgood as (?&Hcount). simplify_eq.
        rewrite /mBA in Heqdest. simpl in *. simplify_eq.
        assert (j = n) as ->.
        { apply prod_ser_str_inv in H0. destruct H0 as [Heq _].
          apply StringOfZ_inv in Heq.
          done. }
        simplify_eq. iPureIntro; lia. }

      iDestruct (lmapsto_agree with "Hcc' Hcc") as %->.
      iDestruct (lmapsto_agree with "Hcs Hcsi") as %Hcseq.

      iCombine "Hcc Hcci Hcc'" as "Hcc".
      replace (1/2 + (1/4 + 1/4))%Qp with 1%Qp by compute_done.
      iDestruct (gen_heap_light_update (L:=socket_address) _ _ _ _ (n+1)%Z
             with "Hw Hcc") as ">[Hw [Hcc [Hccm Hcci]]]".

      destruct Hgood as (?&?).
      iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((ASending (1+n), stB) : stenning_model) with "Hmod [Hf] [Hfr //]").
      { constructor. exists m, msg. naive_solver. }
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
      iModIntro. iApply wp_value'. wp_pures.
      clear Hcseq.
      simplify_eq. (* rewrite bool_decide_true; last by do 2 f_equal. *)
      wp_pures.

      wp_bind (prod_deser _ _ _).

      iApply (prod_deser_spec int_serialization int_serialization
                _ _ _ _ (#n,#m)%V with "Hf").
      { rewrite /mBA. simpl.
        eexists _, _, (StringOfZ n), (StringOfZ m).
        repeat (split; [done|]).
        split.
        { eexists _. done. }
        split.
        { eexists _. done. }
        done. }
      { simpl. lia. }
      iIntros "!> Hf".
      simpl. wp_pures.
      case_bool_decide; [|done].
      wp_pures.
      wp_bind (h _).
      iApply ("Hh" with "[] [$Hf HΨ]"); [iPureIntro;lia|..].
      { iExists _. iFrame. done. }
      iIntros "!>" (w'') "Hf".
      wp_pures.
      wp_bind (f _).
      iApply (is_gen_spec with "[$Hgen $Hf]"); [lia|].
      iIntros "!>" (w''') "(HΦ'&Hgen&Hf)".
      wp_pure _.

      iDestruct ("HΦ'") as (y ->) "HΦ'".

      iApply ("IH" with "[] [] [Hst] [$] [$Hsh] [$Hgen] [$HRT] [] [Hccm Hcs] [$Hcc] [$HΦ'//] [$Hf]").
      { iPureIntro; lia. }
      { iPureIntro; lia. }
      { rewrite Z.add_comm //. }
      { iPureIntro. rewrite -Hmsg. apply client_RT_good=>//. eexists _, _. done. }
      { iIntros (Hnin).  replace (n + 1 - 1)%Z with n by lia. iFrame.
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
      { do 3 wp_pure _.
        iApply ("IH" with "[] [] [$Hst] [$] [$Hsh] [$Hgen] [$HRT] [] [] [$Hcc] [] [$Hf]").
        { iPureIntro; lia. }
        { iPureIntro; lia. }
        { iPureIntro. rewrite -Hmsg. by apply client_RT_garbage_emp. }
        { iIntros (Hnin). exfalso. rewrite -Hmsg in Hnin. set_solver. }
        { rewrite -Hmsg. iIntros (Hin). set_solver. } }
      wp_pures.

      destruct (decide (msg ∈ R)).
      { assert (∃ n' m, msg = mBA n' m) as [n' [m ->]].
        { by apply HinvRT. }

        wp_bind (prod_deser _ _ _).

        iApply (prod_deser_spec int_serialization int_serialization
                  _ _ _ _ (#n',#m)%V with "Hf").
        { rewrite /mBA. simpl.
          eexists _, _, (StringOfZ n'), (StringOfZ m).
          repeat (split; [done|]).
          split.
          { eexists _. done. }
          split.
          { eexists _. done. }
          done. }
        { simpl. lia. }
        iIntros "!> Hf".
        simpl. wp_pures.
        case_bool_decide.
        * exfalso. apply Hbad. inversion Heq.
          eexists _, _. split; [done|]. subst. done.
        * wp_pure _.
          iApply ("IH" with "[] [] [$Hst] [$] [$Hsh] [$Hgen] [$HRT] [] [] [$Hcc] [] [$Hf]").
          { iPureIntro; lia. }
          { iPureIntro; lia. }
          { iPureIntro. rewrite -Hmsg.
            apply client_RT_garbage_emp=>//.
            rewrite subseteq_union_1_L; set_solver. }
          { iIntros (Hnin). exfalso. set_solver. }
          { rewrite -Hmsg. iIntros (Hin). set_solver. }
      }

      iSpecialize ("Hnew" with "[//]").

      iDestruct "Hnew" as (n' m ->) "Hs".
      wp_bind (prod_deser _ _ _).

      iApply (prod_deser_spec int_serialization int_serialization
                _ _ _ _ (#n',#m)%V with "Hf").
      { rewrite /mBA. simpl.
        eexists _, _, (StringOfZ n'), (StringOfZ m).
        repeat (split; [done|]).
        split.
        { eexists _. done. }
        split.
        { eexists _. done. }
        done. }
      { simpl. lia. }
      iIntros "!> Hf".
      simpl. wp_pures.
      case_bool_decide.
      * exfalso. apply Hbad. inversion Heq.
        eexists _, _. split; [done|]. subst. done.
      * wp_pure _.
        destruct (decide (n' >= 0)%Z).
        { iDestruct ("Hs" with "[//]") as "[Hcc' Hcs]".
          iDestruct (lmapsto_agree with "Hcc Hcc'") as %Hcseq. simplify_eq. }
        iApply ("IH" with "[] [] [$Hst] [$] [$Hsh] [$Hgen] [$HRT] [] [] [$Hcc] [] [$Hf]").
        { iPureIntro; lia. }
        { iPureIntro; lia. }
        { iPureIntro. rewrite -Hmsg.
          apply client_RT_garbage_singleton=>//.
          { intros m' Hm' Hmsg'.
            destruct Hmsg' as (m''&msg''&Hmsg''&H'''). simplify_eq.
            apply prod_ser_str_inv in Hmsg'' as [Heq _].
            apply StringOfZ_inv in Heq. subst. done. }
          eexists _, _. done. }
        { iIntros (Hnin). exfalso. set_solver. }
        { rewrite -Hmsg. iIntros (Hin). set_solver. }
  Qed.

  Lemma wp_server Φ Ψ tid (g : val) (f : nat) (Hf: f > 100) :
    let st := ((inhabitant stenning_state):stenning_model) in
    (∃ c, ⌜c < usr_fl st / 10⌝ ∗
          ∀ fl (x:Z), ⌜ fl > c ⌝ -∗
                  {{{ (ipB, tid) ↦M {[ Brole := fl ]} ∗ Φ x }}}
                    mkExpr ipB (g #x) @ (ipB, tid); ⊤
                  {{{ (y:Z), RET mkVal ipB #y; Ψ y ∗ (ipB, tid) ↦M {[ Brole := fl-c ]} }}})%I -∗
    {{{ inv Ns retinv ∗ counter_inv ∗ is_node ipB ∗ saA ⤇ client_si Ψ ∗ saB ⤇ server_si Φ ∗
          own stenning_B_name (◯E (BReceiving 0)) ∗ saB ↦c{1/2} (-1)%Z ∗
          (ipB, tid) ↦M {[ Brole := f ]} ∗ saB ⤳ (∅, ∅) ∗
          free_ports (ip_of_address saB) {[port_of_address saB]} }}}
      (mkExpr (ip_of_address saB) (server saA saB g)) @ (ipB, tid); ⊤
    {{{ v, RET v; (ipB, tid) ↦M ∅ }}}.
  Proof.
    simpl.
    iIntros "(%c&%Hc'&#Hg)" (Φ') "!> (#Hinv&#Hcinv&#Hin&#HsA&#HsB&Hst&Hcs&Hf&HRT&Hfp) HΦ".
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
    remember (-2)%Z as m eqn:Heqm.
    replace (BReceiving 0) with (BReceiving (1+n)); last naive_solver.

    iAssert (∃ R T, saB ⤳ (R, T) ∗ ⌜ server_RT n R T ⌝ ∗ (⌜(n >= 0)%Z → mBA n m ∈ T⌝))%I
      with "[HRT]" as (R T) "(HRT & HinvRT & Hin')".
    { iExists _, _. iFrame. rewrite /server_RT. iPureIntro.
      split_and!; naive_solver (set_solver || lia). }

    assert (n >= -1)%Z as Hn; first lia. clear Heq Heqm.
    iLöb as "IH" forall (f' n Hn m R T) "Hf". iDestruct "Hf'" as %Hf. iDestruct "HinvRT" as %HinvRT.

    iDestruct "Hin'" as %Hin'.

    wp_pures.

    wp_bind (ReceiveFrom _).
    iApply sswp_MU_wp_fupd.
    iInv Ns as "Hi" "Hclose". iInv Nc as "Hw" "Hclose'". iModIntro.

    iApply (wp_recv with "[Hsh] [HRT] [HsA]")=>//=>//=>//.
    iNext. iDestruct "Hi" as "(Hfr & %stA & %stB & Hmod & HstA & HstB & Hcounters)".
    iDestruct (token_agree with "HstB Hst") as %->.

    rewrite /stenning_get_n /=. iDestruct "Hcounters" as "(%Hcrel & Hcci & Hcsi)".
    iDestruct "Hw" as (w) "Hw".

    iIntros (om r) "Hmsg".
    iDestruct "Hmsg" as "[(-> & %Heq & Hsh & HRT)|(%msg' & -> & %Heq & %Heqdest & Hsh & HRT & Hnew)]".
    {                          
      (** Case: No message *)
      destruct om; [done|]. simplify_eq.
      iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((stA, BReceiving (1+n)) : stenning_model) with "Hmod [Hf] [Hfr //]").
      { simpl. apply B_RecvFailEmpty. naive_solver. }
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
      simpl. do 3 wp_pure _.
      iApply ("IH" with "[] [$Hst] [$Hcs] [$HΦ] [$Hsh] [] [$HRT] [] [] [$Hf]")=>//.
      { iPureIntro; lia. }
    }
    (** Case: Message *)
    destruct (decide (good_message true (1+n) (Some msg'))) as [[msg Hgood]|Hbad].
    - (** Case: Good message *)
      destruct Hgood as (?&Hbody&?). simplify_eq.
      iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((stA, BSending (1 + (1 + n))) : stenning_model) with "Hmod [Hf] [Hfr //]").
      { constructor. eexists msg. naive_solver. }
      { set_solver. }
      { set_solver. }
      { rewrite fmap_empty map_union_empty. done. }
      iIntros "Hmod Hf Hfr".
      rewrite map_union_empty /usr_fl /=.

      iDestruct (lmapsto_agree with "Hcsi Hcs") as %->.

      iDestruct ("Hnew" with "[]") as (msg_n msg_m Hmsg) "(Hccm&Hcsm&HΦ')".
      { iPureIntro. destruct HinvRT as (?&?&Hnin&?). intros Hc.
        eapply (Hnin (1+n)%Z). lia. eexists. split=>//. exists msg. naive_solver. }

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

      iModIntro. iApply wp_value'. wp_pures. 
      
      apply prod_ser_str_inv in Hmsg as [Hmsg1 Hmsg2].
      apply StringOfZ_inv in Hmsg1 as Heq1.
      apply StringOfZ_inv in Hmsg2 as Heq2.

      wp_bind (prod_deser _ _ _).
      iApply (prod_deser_spec int_serialization int_serialization
                _ _ _ _ (#msg_n,#msg_m)%V with "Hf").
      { rewrite /mBA. simpl.
        eexists _, _, (StringOfZ msg_n), (StringOfZ msg_m).
        repeat (split; [done|]).
        split.
        { eexists _. done. }
        split.
        { eexists _. done. }
        simplify_eq. done. }
      { simpl. lia. }
      iIntros "!>Hf".
      simpl in *.
      wp_pures.
      simplify_eq.
      rewrite bool_decide_true; last by do 2 f_equal; lia.
      wp_pures.
      
      wp_bind (g _).
      iApply ("Hg" with "[] [$Hf $HΦ']"); [iPureIntro; lia|].
      iIntros "!>" (y) "[HΨ Hf]".
      wp_pures.
      
      wp_bind (prod_ser _ _ _).
      iApply (prod_ser_spec int_serialization int_serialization with "[$Hf]"); [try done..|].
      { rewrite /prod_valid_val. eexists _, _. split; [done|]. simpl.
        split; eexists _; done. }
      { simpl. lia. }
      iIntros "!>" (s) "[%Hser Hf]".
      destruct Hser as (v1&v2&s1&s2&Hv&Hv1&Hv2&->).
      destruct Hv1 as [x1 [-> ->]].
      destruct Hv2 as [x2 [-> ->]].
      
      wp_pures.
      wp_bind (SendTo _ _ _).
      iApply sswp_MU_wp_fupd.

      iInv Ns as "Hi" "Hclose". iModIntro.
      
      iApply (wp_send _ _ false with "[Hsh] [HRT] [HsB] [Hcsm Hccm HΨ]")=>//=>//=>//.
      { iNext. iExists _, y. iFrame.
        replace (1 / 2 / 2)%Qp with (1/4)%Qp by compute_done. iFrame. iPureIntro. cbn.
        split; [|done]. simplify_eq. done. } (* Serialization overhead *)

      iNext. iIntros "Hsh HRT".
      iDestruct "Hi" as "(Hfr & %stA' & %stB & Hmod & HstA & HstB & Hcounters)".
      iDestruct (token_agree with "HstB Hst") as %Heq.
      rewrite /stenning_get_n /=. iDestruct "Hcounters" as "(%Hcrel' & Hcci & Hcsi)".
      iDestruct (lmapsto_agree with "Hcsi Hcs") as %->.

      iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((stA', (BReceiving (1 + (stenning_get_n_A stA))))%Z : stenning_model) with "Hmod [Hf] [Hfr //]").
      { simpl.
        replace (Send _) with (Send (mBA ((1 + ( stenning_get_n_A stA)) - 1) y))%Z. simplify_eq.
        constructor. f_equal.
        simplify_eq.
        rewrite /mBA //=. do 2 f_equal; f_equiv; lia. }
      { set_solver. }
      { set_solver. }
      { rewrite fmap_empty map_union_empty. done. }
      iIntros "Hmod Hf Hfr".
      iMod (token_update with "[$HstB $Hst]") as "[HstB Hst]".
      iMod ("Hclose" with "[Hfr Hmod HstA HstB Hcci Hcsi]").
      { iNext. rewrite /retinv. iFrame. iExists _, _. iFrame. cbn.
        replace (1 + stenning_get_n_A stA - 1)%Z with (stenning_get_n_A stA)%Z by lia.
        iFrame. iPureIntro. naive_solver. }
      rewrite map_union_empty /usr_fl /=. iModIntro. iApply wp_value'. do 2 wp_pure _.
      iApply ("IH" with "[] [$Hst] [$Hcs] [$HΦ] [$Hsh] [] [$HRT] [] [] [$Hf]")=>//.
      { iPureIntro; lia. }
      { iPureIntro; lia. }
      { iPureIntro.
        replace (1 + stenning_get_n_A stA - 1)%Z with (stenning_get_n_A stA)%Z by lia.
        simplify_eq.
        replace {|
         m_sender := saB;
         m_destination := saA;
         m_body := prod_ser_str (int_ser_str (stenning_get_n_A stA)) (int_ser_str x2)
       |} with (mBA (stenning_get_n_A stA) x2); last first.
        { rewrite /mBA. f_equiv. done. }
        apply server_RT_good=>//. eexists _, _. done. }
      { iPureIntro. intro Hn'. rewrite elem_of_union. left.
        simplify_eq. by apply elem_of_singleton. }
    - (** Case: Bad message  *)
      iAssert (⌜∃ n' m, msg' = mAB n' m⌝)%I with "[Hnew]" as %[n' [msg_m ]].
      { destruct (decide (msg' ∈ R)).
        { iPureIntro. by apply HinvRT. }
        iDestruct ("Hnew" with "[//]") as (n' m' ->) "Hnew". iPureIntro. eexists _, _. done. }
      subst.
      iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((stA, BSending (1+n)) : stenning_model) with "Hmod [Hf] [Hfr //]").
      { simpl. subst. by eapply B_RecvFailWrong. }
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
      iModIntro. iApply wp_value'.

      wp_pures.

      wp_bind (prod_deser _ _ _).
      iApply (prod_deser_spec int_serialization int_serialization
                _ _ _ _ (#n',#msg_m)%V with "Hf").
      { rewrite /mBA. simpl.
        eexists _, _, (StringOfZ n'), (StringOfZ msg_m).
        repeat (split; [done|]).
        split.
        { eexists _. done. }
        split.
        { eexists _. done. }
        simplify_eq. done. }
      { simpl. lia. }
      iIntros "!>Hf".
      simpl in *.
      wp_pures.
      assert (n+1 ≠ n')%Z.
      { intros <-. apply Hbad. eexists _, _. split; [done|].
        f_equiv. lia. done. }
      rewrite bool_decide_false; [|done].
      wp_pures.
      wp_bind (prod_ser _ _ _).
      (* iDestruct "HΦ'" as (x ->) "HΦ'".  *)
      iApply (prod_ser_spec int_serialization int_serialization with "[$Hf]"); [try done..|].
      { rewrite /prod_valid_val. eexists _, _. split; [done|]. simpl.
        split; eexists _; done. }
      { simpl. lia. }
      iIntros "!>" (s) "[%Hser Hf]".
      destruct Hser as (v1&v2&s1&s2&Hv&Hv1&Hv2&->).
      destruct Hv1 as [x1 [-> ->]].
      destruct Hv2 as [x2 [-> ->]].
      simpl in *.
      wp_pures.
      
      wp_bind (SendTo _ _ _).
      iApply sswp_MU_wp_fupd. iInv Ns as "Hi" "Hclose". iModIntro.
      iApply (wp_send _ _ (if decide (n >= 0)%Z then true else false) with "[Hsh] [HRT] []")=>//=>//=>//.
      { destruct (decide _).
        - iPureIntro. simplify_eq. by apply Hin'.
        - iNext. iExists n, m. cbn. iSplit=>//; [|by iIntros]. iPureIntro.
          by simplify_eq. }
      iNext. iIntros "Hsh HRT". clear Hcrel stA.
      iDestruct "Hi" as "(Hfr & %stA & %stB & Hmod & HstA & HstB & Hcounters)".
      rewrite /stenning_get_n /=. iDestruct "Hcounters" as "(%Hcrel & Hcci & Hcsi)".
      iDestruct (lmapsto_agree with "Hcsi Hcs") as %->.
      iDestruct (token_agree with "HstB Hst") as %->.
      iApply (mu_step_model _ _ _ _ ∅ ∅ _ ((stA, (BReceiving (1+n))) : stenning_model) with "Hmod [Hf] [Hfr //]").
      { simpl. replace (Send _) with (Send (mBA ((1 + n) - 1) m))%Z. constructor. f_equal.
        rewrite /mBA //=. simplify_eq. do 3 f_equal; lia. }
      { set_solver. }
      { set_solver. }
      { rewrite fmap_empty map_union_empty. done. }
      iIntros "Hmod Hf Hfr".
      iMod (token_update with "[$HstB $Hst]") as "[HstB Hst]".
      iMod ("Hclose" with "[Hfr Hmod HstA HstB Hcci Hcsi]").
      { iNext. rewrite /retinv. iFrame. iExists _, _. iFrame. cbn.
        replace (1 + n - 1)%Z with n. iFrame. iPureIntro. naive_solver. }
      rewrite map_union_empty /usr_fl /=. iModIntro. iApply wp_value'. do 2 wp_pure _.

      (* Guarantee that message is fresh *)
      destruct (decide (mAB n' msg_m ∈ R)); last first.
      { iDestruct ("Hnew" with "[//]") as (???) "[Hcc [Hcs' HΦ']]".
        iDestruct (lmapsto_agree with "Hcs Hcs'") as %Hcseq. simplify_eq.
        apply prod_ser_str_inv in H1 as [H2 H3].
        apply StringOfZ_inv in H2.
        apply StringOfZ_inv in H3.
        simplify_eq.
        lia. } 

      iApply ("IH" with "[] [Hst] [Hcs] [$HΦ] [$Hsh] [] [$HRT] [] [] [$Hf]")=>//.
      { iPureIntro; lia. }
      { iPureIntro.
        simplify_eq.
        replace ({|
         m_sender := saB;
         m_destination := saA;
         m_body := prod_ser_str (int_ser_str x1) (int_ser_str x2)
       |}) with (mBA x1 x2); last first.
        { done. }
        simplify_eq.
        replace ({[mAB n' msg_m]} ∪ R) with R by set_solver.
        by apply server_RT_garbage_4.
      }
      { iPureIntro. intro Hn'. simplify_eq. apply elem_of_union. right. by apply Hin'. }
  Qed.

  Definition pre_example : Z → iProp Σ := λ x, ⌜Z.even x⌝%I.
  Definition post_example : Z → iProp Σ := λ x, ⌜Z.even x⌝%I.

  Definition test_even : val :=
    λ: "v", if: is_even "v" then #() else assert: #false.

  Definition client_example saA saB : val :=
    λ: <>,
      let: "f" := new_gen #() in
      client saA saB "f" test_even.

  Lemma even_rem_0 x : Z.even x → x `rem` 2 = 0.
  Proof. Admitted.

  Lemma even_double_even x : Z.even x → Z.even (x * 2).
  Proof. Admitted.

  Lemma wp_client_example tid (f : nat) (Hf: f > 110) :
    {{{ inv Ns retinv ∗ counter_inv ∗ is_node ipA ∗
        saA ⤇ client_si pre_example ∗ saB ⤇ server_si post_example ∗
          own stenning_A_name (◯E (ASending 0)) ∗ saA ↦c{1/2} 0%Z ∗ saA ↦c{1/4} 0%Z ∗ saB ↦c{1/4} (-1)%Z ∗
          (ipA, tid) ↦M {[ Arole := f ]} ∗ saA ⤳ (∅, ∅) ∗
          free_ports (ip_of_address saA) {[port_of_address saA]} }}}
      (mkExpr (ip_of_address saA) (client_example saA saB #())) @ (ipA, tid); ⊤
    {{{ v, RET v; (ipA, tid) ↦M ∅  }}}.
  Proof.
    iIntros (Φ')"(#Hinv&#Hcinv&#Hin&#HsA&#HsB&Hst&Hcc&Hccm&Hcs&Hf&HRT&Hfp) HΦ".
    wp_pures. rewrite /client_example.
    wp_pures.
    wp_bind (new_gen _).
    iApply (new_gen_spec with "[$]"); [lia|].
    iIntros "!>" (w) "[Hgen Hf]".
    wp_pures.
    iApply (wp_client with "[] [$]"); [lia|simpl;lia| |done].
    iExists 5. iSplit; [iPureIntro;simpl;lia|].
    iIntros (fl v Hfl) "!>".
    iIntros (Φ) "[Hfl Hpre] HΦ".
    iDestruct "Hpre" as (x ->) "%Heven".
    wp_lam. 
    wp_pures.
    wp_lam. wp_pures.
    wp_pures.
    case_bool_decide; last first.
    { by rewrite even_rem_0 in H0. }
    wp_pures.
    iApply wp_value. by iApply "HΦ".
  Qed.
    
  Definition server_example saA saB :=
    server saA saB double_if_even.

  Lemma wp_server_example tid (f : nat) (Hf: f > 100) :
    {{{ inv Ns retinv ∗ counter_inv ∗ is_node ipB ∗ saA ⤇ client_si post_example ∗ saB ⤇ server_si pre_example ∗
          own stenning_B_name (◯E (BReceiving 0)) ∗ saB ↦c{1/2} (-1)%Z ∗
          (ipB, tid) ↦M {[ Brole := f ]} ∗ saB ⤳ (∅, ∅) ∗
          free_ports (ip_of_address saB) {[port_of_address saB]} }}}
      (mkExpr (ip_of_address saB) (server_example saA saB)) @ (ipB, tid); ⊤
    {{{ v, RET v; (ipB, tid) ↦M ∅ }}}.
  Proof.
     iIntros (Φ') "(#Hinv&#Hcinv&#Hin&#HsA&#HsB&Hst&Hcs&Hf&HRT&Hfp) HΦ".
    wp_pures.
    rewrite /server_example.
    iApply (wp_server with "[] [$]"); [lia| |done].
    iExists 6. iSplit; [iPureIntro; simpl; lia|].
    iIntros (fl x Hfl Φ) "!> [Hfl %Heven] HΦ".
    wp_lam.
    wp_pures.
    wp_lam.
    wp_pures.
    case_bool_decide; last first.
    { by rewrite even_rem_0 in H0. }
    wp_pures.
    iApply wp_value. iApply "HΦ".
    iFrame.
    iPureIntro. by apply even_double_even.
  Qed.

End with_Σ.
