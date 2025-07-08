From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From Paco Require Import paco1 paco2 pacotac.
From fairneris Require Export trace_utils fairness env_model network_model.
From fairneris.aneris_lang Require Import ast network lang aneris_lang.
From fairneris Require Export trace_utils ltl_lite strings.
(* TODO: We need this as adequacy.v contains [usr_fair]. We should move it somewhere else *)
From fairneris.aneris_lang Require Import adequacy.

Import derived_laws_later.bi.

Lemma prefix_trans {A} (l1 l2 l3 : list A) :
  l1 `prefix_of` l2 → l2 `prefix_of` l3 → l1 `prefix_of` l3.
Proof. intros [l1' ->] [l2' ->]. by do 2 apply prefix_app_r. Qed.

Lemma suffix_trans {A} (l1 l2 l3 : list A) :
  l1 `suffix_of` l2 → l2 `suffix_of` l3 → l1 `suffix_of` l3.
Proof. intros [l1' ->] [l2' ->]. by do 2 apply suffix_app_r. Qed.

(** The stenning model states *)
Inductive stenning_A_state :=
| ASending (n:Z)
| AReceiving (n:Z).

Inductive stenning_B_state :=
| BSending (n:Z)
| BReceiving (n:Z).

Definition stenning_state : Set := stenning_A_state * stenning_B_state.

Definition stenning_get_n_A (st : stenning_A_state) : Z :=
  match st with
  | ASending n => n
  | AReceiving n => n
  end.
Definition stenning_get_n_B (st : stenning_B_state) : Z :=
  match st with
  | BSending n => n
  | BReceiving n => n
  end.
Definition stenning_get_n (st : stenning_state) : Z * Z :=
  (stenning_get_n_A st.1, stenning_get_n_B st.2).

#[global] Instance stenning_state_eqdec : EqDecision stenning_state.
Proof. intros ??. apply make_decision. Qed.
#[global] Instance stenning_state_inhabited : Inhabited stenning_state.
Proof. exact (populate (ASending 0, BSending 0)). Qed.

Inductive stenning_role := Arole | Brole.

#[global] Instance stenning_node_role_eqdec : EqDecision stenning_role.
Proof. intros ??. apply make_decision. Qed.
#[global] Instance stenning_node_role_inhabited : Inhabited stenning_role.
Proof. exact (populate (Arole)). Qed.
#[global] Instance stenning_node_role_countable : Countable stenning_role.
Proof.
  refine ({|
             encode s := match s with
                         | Arole => 1
                         | Brole => 2
                         end;
             decode n := match n with
                         | 1 => Some Arole
                         | 2 => Some Brole
                         | _ => None
                         end;
         |})%positive.
  by intros [|].
Qed.

From fairneris.aneris_lang.lib Require Import serialization_proof.

Definition saA : socket_address := SocketAddressInet "0.0.0.0" 80.
Definition saB : socket_address := SocketAddressInet "0.0.0.1" 80.
Definition mAB (n m : Z) : message :=
  mkMessage saA saB (prod_ser_str (StringOfZ n) (StringOfZ m)).
Definition mBA (n m : Z) : message :=
  mkMessage saB saA (prod_ser_str (StringOfZ n) (StringOfZ m)).

Definition good_message (sender_is_A : bool) (n : Z) (msg : option message) :=
  ∃ m msg', msg = Some msg' ∧
          if sender_is_A then msg' = mAB n m else msg' = mBA n m.

(* TOOD: Move *)
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

Lemma good_message_inj b b' n n' msg :
  good_message b n msg → good_message b' n' msg → n = n'.
Proof.
  rewrite /good_message. intros H1 H2.
  destruct H1 as (m1&msg1&Hmsg1&H1).
  destruct H2 as (m2&msg2&Hmsg2&H2).
  destruct b, b'; simplify_eq.
  - apply prod_ser_str_inv in Hmsg2 as [H1 _]. by apply StringOfZ_inv in H1.
  - apply prod_ser_str_inv in Hmsg2 as [H1 _]. by apply StringOfZ_inv in H1.
Qed.

Global Instance good_message_decidable b n omsg : Decision (good_message b n omsg).
Proof. apply make_decision. Qed.

Global Instance wrong_message_decidable omsg :
  Decision (omsg = None ∨ ∃ msg : message, omsg = Some msg ∧ m_sender msg ≠ saA).
Proof. apply make_decision. Qed.

Inductive stenning_trans : stenning_state → stenning_role * option aneris_action → stenning_state → Prop :=
| A_Send n m stB :
  stenning_trans (ASending n, stB)
                 (Arole, Some $ Send $ mAB n m)
                 (AReceiving n, stB)
| A_RecvFail n stB msg :
  ¬ good_message false n msg →
  stenning_trans (AReceiving n, stB)
                 (Arole, Some $ Recv saA msg)
                 (ASending n, stB)
| A_RecvSucc n stB msg :
  good_message false n (Some msg) →
  stenning_trans (AReceiving n, stB)
                 (Arole, Some $ Recv saA (Some msg))
                 (ASending (1+n), stB)
| B_Send stA n m :
  stenning_trans (stA, BSending n)
                 (Brole, Some $ Send (mBA (n-1) m))
                 (stA, BReceiving n)
| B_RecvFailEmpty stA n omsg:
  omsg = None ∨ (∃ msg, omsg = Some msg ∧ m_sender msg ≠ saA) →
  stenning_trans (stA, BReceiving n)
                 (Brole, Some $ Recv saB omsg)
                 (stA, BReceiving n)
| B_RecvFailWrong stA n msg:
  m_sender msg = saA →
  ¬ good_message true n (Some msg) →
  stenning_trans (stA, BReceiving n)
                 (Brole, Some $ Recv saB (Some msg))
                 (stA, BSending n)
| B_RecvSucc stA n msg :
  good_message true n (Some msg) →
  stenning_trans (stA, BReceiving n)
                 (Brole, Some $ Recv saB (Some msg))
                 (stA, BSending (1+n))
.


Definition stenning_enum_next_A (n : Z) : list stenning_A_state :=
  [AReceiving n; ASending n; ASending (1 + n)].

Lemma stenning_enum_next_A_spec n stA stA' stB stB' ℓ :
  stenning_trans (stA, stB) ℓ (stA', stB') →
  stenning_get_n_A stA = n →
  stA' ∈ stenning_enum_next_A n.
Proof.
  intros Htr Hgn.
  have : stA ∈ stenning_enum_next_A n.
  { destruct stA; rewrite !elem_of_cons; naive_solver. }
  inversion Htr; simplify_eq =>//; intros _; rewrite !elem_of_cons; naive_solver.
Qed.


Definition stenning_enum_next_B (n : Z) : list stenning_B_state :=
  [BReceiving n; BSending n; BSending (1 + n)].

Lemma stenning_enum_next_B_spec n stA stA' stB stB' ℓ :
  stenning_trans (stA, stB) ℓ (stA', stB') →
  stenning_get_n_B stB = n →
  stB' ∈ stenning_enum_next_B n.
Proof.
  intros Htr Hgn.
  have : stB ∈ stenning_enum_next_B n.
  { destruct stB; rewrite !elem_of_cons; naive_solver. }
  inversion Htr; simplify_eq =>//; intros _; rewrite !elem_of_cons; naive_solver.
Qed.


Definition stenning_enum_next (st : stenning_state) : list (stenning_state * stenning_role) :=
  let '(nA, nB) := stenning_get_n st in
  stA ← stenning_enum_next_A nA;
  stB ← stenning_enum_next_B nB;
  ρ ← [Arole; Brole];
  mret ((stA, stB), ρ).

Lemma stenning_enum_next_spec st st' ρ act :
  stenning_trans st (ρ, act) st' →
  (st', ρ) ∈ stenning_enum_next st.
Proof.
  intros Htr.
  destruct st as [stA stB].
  destruct st' as [stA' stB'].
  apply elem_of_list_bind.
  exists stA'. constructor; last first.
  { eapply stenning_enum_next_A_spec =>//=. }
  apply elem_of_list_bind.
  exists stB'. constructor; last first.
  { eapply stenning_enum_next_B_spec =>//=. }
  apply elem_of_list_bind.
  exists ρ. constructor; last first.
  { destruct ρ; rewrite !elem_of_cons; naive_solver. }
  by apply elem_of_list_ret.
Qed.

Definition stenning_live_roles (s : stenning_state) : gset stenning_role :=
  {[Arole; Brole]}.

Definition stenning_role_enabled_model (ρ : stenning_role) (s : stenning_state) : Prop :=
  ρ ∈ stenning_live_roles s.

Lemma stenning_live_spec_holds s ρ α s' :
  stenning_trans s (ρ,α) s' → ρ ∈ stenning_live_roles s.
Proof. inversion 1; set_solver. Qed.

Definition stenning_lts : Lts (stenning_role * option aneris_action) :=
  {|
            lts_state := stenning_state;
            lts_trans := stenning_trans;
  |}.

Definition stenning_model : UserModel aneris_lang.
Proof.
  refine({|
            usr_role := stenning_role;
            usr_lts := stenning_lts;
            usr_live_roles := stenning_live_roles;
            usr_live_spec := stenning_live_spec_holds;
            usr_fl _ := 200;
          |}).
Defined.


Definition initial_model_state : stenning_state := (ASending 0, BReceiving 0).
Definition safety_inv := λ st, let (n, m) := stenning_get_n st in (n = m ∨ m = n + 1)%Z.

Require Import Coq.Logic.Classical.

Notation stenning_label := (stenning_role * option (action aneris_lang)) % type.
Notation stenning_trace := (lts_trace stenning_model).

Definition A_at (n : Z) : ltl_pred stenning_model stenning_label := ↓ λ s _, (stenning_get_n s).1 = n.
Definition B_at (n : Z) : ltl_pred stenning_model (lts_label stenning_model) := ↓ λ s _, (stenning_get_n s).2 = n.
Definition AB_at (n m : Z) : ltl_pred stenning_model stenning_label := A_at n ⋒ B_at m.

Lemma A_at_iff (tr : stenning_trace) (n m : Z):
  (tr ⊩ A_at n) ↔ stenning_get_n_A (trfirst tr).1 = n.
Proof. rewrite trace_nowI //. Qed.
Lemma B_at_iff (tr : stenning_trace) (n m : Z):
  (tr ⊩ B_at n) ↔ stenning_get_n_B (trfirst tr).2 = n.
Proof. rewrite trace_nowI //. Qed.

Lemma AB_at_iff (tr : stenning_trace) (n m : Z):
  (tr ⊩ AB_at n m) ↔ stenning_get_n (trfirst tr) = (n, m).
Proof. rewrite /AB_at trace_andI !trace_nowI /stenning_get_n. naive_solver. Qed.

Lemma AB_at_iff' (tr : stenning_trace) (n m : Z):
  (AB_at n m tr) ↔ stenning_get_n (trfirst tr) = (n, m).
Proof. have := AB_at_iff tr n m. naive_solver. Qed.

Definition msg (n : Z) : message → Prop := fun m => ∃ j, m = mAB n j.
Definition ack (n : Z) : message → Prop := fun m => ∃ j, m = mBA n j.

Lemma msg_sa n : msg_pred_dest (msg n) saB.
Proof. rewrite /msg_pred_dest /msg. naive_solver. Qed.

Lemma ack_sa n : msg_pred_dest (ack n) saA.
Proof. rewrite /msg_pred_dest /ack. naive_solver. Qed.

Lemma always_n_n_or_eventually_n_Sn (utr : stenning_trace) n :
  (utr ⊩ usr_trace_valid) → (utr ⊩ □ ↓ λ s _, safety_inv s) → (utr ⊩ AB_at n n) → (utr ⊩ (◊ AB_at n (1+n)) ⋓ □ AB_at n n).
Proof.
  intros Hval Hsafe Hnn.
  rewrite trace_orI.
  destruct (classic (utr ⊩ ◊ AB_at n (1 + n))) as [Hev | Hal].
  { left. exact Hev. }
  right. rewrite -trace_notI -trace_always_not_not_eventually in Hal.
  have Ha: (utr ⊩ □ usr_trans_valid aneris_lang ⋒ (□ (⫬ AB_at n (1 + n))) ⋒ □ (↓ λ s _, safety_inv s)).
  { rewrite !trace_always_and. split_and!.
    - naive_solver.
    - rewrite -trace_always_idemp. naive_solver.
    - rewrite -trace_always_idemp. naive_solver. }
  eapply trace_always_next. exact Ha. exact Hnn.
  intros tr Hst [Hval' [Hnr Hinv]%trace_andI]%trace_andI Hnf.
  apply trace_next_elim_inv in Hnf as (s&l&tr'&->&_).
  apply trace_next_intro.
  destruct (trfirst tr') as [a b] eqn:Heq.
  rewrite !ltl_sat_def in Hnr Hval' Hst *.
  rewrite AB_at_iff' /stenning_get_n /stenning_get_n_A /stenning_get_n_B /= in Hst.
  rewrite AB_at_iff' /stenning_get_n /stenning_get_n_A /stenning_get_n_B /=.
  apply trace_always_cons, trace_always_elim in Hinv.
  apply trace_always_cons, trace_always_elim in Hnr.
  rewrite trace_nowI /safety_inv /stenning_get_n /= in Hinv.
  rewrite trace_notI AB_at_iff in Hnr.
  rewrite /trace_now /trace_label /pred_at /usr_trans_valid /=.
  inversion Hval'; simplify_eq=>//; try naive_solver.
  - simpl in *.
    rewrite -> Heq in *.
    simpl in *.
    destruct stB; simplify_eq; simpl in Hinv; lia.
  - simpl in *.
    rewrite -> Heq in *.
    simpl in *.
    destruct stA; simplify_eq; simpl in Hnr.
Qed.

Lemma always_n_Sn_or_eventually_Sn_Sn (utr : stenning_trace) n :
  (utr ⊩ usr_trace_valid) → (utr ⊩ □ ↓ λ s _, safety_inv s) → (utr ⊩ AB_at n (1 + n)) → (utr ⊩ (◊ AB_at (1+n) (1+n)) ⋓ □ AB_at n (1+n)).
Proof.
  intros Hval Hsafe Hnn.
  rewrite trace_orI.
  destruct (classic (utr ⊩ ◊ AB_at (1 + n) (1 + n))) as [Hev | Hal].
  { left. exact Hev. }
  right. rewrite -trace_notI -trace_always_not_not_eventually in Hal.
  have Ha: (utr ⊩ □ usr_trans_valid aneris_lang ⋒ (□ (⫬ AB_at (1 + n) (1 + n))) ⋒ □ (↓ λ s _, safety_inv s)).
  { rewrite !trace_always_and. split_and!.
    - naive_solver.
    - rewrite -trace_always_idemp. naive_solver.
    - rewrite -trace_always_idemp. naive_solver. }
  eapply trace_always_next. exact Ha. exact Hnn.
  intros tr Hst [Hval' [Hnr Hinv]%trace_andI]%trace_andI Hnf.
  apply trace_next_elim_inv in Hnf as (s&l&tr'&->&_).
  apply trace_next_intro.
  destruct (trfirst tr') as [a b] eqn:Heq.
  rewrite !ltl_sat_def in Hnr Hval' Hst *.
  rewrite AB_at_iff' /stenning_get_n /stenning_get_n_A /stenning_get_n_B /= in Hst.
  rewrite AB_at_iff' /stenning_get_n /stenning_get_n_A /stenning_get_n_B /=.
  apply trace_always_cons, trace_always_elim in Hinv.
  apply trace_always_cons, trace_always_elim in Hnr.
  rewrite trace_nowI /safety_inv /stenning_get_n /= in Hinv.
  rewrite trace_notI AB_at_iff in Hnr.
  rewrite /trace_now /trace_label /pred_at /usr_trans_valid /=.
  inversion Hval'; simplify_eq=>//; try naive_solver.
  - simpl in *.
    rewrite -> Heq in *.
    simpl in *.
    destruct stB; simplify_eq; simpl in Hnr; split; lia.
  - simpl in *.
    rewrite -> Heq in *.
    simpl in *.
    destruct stB; simplify_eq; simpl in Hnr; split; lia.
  - simpl in *.
    rewrite -> Heq in *.
    simpl in *.
    destruct stB; simplify_eq; simpl in Hnr; split; lia.
  - simpl in *.
    rewrite -> Heq in *.
    simpl in *.
    destruct stA; simplify_eq; simpl in Hinv; lia.
Qed.

Lemma A_eventually_sends (utr : stenning_trace) (n : Z) :
  (utr ⊩ usr_trace_valid) → (utr ⊩ usr_fair) →
  (utr ⊩ A_at n) → (utr ⊩ ◊ ℓ↓ usr_send_pred_filter (msg n)).
Proof.
Admitted.

Lemma A_always_eventually_sends (utr : stenning_trace) (n : Z) :
  (utr ⊩ usr_trace_valid) → (utr ⊩ usr_fair) →
  (utr ⊩ □ A_at n) → (utr ⊩ □ ◊ ℓ↓ usr_send_pred_filter (msg n)).
Proof.
  (* Can we use the above lemma? *)
Admitted.

Lemma A_always_eventually_receives (utr : stenning_trace) :
  (utr ⊩ usr_trace_valid) → (utr ⊩ usr_fair) →
  (utr ⊩ □ ◊ ℓ↓ usr_any_recv_filter saA).
Proof.
Admitted.

Lemma B_always_eventually_receives (utr : stenning_trace) :
  (utr ⊩ usr_trace_valid) → (utr ⊩ usr_fair) →
  (utr ⊩ □ ◊ ℓ↓ usr_any_recv_filter saB).
Proof.
Admitted.


Lemma B_eventually_receives_n (utr : stenning_trace) n :
  (utr ⊩ usr_trace_valid) → (utr ⊩ usr_fair) → (utr ⊩ □ A_at n) →
  (utr ⊩ ◊ ℓ↓ usr_recv_pred_filter (msg n)).
Proof.
  intros Hval Hfair HA_at.
  destruct (Hfair) as [Hnet Hsched].
  unfold usr_network_fair_send_receive in Hnet.
  specialize (Hnet (msg n) saB (msg_sa n)).
  unfold usr_network_fair_send_receive_of in Hnet.
  apply trace_always_elim in Hnet.
  rewrite !trace_impliesI in Hnet.
  apply Hnet.
  - apply A_always_eventually_sends=>//.
  - eapply B_always_eventually_receives=>//.
Qed.

Lemma B_eventually_receives_n' (utr : stenning_trace) n :
  (utr ⊩ usr_trace_valid) → (utr ⊩ usr_fair) → (utr ⊩ □ A_at n) → (utr ⊩ □ B_at n) → False.
Proof.
  intros Hval Hfair HA HB.
  have Ha := B_eventually_receives_n utr _ Hval Hfair HA.
  rewrite trace_eventuallyI in Ha.
  destruct Ha as (tr1&Hsuff&Htrans).
  rewrite trace_alwaysI_alt in HB.
  specialize (HB tr1 Hsuff).
  rewrite trace_alwaysI in Hval.
  specialize (Hval tr1 Hsuff).
  have HB' := HB.
  apply trace_always_elim in HB'.
  destruct tr1 as [s|s ℓ tr2]; first naive_solver.
  rewrite trace_alwaysI in HB.
  specialize (HB tr2 (trace_suffix_of_cons_r' _ _ _)).
  admit. (* should follow easily from the transition. *)
Admitted.

Lemma B_always_eventually_receives_n (utr : stenning_trace) n :
  (utr ⊩ usr_trace_valid) → (utr ⊩ usr_fair) → (utr ⊩ □ A_at n) →
  (utr ⊩ □ ◊ ℓ↓ usr_recv_pred_filter (msg n)).
Proof.
  intros Hval Hfair Hn.
  assert (utr ⊩ □ (usr_trace_valid ⋒ usr_fair ⋒ □ A_at n)) as H.
  { rewrite !trace_always_and. split_and!.
    - rewrite -trace_always_idemp. naive_solver.
    - rewrite -mtrace_fair_always //.
    - rewrite -trace_always_idemp. naive_solver. }
  eapply trace_always_mono; last exact H.
  intros tr.
  rewrite trace_impliesI !trace_andI.
  have Hccl := B_eventually_receives_n tr n.
  naive_solver.
Qed.

Lemma B_eventually_sends_n (utr : stenning_trace) n :
  (utr ⊩ usr_trace_valid) → (utr ⊩ usr_fair) → (utr ⊩ B_at (1 + n)) →
  (utr ⊩ ℓ↓ usr_recv_pred_filter (msg n)) →
  (utr ⊩ ◊ ℓ↓ usr_send_pred_filter (ack n)).
Proof. Admitted.

Lemma B_always_eventually_sends_n (utr : stenning_trace) n :
  (utr ⊩ usr_trace_valid) → (utr ⊩ usr_fair) → (utr ⊩ □ A_at n) → (utr ⊩ □ B_at (1 + n)) →
  (utr ⊩ □ ◊ ℓ↓ usr_send_pred_filter (ack n)).
Proof.
  intros Hval Hfair HA HB.
  have Has := B_always_eventually_receives_n _ _ Hval Hfair HA.
  assert (utr ⊩ □ (usr_trace_valid ⋒ usr_fair ⋒ (□ B_at (1 + n)) ⋒ (◊ ℓ↓ usr_recv_pred_filter (msg n)))) as H.
  { rewrite !trace_always_and. split_and!.
    - rewrite -trace_always_idemp. naive_solver.
    - rewrite -mtrace_fair_always //.
    - rewrite -trace_always_idemp. naive_solver.
    - naive_solver. }
  eapply trace_always_mono; last exact H.
  intros tr.
  rewrite trace_impliesI !trace_andI.
  intros (Hval1&Hfair1&HB1&Htr).
  rewrite -trace_eventually_idemp trace_eventuallyI.
  rewrite trace_eventuallyI in Htr.
  destruct Htr as (tr1&Hsuff1&Htr1).
  exists tr1. split; first naive_solver.
  apply B_eventually_sends_n=>//.
  - rewrite trace_always_idemp trace_alwaysI in Hval1. naive_solver.
  - rewrite mtrace_fair_always trace_alwaysI in Hfair1. naive_solver.
  - rewrite trace_alwaysI in HB1. naive_solver.
Qed.

Lemma A_eventually_receives_n (utr : stenning_trace) n :
  (utr ⊩ usr_trace_valid) → (utr ⊩ usr_fair) → (utr ⊩ □ A_at n) → (utr ⊩ □ B_at (1 + n)) →
  (utr ⊩ ◊ ℓ↓ usr_recv_pred_filter (ack n)).
Proof.
  intros Hval Hfair HA_at HB_at.
  destruct (Hfair) as [Hnet Hsched].
  unfold usr_network_fair_send_receive in Hnet.
  specialize (Hnet (ack n) saA (ack_sa n)).
  unfold usr_network_fair_send_receive_of in Hnet.
  apply trace_always_elim in Hnet.
  rewrite !trace_impliesI in Hnet.
  apply Hnet.
  - apply B_always_eventually_sends_n=>//.
  - eapply A_always_eventually_receives=>//.
Qed.

Lemma A_eventually_receives_n' (utr : stenning_trace) n :
  (utr ⊩ usr_trace_valid) → (utr ⊩ usr_fair) → (utr ⊩ □ A_at n) → (utr ⊩ □ B_at (1 + n)) → False.
Proof.
  intros Hval Hfair HA HB.
  have Ha := A_eventually_receives_n utr _ Hval Hfair HA HB.
  rewrite trace_eventuallyI in Ha.
  destruct Ha as (tr1&Hsuff&Htrans).
  rewrite trace_alwaysI_alt in HA.
  specialize (HA tr1 Hsuff).
  rewrite trace_alwaysI_alt in Hval.
  specialize (Hval tr1 Hsuff).
  destruct tr1 as [|s ℓ tr2]; first naive_solver.
  rewrite trace_alwaysI in HA.
  specialize (HA tr2 (trace_suffix_of_cons_r' _ _ _)).
  admit. (* should follow easily from the transition. *)
Admitted.

Lemma eventually_increment (utr : stenning_trace) n :
  (utr ⊩ usr_trace_valid) → (utr ⊩ usr_fair) → (utr ⊩ □ ↓ λ s _, safety_inv s) → (utr ⊩ AB_at n n) →
  (utr ⊩ ◊ AB_at (1+n) (1+n)).
Proof.
  intros Hval Hfair Hinv HAB.

  have Hmid := always_n_n_or_eventually_n_Sn utr n Hval Hinv HAB.
  rewrite trace_orI in Hmid.
  destruct Hmid as [Hmid | Hmid]; last first.
  { exfalso. rewrite /AB_at trace_always_and in Hmid. eapply (B_eventually_receives_n' utr n); naive_solver. }

  rewrite trace_eventuallyI in Hmid.
  destruct Hmid as (tr'&Htr'&HAB').

  rewrite trace_alwaysI_alt in Hinv.
  rewrite trace_alwaysI_alt in Hval.
  rewrite mtrace_fair_always trace_alwaysI in Hfair.

  specialize (Hinv _ Htr').
  specialize (Hval _ Htr').
  specialize (Hfair _ Htr').

  have Hend := always_n_Sn_or_eventually_Sn_Sn tr' n Hval Hinv HAB'.
  rewrite trace_orI in Hend.
  destruct Hend as [Hend | Hend]; last first.
  { exfalso. rewrite /AB_at trace_always_and in Hend. eapply (A_eventually_receives_n' tr' n); naive_solver. }

  rewrite trace_eventuallyI_alt. naive_solver.
Qed.

Lemma eventually_increment' (utr : stenning_trace) n :
  (utr ⊩ usr_trace_valid) → (utr ⊩ usr_fair) → (utr ⊩ □ ↓ λ s _, safety_inv s) → (utr ⊩ ◊ AB_at n n) →
  (utr ⊩ ◊ AB_at (1+n) (1+n)).
Proof.
  intros Hval Hfair Hinv Hmid.
  rewrite trace_eventuallyI in Hmid.
  destruct Hmid as (tr'&Htr'&HAB').

  rewrite trace_alwaysI_alt in Hinv.
  rewrite trace_alwaysI_alt in Hval.
  rewrite mtrace_fair_always trace_alwaysI in Hfair.

  rewrite trace_eventuallyI_alt. exists tr'. split; first by apply Htr'.
  apply eventually_increment; naive_solver.
Qed.

Lemma eventually_n_n (utr : stenning_trace) (n : nat) :
  (utr ⊩ usr_trace_valid) → (utr ⊩ usr_fair) → (utr ⊩ □ ↓ λ s _, safety_inv s) → (utr ⊩ AB_at 0 0) →
  (utr ⊩ ◊ AB_at n n).
Proof.
  generalize utr. induction n as [ |n IH].
  - intros. by apply trace_eventually_intro.
  - clear utr. intros utr Hval Hfair Hinv H0.
    specialize (IH _ Hval Hfair Hinv H0).
    have -> : (Z.of_nat (S n)) = (1%Z + Z.of_nat n) % Z by lia.
    apply eventually_increment' in IH; naive_solver.
Qed.

Theorem stenning_fair_live (utr : stenning_trace) (i : Z) :
  (0 ≤ i)%Z →
  trfirst utr = initial_model_state →
  (utr ⊩ usr_trace_valid) →
  (utr ⊩ usr_fair) →
  (utr ⊩ □ ↓ λ s _, safety_inv s) →
  (utr ⊩ ◊ ℓ↓ λ '(_, α), ∃ α', α = Some α' ∧ ∃ j, α' = Send (mAB i j)).
Proof.
  intros Hi Hinit Hval Hfair Hinv.

  pose i' := (Z.to_nat i : nat).
  have Hii: (utr ⊩ ◊ AB_at i' i').
  { apply eventually_n_n; try naive_solver. rewrite AB_at_iff Hinit //=. }

  rewrite /i' in Hii.
  have Heq : (Z.of_nat (Z.to_nat i)) = i by lia.
  rewrite Heq in Hii.

  rewrite trace_eventuallyI in Hii.
  destruct Hii as (tr'&Htr'&Hii).
  rewrite trace_andI in Hii.
  destruct Hii as [Hii _].
  apply A_eventually_sends in Hii.
  + rewrite /usr_send_pred_filter /msg in Hii.
    rewrite trace_eventuallyI_alt. exists tr'. split; first naive_solver.
    eapply trace_eventually_mono; last exact Hii.
    intros tr.
    apply trace_label_mono_strong.
    naive_solver.
  + rewrite trace_alwaysI_alt in Hval. naive_solver.
  + rewrite mtrace_fair_always trace_alwaysI in Hfair. naive_solver.
Qed.
