From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From Paco Require Import paco1 paco2 pacotac.
From fairneris Require Export trace_utils fairness env_model.
From fairneris.aneris_lang Require Import ast network lang aneris_lang.
From fairneris Require Export trace_utils ltl_lite strings.

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
