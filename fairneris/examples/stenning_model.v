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

Definition stenning_get_n (st : stenning_state) : Z * Z :=
  match st with
  | (ASending n, BSending m) => (n, m)
  | (ASending n, BReceiving m) => (n, m)
  | (AReceiving n, BSending m) => (n, m)
  | (AReceiving n, BReceiving m) => (n, m)
  end.

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

Definition saA : socket_address := SocketAddressInet "0.0.0.0" 80.
Definition saB : socket_address := SocketAddressInet "0.0.0.1" 80.
Definition mAB (n : Z) : message := mkMessage saA saB (StringOfZ n).
Definition mBA (n : Z) : message := mkMessage saB saA (StringOfZ n).


(* Maybe split into the parallel composition *)

Definition good_message (sender_is_A : bool) (n : Z) (msg : option message) :=
  ∃ msg', msg = Some msg' ∧
            ZOfString (m_body msg') = Some n ∧
            if sender_is_A
            then m_sender msg' = saA ∧ m_destination msg' = saB
            else m_sender msg' = saB ∧ m_destination msg' = saA.

Global Instance good_message_decidable b n omsg : Decision (good_message b n omsg).
Proof. apply make_decision. Qed.

Global Instance wrong_message_decidable omsg :
  Decision (omsg = None ∨ ∃ msg : message, omsg = Some msg ∧ m_sender msg ≠ saA).
Proof. apply make_decision. Qed.

Inductive stenning_trans : stenning_state → stenning_role * option aneris_action → stenning_state → Prop :=
| A_Send n stB :
  stenning_trans (ASending n, stB)
                 (Arole, Some $ Send $ mAB n)
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
| B_Send stA n :
  stenning_trans (stA, BSending n)
                 (Brole, Some $ Send (mBA (n-1)))
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
            usr_fl _ := 50;
          |}).
Defined.
