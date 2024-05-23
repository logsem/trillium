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
| ASending (n:nat)
| AReceiving (n:nat).

Inductive stenning_B_state :=
| BSending (n:nat)
| BReceiving (n:nat).

Definition stenning_state : Set := stenning_A_state * stenning_B_state.

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
Definition mAB (n : nat) : message := mkMessage saA saB (StringOfZ n).
Definition mBA (n : nat) : message := mkMessage saB saA (StringOfZ n).


(* Maybe split into the parallel composition *)

Inductive stenning_trans : stenning_state → stenning_role * option aneris_action → stenning_state → Prop :=
| A_Send n stB :
  0 < n →
  stenning_trans (ASending n, stB)
                 (Arole, Some $ Send $ mAB n)
                 (AReceiving n, stB)
| A_RecvFailEmpty n stB :
  stenning_trans (AReceiving n, stB)
                 (Arole, Some $ Recv saA None)
                 (ASending n, stB)
| A_RecvFailWrong n stB msg :
  msg ≠ mBA n →
  stenning_trans (AReceiving n, stB)
                 (Arole, Some $ Recv saA (Some msg))
                 (AReceiving n, stB)
| A_RecvSucc n stB :
  stenning_trans (AReceiving n, stB)
                 (Arole, Some $ Recv saA (Some $ mBA n))
                 (ASending (1+n), stB)
| B_Send stA n :
  stenning_trans (stA, BSending n)
                 (Brole, Some $ Send (mBA (n-1)))
                 (stA, BReceiving n)
| B_RecvFailEmpty stA n :
  stenning_trans (stA, BReceiving n)
                 (Brole, Some $ Recv saB None)
                 (stA, BSending n)
| B_RecvFailWrong stA n msg:
  msg ≠ mAB n →
  stenning_trans (stA, BReceiving n)
                 (Brole, Some $ Recv saB (Some msg))
                 (stA, BReceiving n)
| B_RecvSucc stA n :
  stenning_trans (stA, BReceiving n)
                 (Brole, Some $ Recv saB (Some $ mAB n))
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
