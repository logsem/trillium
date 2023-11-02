From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From Paco Require Import paco1 paco2 pacotac.
From fairneris Require Export trace_utils fairness.
From fairneris.aneris_lang Require Import ast network.

Import derived_laws_later.bi.

Lemma prefix_trans {A} (l1 l2 l3 : list A) :
  l1 `prefix_of` l2 → l2 `prefix_of` l3 → l1 `prefix_of` l3.
Proof. intros [l1' ->] [l2' ->]. by do 2 apply prefix_app_r. Qed.

Lemma suffix_trans {A} (l1 l2 l3 : list A) :
  l1 `suffix_of` l2 → l2 `suffix_of` l3 → l1 `suffix_of` l3.
Proof. intros [l1' ->] [l2' ->]. by do 2 apply suffix_app_r. Qed.

(** The retransmit model states *)
Inductive retransmit_base_state :=
| Start
| Received.

Definition retransmit_state : Set :=
  retransmit_base_state * message_multi_soup * gmap socket_address (list message).

#[global] Instance simple_state_eqdec : EqDecision retransmit_state.
Proof. intros ??. apply make_decision. Qed.
#[global] Instance simple_state_inhabited : Inhabited retransmit_state.
Proof. exact (populate (Start,∅,∅)). Qed.

Inductive retransmit_node_role := Arole | Brole.
(* Inductive retransmit_network_role := *)
(* | Ndup *)
(* | Ndrop *)
(* | Ndeliver. *)
Definition retransmit_network_role : Set := unit.
Definition retransmit_role : Set :=
  retransmit_node_role + retransmit_network_role.

Definition retransmit_node_action : Set := option message.
Definition retransmit_network_action : Set := option message.
Definition retransmit_action : Set :=
  retransmit_node_action + retransmit_network_action.

Definition retransmit_node_label : Set :=
  retransmit_node_role * retransmit_node_action.
Definition retransmit_network_label : Set :=
  retransmit_network_role * retransmit_network_action.
Definition retransmit_label : Set :=
  retransmit_node_label + retransmit_network_label.

Definition label_role (l : retransmit_label) : retransmit_role :=
  sum_map fst fst l.
Definition label_action (l : retransmit_label) : retransmit_action :=
  sum_map snd snd l.

#[global] Instance retransmit_node_role_eqdec : EqDecision retransmit_node_role.
Proof. intros ??. apply make_decision. Qed.
#[global] Instance retransmit_node_role_inhabited : Inhabited retransmit_node_role.
Proof. exact (populate (Arole)). Qed.
#[global] Instance retransmit_node_role_countable : Countable retransmit_node_role.
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

#[global] Instance retransmit_role_eqdec : EqDecision retransmit_role.
Proof. intros ??. apply make_decision. Qed.
#[global] Instance retransmit_role_inhabited : Inhabited retransmit_role.
Proof. exact (populate (inl Arole)). Qed.
#[global] Instance retransmit_role_countable : Countable retransmit_role.
Proof.
  refine ({|
             encode s := match s with
                         | inl Arole => 1
                         | inl Brole => 2
                         | inr () => 3
                         end;
             decode n := match n with
                         | 1 => Some $ inl Arole
                         | 2 => Some $ inl Brole
                         | 3 => Some $ inr ()
                         | _ => None
                         end;
         |})%positive.
  by intros [[]|[]].
Qed.

Definition saA : socket_address := SocketAddressInet "0.0.0.0" 80.
Definition saB : socket_address := SocketAddressInet "0.0.0.1" 80.
Definition mAB : message := mkMessage saA saB "Hello".

Inductive retransmit_trans : retransmit_state → retransmit_label → retransmit_state → Prop :=
| A_Send st ms bs :
  retransmit_trans (st, ms, bs)
                   (inl $ (Arole, Some mAB))
                   (st, ms ⊎ {[+ mAB +]}, bs)
| N_Duplicate st ms bs msg :
  msg ∈ ms →
  retransmit_trans (st, ms, bs)
                   (inr ((),None))
                   (st, ms ⊎ {[+ msg +]}, bs)
| N_Drop st ms bs msg :
  msg ∈ ms →
  retransmit_trans (st, ms, bs)
                   (inr ((), None))
                   (st, ms ∖ {[+ msg +]}, bs)
| N_Deliver st ms ms' bs msg :
  msg ∈ ms →
  bs !!! m_destination msg = ms' →
  retransmit_trans (st, ms, bs)
                   (inr ((), Some msg))
                   (st, ms ∖ {[+ msg +]}, <[m_destination msg := msg::ms']>bs)
| B_RecvFail ms bs :
  bs !!! saB = [] →
  retransmit_trans (Start, ms, bs)
                   (inl $ (Brole, None))
                   (Start, ms, bs)
| B_RecvSucc ms bs msg ms' :
  bs !!! saB = ms'++[msg] →
  retransmit_trans (Start, ms, bs)
                   (inl $ (Brole, None))
                   (Received, ms, <[saB := ms']>bs).

Notation mtrace := (trace retransmit_state retransmit_label).

Definition retransmit_live_roles (s : retransmit_state) : gset retransmit_node_role :=
  {[Arole]} ∪
  (match s.1.1 with Start => {[Brole]} | _ => ∅ end).

(* TODO: This should be generalised, and lifted to multiple roles *)
Definition retransmit_terminating_role (ρ : retransmit_node_role) (tr : mtrace) : Prop :=
  ∃ n, after n tr = None ∨
       pred_at tr n (λ st _, ρ ∉ retransmit_live_roles st).

Definition retransmit_role_enabled_model (ρ : retransmit_node_role) (s : retransmit_state) : Prop :=
  ρ ∈ retransmit_live_roles s.

(* TODO: This is likely not needed. *)
Lemma retransmit_live_spec_holds s ρ α s' :
  retransmit_trans s (inl (ρ,α)) s' → ρ ∈ retransmit_live_roles s.
Proof. inversion 1; set_solver. Qed.

(* Definition retransmit_fair_model : FairModel. *)
(* Proof. *)
(*   refine({| *)
(*             fmstate := retransmit_state; *)
(*             fmrole := retransmit_node_role; *)
(*             fmaction := retransmit_node_action; *)
(*             fmconfig := retransmit_network_label; *)
(*             fmtrans := retransmit_trans; *)
(*             fmfairness := retransmit_network_fair_delivery; *)
(*             live_roles := retransmit_live_roles; *)
(*             fm_live_spec := retransmit_live_spec_holds; *)
(*           |}). *)
(* Defined. *)
