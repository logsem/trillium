From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness action_model utils.

Open Scope nat.

(** * Definition of the model! *)

Inductive YN := Y | No.

#[global] Instance YN_eqdec: EqDecision YN.
Proof. solve_decision. Qed.

#[global] Instance YN_countable: Countable YN.
Proof.
  refine ({|
             encode yn := match yn with Y => 1 | No => 2 end;
             decode p := match p with 1 => Some Y | 2 => Some No | _ => None end;
         |})%positive.
  intros yn. by destruct yn.
Qed.

#[global] Instance YN_inhabited: Inhabited YN.
Proof. exact (populate Y). Qed.

Definition yn_act: Action := coPpick (↑ nroot .@ "yesno"). 

Inductive yntrans: nat*bool -> (Action * option YN) -> nat*bool -> Prop :=
| yes_trans n: (n > 0)%nat -> yntrans (n, true) (yn_act, Some Y) (n, false) (* < *)
| yes_fail n: (n > 1)%nat -> yntrans (n, false) (yn_act, Some Y) (n, false) (* ≤ *)
| no_trans n: yntrans (S n, false) (yn_act, Some No) (n, true) (* < *)
| no_fail n: (n > 0)%nat → yntrans (n, true) (yn_act, Some No) (n, true) (* ≤ *)
.

Definition yn_live_roles nb : gset YN :=
  match nb with
  | (0, _) => ∅
  | (1, false) => {[ No ]}
  | _ => {[ No; Y ]}
  end.

Definition yn_AM: ActionModel := {| amTrans := yntrans |}.

Instance yn_step_dec: AM_step_dec yn_AM. 
Proof. 
  red. intros [n1 b1] a oρ [n2 b2].
  Local Ltac nostep := right; intros STEP; inversion STEP; try (subst; tauto || lia). 
  destruct (decide (a = yn_act)) as [-> | ].
  2: { by nostep. }
  destruct oρ as [ρ| ]; [| by nostep].
  destruct (decide (n2 = n1 /\ b1 = true /\ b2 = false /\ ρ = Y /\ 0 < n1)) as [S| ]. 
  { destruct S as (->&->&->&->&?).
    left. simpl. by constructor. } 
  destruct (decide (n2 = n1 /\ b1 = false /\ b2 = false /\ ρ = Y /\ 1 < n1)) as [S| ]. 
  { destruct S as (->&->&->&->&?).
    left. simpl. by constructor. } 
  destruct (decide (n1 = S n2 /\ b1 = false /\ b2 = true /\ ρ = No)) as [S| ]. 
  { destruct S as (->&->&->&->).
    left. simpl. by constructor. } 
  destruct (decide (n2 = n1 /\ b1 = true /\ b2 = true /\ ρ = No /\ 0 < n1)) as [S| ]. 
  { destruct S as (->&->&->&->&?).
    left. simpl. by constructor. }
  by nostep.
Qed. 

Instance yn_fb: AM_fin_branch' yn_AM.
Proof.
  exists (fun '(n, b) => 
         n' ← [n; (n-1)%nat];
         w' ← [b; negb b];
         ℓ ← [Some Y; Some No];
         mret ((n', w'), yn_act, ℓ)). 
  intros [??] [??] ?? Htrans.
  repeat setoid_rewrite elem_of_list_bind.
  setoid_rewrite elem_of_list_ret.
  setoid_rewrite (and_comm (exists _, _) _).
  setoid_rewrite <- utils.ex_and_comm. rewrite utils.ex_prod'.
  setoid_rewrite (and_comm _ (_ /\ _)).
  setoid_rewrite <- (and_assoc _ _). 
  setoid_rewrite (and_comm _ (_ /\ _)).
  setoid_rewrite <- utils.ex_and_comm. rewrite utils.ex_prod'.
  eapply utils.ex_det_iff.
  { intros [[? ?] ?] (?&EQ&?). simpl in EQ.
    inversion EQ. subst. reflexivity. }
  simpl.
  inversion Htrans; subst; simpl; try set_solver.
  repeat split; try set_solver.
  rewrite Nat.sub_0_r. set_solver.
Qed. 

Lemma yn_AM_live_roles (nb: amSt yn_AM) ρ:
  ρ ∈ AM_live_roles nb <-> ρ ∈ yn_live_roles nb.
Proof.
  destruct nb as [n b]. 
  rewrite -AM_live_roles_spec. simpl.
  destruct n as [| [| ]], b; simpl.
  - split; [| done]. intros (?&?&STEP). inversion STEP; lia.
  - split; [| done]. intros (?&?&STEP). inversion STEP; lia.
  - split.
    + intros (?&?&STEP). inversion STEP; set_solver.
    + rewrite elem_of_union !elem_of_singleton. intros [-> | ->].
      all: do 2 eexists; constructor; lia.  
  - rewrite !elem_of_singleton. 
    split.
    + intros (?&?&STEP). inversion STEP; try lia || done.
    + intros ->. do 2 eexists. constructor.
  - split.
    + intros (?&?&STEP). inversion STEP; set_solver.
    + rewrite elem_of_union !elem_of_singleton. intros [-> | ->].
      all: do 2 eexists; constructor; lia.  
  - split.
    + intros (?&?&STEP). inversion STEP; set_solver.
    + rewrite elem_of_union !elem_of_singleton. intros [-> | ->].
      all: do 2 eexists; constructor; lia.  
Qed.

Lemma yn_acts: forall a, is_action_of yn_AM a <-> a = yn_act.
Proof. 
  intros. rewrite /is_action_of. split.
  - intros (?&?&?&STEP). inversion STEP; eauto.
  - intros ->.
    do 3 eexists. econstructor. eauto.
Qed. 

Lemma yn_AM_live_roles' (st: amSt yn_AM):
  AM_live_roles st = yn_live_roles st.
Proof. 
  apply set_eq. intros. rewrite -yn_AM_live_roles. done.
Qed. 

Instance yn_AM_act_dec: forall a, Decision (is_action_of yn_AM a).
Proof.
  intros. eapply Decision_iff_impl; [symmetry; apply yn_acts| ].
  apply _.
Qed. 


