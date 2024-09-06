From trillium.fairness Require Import action_model.
From stdpp Require Import base. 
From trillium.fairness Require Import utils.
From iris.proofmode Require Import proofmode.

Class EnvironmentAM (env_AM: ActionModel) := {
    (* eam_role_eqdec :> EqDecision (amRole env_AM); *)
    (* eam_role_cnt :> Countable (amRole env_AM); *)
    eam_st_eqdec :> EqDecision (amSt env_AM);
    eam_st_inh :> Inhabited (amSt env_AM);
    eam_env_fb :> AM_fin_branch' env_AM;
    eam_act_dec :> forall a, Decision (is_action_of env_AM a);
    eam_step_dec :> AM_step_dec env_AM;
  }.
Existing Instance eam_env_fb.
Existing Instance eam_step_dec.

Instance EnvUnitAM: EnvironmentAM UnitAM.
Proof. 
  unshelve esplit.
  all: by apply _.
Defined.
