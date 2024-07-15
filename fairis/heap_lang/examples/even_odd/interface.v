From iris.algebra Require Import excl_auth.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness.heap_lang.examples.even_odd Require Import action_model utils.


Close Scope Z. 

Inductive PubA := step_sync (k: nat).

Global Instance PubA_EqDec: EqDecision PubA.
Proof.
  intros [x] [y]. destruct (decide (x = y)); [left | right]; set_solver.
Qed. 

Definition BuildSubModel (St Priv Role: Type) Trans := {|
   amSt := St;
   amA := PubA + Priv;
   amRole := Role;
   amTrans := Trans;
|}.


Class ActionModelExtra (AM: ActionModel) := {
    ame_role_eqdec :> EqDecision (amRole AM);
    ame_role_cnt :> Countable (amRole AM);
    ame_st_eqdec :> EqDecision (amSt AM);
    ame_st_inh :> Inhabited (amSt AM);
    ame_role_inh :> Inhabited (amRole AM);

    ame_fin_branch': AM_fin_branch' AM;
    ame_step_dec: AM_step_dec AM;
    ame_strong := fin_branch_strong AM (ame_fin_branch') (ame_step_dec);
}.


Record EvenModel := {
    eSt: Type;
    ePriv: Type;
    eRole: Type;
    eTrans;

    cur_even: eSt -> nat -> Prop;

    even_AM := BuildSubModel eSt ePriv eRole eTrans;
    even_AME :> ActionModelExtra even_AM;

    even_syncable n st (ODD: Nat.odd n) (CUR: cur_even st n):
      exists st', amTrans even_AM st (inl (step_sync n), None) st' /\ cur_even st' (n + 1);
    even_sync_step_inv st__e st__e' k N ρ
      (STEP: amTrans even_AM st__e (inl (step_sync k), Some ρ) st__e')
      (CUR: cur_even st__e N):
      k = N /\ Nat.even N;
    even_sync_lr_nonincr st__e st__e' M
      (STEP: amTrans even_AM st__e (inl (step_sync M), None) st__e'):
      AM_live_roles ame_strong st__e' ⊆ AM_live_roles ame_strong st__e;

    ρ__e: amRole even_AM;
}.




Record OddModel := {
    oSt: Type;
    oPriv: Type;
    oRole: Type;
    oTrans;

    cur_odd: oSt -> nat -> Prop;

    odd_AM := BuildSubModel oSt oPriv oRole oTrans;
    odd_AME :> ActionModelExtra odd_AM;

    odd_syncable n st (ODD: Nat.even n) (CUR: cur_odd st n):
      exists st', amTrans odd_AM st (inl (step_sync n), None) st' /\ cur_odd st' (n + 1);
    odd_sync_step_inv st__e st__e' k N ρ
      (STEP: amTrans odd_AM st__e (inl (step_sync k), Some ρ) st__e')
      (CUR: cur_odd st__e N):
      k = N /\ Nat.odd N;
    odd_sync_lr_nonincr st__e st__e' M
      (STEP: amTrans odd_AM st__e (inl (step_sync M), None) st__e'):
      AM_live_roles ame_strong st__e' ⊆ AM_live_roles ame_strong st__e;

    ρ__o: amRole odd_AM;
}.
