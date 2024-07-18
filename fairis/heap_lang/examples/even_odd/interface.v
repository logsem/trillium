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

(* constructs an ActionModel with pre-defined set of public roles *)
Definition BuildSubModel (St Priv Role: Type) Trans := {|
   amSt := St;
   amA := PubA + Priv;
   amRole := Role;
   amTrans := Trans;
|}.

(* Convention: if the type of ActionModel's actions is defined as a sum,
   the left summand defines "public" actions (used for synchronization)
   and the right one defines "private" actions *)
Definition pub_act {A B: Type} := @inl A B.
Definition priv_act {A B: Type} := @inr A B.


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

    cur_even: eSt -> nat;

    even_AM := BuildSubModel eSt ePriv eRole eTrans;
    even_AME :> ActionModelExtra even_AM;

    even_step_inv st st' k ρ
      (STEP: amTrans even_AM st (pub_act (step_sync k), Some ρ) st'):
      cur_even st = k /\ cur_even st' = k + 1 /\ Nat.even k;
    even_sync_inv st st' k
      (STEP: amTrans even_AM st (pub_act (step_sync k), None) st'):
      cur_even st = k /\ cur_even st' = k + 1 /\ Nat.odd k;
    even_stutter_inv st st' a ρ
      (STEP: amTrans even_AM st (priv_act a, Some ρ) st'):
      cur_even st = cur_even st' (* /\ Nat.odd (cur_even st) *);

    ρ__e: amRole even_AM;
    even_steppable st (EVEN: Nat.even (cur_even st)):
      exists st', amTrans even_AM st (pub_act (step_sync (cur_even st)), Some ρ__e) st';
    even_syncable st (ODD: Nat.odd (cur_even st)):
      exists st', amTrans even_AM st (pub_act (step_sync (cur_even st)), None) st';
    even_stutterable st (ODD: Nat.odd (cur_even st)):
      exists st' a, amTrans even_AM st (priv_act a, Some ρ__e) st';

    even_step_lr_nonincr st st' a oρ
      (STEP: amTrans even_AM st (a, oρ) st'):
      AM_live_roles ame_strong st' ⊆ AM_live_roles ame_strong st;

    even_init: amSt even_AM;
    even_init_0: cur_even even_init = 0;
    even_init_lr: AM_live_roles ame_strong even_init = {[ ρ__e ]};

  (* TODO: ? replace with "private actions don't preempt the sync one forever" condition *)
  even_pub_priv_disj (st__e: amSt even_AM):
    (exists k st__e', amTrans _ st__e (pub_act $ step_sync k, Some ρ__e) st__e') ->
    (exists a st__e', amTrans _ st__e (priv_act a, Some ρ__e) st__e') ->
    False;
}.


Record OddModel := {
    oSt: Type;
    oPriv: Type;
    oRole: Type;
    oTrans;

    cur_odd: oSt -> nat;

    odd_AM := BuildSubModel oSt oPriv oRole oTrans;
    odd_AME :> ActionModelExtra odd_AM;

    odd_step_inv st st' k ρ
      (STEP: amTrans odd_AM st (pub_act (step_sync k), Some ρ) st'):
      cur_odd st = k /\ cur_odd st' = k + 1 /\ Nat.odd k;
    odd_sync_inv st st' k
      (STEP: amTrans odd_AM st (inl (step_sync k), None) st'):
      cur_odd st = k /\ cur_odd st' = k + 1 /\ Nat.even k;
    odd_stutter_inv st st' a ρ
      (STEP: amTrans odd_AM st (priv_act a, Some ρ) st'):
      cur_odd st = cur_odd st' (* /\ Nat.even (cur_odd st) *);

    ρ__o: amRole odd_AM;
    odd_steppable st (ODD: Nat.odd (cur_odd st)):
      exists st', amTrans odd_AM st (pub_act (step_sync (cur_odd st)), Some ρ__o) st';
    odd_syncable st (ODD: Nat.even (cur_odd st)):
      exists st', amTrans odd_AM st (pub_act (step_sync (cur_odd st)), None) st';
    odd_stutterable st (ODD: Nat.even (cur_odd st)):
      exists st' a, amTrans odd_AM st (priv_act a, Some ρ__o) st';

    odd_step_lr_nonincr st st' a oρ
      (STEP: amTrans odd_AM st (a, oρ) st'):
      AM_live_roles ame_strong st' ⊆ AM_live_roles ame_strong st;

    odd_init: amSt odd_AM;
    odd_init_0: cur_odd odd_init = 0;
    odd_init_lr: AM_live_roles ame_strong odd_init = {[ ρ__o ]};

  (* TODO: ? replace with "private actions don't preempt the sync one forever" condition *)
    odd_pub_priv_disj (st__o: amSt odd_AM):
    (exists k st__o', amTrans _ st__o (pub_act $ step_sync k, Some ρ__o) st__o') ->
    (exists a st__o', amTrans _ st__o (priv_act a, Some ρ__o) st__o') ->
    False;
}.

Lemma ρ__e_always_live `{em: EvenModel} st__e:
  ρ__e em ∈ AM_live_roles (@ame_strong _ (even_AME em)) st__e.
Proof.
  apply AM_live_roles_spec. 
  destruct (even_or_odd (cur_even _ st__e)) as [E | O]. 
  - eexists. eapply @even_steppable. intuition.
  - ogeneralize * even_stutterable; eauto.
    intros (?&?&?). eauto.
Qed.

Lemma ρ__o_always_live `{om: OddModel} st__o:
  ρ__o om ∈ AM_live_roles (@ame_strong _ (odd_AME om)) st__o.
Proof.
  apply AM_live_roles_spec. 
  destruct (even_or_odd (cur_odd _ st__o)) as [E | O]. 
  - ogeneralize * odd_stutterable; eauto.
    intros (?&?&?). eauto.
  - eexists. eapply @odd_steppable. intuition.
Qed.
