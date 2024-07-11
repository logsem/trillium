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

Class threadG Σ := ThreadG {
  th_name: gname;
  th_n_G :> inG Σ (excl_authR natO);
}.

Class threadPreG Σ := {
  thread_PreG :> inG Σ (excl_authR natO);
}.

Section ThreadGLemmas.
  Context `{!threadG Σ}.

  Definition th_at (n: nat) := own th_name (◯E n).
  Definition auth_th_at (n: nat) := own th_name (●E n).
  
  Lemma th_agree γ (N M: nat) :
    own γ (◯E N) -∗ own γ (●E M) -∗ ⌜ M = N ⌝.
  Proof.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.
  
  Lemma th_update γ (N M P: nat) :
    own γ (●E N) ∗ own γ (◯E M) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.

End ThreadGLemmas.

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

  even_corr 
    {M__p : FairModel} {LM__p : LiveModel heap_lang M__p}
    {Σ : gFunctors} {heapGS0 : heapGS Σ LM__p}
    (threadG0 : threadG Σ) 
  (proj_st : M__p → amSt even_AM) (l : loc) (st : M__p) 
  (N : nat) :=
  let st__t := proj_st st in
  (frag_model_is st ∗ l ↦ #N ∗ ⌜cur_even st__t N⌝ ∗
   own th_name (●E (if Nat.even N then N else N + 1)))%I;
  glob_step_even {M__p : FairModel}
    (proj_st : fmstate M__p → amSt even_AM)
  (lift_role : amRole even_AM → fmrole M__p) 
  (st st' : M__p) (ρ__t : amRole even_AM) (st__e' : amSt even_AM) := 
  proj_st st' = st__e'
  ∧ fmtrans M__p st (Some (lift_role ρ__t)) st'
    ∧ (AM_live_roles ame_strong (proj_st st')
       ⊆ AM_live_roles ame_strong (proj_st st)
       → live_roles M__p st' ⊆ live_roles M__p st);
  even_vs {M__p : FairModel} {LM__p : LiveModel heap_lang M__p} 
  {Σ : gFunctors} {heapGS0 : heapGS Σ LM__p} {threadG0 : threadG Σ} 
  (proj_st : fmstate M__p → amSt even_AM) (lift_role : 
                                            amRole even_AM → 
                                            fmrole M__p) 
  (l : loc) (ι : namespace) (ρ__t : amRole even_AM) tid := 
  (□ (|={⊤,⊤ ∖ ↑ι}=>
        ∃ (st__p : M__p) (N : nat),
          let st__t := proj_st st__p in
          ▷ even_corr threadG0 proj_st l st__p N ∗
          (⌜Nat.even N⌝
           → ∀ st__t' : amSt even_AM,
               ⌜amTrans even_AM st__t (inl (step_sync N), Some ρ__t)
                  st__t'⌝ ∗ ⌜cur_even st__t' (N + 1)⌝
               → 
                 (* ∃ st__p' : M__p, *)
                 (*   ⌜glob_step_even proj_st lift_role st__p st__p' ρ__t st__t'%nat⌝ ∗ *)
                 (*   (▷ even_corr threadG0 proj_st l st__p' (N + 1) ={⊤ ∖ ↑ι,⊤}=∗ True) *)
                 ∀ f, ⌜ f >= 1 ⌝ -∗ tid ↦M {[ lift_role ρ__t := f ]} -∗ frag_model_is st__p -∗ frag_free_roles_are ∅ -∗
                       MU (⊤ ∖ ↑ι) tid (∃ st__p' f', tid ↦M {[ lift_role ρ__t := f' ]}  ∗ frag_model_is st__p' ∗ frag_free_roles_are ∅ ∗ ⌜ f' > 43 ⌝ ∗
                                         ⌜ proj_st st__p' = st__t' ⌝ ∗
                                         (▷ (even_corr threadG0 proj_st l st__p' (N + 1)) ={⊤ ∖ ↑ι, ⊤}=∗ True))

          ) ∗

          (⌜Nat.odd N⌝
           → ∀ (st__t' : amSt even_AM) (a : ePriv),
               ⌜amTrans even_AM st__t (inr a, Some ρ__t) st__t'⌝ ∗
               ⌜cur_even st__t' N⌝
               → ∃ st__p' : M__p,
                   ⌜glob_step_even proj_st lift_role st__p st__p' ρ__t st__t'⌝ ∗
                   (▷ even_corr threadG0 proj_st l st__p' N ={⊤ ∖ ↑ι,⊤}=∗ True))))%I;
  even_prog: val;
  even_spec {M__p : FairModel} {LM__p : LiveModel heap_lang M__p} 
  {Σ : gFunctors} {heapGS0 : heapGS Σ LM__p} {threadG0 : threadG Σ} 
  (proj_st : M__p → amSt even_AM) (lift_role: amRole even_AM → fmrole M__p) 
  (tid : locale heap_lang) (n : loc) (ρ__t : amRole even_AM) 
  (N f : nat) (FUEL: f > 40) (ι : namespace) (FL: ∀ st : M__p, lm_fl LM__p st ≥ 61):
      {{{ even_vs proj_st lift_role n ι ρ__t tid ∗
        tid ↦M {[lift_role ρ__t := f]} ∗
        own th_name (◯E N) ∗
        frag_free_roles_are ∅ }}}
          even_prog #n #N@tid
        {{{ RET #(); tid ↦M ∅ }}};

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

  odd_corr 
    {M__p : FairModel} {LM__p : LiveModel heap_lang M__p}
    {Σ : gFunctors} {heapGS0 : heapGS Σ LM__p}
    (threadG0 : threadG Σ) 
  (proj_st : M__p → amSt odd_AM) (l : loc) (st : M__p) 
  (N : nat) :=
  let st__t := proj_st st in
  (frag_model_is st ∗ l ↦ #N ∗ ⌜cur_odd st__t N⌝ ∗
   own th_name (●E (if Nat.odd N then N else N + 1)))%I;
  glob_step_odd {M__p : FairModel}
    (proj_st : fmstate M__p → amSt odd_AM)
  (lift_role : amRole odd_AM → fmrole M__p) 
  (st st' : M__p) (ρ__t : amRole odd_AM) (st__e' : amSt odd_AM) := 
  proj_st st' = st__e'
  ∧ fmtrans M__p st (Some (lift_role ρ__t)) st'
    ∧ (AM_live_roles ame_strong (proj_st st')
       ⊆ AM_live_roles ame_strong (proj_st st)
       → live_roles M__p st' ⊆ live_roles M__p st);
  odd_vs {M__p : FairModel} {LM__p : LiveModel heap_lang M__p} 
  {Σ : gFunctors} {heapGS0 : heapGS Σ LM__p} {threadG0 : threadG Σ} 
  (proj_st : fmstate M__p → amSt odd_AM) (lift_role : 
                                            amRole odd_AM → 
                                            fmrole M__p) 
  (l : loc) (ι : namespace) (ρ__t : amRole odd_AM) := 
  (□ (|={⊤,⊤ ∖ ↑ι}=>
        ∃ (st__p : M__p) (N : nat),
          let st__t := proj_st st__p in
          ▷ odd_corr threadG0 proj_st l st__p N ∗
          (⌜Nat.odd N⌝
           → ∀ st__t' : amSt odd_AM,
               ⌜amTrans odd_AM st__t (inl (step_sync N), Some ρ__t)
                  st__t'⌝ ∗ ⌜cur_odd st__t' (N + 1)⌝
               → ∃ st__p' : M__p,
                   ⌜glob_step_odd proj_st lift_role st__p st__p' ρ__t st__t'%nat⌝ ∗
                   (▷ odd_corr threadG0 proj_st l st__p' (N + 1) ={⊤ ∖ ↑ι,⊤}=∗ True)) ∗
          (⌜Nat.even N⌝
           → ∀ (st__t' : amSt odd_AM) (a : oPriv),
               ⌜amTrans odd_AM st__t (inr a, Some ρ__t) st__t'⌝ ∗
               ⌜cur_odd st__t' N⌝
               → ∃ st__p' : M__p,
                   ⌜glob_step_odd proj_st lift_role st__p st__p' ρ__t st__t'⌝ ∗
                   (▷ odd_corr threadG0 proj_st l st__p' N ={⊤ ∖ ↑ι,⊤}=∗ True))))%I;
  odd_prog: val;
  odd_spec {M__p : FairModel} {LM__p : LiveModel heap_lang M__p} 
  {Σ : gFunctors} {heapGS0 : heapGS Σ LM__p} {threadG0 : threadG Σ} 
  (proj_st : M__p → amSt odd_AM) (lift_role: amRole odd_AM → fmrole M__p) 
  (tid : locale heap_lang) (n : loc) (ρ__t : amRole odd_AM) 
  (N f : nat) (FUEL: f > 40) (ι : namespace) (FL: ∀ st : M__p, lm_fl LM__p st ≥ 61):
      {{{ odd_vs proj_st lift_role n ι ρ__t ∗
        tid ↦M {[lift_role ρ__t := f]} ∗
        own th_name (◯E N) ∗
        frag_free_roles_are ∅ }}}
          odd_prog #n #N@tid
        {{{ RET #(); tid ↦M ∅ }}};

  ρ__o: amRole odd_AM;
}.

