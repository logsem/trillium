From RecordUpdate Require Import RecordSet.
From stdpp Require Import binders.
From iris.proofmode Require Import tactics.
From trillium.program_logic Require Import weakestpre lifting ectx_lifting atomic.
From fairneris Require Import fuel fair_resources.
From fairneris.aneris_lang Require Import network_model aneris_lang base_lang resources.
From fairneris.aneris_lang.state_interp Require Import
     state_interp state_interp_events.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
    [head_step]. The tactic will discharge head-reductions starting from values,
    and simplifies hypothesis related to conversions from and to values, and
    finite map operations. This tactic is slightly ad-hoc and tuned for proving
    our lifting lemmas. *)
Ltac inv_head_step :=
  repeat
    match goal with
    | _ => progress simplify_map_eq/= (* simplify memory stuff *)
    | H : aneris_to_val _ = Some _ |- _ => apply to_base_aneris_val in H
    | H : base_lang.head_step ?e _ _ _ _ _ |- _ =>
      try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
      inversion H; subst; clear H
    | H : head_step ?e _ _ _ _ _ |- _ =>
      try (is_var e; fail 1);
      inversion H; subst; clear H
    | H: socket_step _ ?e _ _ _ _ _ _ |- _ =>
      try (is_var e; fail 1);
      inversion H; subst; clear H
    end.

Local Ltac solve_exec_safe :=
  intros;
  repeat match goal with
         | H: _ ∧ _ |- _ => destruct H as [??]
         end;
  simplify_eq;
  do 4 eexists; eapply (LocalStepPureS _ ∅); econstructor; eauto.
Local Ltac solve_exec_puredet :=
  simpl; intros; inv_head_step;
  first (by repeat match goal with
                   | H: _ ∧ _ |- _ => destruct H as [??]; simplify_eq
                   | H : to_val _ = Some _ |- _ =>
                     rewrite to_of_val in H; simplify_eq
                   end);
  try by match goal with
         | H : socket_step _ _ _ _ _ _ _ _ |- _ =>
           inversion H
         end.
Local Ltac solve_pure_exec :=
  simplify_eq; rewrite /PureExec; intros;
  apply nsteps_once, pure_head_step_pure_step;
  constructor; [solve_exec_safe | solve_exec_puredet].

Local Hint Constructors head_step : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

#[global] Instance into_val_val n v : IntoVal (mkExpr n (Val v)) (mkVal n v).
Proof. done. Qed.
#[global] Instance as_val_val n v : AsVal (mkExpr n (Val v)).
Proof. by exists (mkVal n v). Qed.

#[global] Instance into_val_base_val v : IntoVal (Val v) v.
Proof. done. Qed.
#[global] Instance as_val_base_val v : AsVal (Val v).
Proof. by exists v. Qed.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; inv_head_step; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; inv_head_step;
       rewrite /aneris_to_val /is_Some /=; eexists; by
         match goal with
         | H: _ = _ |- _ => rewrite -H
         end
    ].

Lemma aneris_base_fill K ip e :
  mkExpr ip (fill (Λ := base_ectxi_lang) K e) =
  fill (Λ := aneris_ectxi_lang) K (mkExpr ip e).
Proof.
  revert e; induction K as [|k K IHK] using rev_ind; first done.
  intros e.
  rewrite !fill_app /= -IHK /=; done.
Qed.

#[global] Instance aneris_pure_exec_fill
         (K : list ectx_item) ip (φ : Prop) (n : nat) e1 e2 :
  PureExec φ n (mkExpr ip e1) (mkExpr ip e2) →
  @PureExec aneris_lang φ n
            (mkExpr ip (@fill base_ectxi_lang K e1))
            (mkExpr ip (@fill base_ectxi_lang K e2)).
Proof.
  intros.
  rewrite !aneris_base_fill.
  eapply pure_exec_ctx; first apply _; done.
Qed.

#[global] Instance binop_atomic n s op v1 v2 :
  Atomic s (mkExpr n (BinOp op (Val v1) (Val v2))).
Proof. solve_atomic. Qed.
#[global] Instance alloc_atomic lbl n s v : Atomic s (mkExpr n (Alloc lbl (Val v))).
Proof. solve_atomic. Qed.
#[global] Instance load_atomic n s v : Atomic s (mkExpr n (Load (Val v))).
Proof. solve_atomic. Qed.
#[global] Instance store_atomic n s v1 v2 : Atomic s (mkExpr n (Store (Val v1) (Val v2))).
Proof. solve_atomic. Qed.
#[global] Instance cmpxchg_atomic n s v0 v1 v2 :
  Atomic s (mkExpr n (CAS (Val v0) (Val v1) (Val v2))).
Proof. solve_atomic. Qed.
#[global] Instance fork_atomic n s e : Atomic s (mkExpr n (Fork e)).
Proof. solve_atomic. Qed.
#[global] Instance skip_atomic n s : Atomic s (mkExpr n Skip).
Proof. solve_atomic. Qed.
#[global] Instance rec_atomic n s f x e: Atomic s (mkExpr n (Rec f x e)).
Proof. solve_atomic. Qed.
#[global] Instance injr_atomic n s v : Atomic s (mkExpr n (InjR (Val v))).
Proof. solve_atomic. Qed.
#[global] Instance injl_atomic n s v : Atomic s (mkExpr n (InjL (Val v))).
Proof. solve_atomic. Qed.
#[global] Instance fst_atomic n s v : Atomic s (mkExpr n (Fst (Val v))).
Proof. solve_atomic. Qed.
#[global] Instance snd_atomic n s v : Atomic s (mkExpr n (Snd (Val v))).
Proof. solve_atomic. Qed.

#[global] Instance newsocket_atomic n s :
  Atomic s (mkExpr n (NewSocket #())).
Proof. solve_atomic. Qed.
#[global] Instance socketbind_atomic n v0 v1  s :
  Atomic s (mkExpr n (SocketBind (Val v0) (Val v1))).
Proof. solve_atomic. Qed.
#[global] Instance sendto_atomic n v0 v1 v2 s :
  Atomic s (mkExpr n (SendTo (Val v0) (Val v1) (Val v2))).
Proof. solve_atomic. Qed.

#[global] Instance setreceivetimeout_atomic n v0 v1 v2 s:
  Atomic s (mkExpr n (SetReceiveTimeout (Val v0) (Val v1) (Val v2))).
Proof. solve_atomic. Qed.

#[global] Instance receive_from_stutteringatomic n sh s :
  StutteringAtomic s (mkExpr n (ReceiveFrom (Val $ LitV $ sh))).
Proof.
  apply strongly_stutteringatomic_stutteringatomic,
    ectx_language_stutteringatomic.
  - inversion 1; inv_head_step; try naive_solver; [].
    rewrite insert_id; last done.
    match goal with
      |- context [state_heaps ?st] => by destruct st; eauto
    end.
  - apply ectxi_language_sub_redexes_are_values; intros [] **; inv_head_step;
      rewrite /aneris_to_val /is_Some /=; eexists; by
          match goal with
          | H: _ = _ |- _ => rewrite -H
          end.
Qed.

Class AsRecV (v : val _) (f x : binder) (erec : expr _) :=
  as_recv : v = RecV f x erec.
Global Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Global Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

#[global] Instance pure_rec n f x erec :
  PureExec True 1 (mkExpr n (Rec f x erec)) (mkExpr n (Val $ RecV f x erec)).
Proof. solve_pure_exec. Qed.
#[global] Instance pure_pairc n v1 v2:
  PureExec True 1 (mkExpr n (Pair (Val v1) (Val v2)))
           (mkExpr n (Val $ PairV v1 v2)).
Proof. solve_pure_exec. Qed.
#[global] Instance pure_injlc n v :
  PureExec True 1 (mkExpr n (InjL $ Val v)) (mkExpr n (Val $ InjLV v)).
Proof. solve_pure_exec. Qed.
#[global] Instance pure_injrc n v :
  PureExec True 1 (mkExpr n (InjR $ Val v)) (mkExpr n (Val $ InjRV v)).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_beta n f x erec v1 v2 `{!AsRecV v1 f x erec} :
  PureExec True 1 (mkExpr n (App (Val v1) (Val v2)))
           (mkExpr n (subst' x v2 (subst' f v1 erec))).
Proof. unfold AsRecV in *. solve_pure_exec. Qed.

#[global] Instance pure_unop n op v v' :
  PureExec (un_op_eval op v = Some v') 1 (mkExpr n (UnOp op (Val v)))
           (mkExpr n (of_val v')).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_binop n op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1
           (mkExpr n (BinOp op (Val v1) (Val v2))) (mkExpr n (of_val v')).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_if_true n e1 e2 :
  PureExec True 1 (mkExpr n (If (Val $ LitV $ LitBool true) e1 e2)) (mkExpr n e1).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_if_false n e1 e2 :
  PureExec True 1 (mkExpr n (If (Val $ LitV $ LitBool false) e1 e2))
           (mkExpr n e2).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_fst n v1 v2 :
  PureExec True 1 (mkExpr n (Fst (PairV v1 v2))) (mkExpr n (Val v1)).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_snd n v1 v2  :
  PureExec True 1 (mkExpr n (Snd (PairV v1 v2))) (mkExpr n (Val v2)).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_find_from n v0 v1 n1 v2 v' :
  PureExec (index n1 v2 v0 = v' ∧ Z.of_nat n1 = v1) 1
           (mkExpr n (FindFrom (Val $ LitV $ LitString v0)
                       (Val $ LitV $ LitInt v1)
                       (Val $ LitV $ LitString v2)))
           (mkExpr n (of_val (option_nat_to_val v'))).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_substring n v0 v1 n1 v2 n2 v' :
  PureExec (substring n1 n2 v0 = v' ∧ Z.of_nat n1 = v1 ∧ Z.of_nat n2 = v2) 1
           (mkExpr
              n (Substring
                   (LitV $ LitString v0) (LitV $ LitInt v1) (LitV $ LitInt v2)))
           (mkExpr n (of_val (LitV $ LitString v'))).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_case_inl n v e1 e2  :
  PureExec True 1 (mkExpr n (Case (Val $ InjLV v) e1 e2))
           (mkExpr n (App e1 (Val v))).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_case_inr n v e1 e2 :
  PureExec True 1 (mkExpr n (Case (Val $ InjRV v) e1 e2))
           (mkExpr n (App e2 (Val v))).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_make_address n v1 v2 :
  PureExec True 1
           (mkExpr n (MakeAddress (LitV (LitString v1)) (LitV (LitInt (v2)))))
           (mkExpr
              n (LitV (LitSocketAddress (SocketAddressInet v1 (Z.to_pos v2))))).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_get_address_info n ip p :
  PureExec True 1
           (mkExpr n (GetAddressInfo (LitV (LitSocketAddress (SocketAddressInet ip p)))))
           (mkExpr n (PairV #ip #(Zpos p))).
Proof. solve_pure_exec. Qed.

Opaque aneris_state_interp.

Notation state_interp_oos ζ α := (aneris_state_interp_opt (Some (ζ,α))).

Definition sswp `{LM:LiveModel aneris_lang (joint_model M Net)}
           `{!anerisG LM Σ} (s : stuckness)
           E ζ (e1:aneris_expr) (Φ : aneris_expr → option (action aneris_lang) → iProp Σ) : iProp Σ :=
  ⌜TCEq (aneris_to_val e1) None⌝ ∧
  ∀ (extr : execution_trace aneris_lang) (atr : auxiliary_trace LM) K
    (tp1 tp2:list aneris_expr) σ1,
  ⌜valid_exec extr⌝ -∗
  ⌜locale_of tp1 (ectx_fill K e1) = ζ⌝ -∗
  ⌜trace_ends_in extr (tp1 ++ ectx_fill K e1 :: tp2, σ1)⌝ -∗
  state_interp extr atr ={E,∅}=∗
  ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
  ∀ α e2 σ2 efs,
  ⌜prim_step e1 σ1 α e2 σ2 efs⌝ ={∅}▷=∗^(S $ trace_length extr) |={∅,E}=>
  state_interp_oos ζ α
    (trace_extend extr (inl (ζ,α)) (tp1 ++ ectx_fill K e2 :: tp2, σ2))
    atr ∗ Φ e2 α ∗ ⌜efs = []⌝.

Definition MU `{LM:LiveModel aneris_lang (joint_model M Net)}
           `{!anerisG LM Σ} E ζ α (P : iProp Σ) : iProp Σ :=
  ∀ (extr : execution_trace aneris_lang) (atr : auxiliary_trace LM),
  state_interp_oos ζ α extr atr ={E}=∗
  ∃ δ2 ℓ, state_interp extr (trace_extend atr ℓ δ2) ∗ P.

Lemma sswp_MU_wp_fupd `{LM:LiveModel aneris_lang (joint_model M Net)}
           `{!anerisG LM Σ} s E E' ζ e Φ :
  (|={E,E'}=> sswp s E' ζ e (λ e' α, MU E' ζ α ((|={E',E}=> WP e' @ s; ζ; E {{ Φ }}))))%I -∗
  WP e @ s; ζ; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre.
  iIntros "Hsswp".
  replace (language.to_val e) with (aneris_to_val e) by eauto.
  destruct (aneris_to_val e) eqn:Heqn.
  { iMod "Hsswp" as (Hval) "_". inversion Hval as [Heq]. by simplify_eq. }
  iIntros (extr atr K tp1 tp2 σ1 Hvalid Hζ Hextr) "Hσ".
  iMod "Hsswp" as "[_ Hsswp]".
  iMod ("Hsswp" with "[//] [//] [//] Hσ") as (Hs) "Hsswp".
  iModIntro. iSplit; [done|].
  iIntros (α e2 σ2 efs Hstep).
  iDestruct ("Hsswp" with "[//]") as "Hsswp".
  iApply (step_fupdN_wand with "Hsswp"). iIntros ">(Hσ & HMU & ->)".
  iMod ("HMU" with "Hσ") as (??) "[Hσ Hwp]". iMod "Hwp". iModIntro.
  iExists _, _. rewrite right_id_L. by iFrame.
Qed.

Lemma sswp_wand `{LM:LiveModel aneris_lang (joint_model M Net)}
           `{!anerisG LM Σ} s E ζ e
      (Φ Ψ : aneris_expr → option (action aneris_lang) → iProp Σ) :
  (∀ e α, Φ e α -∗ Ψ e α) -∗ sswp s E ζ e Φ -∗ sswp s E ζ e Ψ.
Proof.
  rewrite /sswp. iIntros "HΦΨ [%Hval Hsswp]".
  iSplit; [done|].
  iIntros (extr atr K tp1 tp2 σ1 Hvalid Hζ Hextr) "Hσ".
  iMod ("Hsswp" with "[//] [//] [//] Hσ") as (Hs) "Hsswp".
  iModIntro. iSplit; [done|].
  iIntros (α e2 σ2 efs Hstep).
  iDestruct ("Hsswp" with "[//]") as "Hsswp".
  iApply (step_fupdN_wand with "Hsswp"). iIntros ">(Hσ & HMU & ->)".
  iFrame. iModIntro. iSplit; [|done]. by iApply "HΦΨ".
Qed.

Lemma MU_wand `{LM:LiveModel aneris_lang (joint_model M Net)}
           `{!anerisG LM Σ} E ζ α (P Q : iProp Σ) :
  (P -∗ Q) -∗ MU E ζ α P -∗ MU E ζ α Q.
Proof.
  rewrite /MU. iIntros "HPQ HMU".
  iIntros (extr atr) "Hσ".
  iMod ("HMU" with "Hσ") as (??) "[Hσ HP]". iModIntro.
  iExists _, _. iFrame. by iApply "HPQ".
Qed.

Lemma sswp_MU_wp `{LM:LiveModel aneris_lang (joint_model M Net)}
           `{!anerisG LM Σ} s E ζ e (Φ : aneris_val → iProp Σ) :
  sswp s E ζ e (λ e' α, MU E ζ α (WP e' @ s; ζ;  E {{ Φ }})) -∗
  WP e @ s; ζ; E {{ Φ }}.
Proof.
  iIntros "Hsswp". iApply sswp_MU_wp_fupd. iModIntro.
  iApply (sswp_wand with "[] Hsswp").
  iIntros (??) "HMU". iApply (MU_wand with "[] HMU"). by iIntros "$ !>".
Qed.

Section primitive_laws.
  Context `{LM: LiveModel aneris_lang (joint_model Mod net_model)}.
  Context `{aG : !anerisG LM Σ}.

  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : aneris_val → iProp Σ.
  Implicit Types v : val aneris_lang.
  Implicit Types e : expr aneris_lang.
  Implicit Types σ : base_lang.state.
  Implicit Types M R T : message_soup.
  Implicit Types m : message.
  Implicit Types A B : gset socket_address.
  Implicit Types a : socket_address.
  Implicit Types ip : ip_address.
  Implicit Types sh : socket_handle.
  Implicit Types skt : socket.
  Implicit Types mh : messages_history.

  Lemma mu_step_fuel ζ E fs P :
    fs ≠ ∅ → ▷ ζ ↦M++ fs -∗
    (ζ ↦M fs -∗ P) -∗
    MU E ζ None P.
  Proof.
    iIntros (?) ">HfuelS HP".
    iIntros (ex atr) "[Hσ Hm]".
    iDestruct "Hm" as (ex' Hex' Hvalid Hstep) "Hmi".
    iMod (update_fuel_step with "HfuelS [//] Hmi") as (δ2) "(%Hvse & Hfuel & Hmod)" =>//.
    iIntros "!>".
    iExists _, (Silent_step ζ None). iFrame.
    iSplit; [by destruct Hex' as [ex'' ->]|].
    by iApply "HP".
  Qed.

  Lemma mu_step_model `{!LiveModelEq LM} ζ ρ α (f1 : nat) fs fr s1 s2 E P :
    lts_trans Mod s1 (ρ, α) s2 →
    Mod.(usr_live_roles) s2 ⊆ Mod.(usr_live_roles) s1 →
    ρ ∉ dom fs →
    ▷ frag_model_is s1 -∗
    ▷ ζ ↦M ({[ρ:=f1]} ∪ fmap S fs) -∗
    ▷ frag_free_roles_are fr -∗
    (frag_model_is s2 -∗
     ζ ↦M ({[ρ:=(Mod.(usr_fl) s2)]} ∪ fs) -∗
     frag_free_roles_are fr -∗ P) -∗
    MU E ζ α P.
  Proof.
    iIntros (Htrans Hlive Hdom) ">Hst >Hfuel1 >Hfr HP".
    iIntros (ex atr) "[Hσ Hm]".
    iDestruct "Hm" as (ex' Hex' Hstep Hvalid) "Hmi".
    iAssert (⌜(trace_last atr).(ls_data).(ls_under).1 = s1⌝)%I
      with "[Hst Hmi]" as %Heq.
    { iDestruct "Hmi" as (fm Hfmle Hfmdead Hfmtp) "[Hauth Hmi]".
      by iDestruct (model_agree with "Hauth Hst") as %Heq. }
    destruct α; last first.
    {
      iAssert (⌜config_net_match (trace_last ex) (trace_last atr).(ls_data).(ls_under).2⌝)%I as %Hmatch.
      { iDestruct "Hmi" as (fm Hfmle Hfmdead Hfmtp) "[Hauth [Hmi %Hmatch]]".
        destruct Hmatch. simpl in *. iPureIntro.
        simpl.
        inversion Hstep. subst.
        inversion H7. subst.
        inv_head_step.
        rewrite H3 in H. simpl in *. rewrite H5.
        admit. }
      (* set (δ2 := (s2, trace_last atr).2). *)
      iMod (update_model_step _ _ _
                              ((trace_last atr).(ls_data).(ls_under).1, (trace_last atr).(ls_data).(ls_under).2) ((s2, (trace_last atr).(ls_data).(ls_under).2)) _ _ _ _ _ None
             with "[$Hfuel1] [Hst] [//] [$Hmi]") as
        (δ2 Hvse) "(Hfuel & Hst & Hmod)"; [|done|done|done|..].
      { simpl. rewrite Heq. apply Hlive. }
      { simpl. done. }
      { simpl. econstructor. rewrite Heq. done. }
      { done. }
      { simpl. rewrite Heq. done. }
      iModIntro.
      iExists δ2.
      iExists (Take_step (ρ:fmrole (joint_model Mod _)) None ζ None).
      iFrame.
      destruct Hex' as [ex'' ->].
      simpl in *. iSplit; [done|].
      iApply ("HP" with "Hst Hfuel Hfr"). }
    destruct a.
    - admit.                    (* Send case: Construct new model state, where a message has been added, and prove config_net_match *)
    - admit.                    (* Recv case: Construct new model state, depending on whether a message was received or not, and prove config_net_match *)
  Admitted.

  Lemma has_fuels_decr E tid fs :
    tid ↦M++ fs -∗ |~{E}~| tid ↦M fs.
  Proof.
    iIntros "Hf". rewrite weakestpre.pre_step_unseal.
    iIntros (extr atr) "[Hσ [% Hm]]"=> /=.
    iMod (model_state_interp_has_fuels_decr with "Hm Hf") as "[$ $]". by iFrame.
  Qed.

  Lemma has_fuels_dealloc E tid fs ρ (δ:joint_model Mod net_model) :
    ρ ∉ live_roles _ δ → frag_model_is δ.1 -∗ tid ↦M fs -∗
    |~{E}~| frag_model_is δ.1 ∗ tid ↦M (delete ρ fs).
  Proof.
    iIntros (Hnin) "Hst Hf". rewrite weakestpre.pre_step_unseal.
    iIntros (extr atr) "[Hσ [% Hm]]".
    iMod (model_state_interp_has_fuels_dealloc with "Hm Hst Hf") as "[Hm Hf]";
      [done|by iFrame].
  Qed.

  Lemma message_history_evolution_id x y mh :
    mh = message_history_evolution x x y y mh.
  Proof.
    rewrite /message_history_evolution !gmultiset_difference_diag.
    destruct mh. f_equal; set_solver.
  Qed.

  Lemma sswp_pure_step s E ζ (e1 e2 : aneris_expr) (Φ : Prop) (Ψ : aneris_expr → option (action aneris_lang) → iProp Σ) :
    PureExec Φ 1 e1 e2 → Φ → ▷ (Ψ e2 None) -∗
    sswp s E ζ e1 Ψ.
  Proof.
    iIntros (Hpe HΦ) "HΨ".
    assert (pure_step e1 e2) as Hps.
    { specialize (Hpe HΦ). by apply nsteps_once_inv in Hpe. }
    rewrite /sswp /=.
    assert (aneris_to_val e1 = None) as ->.
    { destruct Hps as [Hred _].
      specialize (Hred (mkState ∅ ∅ ∅)).
      by eapply reducible_not_val. }
    iSplit; [done|].
    iIntros (extr atr K tp1 tp2 σ1 Hvalid Htp1 Hex) "Hσ".
    iMod fupd_mask_subseteq as "Hclose"; last iModIntro; [by set_solver|].
    iSplit.
    { destruct s; [|done]. by destruct Hps as [Hred _]. }
    iIntros (α e2' σ2 efs Hstep) "!>!>!>".
    iDestruct "Hσ" as "[[Hσ Hauth] [%Hvalid' Hm]]".
    iApply step_fupdN_intro; [done|]. iIntros "!>".
    iMod (steps_auth_update _ (S (trace_length extr)) with "Hauth")
      as "[Hauth _]"; [by eauto|].
    iMod "Hclose" as "_". iModIntro. destruct Hps as [H' Hstep'].
    pose proof Hstep as Hstep''.
    apply Hstep' in Hstep as [-> [-> [-> ->]]]. iFrame.
    inv_head_step.
    simpl.
    iFrame.
    iSplit; [|done].
    iSplitL "Hσ"; last first.
    { simpl.
      iExists extr.
      iSplit.
      { iPureIntro. simpl. by eexists _. }
      rewrite /aneris_state_interp_δ. rewrite Hex. iFrame.
      iSplit; [|done].
      iPureIntro.
      eapply (locale_step_atomic _ _ _ _ _ _ _ []); try done.
      { by rewrite right_id_L. }
      apply fill_step.
      done. }
    iFrame.
    simpl.
    rewrite Hex.
    rewrite -message_history_evolution_id.
    done.
  Qed.

  Lemma wp_alloc n s E ζ v (Φ : aneris_expr → option (action aneris_lang) → iProp Σ) :
    ▷ is_node n -∗
    (∀ (l:loc), l ↦[n] v -∗ Φ (mkExpr n (Val $ LitV $ LitLoc l)) None) -∗
    sswp s E ζ (mkExpr n (Alloc None (Val v))) Φ.
  Proof.
    iIntros "Hn HΦ".
    rewrite /sswp.
    iSplit; [done|].
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hlocale Hex) "([Hσ Hauth] & [% Hm])".
    iMod "Hn".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (is_node_heap_valid with "Hσ Hn") as (h) "%Hσ".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplitR; [iPureIntro; eauto|].
    { destruct s; [|done]. do 4 eexists. eapply head_prim_step.
      eapply LocalStepS; eauto.  }
    iIntros (α v2 σ2 efs Hstep).
    apply head_reducible_prim_step in Hstep; last first.
    { do 4 eexists. eapply LocalStepS; eauto. }
    pose proof (conj Hstep I) as Hstep'.
    inv_head_step.
    destruct Hstep' as [Hstep' _].
    iApply step_fupdN_intro; [done|].
    iIntros "!>!>".
    iMod (aneris_state_interp_alloc_heap _ _ _ l with "Hn Hσ")
      as "[Hσ Hl]"; [done..|].
    iModIntro. iIntros "!>".
    iMod (steps_auth_update _ (S (trace_length ex)) with "Hauth")
      as "[Hauth _]"; [by eauto|].
    iMod "Hclose" as "_".
    iModIntro. iFrame. simpl.
    rewrite (last_eq_trace_ends_in _ _ Hex). simpl.
    rewrite -message_history_evolution_id; iFrame.
    iSplitL "Hm".
    { iExists ex.
      iSplit.
      { iPureIntro. simpl. by eexists _. }
      rewrite /aneris_state_interp_δ. rewrite Hex. iFrame.
      iSplit; [|done].
      iPureIntro.
      eapply (locale_step_atomic _ _ _ _ _ _ _ []); try done.
      { by rewrite right_id_L. }
      apply fill_step.
      eapply head_prim_step. simpl. done. }
    iSplit; [|done]. by iApply "HΦ".
  Qed.

  Lemma wp_load n s E ζ l q v (Φ : aneris_expr → option (action aneris_lang) → iProp Σ) :
    ▷ l ↦[n]{q} v -∗
    ▷ (l ↦[n]{q} v -∗ Φ (mkExpr n v) None) -∗
    sswp s E ζ (mkExpr n (Load (Val $ LitV $ LitLoc l))) Φ.
  Proof.
    iIntros "Hl HΦ".
    rewrite /sswp.
    iSplit; [done|].
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hlocale Hex) "([Hσ Hauth] & [% Hm])".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_heap_valid with "Hσ Hl") as (h') "#>[%Hσ %Hl]".
    simpl in *.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplitR; [iPureIntro; eauto|].
    { destruct s; [|done]. do 4 eexists. eapply head_prim_step.
      eapply LocalStepS; eauto. by constructor. }
    iIntros (α v2 σ2 efs Hstep).
    apply head_reducible_prim_step in Hstep; last first.
    { do 4 eexists. eapply LocalStepS; eauto. by constructor. }
    pose proof (conj Hstep I) as Hstep'.
    inv_head_step.
    destruct Hstep' as [Hstep' _].
    iApply step_fupdN_intro; [done|].
    iIntros "!>!>".
    iModIntro. iIntros "!>".
    iMod (steps_auth_update _ (S (trace_length ex)) with "Hauth")
      as "[Hauth _]"; [by eauto|].
    iMod "Hclose" as "_".
    iModIntro. iFrame. simpl.
    rewrite (last_eq_trace_ends_in _ _ Hex). simpl.
    rewrite -message_history_evolution_id; iFrame.
    rewrite insert_id //; iFrame.
    rewrite insert_id in Hstep'=> //.
    iSplitL "Hm".
    { iExists ex.
      iSplit.
      { iPureIntro. simpl. by eexists _. }
      rewrite /aneris_state_interp_δ. rewrite Hex. iFrame.
      iSplit; [|done].
      iPureIntro.
      eapply (locale_step_atomic _ _ _ _ _ _ _ []); try done.
      { by rewrite right_id_L. }
      apply fill_step.
      eapply head_prim_step. simpl. done. }
    iSplit; [|done]. by iApply "HΦ".
  Qed.

  Lemma wp_store n s E ζ l v1 v2 (Φ : aneris_expr → option (action aneris_lang) → iProp Σ) :
    ▷ l ↦[n] v1 -∗
    ▷ (l ↦[n] v2 -∗ Φ (mkExpr n #()) None) -∗
    sswp s E ζ (mkExpr n (Store #l (Val v2))) Φ.
  Proof.
    iIntros "Hl HΦ".
    rewrite /sswp.
    iSplit; [done|].
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hlocale Hex) "([Hσ Hauth] & [% Hm])".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_heap_valid with "Hσ Hl") as (h') "#>[%Hσ %Hl]".
    simpl in *.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplitR; [iPureIntro; eauto|].
    { destruct s; [|done]. do 4 eexists. eapply head_prim_step.
      eapply LocalStepS; eauto. by constructor. }
    iIntros (α w σ2 efs Hstep).
    apply head_reducible_prim_step in Hstep; last first.
    { do 4 eexists. eapply LocalStepS; eauto. by constructor. }
    pose proof (conj Hstep I) as Hstep'.
    inv_head_step.
    destruct Hstep' as [Hstep' _].
    iApply step_fupdN_intro; [done|].
    iIntros "!>!>".
    iModIntro. iIntros "!>".
    iMod (aneris_state_interp_heap_update with "[$Hσ $Hl]") as "[Hσ Hl]";
      [done|].
    iMod (steps_auth_update _ (S (trace_length ex)) with "Hauth")
      as "[Hauth _]"; [by eauto|].
    iMod "Hclose" as "_".
    iModIntro. iFrame. simpl.
    rewrite (last_eq_trace_ends_in _ _ Hex). simpl.
    rewrite -message_history_evolution_id; iFrame.
    iSplitL "Hm".
    { iExists ex.
      iSplit.
      { iPureIntro. simpl. by eexists _. }
      rewrite /aneris_state_interp_δ. rewrite Hex. iFrame.
      iSplit; [|done].
      iPureIntro.
      eapply (locale_step_atomic _ _ _ _ _ _ _ []); try done.
      { by rewrite right_id_L. }
      apply fill_step.
      eapply head_prim_step. simpl. done. }
    iSplit; [|done]. by iApply "HΦ".
  Qed.

  Lemma wp_send φ mbody (is_dup : bool) sh skt a to k E
        ζ R T
        (Φ : (aneris_expr → option (action aneris_lang) → iProp Σ)) :
    let msg := mkMessage a to mbody in
    saddress skt = Some a →
    ▷ sh ↪[ip_of_address a] skt -∗
    ▷ a ⤳ (R, T) -∗
    ▷ to ⤇ φ -∗
    (if is_dup then ⌜msg ∈ T⌝ else ▷ φ msg) -∗
    (sh ↪[ip_of_address a] skt -∗ a ⤳ (R, {[ msg ]} ∪ T) -∗
     Φ (mkVal (ip_of_address a) #(String.length mbody)) (Some (Send msg))) -∗
    sswp k E ζ
         (mkExpr (ip_of_address a)
                 (SendTo (Val $ LitV $ LitSocket sh) #mbody #to)) Φ.
  Proof.
    iIntros (msg Hskt) "Hsh Hrt Hφ Hmsg HΦ".
    iAssert (▷ socket_address_group_own {[a]})%I as "#Ha".
    { iDestruct "Hrt" as "[(%send & %recv & _ & _ & _ & $ & _) _]". }
    iAssert (▷ socket_address_group_own {[to]})%I as "#Hto".
    { iNext. by iDestruct "Hφ" as (γ) "[H _]". }
    iDestruct "Hrt" as "[Hrt Hown]".
    rewrite /sswp.
    iSplit; [done|].
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hlocale Hex) "[[Hσ Hauth] [%Hvalid Hm]]".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    iMod "Hsh". iMod "Hrt".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_network_sockets_coh_valid with "Hσ") as %Hcoh.
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose".
    iSplitR.
    { destruct k; [|done].
      iPureIntro; do 4 eexists. eapply head_prim_step. eapply SocketStepS; eauto.
        by econstructor; naive_solver. }
    iIntros (α e2 σ2 efs Hstep).
    apply head_reducible_prim_step in Hstep; last first.
    { do 4 eexists. eapply SocketStepS; eauto. by econstructor. }
    pose proof (conj Hstep I) as Hstep'.
    inv_head_step.
    destruct Hstep' as [Hstep' _].
    iApply step_fupdN_intro; [done|].
    destruct is_dup; last first.
    - iIntros "!>!>".
      iModIntro.
      iIntros "!>".
      iMod (aneris_state_interp_send sh a {[a]} to {[to]} _ _ skt
             with "[] [] [$Hsh] [$Hrt] [Hφ] [Hmsg] [$Hσ]")
        as "(%Hmhe & Hσ & Hsh & Hrt)"; try done.
      { apply message_group_equiv_refl; try set_solver. }
      { iSplit; [|done]. iPureIntro. set_solver. }
      { iSplit; [|done]. iPureIntro. set_solver. }
      { iSplit; [|done]. done. }
      iMod "Hclose". iModIntro.
      iSplitL "Hσ Hauth Hm".
      { iFrame.
        iSplitL "Hσ".
        - simpl.
          rewrite (last_eq_trace_ends_in _ _ Hex). simpl.
          rewrite Hmhe.
          simpl.
          rewrite insert_id; [|done].
          rewrite - /msg.
          simpl.
          iFrame.
        - simpl.
          iExists ex.
          iSplit.
          { iPureIntro. simpl. by eexists _. }
          rewrite /aneris_state_interp_δ. rewrite Hex. iFrame.
          iSplit; [|done].
          iPureIntro.
          eapply (locale_step_atomic _ _ _ _ _ _ _ []); try done.
          { by rewrite right_id_L. }
          apply fill_step.
          eapply head_prim_step. simpl. done. }
      iSplit; [|done].
      iApply ("HΦ" with "Hsh [$Hrt $Hown]").
    - iIntros "!>!>".
      iModIntro.
      iIntros "!>".
      iDestruct "Hmsg" as "%Hmsg".
      iMod (aneris_state_interp_send_duplicate sh a {[a]} to {[to]} _ _ skt
             with "[] [] [$Hsh] [$Hrt] [$Hσ]")
        as "(%Hmhe & Hσ & Hsh & Hrt)"; try done.
      { eexists _. split; [done|].
        apply message_group_equiv_refl; try set_solver. }
      { iSplit; [|done]. iPureIntro. set_solver. }
      { iSplit; [|done]. iPureIntro. set_solver. }
      iMod "Hclose". iModIntro.
      iSplitL "Hσ Hauth Hm".
      { iFrame.
        iSplitL "Hσ".
        - simpl.
          rewrite (last_eq_trace_ends_in _ _ Hex). simpl.
          rewrite Hmhe.
          simpl.
          rewrite insert_id; [|done].
          rewrite - /msg.
          simpl.
          iFrame.
        - simpl.
          iExists ex.
          iSplit.
          { iPureIntro. simpl. by eexists _. }
          rewrite /aneris_state_interp_δ. rewrite Hex. iFrame.
          iSplit; [|done].
          iPureIntro.
          eapply (locale_step_atomic _ _ _ _ _ _ _ []); try done.
          { by rewrite right_id_L. }
          apply fill_step.
          eapply head_prim_step. simpl. done. }
      iSplit; [|done].
      iApply ("HΦ" with "Hsh [$Hrt $Hown]").
  Qed.

  Lemma wp_recv
        (φ : socket_interp Σ) k saR E sh skt ζ R T
        (Φ : (aneris_expr → option (action aneris_lang) → iProp Σ)) :
    saddress skt = Some saR →
    sblock skt = false →
    ▷ sh ↪[ip_of_address saR] skt -∗
    ▷ saR ⤳ (R, T) -∗
    saR ⤇ φ -∗
    (∀ om r,
       ((⌜r = NONEV⌝ ∗ ⌜om = Recv saR None⌝ ∗
        sh ↪[ip_of_address saR] skt ∗ saR ⤳ (R, T)) ∨
       (∃ msg,
           ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                             (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
           ⌜om = Recv saR (Some msg)⌝ ∗
           ⌜m_destination msg = saR⌝ ∗
           sh ↪[ip_of_address saR] skt ∗
           saR ⤳ ({[msg]} ∪ R, T) ∗
           (⌜msg ∉ R⌝ -∗ φ msg))) -∗
       Φ (mkVal (ip_of_address saR) r) (Some om)) -∗
    sswp k E ζ
         (mkExpr (ip_of_address saR)
                 (ReceiveFrom (Val $ LitV $ LitSocket sh))) Φ.
  Proof.
    iIntros (Hskt Hblock) "Hsh Hrt #Hφ HΦ".
    iAssert (▷ socket_address_group_own {[saR]})%I as "#HsaR".
    { iDestruct "Hrt" as "[(%send & %recv & _ & _ & _ & $ & _) _]". }
    iDestruct "Hrt" as "[Hrt Hown]".
    rewrite /sswp.
    iSplit; [done|].
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hlocale Hex) "[[Hσ Hauth] [%Hvalid Hm]]".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    iMod "Hsh". iMod "Hrt".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_network_sockets_coh_valid with "Hσ") as %Hcoh.
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    destruct (decide (r = [])) as [-> | Hneq].
    - iApply fupd_mask_intro; [set_solver|].
      iIntros "Hclose".
      iSplitR.
      { destruct k; [|done].
        iPureIntro; do 4 eexists. eapply head_prim_step.
        eapply SocketStepS; eauto.
        by eapply ReceiveFromNoneS. }
      iIntros (α e2 σ2 efs Hstep).
      apply head_reducible_prim_step in Hstep; last first.
      { do 4 eexists. eapply SocketStepS; eauto. by econstructor. }
      pose proof (conj Hstep I) as Hstep'.
      inv_head_step.
      { assert (length (r ++ [m]) = length ([] : list message)) as Hdone; first by f_equal.
        rewrite app_length /= in Hdone. lia. }
      2: { assert (false = true) by by rewrite -Hblock. done. }
      iIntros "!>!>".
      iModIntro.
      iApply step_fupdN_intro; [done|].
      destruct Hstep' as [Hstep' _].
      iIntros "!>".
      iMod "Hclose". iModIntro.
      simpl.
      iSplitL "Hσ Hauth Hm".
      { iFrame.
        iSplitL "Hσ".
        - simpl.
          rewrite insert_id; [|done].
          rewrite (last_eq_trace_ends_in _ _ Hex). simpl.
          rewrite -message_history_evolution_id.
          iFrame.
        - simpl.
          iExists ex.
          iSplit.
          { iPureIntro. simpl. by eexists _. }
          rewrite /aneris_state_interp_δ. rewrite Hex. iFrame.
          iSplit; [|done].
          iPureIntro.
          eapply (locale_step_atomic _ _ _ _ _ _ _ []); try done.
          { by rewrite right_id_L. }
          apply fill_step.
          eapply head_prim_step. simpl. done. }
      iSplit; [|done].
      iApply ("HΦ" with "[Hsh Hrt Hown]").
      iLeft. by iFrame.
    - iApply fupd_mask_intro; [set_solver|].
      iIntros "Hclose".
      apply last_is_Some in Hneq as [m Hneq].
      apply last_Some in Hneq as [? ->].
      iSplitR.
      { destruct k; [|done].
        iPureIntro; do 4 eexists. eapply head_prim_step.
        eapply SocketStepS; eauto.
        by eapply ReceiveFromSomeS. }
      iIntros (α e2 σ2 efs Hstep).
      apply head_reducible_prim_step in Hstep; last first.
      { do 4 eexists. eapply SocketStepS; eauto.
        by eapply ReceiveFromSomeS. }
      pose proof (conj Hstep I) as Hstep'.
      inv_head_step.
      2: { assert (length (x ++ [m]) = length ([] : list message)) as Hdone; first by f_equal.
        rewrite app_length /= in Hdone. lia. }
      2: { assert (false = true) by by rewrite -Hblock. done. }
      iDestruct (messages_mapsto_observed with "Hrt")
        as "[Hrt (%As & %Ar & _ & _ & #Hvalid & _)]".
      simpl.
      iMod "Hown".
      iMod "HsaR".
      iDestruct (aneris_state_interp_receive_some saR {[saR]} _ _ _ _ (Some (from_singleton φ))
                   with "[] [] [$Hσ] [$Hsh] [$Hrt]") as (R' sagT) "(% & [%Hhst #Hin] & %Hhist & %HR & Hrt & Hrest)"; [try set_solver..|].
      { iFrame "HsaR". iPureIntro. set_solver. }
      iMod "Hrest" as "(Hσ & Hsh & Ha)".
      iModIntro.
      simpl.
      assert (m0 = m) as ->.
      { by eapply app_inj_tail_iff. }
      assert (r = x) as ->.
      { by eapply app_inv_tail. }
      destruct (decide (m ∈ R)) as [Hin|Hnin].
      + iDestruct "Hrt" as "[Hrt|Hrt]".
        { iDestruct "Hrt" as "(%Hm & Hrt)".
          specialize (Hm m Hin).
          assert (false).
          { apply Hm. apply message_group_equiv_refl. set_solver. set_solver. }
          done. }
        iIntros "!>!>".
        iApply step_fupdN_intro; [done|].
        destruct Hstep' as [Hstep' _].
        iIntros "!>".
        iMod "Hclose". iModIntro.
        simpl.
        iSplitL "Hσ Hauth Hm".
        { iFrame.
          iSplitL "Hσ".
          - simpl.
            simpl in *.
            rewrite (last_eq_trace_ends_in _ _ Hex). simpl.
            rewrite Hhist. iFrame.
          - simpl.
            iExists ex.
            iSplit.
            { iPureIntro. simpl. by eexists _. }
            rewrite /aneris_state_interp_δ. rewrite Hex. iFrame.
            iSplit; [|done].
            iPureIntro.
            eapply (locale_step_atomic _ _ _ _ _ _ _ []); try done.
            { by rewrite right_id_L. }
            apply fill_step.
            eapply head_prim_step. simpl. done. }
        iSplit; [|done].
        iApply ("HΦ").
        iRight.
        iExists m.
        iSplit; [done|].
        iSplit; [done|].
        iFrame.
        rewrite HR. iFrame.
        simpl. replace ({[m]} ∪ R) with R by set_solver.
        iFrame. iSplit; [done|].
        iIntros (Hnin). set_solver.
      + iDestruct "Hrt" as "[Hrt|Hrt]"; last first.
        { iDestruct "Hrt" as %Hm.
          destruct Hm as [m' [Hmin Hmeq]].
          iAssert (⌜sagT = {[m_sender m']}⌝)%I as %->.
          {
            iDestruct (big_sepS_elem_of with "Hown") as "Hown_m"; [done|].
            destruct Hmeq as (Hm11 & Hm12 & _).
            iApply (socket_address_group_own_agree with "Hin Hown_m");
              set_solver.
          }
          assert (m = m').
          { destruct m, m'. rewrite /message_group_equiv in Hmeq.
            simpl in *.
            destruct Hmeq as (Hm11 & Hm12 & Hm21 & Hm22 & <-).
            (* destruct Hmeq as (<- & <- & <- & Hm1 & Hm2). *)
            assert (m_sender = m_sender0) as <- by set_solver.
            assert (m_destination = m_destination0) as <- by set_solver.
            done. }
          set_solver.
        }
        iDestruct "Hrt" as (Hall m' Hmeq) "Hrt".
        iAssert (▷ socket_address_group_own {[m_sender m']})%I as "#>Hown'".
        { iNext. iDestruct "Hrt" as "[$ Hrt]". }
        iAssert (⌜m_sender m = m_sender m'⌝)%I as %Hsender.
        {
          destruct Hmeq as (Hm11 & Hm12 & _).
          iDestruct (socket_address_group_own_agree with "Hin Hown'")
            as %->; [set_solver.. |].
          iPureIntro. set_solver. }
        assert (m = m') as <-.
        {
          destruct m. destruct m'. simpl in *.
          destruct Hmeq as (Hm11 & Hm12 & Hm21 & Hm22 & Hprot).
          repeat f_equiv; eauto. set_solver. }
        iApply step_fupdN_intro; [done|].
        destruct Hstep' as [Hstep' _].
        iIntros "!>!>!>".
        iMod "Hclose". iIntros "!>".
        simpl.
        iSplitL "Hσ Hauth Hm".
        { iFrame.
          iSplitL "Hσ".
          - simpl.
            simpl in *.
            rewrite (last_eq_trace_ends_in _ _ Hex). simpl.
            rewrite Hhist. iFrame.
          - simpl.
            iExists ex.
            iSplit.
            { iPureIntro. simpl. by eexists _. }
            rewrite /aneris_state_interp_δ. rewrite Hex. iFrame.
            iSplit; [|done].
            iPureIntro.
            eapply (locale_step_atomic _ _ _ _ _ _ _ []); try done.
            { by rewrite right_id_L. }
            apply fill_step.
            eapply head_prim_step. simpl. done. }
        iSplit; [|done].
        iApply ("HΦ").
        iRight.
        iExists m.
        iSplit; [done|].
        iSplit; [done|].
        iFrame.
        rewrite HR. iFrame.
        simpl.
        iSplit; [done|].
        iSplitL "Hown".
        { iApply big_sepS_union; [set_solver|].
          iFrame. iApply big_sepS_singleton. eauto. }
        iIntros "Hnin'".
        iDestruct "Hrt" as "[??]". iFrame.
  Qed.

  (* #[global] Instance aneris_lang_allows_stuttering : *)
  (*   AllowsStuttering (aneris_to_trace_model Mdl) Σ. *)
  (* Proof. *)
  (*   refine ({| stuttering_label := () |}). *)

  (*   iIntros (ex atr c δ ? ? Hval Hc Hδ) "(? & ? & ? & ? & Hauth)". *)
  (*   rewrite /state_interp /=. *)
  (*   rewrite (last_eq_trace_ends_in ex c) //=. *)
  (*   rewrite (last_eq_trace_ends_in atr δ) //=. *)
  (*   rewrite aneris_events_state_interp_same_tp; [| |done|done]; last first. *)
  (*   { eapply extend_valid_exec; eauto. } *)
  (*   iMod (steps_auth_update_S with "Hauth") as "Hauth". *)
  (*   iModIntro. *)
  (*   rewrite -message_history_evolution_id; iFrame. *)
  (*   iPureIntro; apply user_model_evolution_id. *)
  (* Qed. *)

  (* #[global] Instance aneris_lang_allows_pure_step : *)
  (*   AllowsPureStep (aneris_to_trace_model Mdl) Σ. *)
  (* Proof. *)
  (*   refine ({| pure_label := () |}). *)

  (*   iIntros (ex atr tp tp' σ δ ? ? ? Hex Hδ) "(?&?&?&?&Hauth)". *)
  (*   rewrite /state_interp /=. *)
  (*   rewrite (last_eq_trace_ends_in ex (tp, σ)) //=. *)
  (*   rewrite (last_eq_trace_ends_in atr δ) //=. *)
  (*   rewrite aneris_events_state_interp_pure; [| |done|done]; last first. *)
  (*   { eapply extend_valid_exec; eauto. } *)
  (*   iMod (steps_auth_update_S with "Hauth") as "Hauth". *)
  (*   iModIntro. *)
  (*   rewrite -message_history_evolution_id; iFrame. *)
  (*   iPureIntro; apply user_model_evolution_id. *)
  (* Qed. *)

End primitive_laws.
