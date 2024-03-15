From RecordUpdate Require Import RecordSet.
From stdpp Require Import binders.
From iris.proofmode Require Import tactics.
From trillium.program_logic Require Import weakestpre lifting ectx_lifting atomic.
From fairneris.aneris_lang Require Import aneris_lang base_lang.
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

Class AsRecV (v : val) (f x : binder) (erec : expr) :=
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

Section primitive_laws.
  Context `{LM: LiveModel aneris_lang Mod}.
  Context `{aG : !anerisG LM Σ}.

  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : aneris_val → iProp Σ.
  Implicit Types v : val.
  Implicit Types e : expr.
  Implicit Types σ : base_lang.state.
  Implicit Types M R T : message_soup.
  Implicit Types m : message.
  Implicit Types A B : gset socket_address.
  Implicit Types a : socket_address.
  Implicit Types ip : ip_address.
  Implicit Types sh : socket_handle.
  Implicit Types skt : socket.
  Implicit Types mh : messages_history.

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
