From Paco Require Import pacotac.
From stdpp Require Import finite.
From iris.proofmode Require Import proofmode.
From trillium Require Import adequacy.
From fairneris Require Import fairness retransmit_model.
From fairneris.aneris_lang Require Import aneris_lang resources.
From fairneris.aneris_lang.state_interp Require Import state_interp_def.
From fairneris.aneris_lang.state_interp Require Import state_interp_config_wp.
From fairneris.aneris_lang.state_interp Require Import state_interp.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From fairneris Require Import from_locale_utils trace_utils ltl_lite
     partial_termination.

(* TODO: Move to stdpp *)
Lemma gset_union_difference_intersection_L `{Countable A} (X Y : gset A) :
  X = (X ∖ Y) ∪ (X ∩ Y).
Proof. rewrite union_intersection_l_L difference_union_L. set_solver. Qed.

(* TODO: Move *)
Definition tr_starts_in {S L} (tr : trace S L) (s : S) := trfirst tr = s.

Definition extrace_property {Λ} (c : cfg Λ) (Φ : extrace Λ → Prop) :=
  ∀ extr, tr_starts_in extr c → extrace_valid extr → Φ extr.

Lemma extrace_property_impl {Λ} c (Φ Ψ : extrace Λ → Prop) :
  extrace_property c Φ →
  (∀ extr, tr_starts_in extr c → extrace_valid extr → Φ extr → Ψ extr) →
  extrace_property c Ψ.
Proof. intros HΦ Himpl extr Hstarts Hvalid. by apply Himpl, HΦ. Qed.

Definition valid_state_evolution_fairness
           (extr : execution_trace aneris_lang)
           (auxtr : auxiliary_trace (fair_model_to_model retransmit_fair_model)) :=
  auxtr_valid auxtr ∧
  labels_match_trace extr auxtr ∧
  live_tids (trace_last extr) (trace_last auxtr) ∧
  config_state_valid (trace_last extr) (trace_last auxtr).

Definition trace_last_label {A L} (ft : finite_trace A L) : option L :=
  match ft with
  | {tr[a]} => None
  | _ :tr[ℓ]: _ => Some ℓ
  end.

Lemma rel_finitary_valid_state_evolution_fairness :
  rel_finitary valid_state_evolution_fairness.
Proof. Admitted.

Definition locale_dead_role_disabled (c : cfg aneris_lang)
           (δ : retransmit_state) :=
  ∀ (ℓ:fmrole retransmit_fair_model) ζ,
  roles_match ζ ℓ →
  ∀ e, from_locale c.1 ζ = Some e → is_Some (language.to_val e) →
       ¬ role_enabled_model ℓ δ.

Lemma derive_live_tid_inl c δ (ℓ : fmrole retransmit_fair_model) ζ :
  role_enabled_locale_exists c δ →
  locale_dead_role_disabled c δ →
  live_tid c δ ℓ ζ.
Proof.
  intros Himpl1 Himpl2 Hmatch Hrole.
  specialize (Himpl1 _ _ Hmatch Hrole) as [e He].
  exists e.
  split; [done|].
  destruct (language.to_val e) eqn:Heqn; [|done].
  specialize (Himpl2 _ _ Hmatch e He).
  assert (is_Some $ language.to_val e) as Hsome by done.
  by specialize (Himpl2 Hsome).
Qed.

Lemma valid_state_live_tids ex atr :
  simple_valid_state_evolution ex atr →
  locale_dead_role_disabled (trace_last ex) (trace_last atr) →
  live_tids (trace_last ex) (trace_last atr).
Proof.
  intros (_&_&Hlive1&Hnm) Hlive2 ℓ ζ Hlabels.
  by apply derive_live_tid_inl.
Qed.

Definition continued_simulation_init {Λ M}
           (ξ : execution_trace Λ → auxiliary_trace M → Prop)
           (c : cfg Λ) (s : mstate M) :=
  continued_simulation ξ {tr[c]} {tr[s]}.

Definition addrs_to_ip_ports_map (A : gset socket_address) : gmap ip_address (gset port) :=
  fold_right union ∅ $
             (λ sa, {[ip_of_address sa := {[port_of_address sa]}]}) <$> (elements A).

Definition ports_in_use (skts : gmap ip_address sockets) : gset socket_address :=
  map_fold (λ ip skts A,
              map_fold
                (λ sh skt A, match saddress skt.1 with
                             | Some a => {[a]}
                             | None => ∅
                             end ∪ A) ∅ skts ∪ A) ∅ skts.

Definition wp_proto_multiple_strong `{anerisPreG retransmit_fair_model Σ} A
           σ (s:stuckness) (es : list aneris_expr) st :=
  (∀ (aG : anerisG retransmit_fair_model Σ), ⊢ |={⊤}=>
     unallocated A -∗
     ([∗ set] sa ∈ A, sa ⤳ (∅, ∅)) -∗
     live_roles_frag_own (retransmit_live_roles st) -∗
     dead_roles_frag_own ((all_roles ∖ retransmit_live_roles st) : gset $ fmrole retransmit_fair_model) -∗
     ([∗ set] ip ∈ dom (state_heaps σ),
        ([∗ map] l ↦ v ∈ (state_heaps σ !!! ip), l ↦[ip] v) ∗
        ([∗ map] sh ↦ s ∈ (state_sockets σ !!! ip), sh ↪[ip] s.1)) -∗
     ([∗ map] ip ↦ ports ∈ (addrs_to_ip_ports_map
                              (A ∖ (ports_in_use $ state_sockets σ))),
        free_ports ip ports)%I -∗
     frag_st st -∗
     ([∗ set] ip ∈ dom (state_heaps σ), is_node ip) -∗
     aneris_state_interp σ (∅, ∅) ={⊤}=∗
     aneris_state_interp σ (∅, ∅) ∗
     wptp s es (map (λ '(tnew,e), λ v, fork_post (locale_of tnew e) v)
                    (prefixes es))).

Definition wp_proto `{anerisPreG retransmit_fair_model Σ} IPs A
           s es ip st :=
  (∀ (aG : anerisG retransmit_fair_model Σ), ⊢ |={⊤}=>
     unallocated A -∗
     ([∗ set] a ∈ A, a ⤳ (∅, ∅)) -∗
     live_roles_frag_own (retransmit_live_roles st : gset $ fmrole retransmit_fair_model) -∗
     dead_roles_frag_own ((all_roles ∖ retransmit_live_roles st) : gset $ fmrole retransmit_fair_model) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     is_node ip ={⊤}=∗
     wptp s es (map (λ '(tnew,e), λ v, fork_post (locale_of tnew e) v)
                    (prefixes es))
     (* OBS: Can add [always_holds ξ] here *)).

Theorem simulation_adequacy_multiple_strong
        `{anerisPreG retransmit_fair_model Σ}
        A s (es : list aneris_expr) σ st :
  role_enabled_locale_exists (es, σ) st →
  config_state_valid (es, σ) st →
  length es >= 1 →
  (* aneris_model_rel_finitary Mdl → *)
  dom (state_heaps σ) = dom (state_sockets σ) →
  (* Port coherence *)
  ((∀ ip ps, (GSet <$> (addrs_to_ip_ports_map
                              (A ∖ (ports_in_use $ state_sockets σ))))
               !! ip = Some (GSet ps) →
             ∀ Sn, (state_sockets σ) !! ip = Some Sn →
                   ∀ p, p ∈ ps → port_not_in_use p Sn)) →
  (* Socket buffers are initially empty *)
  map_Forall (λ ip s, map_Forall (λ sh sb, sb.2 = []) s) (state_sockets σ) →
  map_Forall (λ ip s, socket_handlers_coh s) (state_sockets σ) →
  map_Forall (λ ip s, socket_addresses_coh s ip) (state_sockets σ) →
  (* Message soup is initially empty *)
  state_ms σ = ∅ →
  wp_proto_multiple_strong A σ s es st →
  continued_simulation_init valid_state_evolution_fairness (es, σ) st.
Proof.
  intros Hexists Hconfig Hlen Hdom Hport_coh Hbuf_coh Hsh_coh Hsa_coh Hms Hwp.
  apply (wp_strong_adequacy_multiple aneris_lang
                                     (fair_model_to_model retransmit_fair_model) Σ s);
    [done| |].
  { apply rel_finitary_valid_state_evolution_fairness. }
  iIntros (?) "".
  iMod node_gnames_auth_init as (γmp) "Hmp".
  iMod saved_si_init as (γsi) "[Hsi Hsi']".
  iMod (unallocated_init (to_singletons A)) as (γsif)
    "[Hunallocated_auth Hunallocated]".
  iMod (free_ips_init ∅) as (γips) "[HIPsCtx HIPs]".
  iMod (free_ports_auth_init_multiple) as (γpiu) "[HPiu HPs]".
  iMod (allocated_address_groups_init (to_singletons ∅)) as
      (γobserved_send) "#Hobserved_send".
  iMod (allocated_address_groups_init (to_singletons ∅)) as
      (γobserved_receive) "#Hobserved_receive".
  iMod (socket_address_group_ctx_init (to_singletons A)) as (γC) "Hauth";
    [apply to_singletons_all_disjoint|].
  iMod (socket_address_group_own_alloc_subseteq_pre _ (to_singletons A)
                                                      (to_singletons A)
         with "Hauth") as
      "[Hauth HownA]"; [done|].
  iDestruct (socket_address_group_own_big_sepS with "HownA") as "#HownAS".
  iMod (messages_ctx_init (to_singletons A) _ _ _ _ with "HownAS Hobserved_send Hobserved_receive" ) as (γms) "[Hms HB]".
  iMod (steps_init 1) as (γsteps) "[Hsteps _]".
  iMod (roles_init ((retransmit_live_roles st) : gset $ fmrole retransmit_fair_model)) as (γlive) "[Hlivefull Hlivefrag]".
  iMod (roles_init ((all_roles ∖ retransmit_live_roles st) : gset $ fmrole retransmit_fair_model))
    as (γdead) "[Hdeadfull Hdeadfrag]".
  iMod (alloc_evs_init ∅) as (γalevs) "[Halobctx Halobs]".
  iMod (sendreceive_evs_init (to_singletons A)) as
      (γsendevs) "[Hsendevsctx Hsendevs]".
  iMod (sendreceive_evs_init (to_singletons A)) as
    (γreceiveevs) "[Hreceiveevsctx Hreceiveevs]".
  iMod (model_init (st:(fair_model_to_model retransmit_fair_model).(mstate))) as (γm) "[Hmfull Hmfrag]".
  set (dg :=
         {|
           aneris_node_gnames_name := γmp;
           aneris_si_name := γsi;
           aneris_socket_address_group_name := γC;
           aneris_unallocated_socket_address_groups_name := γsif;
           aneris_freeips_name := γips;
           aneris_freeports_name := γpiu;
           aneris_messages_name := γms;
           aneris_model_name := γm;
           aneris_live_roles_name := γlive;
           aneris_dead_roles_name := γdead;
           aneris_steps_name := γsteps;
           aneris_allocEVS_name := γalevs;
           aneris_sendonEVS_name := γsendevs;
           aneris_receiveonEVS_name := γreceiveevs;
           aneris_observed_send_name := γobserved_send;
           aneris_observed_recv_name := γobserved_receive;
         |}).
  iMod (Hwp dg) as "Hwp".
  iMod (is_node_alloc_multiple σ with "[Hmp]")
    as (γs Hheaps_dom' Hsockets_dom') "[Hγs [#Hn [Hσctx Hσ]]]"; [set_solver|done|].
  iExists
    (λ ex atr,
      (⌜simple_valid_state_evolution ex atr⌝ ∗
      aneris_state_interp
        (trace_last ex).2
        (trace_messages_history ex) ∗
      thread_live_roles_interp (trace_last atr) ∗
      steps_auth (trace_length ex)))%I.
  iExists (map (λ '(tnew,e) v, fork_post (locale_of tnew e) v) (prefixes es))%I,
            (fork_post)%I.
  iSplitR; [iApply config_wp_correct|].
  iMod (socket_address_group_own_alloc_subseteq_pre _
    (to_singletons A) (to_singletons A) with "Hauth")
    as "[Hauth Hown]"; [by set_solver|].
  iPoseProof (aneris_state_interp_init_strong ∅ (to_singletons A)
    (addrs_to_ip_ports_map (A ∖ ports_in_use (state_sockets σ))) with
               "Hγs Hσctx Hms [$Hauth $Hown]
               Hunallocated_auth Hsi HIPsCtx HPiu") as "Hinterp";
    [set_solver|set_solver|set_solver|done|done|done|done|done|done|done| |..].
  { iPureIntro. apply to_singletons_is_ne. }
  iDestruct ("Hwp" with "Hunallocated [HB] Hlivefrag Hdeadfrag Hσ HPs Hmfrag Hn Hinterp")
    as ">[Hσ $]".
  { iApply (big_sepS_to_singletons with "[] HB").
    iIntros "!>" (sa).
    iDestruct 1 as (As' Ar') "(?&?&[%HAs' %HAr']&$&$)".
    simpl. iSplit; [|done].
    iExists _, _. iFrame.
    iPureIntro. set_solver. }
  simpl. rewrite Hms=> /=. rewrite dom_empty_L.
  iFrame.
  iModIntro.
  iSplit.
  { iPureIntro. split; [by constructor|done]. }
  iIntros (ex atr c Hvalex Hstartex Hstartatr Hendex Hcontr Hstuck Htake)
          "Hsi Hposts".
  iDestruct "Hsi" as "(%Hvalid&_&Hlive&_)".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "_".
  iAssert (⌜locale_dead_role_disabled c (trace_last atr)⌝)%I as "%Hrole".
  { iIntros (ℓ ζ Hmatch e Hlocale Hval).
    iAssert (dead_role_frag_own ℓ)%I with "[Hposts]" as "H".
    { rewrite -map_app -prefixes_from_app.
      iDestruct (posts_of_length_drop with "Hposts") as "Hposts"; [done|].
      destruct Hval as [v Hv].
      iDestruct (posts_of_idx with "Hposts") as (ℓ' Hmatch') "H"; [done|done|].
      rewrite /roles_match in Hmatch.
      rewrite /roles_match in Hmatch'.
      rewrite -Hmatch in Hmatch'. simplify_eq. done. }
    simpl in *.
    iDestruct "Hlive" as "(_&Hdead)".
    iDestruct (dead_role_auth_elem_of with "Hdead H") as %Hin.
    iPureIntro.
    intros Hneq.
    rewrite /role_enabled_model in Hneq.
    set_solver. }
  iPureIntro.
  pose proof Hvalid as Hvalid'.
  destruct Hvalid as (Htrace&Hlabels&Hstate&Hconfig').
  split; [done|].
  split; [done|].
  split; [|done].
  apply valid_state_live_tids; [done|].
  by rewrite Hendex.
Qed.

Definition auxtrace (M : Model) := trace (M.(mstate)) (M.(mlabel)).

Lemma valid_inf_system_trace_implies_traces_match_strong {Λ} {Mdl:Model}
      (φ : execution_trace Λ → auxiliary_trace Mdl → Prop)
      (Rs : _ → _ → Prop) (Rℓ : _ → _ → Prop)
      ex atr iex iatr progtr auxtr :
  (∀ extr auxtr, φ extr auxtr → Rs (trace_last extr) (trace_last auxtr)) →
  (∀ extr auxtr, φ extr auxtr →
                 ∀ ζ ℓ, trace_last_label extr = Some ζ →
                        trace_last_label auxtr = Some ℓ →
                        Rℓ ζ ℓ) →
  (∀ extr auxtr, φ extr auxtr →
                 match extr, auxtr with
                 | _ :tr[_]: _, auxtr :tr[ℓ]: ρ =>
                     Mdl.(mtrans) (trace_last auxtr) ℓ ρ
                 | _,_ => True
                 end) →
  exec_trace_match ex iex progtr →
  exec_trace_match atr iatr auxtr →
  valid_inf_system_trace φ ex atr iex iatr →
  traces_match Rℓ Rs locale_step mtrans progtr auxtr.
Proof.
  intros Hφ1 Hφ2 Hφ3.
  revert ex atr iex iatr auxtr progtr. cofix IH.
  intros ex atr iex iatr auxtr progtr Hem Ham Hval.
  inversion Hval as [?? Hphi |ex' atr' c [? σ'] δ' iex' iatr' oζ ℓ Hphi [=] ? Hinf]; simplify_eq.
  - inversion Hem; inversion Ham. econstructor; eauto.
    pose proof (Hφ1 ex atr Hphi). simplify_eq. by eapply Hφ1.
  - inversion Hem; inversion Ham. subst.
    pose proof (valid_inf_system_trace_inv _ _ _ _ _ Hinf) as Hphi'.
    econstructor.
    + eauto.
    + eauto.
    + match goal with
      | [H: exec_trace_match _ iex' _ |- _] => inversion H; clear H; simplify_eq
      end; done.
    + match goal with
      | [H: exec_trace_match _ iatr' _ |- _] => inversion H; clear H; simplify_eq
      end; by eapply (Hφ3 (ex :tr[ oζ ]: (l, σ')) (atr :tr[ ℓ ]: δ')).
    + eapply IH; eauto.
Qed.

(* OBS: This is not needed. *)
Lemma valid_inf_system_trace_implies_traces_match
      ex atr iex iatr progtr auxtr :
  exec_trace_match ex iex progtr →
  exec_trace_match atr iatr auxtr →
  valid_inf_system_trace
    (continued_simulation valid_state_evolution_fairness) ex atr iex iatr →
  live_traces_match progtr auxtr.
Proof.
  intros.
  eapply (valid_inf_system_trace_implies_traces_match_strong
          (continued_simulation valid_state_evolution_fairness)); [| | |done..].
  - by intros ?? (?&?&?&?)%continued_simulation_rel.
  - intros [][] (?&?&?)%continued_simulation_rel; try done.
    intros. simpl in *. by simplify_eq.
  - intros [][] (Hvalid&?&?)%continued_simulation_rel; try done.
    simpl in *. inversion Hvalid. simplify_eq. by rewrite H7.
Qed.

Definition extrace_matching_mtrace_exists
           {Λ} {M} (Rs : cfg Λ → M.(mstate) → Prop) Rℓ st extr :=
  ∃ mtr, trfirst mtr = st ∧
         traces_match Rℓ Rs language.locale_step (M.(mtrans)) extr mtr.

Lemma continued_simulation_traces_match {Λ} {M}
      (ξ : _ → _ → Prop) (Rs : cfg Λ → M.(mstate) → Prop) (Rℓ : _ → _ → Prop)
      extr st :
  (∀ extr auxtr, continued_simulation ξ extr auxtr →
                 Rs (trace_last extr) (trace_last auxtr)) →
  (∀ extr auxtr, continued_simulation ξ extr auxtr →
                 ∀ ζ ℓ, trace_last_label extr = Some ζ →
                        trace_last_label auxtr = Some ℓ →
                        Rℓ ζ ℓ) →
  (∀ extr auxtr, continued_simulation ξ extr auxtr →
                 match extr, auxtr with
                 | _ :tr[_]: _, auxtr :tr[ℓ]: ρ =>
                     mtrans (trace_last auxtr) ℓ ρ
                 | _,_ => True
                 end) →
  extrace_valid extr →
  continued_simulation_init ξ (trfirst extr) st →
  extrace_matching_mtrace_exists Rs Rℓ st extr.
Proof.
  intros HRs HRℓ Htrans Hvalid Hsim.
  assert (∃ iatr,
             valid_inf_system_trace
               (continued_simulation ξ)
               (trace_singleton (trfirst extr))
               (trace_singleton (st))
               (from_trace extr)
               iatr) as [iatr Hiatr].
  { eexists _. eapply produced_inf_aux_trace_valid_inf. econstructor.
    Unshelve.
    - done.
    - eapply from_trace_preserves_validity; eauto; first econstructor. }
  eexists _.
  split; last first.
  { eapply (valid_inf_system_trace_implies_traces_match_strong); eauto.
    - by apply from_trace_spec.
    - by apply to_trace_spec. }
  destruct iatr; [done|by destruct x].
Qed.

Definition extrace_matching_mtrace_exists_live st extr :=
  extrace_matching_mtrace_exists (live_tids : cfg aneris_lang → mstate (fair_model_to_model retransmit_fair_model) → Prop) labels_match st extr.

Lemma continued_simulation_traces_match_live extr st :
  extrace_valid extr →
  continued_simulation_init valid_state_evolution_fairness
                       (trfirst extr) st →
  extrace_matching_mtrace_exists_live st extr.
Proof.
  intros. eapply continued_simulation_traces_match; eauto.
  - by intros ?? (?&?&?&?)%continued_simulation_rel.
  - intros [][] (?&?&?)%continued_simulation_rel; try done.
    intros. simpl in *. by simplify_eq.
  - intros [][] (Hvalid&?&?)%continued_simulation_rel; try done.
    simpl in *. inversion Hvalid. simplify_eq. by rewrite H6.
Qed.

Definition matching_mtrace_exists c st :=
  extrace_property c (extrace_matching_mtrace_exists_live st).

(** A continued simulation exists between some initial configuration [c]
    and the initial state [init_state] of a fair model. *)
Definition live_simulation (c : cfg aneris_lang) (st : retransmit_state) :=
  continued_simulation_init valid_state_evolution_fairness c st.

Lemma continued_simulation_traces_match_init c st :
  live_simulation c st → matching_mtrace_exists c st.
Proof.
  intros Hsim extr <- Hvalid.
  apply (continued_simulation_traces_match_live) in Hsim
      as (mtr & Hmtr & Hmatch); [by eexists _|done].
Qed.

Definition extrace_fairly_terminating_locale ζ (extr : extrace aneris_lang) :=
  extrace_fair extr -> extrace_terminating_locale ζ extr.

Definition fairly_terminating ζ (c : cfg aneris_lang) :=
  extrace_property c (extrace_fairly_terminating_locale ζ).

Lemma traces_match_fair_termination_preserved_init c st :
  matching_mtrace_exists c st → fairly_terminating localeB c.
Proof.
  intros Hmatches.
  eapply extrace_property_impl; [done|].
  intros extr Hstart Hvalid (mtr & Hstart' & Hmtr) Hfair.
  eapply terminating_role_preserved;
    [done|done|done|].
  apply retransmit_fair_traces_terminate.
  - by eapply traces_match_valid_preserved.
  - by eapply traces_match_fairness_preserved.
Qed.

Theorem continued_simulation_fair_termination c st :
  live_simulation c st → fairly_terminating localeB c.
Proof.
  intros ?.
  by eapply traces_match_fair_termination_preserved_init,
    continued_simulation_traces_match_init.
Qed.

Theorem simulation_adequacy_fair_termination_multiple
        `{anerisPreG retransmit_fair_model Σ}
        A s (es : list aneris_expr) σ st :
  role_enabled_locale_exists (es, σ) st →
  config_state_valid (es, σ) st →
  length es >= 1 →
  (* aneris_model_rel_finitary Mdl → *)
  dom (state_heaps σ) = dom (state_sockets σ) →
  (* Port coherence *)
  ((∀ ip ps, (GSet <$> (addrs_to_ip_ports_map
                              (A ∖ (ports_in_use $ state_sockets σ))))
               !! ip = Some (GSet ps) →
             ∀ Sn, (state_sockets σ) !! ip = Some Sn →
                   ∀ p, p ∈ ps → port_not_in_use p Sn)) →
  (* Socket buffers are initially empty *)
  map_Forall (λ ip s, map_Forall (λ sh sb, sb.2 = []) s) (state_sockets σ) →
  map_Forall (λ ip s, socket_handlers_coh s) (state_sockets σ) →
  map_Forall (λ ip s, socket_addresses_coh s ip) (state_sockets σ) →
  (* Message soup is initially empty *)
  state_ms σ = ∅ →
  wp_proto_multiple_strong A σ s es st (* φs *) →
  fairly_terminating localeB (es,σ).
Proof.
  intros. eapply continued_simulation_fair_termination,
            simulation_adequacy_multiple_strong; try done.
Qed.
