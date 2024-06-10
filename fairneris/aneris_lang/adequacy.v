From Paco Require Import pacotac.
From stdpp Require Import finite.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From trillium Require Import adequacy.
From trillium.prelude Require Import relations.
From fairneris Require Import fairness fair_resources.
From fairneris.aneris_lang Require Import aneris_lang resources network_model.
From fairneris.aneris_lang.state_interp Require Import state_interp_def.
From fairneris.aneris_lang.state_interp Require Import state_interp_config_wp.
From fairneris.aneris_lang.state_interp Require Import state_interp.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From fairneris Require Import from_locale_utils trace_utils ltl_lite fuel_jm_scheduling_fairness.

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

Definition valid_state_evolution_fairness `(LM: LiveModel aneris_lang (joint_model M Net))
           (inv : M → Prop)
           (extr : execution_trace aneris_lang)
           (auxtr : auxiliary_trace (live_model_to_model LM)) :=
  trace_steps LM.(lm_ls_trans) auxtr ∧
  trace_labels_match extr auxtr ∧
  live_tids (LM := LM) (trace_last extr) (trace_last auxtr) ∧
  inv (trace_last auxtr).(ls_under).1.

Definition trace_last_label {A L} (ft : finite_trace A L) : option L :=
  match ft with
  | {tr[a]} => None
  | _ :tr[ℓ]: _ => Some ℓ
  end.

Lemma rel_finitary_valid_state_evolution_fairness `(LM: LiveModel aneris_lang (joint_model M Net)) inv:
  rel_finitary (valid_state_evolution_fairness LM inv).
Proof. Admitted.

(* Lemma derive_live_tid_inl c δ (ℓ : fmrole retransmit_fair_model) ζ : *)
(*   role_enabled_locale_exists c δ → *)
(*   locale_dead_role_disabled c δ → *)
(*   live_tid c δ ℓ ζ. *)
(* Proof. *)
(*   intros Himpl1 Himpl2 Hmatch Hrole. *)
(*   specialize (Himpl1 _ _ Hmatch Hrole) as [e He]. *)
(*   exists e. *)
(*   split; [done|]. *)
(*   destruct (language.to_val e) eqn:Heqn; [|done]. *)
(*   specialize (Himpl2 _ _ Hmatch e He). *)
(*   assert (is_Some $ language.to_val e) as Hsome by done. *)
(*   by specialize (Himpl2 Hsome). *)
(* Qed. *)

(* Lemma valid_state_live_tids ex atr : *)
(*   simple_valid_state_evolution ex atr → *)
(*   locale_dead_role_disabled (trace_last ex) (trace_last atr) → *)
(*   live_tids (trace_last ex) (trace_last atr). *)
(* Proof. *)
(*   intros (_&_&Hlive1&Hnm) Hlive2 ℓ ζ Hlabels. *)
(*   by apply derive_live_tid_inl. *)
(* Qed. *)

(* Lemma posts_of_empty_mapping `(M: UserModel aneris_lang) `{@anerisG M net_model LM Σ} *)
(*   (e1 e: aneris_expr) v (tid : locale aneris_lang) (tp : list aneris_expr): *)
(*   from_locale tp tid = Some e -> *)
(*   to_val e = Some v -> *)
(*   posts_of tp *)
(*     ((λ (_ : aneris_val), (locale_of [] e) ↦M ∅) :: (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [e1] (drop (length [e1]) tp)))) -∗ *)
(*   tid ↦M (∅ : gmap (usr_role M) nat). *)
(* Proof. *)
(*   intros Hsome Hval. simpl. *)
(*   rewrite (big_sepL_elem_of (λ x, x.2 x.1) _ (v, (λ _: val, tid ↦M ∅)%I) _) //. *)
(*   apply elem_of_list_omap. *)
(*   exists (e, (λ _: val, tid ↦M ∅)%I); split; last first. *)
(*   - simpl. apply fmap_Some. exists v. split; done. *)
(*   - destruct tp as [|e1' tp]; first set_solver. simpl. *)
(*     apply elem_of_cons. *)
(*     destruct tid as [|tid]; [left|right]; first by simpl in Hsome; simplify_eq. *)
(*     apply elem_of_lookup_zip_with. eexists tid, e, _. do 2 split =>//. *)
(*     rewrite /locale_of /=. *)
(*     rewrite list_lookup_fmap fmap_Some. simpl in Hsome. *)
(*     exists (e1 :: take tid tp, e). rewrite drop_0. split. *)
(*     + erewrite prefixes_from_lookup =>//. *)
(*     + rewrite /locale_of /= take_length_le //. *)
(*       assert (tid < length tp)%nat; last lia. by eapply lookup_lt_Some. *)
(* Qed. *)

Definition continued_simulation_init {Λ M}
           (ξ : execution_trace Λ → auxiliary_trace M → Prop)
           (c : cfg Λ) (s : mstate M) :=
  continued_simulation ξ {tr[c]} {tr[s]}.

Definition addrs_to_ip_ports_map (A : gset socket_address) : gmap ip_address (gset port) :=
  set_fold (λ sa R, <[ ip_of_address sa := {[ port_of_address sa ]} ]> R) ∅ A.

Definition ports_in_use (skts : gmap ip_address sockets) : gset socket_address :=
  map_fold (λ ip skts A,
              map_fold
                (λ sh skt A, match saddress skt.1 with
                             | Some a => {[a]}
                             | None => ∅
                             end ∪ A) ∅ skts ∪ A) ∅ skts.

Lemma ports_in_use_empty skts :
  (∀ ip m, skts !! ip = Some m → m = ∅) →
  ports_in_use skts = ∅.
Proof.
  induction skts as [|ip m skts Hnew IH] using map_ind; first naive_solver.
  intros Hemp. rewrite /ports_in_use. rewrite map_fold_insert=>//.
  - rewrite /ports_in_use in IH. rewrite IH ?union_empty_r_L.
    + ospecialize (Hemp ip _ _); first rewrite lookup_insert //. rewrite Hemp map_fold_empty //.
    + intros ip' m' Hlk. eapply (Hemp ip')=>//. rewrite lookup_insert_ne //. naive_solver.
  - intros j1 j2 z1 z2 y Hneq Hlk1%Hemp Hlk2%Hemp; simplify_eq. rewrite map_fold_empty //.
Qed.

Definition initial_fuel_map_from `(M: UserModel aneris_lang) `{LMeq: !LiveModelEq LM} `{@anerisPreG M net_model LM LMeq Σ}
  (tp0 : list aneris_expr)
  (es: list aneris_expr) (fss: list (gset M.(usr_role))) (st : M) : gmap aneris_locale (gmap _ _) :=
  let esfss := zip (prefixes_from tp0 es) fss in
  foldr (λ '((tp, e), fs) fss, <[ locale_of tp e := gset_to_gmap (usr_fl st) fs]> fss) ∅ esfss.

Definition initial_fuel_map `(M: UserModel aneris_lang) `{LMeq: !LiveModelEq LM} `{@anerisPreG M net_model LM LMeq Σ} :=
  initial_fuel_map_from M nil.

Definition wp_proto_multiple_strong
  `(M: UserModel aneris_lang)
  (inv : M → Prop)
  `{LM: LiveModel aneris_lang (joint_model M net_model)}
  `{LMeq: !LiveModelEq LM} `{@anerisPreG M net_model LM LMeq Σ}
  (A: gset socket_address) (σ: aneris_lang.state) (s:stuckness) (es : list aneris_expr) (FR: gset (usr_role M))
  (st: M) (fss: list (gset M.(usr_role))):=
  (∀ (aG : anerisG LM Σ),  ⊢ |={⊤}=>
     unallocated A -∗
     ([∗ set] sa ∈ A, sa ⤳ (∅, ∅)) -∗
     ([∗ set] ip ∈ dom (state_heaps σ),
        ([∗ map] l ↦ v ∈ (state_heaps σ !!! ip), l ↦[ip] v) ∗
        ([∗ map] sh ↦ s ∈ (state_sockets σ !!! ip), sh ↪[ip] s.1)) -∗
     ([∗ map] ip ↦ ports ∈ (addrs_to_ip_ports_map
                              (A ∖ (ports_in_use $ state_sockets σ))),
        free_ports ip ports)%I -∗
     frag_model_is st -∗
     frag_free_roles_are (FR ∖ usr_live_roles st) -∗
     ([∗ map] ζ ↦ fs ∈ (initial_fuel_map M es fss st), ζ ↦M fs) -∗
     ([∗ set] ip ∈ dom (state_heaps σ), is_node ip) -∗
     aneris_state_interp σ (∅, ∅) ={⊤}=∗
     ((aneris_state_interp σ (∅, ∅)) : iProp Σ) ∗
     (□ ∀ st, auth_model_is st ={⊤, ∅}=∗ ⌜ inv st ⌝ ∗ auth_model_is st) ∗
     wptp s es (fmap (λ '(tnew,e), λ v, fork_post (locale_of tnew e) v)
                    (prefixes es))).

(* Definition wp_proto `{anerisPreG retransmit_fair_model Σ} IPs A *)
(*            s es ip st := *)
(*   (∀ (aG : anerisG retransmit_fair_model Σ), ⊢ |={⊤}=> *)
(*      unallocated A -∗ *)
(*      ([∗ set] a ∈ A, a ⤳ (∅, ∅)) -∗ *)
(*      live_roles_frag_own (retransmit_live_roles st : gset $ fmrole retransmit_fair_model) -∗ *)
(*      dead_roles_frag_own ((all_roles ∖ retransmit_live_roles st) : gset $ fmrole retransmit_fair_model) -∗ *)
(*      ([∗ set] i ∈ IPs, free_ip i) -∗ *)
(*      is_node ip ={⊤}=∗ *)
(*      wptp s es (map (λ '(tnew,e), λ v, fork_post (locale_of tnew e) v) *)
(*                     (prefixes es)) *)
(*      (* OBS: Can add [always_holds ξ] here *)). *)

Definition good_fuel_alloc
  `{M: UserModel aneris_lang} `{@anerisPreG M net_model LM LMeq Σ} {HLMEq: LiveModelEq LM}
  (es : list aneris_expr) (st : lts_state M) (fss : list $ gset (usr_role M)) :=
    (length es = length fss) ∧
    (∀ (n1 n2 : nat) fs1 fs2, n1 ≠ n2 → fss !! n1 = Some fs1 → fss !! n2 = Some fs2 → fs1 ## fs2) ∧
    (∀ ρ, ρ ∈ usr_live_roles st → ∃ n fs, fss !! n = Some fs ∧ ρ ∈ fs).

Lemma initial_fuel_map_inv'
  `{M: UserModel aneris_lang} `{@anerisPreG M net_model LM LMeq Σ} {HLMEq: LiveModelEq LM}
  (tp0 es : list aneris_expr)
  (st : lts_state M) fss ζ (fs : gmap _ _):
  initial_fuel_map_from M tp0 es fss st !! ζ = Some fs →
    ∃ n e, fss !! n = Some (dom fs) ∧
           es !! n = Some e ∧
           ζ = locale_of (tp0 ++ take n es) e.
Proof.
  revert tp0 fs fss. induction es as [|e es IH]; first naive_solver.
  intros tp0 fs fss. rewrite /initial_fuel_map /initial_fuel_map_from /=.
  destruct fss as [|fs' fss]; first naive_solver. simpl.
  destruct (decide (ζ = locale_of tp0 e)) as [->|Hneq].
  { rewrite lookup_insert. intros; simplify_eq. exists 0, e.
    rewrite dom_gset_to_gmap /=. list_simplifier. naive_solver. }
  rewrite lookup_insert_ne //.
  intros Hlk.
  destruct (IH _ _ _ Hlk) as (n&fs''&?&?&?).
  eexists (1+n), fs''. simpl. list_simplifier. naive_solver.
Qed.

Lemma initial_fuel_map_inv
  `{M: UserModel aneris_lang} `{@anerisPreG M net_model LM LMeq Σ} {HLMEq: LiveModelEq LM}
  (es : list aneris_expr)
  (st : lts_state M) fss ζ (fs : gmap _ _):
  initial_fuel_map M es fss st !! ζ = Some fs →
    ∃ n e, fss !! n = Some (dom fs) ∧
           es !! n = Some e ∧
           ζ = locale_of (take n es) e.
Proof. intros ?%initial_fuel_map_inv'. naive_solver. Qed.


Program Definition lm_init
  `{M: UserModel aneris_lang} `{@anerisPreG M net_model LM LMeq Σ} {HLMEq: LiveModelEq LM}
  (es : list aneris_expr)
  (st : lts_state M) fss net_init
  (Hfss: good_fuel_alloc es st fss)
  : mstate LM :=
{|
  ls_data := {|
              ls_under := (st, net_init);
              ls_map := initial_fuel_map M es fss st;
  |}
|}.
Next Obligation.
  simpl. intros M LM LMeq Σ Haneris Hlmeq es st fss ? [Hlen [Hgood _]] ζ1 ζ2 fs1 fs2 Hneq.
  intros (n1&?&?&?&?)%initial_fuel_map_inv.
  intros (n2&?&?&?&?)%initial_fuel_map_inv.
  apply map_disjoint_dom_2. eapply Hgood; try eassumption.
  intros Heq. simplify_eq.
Qed.
Next Obligation.
  simpl. intros M LM LMeq Σ Haneris Hlmeq es st fss ? [Hlen [_ Hgood]] ρ Hin.
  rewrite /initial_fuel_map. destruct (Hgood _ Hin) as (n&fs&HSome&Hinfs).
  destruct (es !! n) as [e|] eqn:Heq; last first.
  { apply lookup_ge_None_1 in Heq. apply lookup_lt_Some in HSome. lia. }
  exists (locale_of (take n es) e). exists (gset_to_gmap (usr_fl st) fs).
  split; last by rewrite dom_gset_to_gmap //.
  pose ctx := @nil aneris_expr.

  have // : foldr
    (λ '(tp, e0, fs0) (fss0 : gmap aneris_locale (gmap (usr_role M) nat)),
       <[locale_of tp e0:=gset_to_gmap (usr_fl st) fs0]> fss0) ∅ (zip (prefixes_from ctx es) fss)
  !! locale_of (ctx ++ take n es) e = Some (gset_to_gmap (usr_fl st) fs).

  generalize ctx. clear ctx.
  clear ρ Hinfs Hin Hgood.
  revert n e fss Hlen fs Heq HSome.

  induction es as [|e' es IH].
  { move=> [] //. }
  intros n e fss Hlen fs Heq HSome ctx. destruct fss as [|fs' fss] =>//.
  simpl.
  destruct n as [|n].
  { simpl in *. list_simplifier. rewrite lookup_insert //. }
  rewrite /=.

  rewrite lookup_insert_ne; last first.
  { eapply (locale_injective _ _ (take n es ++ [e])).
    rewrite prefixes_from_app. apply elem_of_app; right.
    simpl. list_simplifier. by apply elem_of_list_singleton. }

  replace (ctx ++ e' :: take n es) with ((ctx ++ [e'] ++ take n es)); last by list_simplifier.

  list_simplifier.
  ospecialize (IH n e fss Hlen _ Heq HSome (ctx ++ [e'])).
  list_simplifier.
  rewrite IH //.
Qed.


Theorem simulation_adequacy_multiple_strong
        `(M: UserModel aneris_lang) `{@anerisPreG M net_model LM LMeq Σ}
        A s (es : list aneris_expr) σ st fss FR net_init
        (Hfss: good_fuel_alloc es st fss) inv :
  length es >= 1 →
  (* aneris_model_rel_finitary Mdl → *)
  dom (state_heaps σ) = dom (state_sockets σ) →
  config_net_match (es, σ) net_init →
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
  wp_proto_multiple_strong M inv A σ s es FR st fss →
  continued_simulation_init (valid_state_evolution_fairness LM inv) (es, σ) (lm_init es st fss net_init Hfss).
Proof.
  intros Hlen Hdom Hnetinit Hport_coh Hbuf_coh Hsh_coh Hsa_coh Hms Hwp.
  apply (wp_strong_adequacy_multiple aneris_lang
                                     (live_model_to_model LM) Σ s);
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
  iMod (alloc_evs_init ∅) as (γalevs) "[Halobctx Halobs]".
  iMod (sendreceive_evs_init (to_singletons A)) as
      (γsendevs) "[Hsendevsctx Hsendevs]".
  iMod (sendreceive_evs_init (to_singletons A)) as
    (γreceiveevs) "[Hreceiveevsctx Hreceiveevs]".
  iMod (model_state_init st) as (γmod) "[Hmoda Hmodf]".
  iMod (model_fuel_mapping_init_gen (initial_fuel_map M es fss st)) as (γmap) "[Hmapa Hmapf]".
  iMod (model_free_roles_init st (FR ∖ usr_live_roles st)) as (γfr) "[HFR Hfr]".
  set (dg :=
         {|
           aneris_node_gnames_name := γmp;
           aneris_si_name := γsi;
           aneris_socket_address_group_name := γC;
           aneris_unallocated_socket_address_groups_name := γsif;
           aneris_freeips_name := γips;
           aneris_freeports_name := γpiu;
           aneris_messages_name := γms;
           aneris_steps_name := γsteps;
           aneris_allocEVS_name := γalevs;
           aneris_sendonEVS_name := γsendevs;
           aneris_receiveonEVS_name := γreceiveevs;
           aneris_observed_send_name := γobserved_send;
           aneris_observed_recv_name := γobserved_receive;
           aneris_fairnessG := {|
                              fairness_model_name := γmod;
                              fairness_model_fuel_mapping_name := γmap;
                              fairness_model_free_roles_name := γfr;
                              |}
         |}).
  iMod (Hwp dg) as "Hwp".
  iMod (is_node_alloc_multiple σ with "[Hmp]")
    as (γs Hheaps_dom' Hsockets_dom') "[Hγs [#Hn [Hσctx Hσ]]]"; [set_solver|done|].
  iExists (@state_interp aneris_lang LM Σ (@anerisG_irisG M net_model LM LMeq Σ dg)).
  iExists (fmap (λ '(tnew,e) v, fork_post (locale_of tnew e) v) (prefixes es))%I,
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
  iSpecialize ("Hwp" with "Hunallocated [HB] Hσ HPs Hmodf Hfr [Hmapf] Hn Hinterp").
  { iApply (big_sepS_to_singletons with "[] HB").
    iIntros "!>" (sa).
    iDestruct 1 as (As' Ar') "(?&?&[%HAs' %HAr']&$&$)".
    simpl. iSplit; [|done].
    iExists _, _. iFrame.
    iPureIntro. set_solver. }
  { rewrite /has_fuels /frag_fuel_mapping_is. simpl.
    rewrite -big_opM_own_1.
    rewrite -big_opM_auth_frag.
    iApply (fair_resources.own_proper with "Hmapf").
    f_equiv.
    (* rewrite leibniz_equiv_iff. *)
    transitivity (([^ op map] k↦x ∈ Excl <$> initial_fuel_map M es fss st,
                     {[k := x]} : gmap.gmapUR _ (exclR (gmap.gmapUR _ natO)))); last first.
    { rewrite (big_opM_fmap). f_equiv. intros ??. rewrite map_fmap_singleton //. }
    rewrite gmap.big_opM_singletons //. }
  iDestruct ("Hwp") as ">(Hσ & #Hinv & $)".
  simpl. rewrite /aneris_state_interp_opt /aneris_state_interp_σ /aneris_state_interp_δ /= Hms /= dom_empty_L.
  iFrame.
  iModIntro.
  iSplitL "Hmapa"; first iSplit.
  { iPureIntro. rewrite /fuel.valid_state_evolution_fairness /=. split; [constructor|split=>//].
    intros ζ Hin. rewrite /lm_init /= in Hin.
    apply elem_of_dom in Hin as [fs Hfs].
    apply initial_fuel_map_inv in Hfs as (n&e&?&Hlk&->).
    exists e. apply from_locale_from_Some. apply prefixes_from_spec. list_simplifier.
    apply take_drop_middle in Hlk. naive_solver. }
  { rewrite /model_state_interp. iExists _.
    rewrite /usr_state. iFrame.
    (iSplit; [|iSplit;[|iSplit; [|iSplit]]]); iPureIntro; simpl=>//.
    - intros ρ Hlive.
      change (initial_fuel_map M es fss st) with (ls_map (lm_init es st fss net_init Hfss)).
      by apply (ls_map_live (lm_init es st fss net_init Hfss)) in Hlive.
    - intros ζ Hnotin. destruct (initial_fuel_map M es fss st !! ζ) as [fs|] eqn:Heq=>//;
        last rewrite Heq //. exfalso.
      apply initial_fuel_map_inv in Heq as (n&e&?&Hlk&->).
      apply Hnotin.
      apply locales_of_list_from_locale_from.
      exists e. apply from_locale_from_Some. apply prefixes_from_spec. list_simplifier.
      apply take_drop_middle in Hlk. naive_solver.
    - intros ip Sn Hlk. split_and!.
      + apply (map_Forall_lookup_1 _ _ _ _ Hsh_coh Hlk).
      + intros ???? Hlk' ?.
        have Hfa := map_Forall_lookup_1 _ _ _ _ Hbuf_coh Hlk.
        have /= -> := map_Forall_lookup_1 _ _ _ _ Hfa Hlk'.
        set_solver.
      + apply (map_Forall_lookup_1 _ _ _ _ Hsa_coh Hlk).
      + intros ??? Hlk' ?.
        have Hfa := map_Forall_lookup_1 _ _ _ _ Hbuf_coh Hlk.
        apply (map_Forall_lookup_1 _ _ _ _ Hfa Hlk'). }

  iIntros (ex atr c Hvalex Hstartex Hstartatr Hendex Hcontr Hstuck Htake)
          "Hsi Hposts".
  iDestruct "Hsi" as "(Hasi&%Hvalid&Hmod)".

  iAssert (|={⊤, ∅}=>
             ⌜inv (trace_last atr).(ls_under).1⌝ ∗ model_state_interp (trace_last ex) (trace_last atr))%I with "[Hmod]" as "H".
  { iDestruct "Hmod" as "(%fm & ? & ? & ? & Hmod & ? & ? &?)".
    iMod ("Hinv" with "[Hmod]") as "[%SS Hmod]". iFrame.
    iModIntro. iSplit; first done. iExists fm. iFrame. }
  iMod "H" as "[%Hinv' Hmod]".

  (* iApply fupd_mask_intro; [set_solver|]. *)
  (* iIntros "_". *)
  iModIntro.
  pose proof Hvalid as Hvalid'.
  rewrite /fuel.valid_state_evolution_fairness in Hvalid.
  destruct Hvalid as (Hsteps&Hlabs&Htids).
  iSplit; [done|].
  iSplit; [done|].
  iSplit; [iSplit|done].
  { iPureIntro. rewrite /tids_smaller in Htids.
    intros ρ ζ Hlk. apply ls_mapping_data_inv in Hlk as [?[??]]. apply Htids=>//.
    by eapply elem_of_dom_2. }
  iIntros (ζ' e' Hsome Hnoval ρ HSome). simpl.
  iAssert (ζ' ↦M ∅)%I with "[Hposts]" as "H".
  { destruct (to_val e') as [?|] eqn:Heq; last done.

  rewrite (big_sepL_elem_of (λ x, x.2 x.1) _ (v, (λ _, ζ' ↦M ∅)%I) _) //.
  have Hceq: c = trace_last ex.
  { symmetry. eapply last_eq_trace_ends_in. done. }
  apply elem_of_list_omap.
  exists (e', (λ _: aneris_val, ζ' ↦M ∅)%I); split; last first.
  - simpl. apply fmap_Some. exists v. split; done.
  - destruct (trace_last ex).1 as [|e1' tp] eqn:Htpeq; first set_solver. simpl.
    destruct (from_locale_from_elem_of' _ _ ζ' e' Hsome) as [i [Htplk Hloc]].
    apply elem_of_lookup_zip_with. eexists i, _, _. do 2 split =>//.
    { rewrite -Htplk Hceq Htpeq //. }
    rewrite lookup_app. rewrite list_lookup_fmap.
    list_simplifier.

    destruct (prefixes es !! i) as [] eqn:Hlk.
    + have Hleni: i < length es.
      { rewrite -(prefixes_from_length []). by eapply lookup_lt_Some. }
      simpl. f_equiv. destruct p as [tnew e]. simpl.
      have -> //: locale_of (take i (e1' :: tp)) e' = aneris_lang.locale_of tnew e.
      rewrite Htpeq in Htake.
      rewrite Forall2_lookup in Htake. specialize (Htake i).
      rewrite Hlk in Htake.

      rewrite prefixes_from_take in Htake.
      rewrite lookup_take // in Htake.
      apply (prefixes_from_lookup []) in Htplk.
      rewrite Htplk /= in Htake.
      inversion Htake. done.
    + simpl. rewrite list_lookup_fmap.
      rewrite Htpeq fmap_length prefixes_from_length.

      have Hleni: i >= length es.
      { rewrite -(prefixes_from_length []). by eapply lookup_ge_None. }


      have Hlk': (drop (length es) (e1' :: tp)) !! (i - length es) = Some e'.
      { rewrite lookup_drop. rewrite -Htplk. f_equal. lia. }

      apply (prefixes_from_lookup es) in Hlk'.
      rewrite Hlk' /=. f_equal.
      rewrite -skipn_firstn_comm.

      have Hequiv: locales_equiv (es ++ drop (length es) (take i (e1' :: tp))) (take i (e1' :: tp)).
      { rewrite Htpeq in Htake.
        eapply (locales_equiv_transitive _
           ((take (length es) (e1' :: tp)) ++ drop (length es) (take i (e1' :: tp))) (take i (e1' :: tp))).
        - eapply locales_equiv_from_app. apply Htake.
          list_simplifier. apply locales_equiv_from_refl. done.
        - have ->: take (length es) (e1' :: tp) = take (length es) (take i $ e1' :: tp).
          { rewrite take_take. f_equal. lia. }
          rewrite take_drop. apply locales_equiv_refl. }
      rewrite (locale_equiv _ _ _ Hequiv) //. }
   (* Now conclude using fuel_map_le somehow *)
   unfold model_state_interp.
   iDestruct "Hmod" as (fm) "(%Hle & %Hdead & ? & ? & Hfm & ?)".
   iDestruct (has_fuels_agree with "Hfm H") as %Hfm.
   rewrite /fuel_map_preserve_dead in Hdead.
   iPureIntro. intros Ha. destruct (Hdead _ Ha) as (ζ'' & fs' & Hfm' & Hin).

   have Hccl: ζ'' = ζ'; last first.
   { rewrite -Hccl in Hfm. set_solver. }

   apply ls_mapping_data_inv in HSome as [fs1 [Hfs1 Hinfs1]].


   rewrite /fuel_map_le /fuel_map_le_inner in Hle.
   rewrite map_included_utils.map_included_spec in Hle. destruct Hle as [Hle Hdoms].
   destruct (Hle _ _ Hfm') as [fs2 [Hfs2 Hincl2]].

   opose proof (ls_map_agree Hfs1 Hfs2 Hinfs1 _).
   { apply map_included_utils.map_included_subseteq_inv in Hincl2. set_solver. }
   naive_solver.
Qed.

Definition aneris_trace := extrace aneris_lang.
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

Lemma continued_simulation_infinite_model_trace
  `(M: UserModel aneris_lang) `{@anerisPreG M net_model LM LMeq Σ}
  inv
  es σ m0 iex:
  continued_simulation_init (valid_state_evolution_fairness LM inv) (es, σ) m0 →
  valid_inf_exec {tr[ (es, σ) ]} iex →
  exists iatr,
  @valid_inf_system_trace _ LM
    (continued_simulation
       (valid_state_evolution_fairness LM inv))
    (trace_singleton (es, σ))
    (trace_singleton m0)
    iex
    iatr.
Proof. intros Hcs. eexists. (unshelve apply produced_inf_aux_trace_valid_inf)=>//. constructor. Qed.

Lemma valid_inf_system_trace_implies_always
  `{M: UserModel aneris_lang} `{@anerisPreG M net_model LM LMeq Σ}
  inv Ψ
  (tr1 : execution_trace aneris_lang) tr2 tr1' (tr2' : inf_auxiliary_trace LM) :
  valid_inf_system_trace Ψ tr1 tr2  tr1' tr2' →
  (∀ ex tr, Ψ ex tr → inv (trace_last tr)) →
  (to_trace (trace_last tr2) tr2' ⊩ □ ↓ λ (s : LiveState _ (joint_model _ _)) _, inv s).
Proof.
    rewrite trace_alwaysI. intros Hval Himpl tr' [n Hn].
    revert tr' tr1 tr1' tr2 tr2' Hval Hn.
    induction n as [|n IHn]; intros tr' tr1 tr1' tr2 tr2' Hval Hn.
    - simpl in *. simplify_eq. rewrite ltl_sat_def /trace_now /pred_at /=.
      have ?: inv (trace_last tr2); last by destruct tr2' as [|[??]?].
      inv Hval as [?? Hcs| ????????? Hcs]; naive_solver.
    - destruct tr2' as [|[ℓ m1]?] eqn:Heq; first (exfalso; naive_solver).
      cbn in Hn. inv Hval. by eapply IHn.
Qed.

Lemma simulation_adequacy_traces Σ
  `(M: UserModel aneris_lang) `{@anerisPreG M net_model LM LMeq Σ}
        inv es σ m0
        (extr : aneris_trace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr) = (es, σ))
  :
  continued_simulation_init (valid_state_evolution_fairness LM inv) (es, σ) m0 →
  ∃ (auxtr : auxtrace LM), exaux_traces_match (LM := LM) extr auxtr ∧ trfirst auxtr = m0 ∧
    (auxtr ⊩ □ ↓ λ (s : LiveState aneris_lang (joint_model M net_model)) _, inv s.(ls_under).1).
Proof.
  intros Hcci.
  opose proof (from_trace_preserves_validity _ (trace_singleton (es, σ)) Hvex _ _) as Hval.
  { constructor. }
  { rewrite Hexfirst //. }
  eapply continued_simulation_infinite_model_trace in Hcci=>//.
  destruct Hcci as [atr Hatr].
  exists (to_trace m0 atr). split; last first.
  { split; first destruct atr as [| [??] ?] =>//=.
    change m0 with (trace_last (L := mlabel LM) {tr[ m0 ]}).
    eapply valid_inf_system_trace_implies_always=>//.
    intros ex tr Hcs%continued_simulation_rel. rewrite /valid_state_evolution_fairness in Hcs.
    naive_solver. }
  eapply (valid_inf_system_trace_implies_traces_match_strong (valid_state_evolution_fairness LM inv)
            _ _ _ (trace_singleton m0) (from_trace extr) atr
         ).
  - intros ex atr' Hvse. unfold valid_state_evolution_fairness in Hvse. naive_solver.
  - intros ex auxtr (?&Hlm&?) ζ ℓ Hlab Hlab'.
    rewrite /trace_labels_match in Hlm.
    destruct ex as [|?? [??]]=>//. destruct auxtr=>//. naive_solver.
  - intros ex autr (Hsteps&?&?). destruct ex=>//. destruct autr=>//.
    inversion Hsteps; simplify_eq. simpl. unfold trace_ends_in in *. naive_solver.
  - apply (from_trace_spec (trace_singleton (es, σ))). rewrite Hexfirst //.
  - change m0 with (trace_last (L := mlabel LM) (trace_singleton m0)). apply to_trace_spec.
  - eapply valid_inf_system_trace_mono; last eassumption. by intros ??[??]%continued_simulation_unfold.
Qed.

Definition ex_fair_scheduling (tr: aneris_trace) := ∀ ζ, fair_scheduling_ex ζ tr.

Definition ex_fair (tr: aneris_trace) :=
  ex_fair_network tr ∧ ex_fair_scheduling tr.

Section lm_network.
  Context {M: UserModel aneris_lang}.
  Context `{@anerisPreG M net_model LM LMeq Σ}.

  Definition lm_send_filter msg : mlabel LM → Prop :=
    λ l, ∃ ρ ζ, l = Take_step ρ (Some $ Send msg : fmaction (joint_model M net_model)) ζ (Some $ Send msg).
  Instance lm_send_filter_decision msg l : Decision (lm_send_filter msg l).
  Proof. apply make_decision. Qed.

  Definition lm_deliver_filter msg : mlabel LM → Prop :=
    λ l, l = Config_step (Deliver msg : fmconfig (joint_model M net_model)) (Deliver msg).
  Instance lm_deliver_filter_decision msg l : Decision (lm_deliver_filter msg l).
  Proof. apply make_decision. Qed.

  Definition lm_network_fair_delivery_of msg : auxtrace LM → Prop :=
    □ (□◊ ℓ↓lm_send_filter msg → ◊ ℓ↓ lm_deliver_filter msg).

  Definition lm_network_fair_delivery (mtr : auxtrace LM) : Prop :=
    ∀ msg, lm_network_fair_delivery_of msg mtr.

  Definition lm_fair_scheduling (tr: auxtrace LM) :=
    ∀ ρ, fair_aux (LM := LM) ρ tr.

  Definition lm_fair (tr: auxtrace LM) :=
    fuel_network_fair_delivery tr ∧ lm_fair_scheduling tr.

  Notation ff :=
    (ltl_tme labels_match live_tids locale_step (lm_ls_trans LM)).

  Lemma simulation_adequacy_traces_fairness
          inv es σ m0
          (extr : aneris_trace)
          (Hvex : extrace_valid extr)
          (Hexfirst : (trfirst extr) = (es, σ))
    :
    continued_simulation_init (valid_state_evolution_fairness LM inv) (es, σ) m0 →
    ex_fair extr →
    ∃ (auxtr : auxtrace LM), lm_fair auxtr ∧ exaux_traces_match (LM := LM) extr auxtr ∧ trfirst auxtr = m0 ∧
      (auxtr ⊩ □ ↓ λ (s : LiveState aneris_lang (joint_model M net_model)) _, inv s.(ls_under).1).
  Proof.
    intros Hcs [Hfn Hfs].
    destruct (simulation_adequacy_traces _ _ _ _ _ _ extr Hvex Hexfirst Hcs) as [atr [Hatr [??]]].
    eexists _; split=>//. split.
    - rewrite /lm_network_fair_delivery /ex_fair_network in Hfn *.
      rewrite /lm_network_fair_delivery_of /ex_fair_network_of in Hfn *.
      intros msg. specialize (Hfn msg).

      unshelve eapply (ltl_tme_use _ _ _ _ _ Hatr Hfn).
      apply ltl_tme_always, ltl_tme_impl.
      + apply ltl_tme_always, ltl_tme_eventually, ltl_tme_now.
        rewrite /labels_match.
        rewrite /ex_send_filter /fuel_send_filter /=.
        intros [[]|] [] Hlm=>//.
        * destruct Hlm as (?&?&Ham). simplify_eq. rewrite actions_match_is_eq in Ham. naive_solver.
        * destruct Hlm as (?&?&Ham). simplify_eq. simpl. split; naive_solver.
        * destruct Hlm as (?&Ham). simplify_eq. simpl. split; naive_solver.
      + apply ltl_tme_eventually, ltl_tme_now.
        rewrite /labels_match.
        rewrite /ex_deliver_filter /fuel_deliver_filter /=.
        intros [[]|] [] Hlm=>//; [naive_solver| naive_solver |].
        destruct Hlm as (?&Ham). simplify_eq. simpl. rewrite cfg_labels_match_is_eq in Ham; naive_solver.
    - rewrite /lm_fair_scheduling /ex_fair_scheduling in Hfn *. eapply fairness_preserved=>//.
  Qed.

  Notation jmtrace := (trace (joint_model M net_model) (fmlabel (joint_model M net_model))).
  Definition jm_fair (tr: jmtrace) :=
    jm_network_fair_delivery tr ∧ jm_fair_scheduling tr.

  Definition usr_fair (tr: lts_trace M) :=
    usr_network_fair_send_receive tr ∧ usr_fair_scheduling tr.

  Lemma simulation_adequacy_trace_remove_fuel
          (auxtr : auxtrace LM) inv :
    lm_fair auxtr →
    auxtrace_valid (LM := LM) auxtr →
    (auxtr ⊩ □ ↓ λ (s : LiveState aneris_lang (joint_model M net_model)) _, inv s.(ls_under).1) →
    ∃ jmtr, jm_fair jmtr ∧ jmtrace_valid jmtr ∧ upto_stutter_aux auxtr jmtr ∧
              trfirst jmtr = (trfirst auxtr).(ls_under) ∧
      (jmtr ⊩ □ ↓ λ (s : joint_model M net_model) _, inv s.1).
  Proof.
    intros [Hnf Hsf] Hval Hinv. have Hval' := Hval.
    apply can_destutter_auxtr in Hval as [jmtr Hupto].
    exists jmtr; split; [|split; [|split; [|split]]]=>//.
    - split.
      + eapply fuel_network_fairness_destutter=>//.
      + apply (upto_stutter_fairness_ltl _ _) in Hupto=>//.
    - eapply (upto_stutter_preserves_validity (Λ := aneris_lang)) =>//.
    - punfold Hupto; last apply upto_stutter_mono. inversion Hupto; naive_solver.
    - eapply ltl_se_use. 2: try apply Hupto. 2: apply Hinv.
      apply ltl_se_always, ltl_se_now_state. naive_solver.
  Qed.

  Lemma simulation_adequacy_trace_trimed
          (jmtr : jmtrace) inv :
    jm_fair jmtr →
    jmtrace_valid jmtr →
    (jmtr ⊩ □ ↓ λ (s : joint_model M net_model) _, inv s.1) →
    ∃ ttr, jm_fair ttr ∧ jmtrace_valid ttr ∧ trimmed_of jmtr ttr ∧ trfirst ttr = trfirst jmtr ∧
           (ttr ⊩ □ ↓ λ (s : joint_model M net_model) _, inv s.1).
  Proof.
    intros [Ha Hb] Hval Hinv. exists (trim_trace jmtr). split_and!.
    - split.
      + eapply trim_preserves_network_fairness =>//.
      + eapply trimming_preserves_fair_scheduling=>//.
    - rewrite /jmtrace_valid in Hval *. by apply trim_trace_valid.
    - apply trim_trace_trimmed_of.
    - destruct jmtr=>//=. destruct (decide _)=>//.
    - rewrite trace_alwaysI. intros ttr' Hsuff.
      eapply trimmed_of_suffix_of in Hsuff. 2: apply trim_trace_trimmed_of.
      destruct Hsuff as (jmtr' & Hsuff & Htrim).
      rewrite trace_alwaysI in Hinv. specialize (Hinv _ Hsuff).
      rewrite !trace_now_state_trfirst in Hinv *.
      punfold Htrim. inv Htrim=>//. apply trimmed_of_mono.
  Qed.

  Lemma simulation_adequacy_trace_trimmed_user
          (ttr : jmtrace) inv :
    jm_fair ttr →
    jmtrace_valid ttr →
    trace_is_trimmed ttr →
    (ttr ⊩ □ ↓ λ (s : joint_model M net_model) _, inv s.1) →
    ∃ utr, usr_fair utr ∧ usr_trace_valid utr ∧ upto_stutter_env ttr utr ∧ trfirst utr = (trfirst ttr).1 ∧
       (utr ⊩ □ ↓ λ (s : M) _, inv s).
  Proof.
    intros [Hnf Hsf] Hval Htrim Hinv.
    have [utr Huts] : ∃ utr, upto_stutter_env ttr utr.
    { eapply can_destutter. apply env_steps_dec_unless=>//. }
    exists utr. split_and!=>//.
    - split. eapply network_fairness_project_usr=>//. eapply usr_project_scheduler_fair=>//.
    - eapply usr_project_valid=>//.
    - punfold Huts. inversion Huts; naive_solver. apply upto_stutter_mono.
    - eapply ltl_se_use. 2: try apply Huts. 2: apply Hinv.
      apply ltl_se_always, ltl_se_now_state. naive_solver.
  Qed.

  Definition model_refinement : rel (auxtrace LM) (lts_trace M) :=
    upto_stutter_aux
    >> trimmed_of
    >> upto_stutter_env.

  Definition program_model_refinement : rel (extrace aneris_lang) (lts_trace M) :=
    exaux_traces_match (LM := LM) >> model_refinement.

  Lemma model_refinement_preserves_upward auxtr inv :
    lm_fair auxtr →
    auxtrace_valid (LM := LM) auxtr →
    (auxtr ⊩ □ ↓ λ (s : LiveState aneris_lang (joint_model M net_model)) _, inv s.(ls_under).1) →
    ∃ utr, model_refinement auxtr utr ∧ usr_fair utr ∧ usr_trace_valid utr ∧
             trfirst utr = (trfirst auxtr).(ls_under).1 ∧
             (utr ⊩ □ ↓ λ (s : M) _, inv s).
  Proof.
    intros Hf Hval Hinv.
    eapply simulation_adequacy_trace_remove_fuel in Hval as (?&?&Hval&?&?&?) =>//.
    eapply simulation_adequacy_trace_trimed in Hval as (?&?&Hval&?&?&?) =>//.
    eapply simulation_adequacy_trace_trimmed_user in Hval as (utr&?&Hval&?&?&?) =>//;
      last by eapply trimmed_of_is_trimmed.
    rewrite /model_refinement /rel_compose. naive_solver congruence.
  Qed.

  Proposition program_model_refinement_preserves_upward extr m0 inv es σ :
    continued_simulation_init (valid_state_evolution_fairness LM inv) (es, σ) m0 →
    extrace_valid extr →
    ex_fair extr →
    (trfirst extr) = (es, σ) →
    ∃ utr, program_model_refinement extr utr ∧ usr_fair utr ∧ usr_trace_valid utr ∧ trfirst utr = m0.(ls_under).1.
  Proof.
    intros Hf Hval ??.
    eapply simulation_adequacy_traces_fairness in Hval as (?&?&Hmatch&?&?) =>//.
    have Hmatch' := Hmatch.
    apply exaux_preserves_validity in Hmatch.
    eapply model_refinement_preserves_upward in Hmatch as (utr&?&?&?&?&?) =>//.
    rewrite /program_model_refinement /rel_compose. naive_solver congruence.
  Qed.

  Proposition program_model_refinement_downward_eventually extr utr (P : action aneris_lang → Prop) :
    program_model_refinement extr utr →
    (utr ⊩ ◊ ℓ↓ (λ '(_, α), ∃ α', α = Some α' ∧ P α'))→
    (extr ⊩ ◊ ℓ↓ (λ ℓ, ∃ ℓ' ζ, ℓ = inl (ζ, Some ℓ') ∧ P ℓ')).
  Proof.
    rewrite /program_model_refinement /model_refinement /rel_compose.
    intros (auxtr&?&jmtr&?&ttr&?&?) Hev.

    have Heq: ltl_se_env (M := M) (N := net_model)
      (◊ ℓ↓ (λ ℓ, ∃ ℓ' ζ, ℓ = inl (ζ, Some ℓ') ∧ P ℓ')) ((◊ ℓ↓ λ '(_, α), ∃ α', α = Some α' ∧ P α')) .
    { apply ltl_se_eventually_now. intros [[??]|?]; naive_solver. }
    rewrite -(Heq ttr) // in Hev. clear Heq.

    have {}Hev : (jmtr ⊩ ◊ ℓ↓ (λ ℓ, ∃ ℓ' ζ, ℓ = inl (ζ, Some ℓ') ∧ P ℓ')).
    { by eapply trimmed_of_eventually_back. }

    have Heq: fuel_se
      (◊ ℓ↓ (λ (ℓ : mlabel LM), ∃ ρ α1 (α α': fmaction (joint_model M net_model)) ζ,
          α = Some α1 ∧ ℓ = Take_step ρ α ζ α' ∧ P α1))
      (◊ ℓ↓ (λ ℓ, ∃ ℓ' ζ, ℓ = inl (ζ, Some ℓ') ∧ P ℓ')).
    { apply ltl_se_eventually_now. intros [? α ??|?|?]; [|naive_solver|naive_solver]. split.
      - intros (?&?&?&?&?). simplify_eq. naive_solver.
      - intros (?&?&?&?&?&?). simpl in *. simplify_eq. naive_solver. }
    rewrite -(Heq auxtr) // in Hev. clear Heq.

    have Heq: exaux_tme (LM := LM)
      (◊ ℓ↓ (λ ℓ, ∃ ℓ' ζ, ℓ = inl (ζ, Some ℓ') ∧ P ℓ'))
      (◊ ℓ↓ (λ (ℓ : mlabel LM), ∃ ρ α1 (α α': fmaction (joint_model M net_model)) ζ,
          α = Some α1 ∧ ℓ = Take_step ρ α ζ α' ∧ P α1)).
    { apply ltl_tme_eventually, ltl_tme_now. rewrite /labels_match.
      intros [[ζ oα]|?]; last naive_solver. intros [?|?|?]; last naive_solver.
      - intros (?&?&?%actions_match_is_eq). naive_solver.
      - intros (?&?&?). simplify_eq. naive_solver. }
    rewrite -(Heq extr) // in Hev.
  Qed.
End lm_network.

(* (* OBS: This is not needed. *) *)
(* Lemma valid_inf_system_trace_implies_traces_match *)
(*       ex atr iex iatr progtr auxtr : *)
(*   exec_trace_match ex iex progtr → *)
(*   exec_trace_match atr iatr auxtr → *)
(*   valid_inf_system_trace *)
(*     (continued_simulation valid_state_evolution_fairness) ex atr iex iatr → *)
(*   live_traces_match progtr auxtr. *)
(* Proof. *)
(*   intros. *)
(*   eapply (valid_inf_system_trace_implies_traces_match_strong *)
(*           (continued_simulation valid_state_evolution_fairness)); [| | |done..]. *)
(*   - by intros ?? (?&?&?&?)%continued_simulation_rel. *)
(*   - intros [][] (?&?&?)%continued_simulation_rel; try done. *)
(*     intros. simpl in *. by simplify_eq. *)
(*   - intros [][] (Hvalid&?&?)%continued_simulation_rel; try done. *)
(*     simpl in *. inversion Hvalid. simplify_eq. by rewrite H7. *)
(* Qed. *)

(* Definition extrace_matching_mtrace_exists *)
(*            {Λ} {M} (Rs : cfg Λ → M.(mstate) → Prop) Rℓ st extr := *)
(*   ∃ mtr, trfirst mtr = st ∧ *)
(*          traces_match Rℓ Rs language.locale_step (M.(mtrans)) extr mtr. *)

(* Lemma continued_simulation_traces_match {Λ} {M} *)
(*       (ξ : _ → _ → Prop) (Rs : cfg Λ → M.(mstate) → Prop) (Rℓ : _ → _ → Prop) *)
(*       extr st : *)
(*   (∀ extr auxtr, continued_simulation ξ extr auxtr → *)
(*                  Rs (trace_last extr) (trace_last auxtr)) → *)
(*   (∀ extr auxtr, continued_simulation ξ extr auxtr → *)
(*                  ∀ ζ ℓ, trace_last_label extr = Some ζ → *)
(*                         trace_last_label auxtr = Some ℓ → *)
(*                         Rℓ ζ ℓ) → *)
(*   (∀ extr auxtr, continued_simulation ξ extr auxtr → *)
(*                  match extr, auxtr with *)
(*                  | _ :tr[_]: _, auxtr :tr[ℓ]: ρ => *)
(*                      mtrans (trace_last auxtr) ℓ ρ *)
(*                  | _,_ => True *)
(*                  end) → *)
(*   extrace_valid extr → *)
(*   continued_simulation_init ξ (trfirst extr) st → *)
(*   extrace_matching_mtrace_exists Rs Rℓ st extr. *)
(* Proof. *)
(*   intros HRs HRℓ Htrans Hvalid Hsim. *)
(*   assert (∃ iatr, *)
(*              valid_inf_system_trace *)
(*                (continued_simulation ξ) *)
(*                (trace_singleton (trfirst extr)) *)
(*                (trace_singleton (st)) *)
(*                (from_trace extr) *)
(*                iatr) as [iatr Hiatr]. *)
(*   { eexists _. eapply produced_inf_aux_trace_valid_inf. econstructor. *)
(*     Unshelve. *)
(*     - done. *)
(*     - eapply from_trace_preserves_validity; eauto; first econstructor. } *)
(*   eexists _. *)
(*   split; last first. *)
(*   { eapply (valid_inf_system_trace_implies_traces_match_strong); eauto. *)
(*     - by apply from_trace_spec. *)
(*     - by apply to_trace_spec. } *)
(*   destruct iatr; [done|by destruct x]. *)
(* Qed. *)

(* Definition extrace_matching_mtrace_exists_live st extr := *)
(*   extrace_matching_mtrace_exists (live_tids : cfg aneris_lang → mstate (fair_model_to_model retransmit_fair_model) → Prop) labels_match st extr. *)

(* Lemma continued_simulation_traces_match_live extr st : *)
(*   extrace_valid extr → *)
(*   continued_simulation_init valid_state_evolution_fairness *)
(*                        (trfirst extr) st → *)
(*   extrace_matching_mtrace_exists_live st extr. *)
(* Proof. *)
(*   intros. eapply continued_simulation_traces_match; eauto. *)
(*   - by intros ?? (?&?&?&?)%continued_simulation_rel. *)
(*   - intros [][] (?&?&?)%continued_simulation_rel; try done. *)
(*     intros. simpl in *. by simplify_eq. *)
(*   - intros [][] (Hvalid&?&?)%continued_simulation_rel; try done. *)
(*     simpl in *. inversion Hvalid. simplify_eq. by rewrite H6. *)
(* Qed. *)

(* Definition matching_mtrace_exists c st := *)
(*   extrace_property c (extrace_matching_mtrace_exists_live st). *)

(* (** A continued simulation exists between some initial configuration [c] *)
(*     and the initial state [init_state] of a fair model. *) *)
(* Definition live_simulation (c : cfg aneris_lang) (st : retransmit_state) := *)
(*   continued_simulation_init valid_state_evolution_fairness c st. *)

(* Lemma continued_simulation_traces_match_init c st : *)
(*   live_simulation c st → matching_mtrace_exists c st. *)
(* Proof. *)
(*   intros Hsim extr <- Hvalid. *)
(*   apply (continued_simulation_traces_match_live) in Hsim *)
(*       as (mtr & Hmtr & Hmatch); [by eexists _|done]. *)
(* Qed. *)

(* Definition extrace_fairly_terminating_locale ζ (extr : extrace aneris_lang) := *)
(*   extrace_fair extr -> extrace_terminating_locale ζ extr. *)

(* Definition fairly_terminating ζ (c : cfg aneris_lang) := *)
(*   extrace_property c (extrace_fairly_terminating_locale ζ). *)

(* Lemma traces_match_fair_termination_preserved_init c st : *)
(*   matching_mtrace_exists c st → fairly_terminating localeB c. *)
(* Proof. *)
(*   intros Hmatches. *)
(*   eapply extrace_property_impl; [done|]. *)
(*   intros extr Hstart Hvalid (mtr & Hstart' & Hmtr) Hfair. *)
(*   eapply terminating_role_preserved; *)
(*     [done|done|done|]. *)
(*   apply retransmit_fair_traces_terminate. *)
(*   - by eapply traces_match_valid_preserved. *)
(*   - by eapply traces_match_fairness_preserved. *)
(* Qed. *)

(* Theorem continued_simulation_fair_termination c st : *)
(*   live_simulation c st → fairly_terminating localeB c. *)
(* Proof. *)
(*   intros ?. *)
(*   by eapply traces_match_fair_termination_preserved_init, *)
(*     continued_simulation_traces_match_init. *)
(* Qed. *)

(* Theorem simulation_adequacy_fair_termination_multiple *)
(*         `{anerisPreG retransmit_fair_model Σ} *)
(*         A s (es : list aneris_expr) σ st : *)
(*   role_enabled_locale_exists (es, σ) st → *)
(*   config_state_valid (es, σ) st → *)
(*   length es >= 1 → *)
(*   (* aneris_model_rel_finitary Mdl → *) *)
(*   dom (state_heaps σ) = dom (state_sockets σ) → *)
(*   (* Port coherence *) *)
(*   ((∀ ip ps, (GSet <$> (addrs_to_ip_ports_map *)
(*                               (A ∖ (ports_in_use $ state_sockets σ)))) *)
(*                !! ip = Some (GSet ps) → *)
(*              ∀ Sn, (state_sockets σ) !! ip = Some Sn → *)
(*                    ∀ p, p ∈ ps → port_not_in_use p Sn)) → *)
(*   (* Socket buffers are initially empty *) *)
(*   map_Forall (λ ip s, map_Forall (λ sh sb, sb.2 = []) s) (state_sockets σ) → *)
(*   map_Forall (λ ip s, socket_handlers_coh s) (state_sockets σ) → *)
(*   map_Forall (λ ip s, socket_addresses_coh s ip) (state_sockets σ) → *)
(*   (* Message soup is initially empty *) *)
(*   state_ms σ = ∅ → *)
(*   wp_proto_multiple_strong A σ s es st (* φs *) → *)
(*   fairly_terminating localeB (es,σ). *)
(* Proof. *)
(*   intros. eapply continued_simulation_fair_termination, *)
(*             simulation_adequacy_multiple_strong; try done. *)
(* Qed. *)
