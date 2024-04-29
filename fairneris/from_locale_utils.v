(* TODO: Clean up imports *)
From Paco Require Import pacotac.
From stdpp Require Import finite.
From iris.proofmode Require Import proofmode.
From trillium.program_logic Require Import adequacy.
From fairneris.aneris_lang.state_interp Require Import state_interp_def.
From fairneris.aneris_lang.state_interp Require Import state_interp_config_wp.
From fairneris.aneris_lang.state_interp Require Import state_interp.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.

(* TODO: Should likely move this to [lang.v] *)
Definition locale_of' (ips : list ip_address) ip :=
  (ip, length $ (filter (λ ip', ip' = ip)) ips).

Lemma locale_of_locale_of' es e :
  locale_of es e = locale_of' (map expr_n es) (expr_n e).
Proof.
  induction es; [done|].
  rewrite /locale_of /locale_of'. simpl.
  rewrite !filter_cons. case_decide; [|done]=> /=.
  f_equiv. rewrite /locale_of /locale_of' in IHes. simplify_eq. by rewrite IHes.
Qed.

Lemma prefixes_map_from_locale_of_locale_of' tp0 tp1 :
  map (λ '(t,e), locale_of t e) (prefixes_from tp0 tp1) =
  map (λ '(t,e), locale_of' t e) (prefixes_from (map expr_n tp0) (map expr_n tp1)).
Proof.
  revert tp0.
  induction tp1; [done|]; intros tp0=> /=.
  rewrite locale_of_locale_of'. f_equiv.
  replace ([expr_n a]) with (map expr_n [a]) by done.
  rewrite -(map_app _ tp0 [a]).
  apply IHtp1.
Qed.

(* This is almost identical to above lemma, but differs in [map] vs [list_fmap] *)
Lemma prefixes_list_fmap_from_locale_of_locale_of' tp0 tp1 :
  (λ '(t,e), locale_of t e) <$> prefixes_from tp0 tp1 =
  (λ '(t,e), locale_of' t e) <$> prefixes_from (map (expr_n) tp0) (map expr_n tp1).
Proof.
  revert tp0.
  induction tp1; [done|]; intros tp0=> /=.
  rewrite locale_of_locale_of'. f_equiv.
  replace ([expr_n a]) with (map expr_n [a]) by done.
  rewrite -(map_app _ tp0 [a]).
  apply IHtp1.
Qed.

Lemma prefixes_from_take {A} n (xs ys : list A) :
  prefixes_from xs (take n ys) = take n (prefixes_from xs ys).
Proof.
  revert n xs.
  induction ys as [|y ys IHys]; intros n xs.
  { by rewrite !take_nil. }
  destruct n; [done|]=> /=. by f_equiv.
Qed.

Lemma locales_of_list_from_drop
  `{LM: LiveModel aneris_lang (joint_model Mod Net)} `{!LiveModelEq LM} `{aG : !anerisG LM Σ} es es' tp :
  locales_equiv_prefix_from es' es tp →
  (λ '(t,e) v, fork_post (locale_of t e) v) <$>
      (prefixes_from es' tp) =
  (λ '(t,e) v, fork_post (locale_of t e) v) <$>
      (prefixes_from es' (es ++ drop (length es) tp)).
Proof.
  intros Hζ. apply locales_of_list_from_fork_post.
  by apply locales_of_list_equiv, locales_equiv_prefix_from_drop.
Qed.

Lemma posts_of_length_drop
    `{LM: LiveModel aneris_lang (joint_model Mod Net)} `{!LiveModelEq LM} `{aG : !anerisG LM Σ} es es' tp :
  locales_equiv_prefix_from es' es tp →
  posts_of tp ((λ '(t,e) v, fork_post (locale_of t e) v) <$>
                   (prefixes_from es' (es ++ drop (length es) tp))) -∗
  posts_of tp ((λ '(t,e) v, fork_post (locale_of t e) v) <$>
                   (prefixes_from es' tp)).
Proof. iIntros (Hζ) "H". by erewrite <-locales_of_list_from_drop. Qed.
