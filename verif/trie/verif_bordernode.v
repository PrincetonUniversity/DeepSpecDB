(** * verif_bordernode.v: Correctness proof of bordernode *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import bordernode.
Require Import specs.

Require Import common.
Require Import bordernode_fun.
Require Import keyslice_fun.

Import Coq.Lists.List.ListNotations.

Lemma Forall_upd_Znth {A: Type} {Inh: Inhabitant A}: forall (l: list A) (k: Z) (v: A) (P: A -> Prop),
    0 <= k < Zlength l ->
    Forall P l ->
    P v ->
    Forall P (upd_Znth k l v).
Proof.
  intros.
  rewrite <- (sublist_same 0 (Zlength l) l) by reflexivity.
  rewrite (sublist_split 0 k) by list_solve.
  rewrite (sublist_split k (k + 1)) by list_solve.
  rewrite upd_Znth_app2 by list_solve.
  rewrite upd_Znth_app1 by list_solve.
  do 2 rewrite Forall_app.
  split3; try (apply Forall_sublist; assumption).
  rewrite Zlength_sublist by list_solve.
  replace (k - (k - 0)) with 0 by omega.
  rewrite sublist_len_1 by list_solve.
  rewrite upd_Znth0.
  rewrite sublist_nil.
  auto.
Qed.

Definition bordernode_rep_length_inv: forall sh s p,
    bordernode_rep sh s p |-- !! (Zlength (fst s) = keyslice_length).
Proof.
  intros.
  unfold bordernode_rep.
  destruct s as [? [[] | ]].
  - Intros p'.
    Intros sh_string.
    entailer!.
    simplify_value_fits in H2.
    destruct H2 as [? _].
    simplify_value_fits in H2.
    rep_omega.
  - entailer!.
    simplify_value_fits in H1.
    destruct H1 as [? _].
    simplify_value_fits in H1.
    rep_omega.
Qed.
Hint Resolve bordernode_rep_length_inv: saturate_local.

Definition Gprog : funspecs :=
  ltac:(with_library prog [
          surely_malloc_spec; UTIL_StrEqual_spec;
          BN_NewBorderNode_spec; BN_SetPrefixValue_spec;
          BN_GetPrefixValue_spec; BN_GetSuffixValue_spec
       ]).

Lemma body_BN_NewBorderNode: semax_body Vprog Gprog f_BN_NewBorderNode BN_NewBorderNode_spec.
Proof.
  start_function.
  forward_call (tbordernode).
  split3; auto; simpl; rep_omega.
  Intros p.
  forward_for_simple_bound (keyslice_length) (EX i: Z,
    PROP (0 <= i <= keyslice_length)
    LOCAL (temp _bordernode p)
    SEP (malloc_token Tsh tbordernode p;
         data_at Tsh tbordernode (list_repeat (Z.to_nat i) nullval ++ list_repeat (Z.to_nat (keyslice_length - i)) Vundef, (Vundef, (Vundef, Vundef))) p))%assert.
  entailer!.
  unfold_data_at 1%nat.
  unfold data_at_.
  unfold field_at_.
  unfold_field_at 1%nat.
  entailer!.
  - forward.
    entailer!.
    rewrite <- list_repeat_app' by list_solve.
    rewrite upd_Znth_app2 by list_solve.
    rewrite Zlength_list_repeat by list_solve.
    rewrite Z.sub_diag.
    simpl.
    rewrite upd_Znth0.
    rewrite sublist_list_repeat by list_solve.
    rewrite Zlength_list_repeat by list_solve.
    rewrite <- app_assoc.
    rewrite semax_lemmas.cons_app.
    replace (keyslice_length  - (i + 1)) with (keyslice_length - i - 1) by rep_omega.
    entailer!.
  - forward.
    forward.
    forward.
    forward.
    Exists p.
    rewrite Z.sub_diag.
    simpl.
    rewrite app_nil_r.
    entailer!.
    apply Forall_list_repeat.
    auto.
Qed.

Lemma body_BN_SetPrefixValue: semax_body Vprog Gprog f_BN_SetPrefixValue BN_SetPrefixValue_spec.
Proof.
  start_function.
  forward_if (True); [(forward; entailer!) | rep_omega | ]; Intros.
  forward_if (True); [(forward; entailer!) | rep_omega | ]; Intros.
  assert_PROP (Zlength (fst bordernode) = keyslice_length). {
    entailer!.
  }
  unfold bordernode_rep.
  destruct bordernode as [? [[]|]]; simpl in H0.
  - Intros p'.
    Intros sh_string.
    forward.
    forward.
    Exists p'.
    Exists sh_string.
    entailer!.
    apply Forall_upd_Znth; first [list_solve | assumption].
  - Intros.
    forward.
    forward.
    entailer!.
    apply Forall_upd_Znth; first [list_solve | assumption].
Qed.

Lemma body_BN_GetPrefixValue: semax_body Vprog Gprog f_BN_GetPrefixValue BN_GetPrefixValue_spec.
Proof.
  start_function.
  forward_if (True); [(forward; entailer!) | rep_omega | ]; Intros.
  forward_if (True); [(forward; entailer!) | rep_omega | ]; Intros.
  assert_PROP (Zlength (fst bordernode) = keyslice_length). {
    entailer!.
  }
  unfold bordernode_rep.
  destruct bordernode as [? [[] | ]]; simpl in H0.
  - Intros p'.
    Intros sh_string'.
    forward.
    + entailer!.
      apply Forall_Znth.
      * rep_omega.
      * assumption.
    + forward.
      Exists p'.
      Exists sh_string'.
      entailer!.
  - Intros.
    forward.
    + entailer!.
      apply Forall_Znth.
      * rep_omega.
      * assumption.
    + forward.
Qed.

Lemma body_BN_GetSuffixValue: semax_body Vprog Gprog f_BN_GetSuffixValue BN_GetSuffixValue_spec.
Proof.
  start_function.
  unfold bordernode_rep.
  destruct bordernode as [? [[] |]].
  - Intros p'.
    unfold cstring_len.
    Intros sh_string'.
    forward.
    forward_if (p' <> nullval).
    (* entailer! does not solve the type check here *)
    apply denote_tc_test_eq_split; first [entailer!].
    assert (data_at sh_string' (tarray tschar (Zlength s0)) (map Vbyte s0) p' |-- valid_pointer p'). {
      apply data_at_valid_ptr.
      auto.
      simpl.
      rewrite Z.mul_1_l.
      rewrite Z.max_r by rep_omega.
      rep_omega.
    }
    entailer!.
    + assert_PROP (False). { entailer!. }
      contradiction.
    + forward.
      entailer!.
    + forward.
      forward.
      forward_call (sh_string, s, key, sh_string', p', s0).
      entailer!. (* I don't know what's this goal *)
      unfold cstring_len.
      entailer!.
      forward_if.
      * if_tac in H5; [ | contradiction].
        forward.
        forward.
        Exists p'.
        Exists sh_string'.
        rewrite if_true by auto.
        entailer!.
      * if_tac in H5; [discriminate H5 | ].
        forward.
        Exists p'.
        Exists sh_string'.
        rewrite if_false by auto.
        entailer!.
  - Intros.
    forward.
    forward_if (nullval <> nullval).
    + forward.
    + discriminate H1.
    + Intros.
      contradiction.
Qed.
