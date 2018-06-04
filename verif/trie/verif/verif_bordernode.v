(** * verif_bordernode.v: Correctness proof of bordernode *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import deepDB.common.
Require Import deepDB.tactics.

Require Import deepDB.functional.bordernode.
Require Import deepDB.functional.keyslice.

Require Import deepDB.representation.bordernode.
Require Import deepDB.representation.string.
Require Import deepDB.representation.key.

Require Import deepDB.specs.

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

Definition Gprog : funspecs :=
  ltac:(with_library prog [
          surely_malloc_spec; UTIL_StrEqual_spec;
          BN_NewBorderNode_spec; BN_SetPrefixValue_spec;
          BN_GetPrefixValue_spec; BN_GetSuffixValue_spec;
          BN_SetSuffixValue_spec; BN_TestSuffix_spec;
          BN_SetLink_spec; BN_GetLink_spec
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
    unfold_data_at 1%nat.
    entailer!.
    apply Forall_list_repeat.
    auto.
Qed.

Lemma body_BN_SetPrefixValue: semax_body Vprog Gprog f_BN_SetPrefixValue BN_SetPrefixValue_spec.
Proof.
  start_function.
  forward_if (True); [(forward; entailer!) | rep_omega | ]; Intros.
  forward_if (True); [(forward; entailer!) | rep_omega | ]; Intros.
  assert_PROP (Zlength (fst (fst bordernode)) = keyslice_length). {
    entailer!.
  }
  unfold bordernode_rep.
  destruct bordernode as [[]]; simpl in H0.
  Intros.
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
  assert_PROP (Zlength (fst (fst bordernode)) = keyslice_length). {
    entailer!.
  }
  unfold bordernode_rep.
  destruct bordernode as [[]]; simpl in H0.
  Intros.
  forward.
  + entailer!.
    apply Forall_Znth; [rep_omega | assumption].
  + forward.
    entailer!.
Qed.

Lemma body_BN_GetSuffixValue: semax_body Vprog Gprog f_BN_GetSuffixValue BN_GetSuffixValue_spec.
Proof.
  start_function.
  unfold bordernode_rep.
  destruct bordernode as [[? [|]]].
  - unfold cstring_len.
    Intros p'.
    forward.
    forward_if (p' <> nullval).
    + assert_PROP (False). { entailer!. }
      contradiction.
    + forward.
      entailer!.
    + forward.
      forward.
      forward_call (sh_string, s, key, Tsh, p', s0).
      unfold cstring_len.
      entailer!.
      forward_if.
      * match goal with
        | [H: context [if _ then _ else _] |- _] => if_tac in H; try (solve [inversion H | contradiction])
        end.
        forward.
        forward.
        rewrite if_true by auto.
        Exists p'.
        entailer!.
      * match goal with
        | [H: context [if _ then _ else _] |- _] => if_tac in H; try (solve [inversion H | contradiction])
        end.
        forward.
        rewrite if_false by (inversion 1; auto).
        Exists p'.
        entailer!.
  - Intros.
    forward.
    forward_if (nullval <> nullval).
    + forward.
      entailer!.
   + discriminate H0.
   + Intros.
     contradiction.
Qed.

Lemma body_BN_SetSuffixValue: semax_body Vprog Gprog f_BN_SetSuffixValue BN_SetSuffixValue_spec.
Proof.
  start_function.
  unfold bordernode_rep.
  destruct bordernode as [[? [|]]].
  - Intros p'.
    unfold cstring_len. Intros.
    fold_tbordernode.
    forward.
    forward_if (
      PROP ( )
      LOCAL (temp _t'4 p'; temp _bn p; temp _suffix s; temp _len (Vint (Int.repr (Zlength key)));
             temp _val value)
      SEP (data_at sh_bordernode tbordernode
                   (l, (v, (p', Vint (Int.repr (Zlength s0))))) p;
           data_at sh_string (tarray tschar (Zlength key)) (map Vbyte key) s;
           malloc_token sh_bordernode tbordernode p)).
    + forward.
      forward_call (tarray tschar (Zlength s0), p').
      entailer!.
    + forward.
      entailer!.
    + forward_call (tarray tschar (Zlength key)).
      split3; simpl; auto. rewrite Z.max_r; rep_omega.
      Intros p''.
      forward.
      elim_cast_pointer.
      forward_for_simple_bound (Zlength key) (EX i:Z,
        PROP ()
        LOCAL (temp _t'1 p''; temp _t'4 p'; temp _bn p; temp _suffix s;
               temp _len (Vint (Int.repr (Zlength key))); temp _val value)
        SEP (malloc_token Tsh (tarray tschar (Zlength key)) p'';
             data_at Tsh (tarray tschar (Zlength key))
                     (map Vbyte (sublist 0 i key) ++ list_repeat (Z.to_nat (Zlength key - i)) Vundef) p'';
             data_at sh_string (tarray tschar (Zlength key)) (map Vbyte key) s;
             data_at sh_bordernode tbordernode (l, (v, (p'', Vint (Int.repr (Zlength s0))))) p;
             malloc_token sh_bordernode tbordernode p))%assert.
      rewrite sublist_nil by list_solve.
      rewrite Z.sub_0_r.
      rewrite app_nil_l.
      entailer!.
      * forward.
        forward.
        forward.
        entailer!.
        rewrite upd_Znth_app2 by list_solve.
        rewrite <- sublist_map.
        rewrite Zlength_sublist  by list_solve.
        replace (i - (i - 0)) with 0 by omega.
        rewrite upd_Znth0.
        rewrite semax_lemmas.cons_app.
        rewrite sublist_last_1 by list_solve.
        rewrite sublist_list_repeat by list_solve.
        rewrite sublist_map.
        rewrite Zlength_list_repeat by list_solve.
        replace (Zlength key - i - 1) with (Zlength key - (i + 1)) by omega.
        rewrite map_app.
        rewrite <- app_assoc.
        entailer!.
      * forward.
        forward.
        forward.
        Exists p''.
        unfold cstring_len.
        entailer!.
        rewrite Z.sub_diag.
        rewrite sublist_same by list_solve.
        rewrite list_repeat_0.
        rewrite app_nil_r.
        unfold_data_at 2%nat.
        entailer!.
  - unfold cstring_len.
    Intros.
    fold_tbordernode.
    forward.
    forward_if (True); [rep_omega | forward; entailer! | ].
    forward_call (tarray tschar (Zlength key)).
    split3; simpl; auto. rewrite Z.max_r; rep_omega.
    Intros p''.
    forward.
    elim_cast_pointer.
    forward_for_simple_bound (Zlength key) (EX i:Z,
      PROP ()
      LOCAL (temp _t'1 p''; temp _bn p; temp _suffix s;
             temp _len (Vint (Int.repr (Zlength key))); temp _val value)
      SEP (malloc_token Tsh (tarray tschar (Zlength key)) p'';
           data_at Tsh (tarray tschar (Zlength key))
                   (map Vbyte (sublist 0 i key) ++ list_repeat (Z.to_nat (Zlength key - i)) Vundef) p'';
           data_at sh_string (tarray tschar (Zlength key)) (map Vbyte key) s;
           data_at sh_bordernode tbordernode (l, (v, (p'', Vint Int.zero))) p;
           malloc_token sh_bordernode tbordernode p))%assert.
    rewrite sublist_nil by list_solve.
    rewrite Z.sub_0_r.
    rewrite app_nil_l.
    entailer!.
    + forward.
      forward.
      forward.
      entailer!.
      rewrite upd_Znth_app2 by list_solve.
      rewrite <- sublist_map.
      rewrite Zlength_sublist  by list_solve.
      replace (i - (i - 0)) with 0 by omega.
      rewrite upd_Znth0.
      rewrite semax_lemmas.cons_app.
      rewrite sublist_last_1 by list_solve.
      rewrite sublist_list_repeat by list_solve.
      rewrite sublist_map.
      rewrite Zlength_list_repeat by list_solve.
      replace (Zlength key - i - 1) with (Zlength key - (i + 1)) by omega.
      rewrite map_app.
      rewrite <- app_assoc.
      entailer!.
    + forward.
      forward.
      forward.
      Exists p''.
      unfold cstring_len.
      entailer!.
      rewrite Z.sub_diag.
      rewrite sublist_same by list_solve.
      rewrite list_repeat_0.
      rewrite app_nil_r.
      unfold_data_at 2%nat.
      entailer!.
Qed.

Lemma body_BN_GetLink: semax_body Vprog Gprog f_BN_GetLink BN_GetLink_spec.
Proof.
  start_function.
  unfold bordernode_rep.
  destruct bordernode as [[? [|]]].
  - unfold cstring_len.
    Intros p'.
    forward.
    forward_if (False).
    + forward.
      Exists p'.
      unfold cstring_len.
      entailer!.
    + forward.
      entailer!.
  - Intros.
    forward.
    forward_if (True); [rep_omega | forward; entailer! | ].
    forward.
    forward.
    entailer!.
Qed.

Lemma body_BN_SetLink: semax_body Vprog Gprog f_BN_SetLink BN_SetLink_spec.
Proof.
  start_function.
  unfold bordernode_rep.
  destruct bordernode as [[? [|]]].
  - unfold cstring_len.
    Intros p'.
    forward.
    forward_if (
      PROP ( )
      LOCAL (temp _t'1 p'; temp _bn p; temp _val value)
      SEP (malloc_token sh_bordernode tbordernode p;
           field_at sh_bordernode tbordernode [StructField _prefixLinks] l p;
           field_at sh_bordernode tbordernode [StructField _suffixLink] v p;
           field_at sh_bordernode tbordernode [StructField _keySuffix] p' p;
           field_at sh_bordernode tbordernode [StructField _keySuffixLength] (Vint (Int.repr (Zlength s))) p)).
    + forward.
      forward_call (tarray tschar (Zlength s), p').
      entailer!.
    + assert_PROP (False) by entailer!. contradiction.
    + forward.
      forward.
      forward.
      forward.
      entailer!.
  - Intros.
    forward.
    forward_if (True); [rep_omega | forward; entailer! | ].
    forward.
    forward.
    forward.
    forward.
    entailer!.
Qed.
