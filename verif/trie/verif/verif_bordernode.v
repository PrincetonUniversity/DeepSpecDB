(** * verif_bordernode.v: Correctness proof of bordernode *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import DB.common.
Require Import DB.tactics.
Require Import DB.lemmas.

Require Import DB.functional.bordernode.
Require Import DB.functional.keyslice.

Require Import DB.representation.bordernode.
Require Import DB.representation.string.
Require Import DB.representation.key.

Require Import DB.specs.

Import Coq.Lists.List.ListNotations.

Definition Gprog : funspecs :=
  ltac:(with_library prog [
          surely_malloc_spec; UTIL_StrEqual_spec;
          BN_NewBorderNode_spec; BN_FreeBorderNode_spec;
          BN_SetPrefixValue_spec; BN_GetPrefixValue_spec;
          BN_GetSuffixValue_spec; BN_SetSuffixValue_spec;
          BN_TestSuffix_spec; BN_ExportSuffixValue_spec;
          BN_SetLink_spec; BN_GetLink_spec;
          BN_HasSuffix_spec; BN_SetValue_spec;
          move_key_spec
       ]).

Lemma body_BN_FreeBorderNode: semax_body Vprog Gprog f_BN_FreeBorderNode BN_FreeBorderNode_spec.
Proof.
  start_function.
  forward_if (True); [assert_PROP (False) by entailer!; contradiction | forward; entailer! | ].
  unfold bordernode_rep.
  destruct bordernode as [[? [|]]].
  - Intros p'.
    forward.
    forward_if (
        PROP ( )
        LOCAL (temp _t'1 p'; temp _bordernode p)
        SEP (malloc_token Ews tbordernode p; field_at Ews tbordernode [StructField _prefixLinks] l p;
             field_at Ews tbordernode [StructField _suffixLink] v p;
             field_at Ews tbordernode [StructField _keySuffix] p' p;
             field_at Ews tbordernode [StructField _keySuffixLength]
                      (Vint (Int.repr (Zlength s))) p));
      [ | assert_PROP (False) by entailer!; contradiction | ].
    forward.
    unfold cstring_len.
    Intros.
    forward_call (tarray tschar (Zlength s), p').
    entailer!.
    fold_tbordernode.
    forward_call (tbordernode, p).
    forward.
  - Intros.
    forward.
    forward_if (True); [contradiction | forward; entailer! |].
    fold_tbordernode.
    forward_call (tbordernode, p).
    forward.
Qed.

Lemma body_BN_NewBorderNode: semax_body Vprog Gprog f_BN_NewBorderNode BN_NewBorderNode_spec.
Proof.
  start_function.
  forward_call (tbordernode).
  split3; auto; simpl; rep_lia.
  Intros p.
  forward_for_simple_bound (keyslice_length) (EX i: Z,
    PROP (0 <= i <= keyslice_length)
    LOCAL (temp _bordernode p)
    SEP (malloc_token Ews tbordernode p;
         data_at Ews tbordernode (list_repeat (Z.to_nat i) nullval ++ list_repeat (Z.to_nat (keyslice_length - i)) Vundef, (Vundef, (Vundef, Vundef))) p))%assert.
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
    replace (keyslice_length  - (i + 1)) with (keyslice_length - i - 1) by rep_lia.
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
    apply Forall_list_repeat. auto.
Qed.

Lemma body_BN_SetPrefixValue: semax_body Vprog Gprog f_BN_SetPrefixValue BN_SetPrefixValue_spec.
Proof.
  start_function.
  assert_PROP (Zlength (fst (fst bordernode)) = keyslice_length). {
    entailer!.
  }
  unfold bordernode_rep.
  destruct bordernode as [[]]; simpl in H0.
  Intros.
  forward.
  entailer!.
  forward.
  entailer!.
  apply Forall_upd_Znth; first [list_solve | assumption].
Qed.

Lemma body_BN_GetPrefixValue: semax_body Vprog Gprog f_BN_GetPrefixValue BN_GetPrefixValue_spec.
Proof.
  start_function.
  assert_PROP (Zlength (fst (fst bordernode)) = keyslice_length). {
    entailer!.
  }
  unfold bordernode_rep.
  destruct bordernode as [[]]; simpl in H0.
  Intros.
  forward.
  + entailer!.
  + entailer!.
    apply Forall_Znth; [rep_lia | assumption].
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
      forward_call (sh_string, s, key, Ews, p', s0).
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
           data_at sh_string (tarray tschar (Zlength key)) (map Vbyte key) s)).
    + forward.
      forward_call (tarray tschar (Zlength s0), p').
      entailer!.
    + forward.
      entailer!.
    + forward_call (tarray tschar (Zlength key)).
      split3; simpl; auto. rewrite Z.max_r; rep_lia.
      Intros p''.
      forward.
      forward_for_simple_bound (Zlength key) (EX i:Z,
        PROP ()
        LOCAL (temp _t'1 p''; temp _t'4 p'; temp _bn p; temp _suffix s;
               temp _len (Vint (Int.repr (Zlength key))); temp _val value)
        SEP (malloc_token Ews (tarray tschar (Zlength key)) p'';
             data_at Ews (tarray tschar (Zlength key))
                     (map Vbyte (sublist 0 i key) ++ list_repeat (Z.to_nat (Zlength key - i)) Vundef) p'';
             data_at sh_string (tarray tschar (Zlength key)) (map Vbyte key) s;
             data_at sh_bordernode tbordernode (l, (v, (p'', Vint (Int.repr (Zlength s0))))) p))%assert.
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
        replace (i - (i - 0)) with 0 by lia.
        rewrite upd_Znth0.
        rewrite semax_lemmas.cons_app.
        rewrite sublist_last_1 by list_solve.
        rewrite sublist_list_repeat by list_solve.
        rewrite sublist_map.
        rewrite Zlength_list_repeat by list_solve.
        replace (Zlength key - i - 1) with (Zlength key - (i + 1)) by lia.
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
    forward_if (True); [rep_lia | forward; entailer! | ].
    forward_call (tarray tschar (Zlength key)).
    split3; simpl; auto. rewrite Z.max_r; rep_lia.
    Intros p''.
    forward.
    forward_for_simple_bound (Zlength key) (EX i:Z,
      PROP ()
      LOCAL (temp _t'1 p''; temp _bn p; temp _suffix s;
             temp _len (Vint (Int.repr (Zlength key))); temp _val value)
      SEP (malloc_token Ews (tarray tschar (Zlength key)) p'';
           data_at Ews (tarray tschar (Zlength key))
                   (map Vbyte (sublist 0 i key) ++ list_repeat (Z.to_nat (Zlength key - i)) Vundef) p'';
           data_at sh_string (tarray tschar (Zlength key)) (map Vbyte key) s;
           data_at sh_bordernode tbordernode (l, (v, (p'', Vint Int.zero))) p))%assert.
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
      replace (i - (i - 0)) with 0 by lia.
      rewrite upd_Znth0.
      rewrite semax_lemmas.cons_app.
      rewrite sublist_last_1 by list_solve.
      rewrite sublist_list_repeat by list_solve.
      rewrite sublist_map.
      rewrite Zlength_list_repeat by list_solve.
      replace (Zlength key - i - 1) with (Zlength key - (i + 1)) by lia.
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

Lemma body_BN_TestSuffix: semax_body Vprog Gprog f_BN_TestSuffix BN_TestSuffix_spec.
Proof.
  start_function.
  unfold bordernode_rep.
  destruct bordernode as [[? [|]]].
  - Intros p'.
    forward.
    forward_if.
    + unfold key_rep.
      Intros k'.
      forward.
      forward.
      forward.
      forward.
      rewrite (cstring_len_split _ key k' keyslice_length) by rep_lia.
      Intros.
      fold (get_suffix key).
      forward_call (
          Ews, (field_address (tarray tschar (Zlength key)) [ArraySubsc keyslice_length] k'), get_suffix key,
          Ews, p', s).
      { unfold cstring_len.
        entailer!.
        split.
        - rewrite field_address_offset by (auto with field_compatible).
          simpl.
          replace (0 + 1 * keyslice_length) with 4 by rep_lia.
          f_equal.
        - unfold get_suffix.
          rewrite Zlength_sublist by rep_lia.
          reflexivity.
      }
      forward.
      Exists p'.
      entailer!.
      * if_tac.
        -- rewrite if_true.
           auto.
           f_equal.
           assumption.
        -- rewrite if_false.
           auto.
           inversion 1.
           auto.
      * unfold key_rep.
        Exists k'.
        rewrite (cstring_len_split _ key k' keyslice_length) by rep_lia.
        entailer!.
        apply derives_refl.
    + assert_PROP (False) by entailer!. contradiction.
  - Intros.
    forward.
    forward_if.
    + assert_PROP (False) by entailer!. contradiction.
    + forward.
      entailer!.
Qed.

Lemma body_BN_ExportSuffixValue: semax_body Vprog Gprog f_BN_ExportSuffixValue BN_ExportSuffixValue_spec.
Proof.
  start_function.
  unfold bordernode_rep.
  destruct bordernode as [[? [|]]].
  - Intros p'.
    forward.
    forward_if (EX k': val,
        PROP ()
        LOCAL (temp _bn p; temp _key k)
        SEP (key_rep Ews s k'; malloc_token Ews tkey k';
             field_at sh_bordernode tbordernode [StructField _prefixLinks] l p;
             field_at sh_bordernode tbordernode [StructField _suffixLink] v p;
             field_at sh_bordernode tbordernode [StructField _keySuffix] (Vint (Int.repr 0)) p;
             field_at sh_bordernode tbordernode [StructField _keySuffixLength] (Vint (Int.repr 0)) p;
             data_at sh_keybox tkeybox k' k)
      )%assert; [ | assert_PROP (False) by entailer!; contradiction | ].
    + forward.
      forward.
      forward_call (s, p').
      Intros k'.
      forward.
      forward.
      forward.
      Exists k'.
      entailer!.
    + Intros k'.
      forward.
      forward.
      forward.
      Exists k'.
      entailer!.
  - Intros.
    forward.
    forward_if (
        PROP ()
        LOCAL (temp _t'2 nullval; temp _bn p; temp _key k)
        SEP (field_at sh_bordernode tbordernode [StructField _prefixLinks] l p;
             field_at sh_bordernode tbordernode [StructField _suffixLink] v p;
             field_at sh_bordernode tbordernode [StructField _keySuffix] nullval p;
             field_at sh_bordernode tbordernode [StructField _keySuffixLength] (Vint Int.zero) p;
             data_at sh_keybox tkeybox (Vint (Int.repr 0)) k)
      )%assert; [contradiction | | ].
    forward.
    entailer!.
    forward.
    forward.
    forward.
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
    forward_if (True); [rep_lia | forward; entailer! | ].
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
      SEP (field_at sh_bordernode tbordernode [StructField _prefixLinks] l p;
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
    forward_if (True); [rep_lia | forward; entailer! | ].
    forward.
    forward.
    forward.
    forward.
    entailer!.
Qed.

Lemma body_BN_HasSuffix: semax_body Vprog Gprog f_BN_HasSuffix BN_HasSuffix_spec.
Proof.
  start_function.
  unfold bordernode_rep.
  destruct bordernode as [[? [|]]].
  - Intros p'.
    forward.
    forward.
    Exists p'.
    entailer!.
    destruct p'; try contradiction; reflexivity.
  - Intros.
    forward.
    forward.
    entailer!.
Qed.

Lemma body_BN_SetValue: semax_body Vprog Gprog f_BN_SetValue BN_SetValue_spec.
Proof.
  start_function.
  unfold key_rep.
  Intros k'.
  forward.
  assert_PROP (Int.unsigned (Int.repr (Zlength key)) = Zlength key). {
    unfold key_rep.
    unfold cstring_len.
    entailer!.
  }
  forward_if (
      PROP ()
      LOCAL ()
      SEP (bordernode_rep sh_node (BorderNode.put_value key v bordernode) p;
           key_rep sh_key key k))%assert.
  - forward.
    forward.
    rewrite (cstring_len_split _ key k' keyslice_length) by rep_lia.
    Intros.
    fold (get_suffix key).
    forward_call (Ews, get_suffix key,
                  field_address (tarray tschar (Zlength key)) [ArraySubsc keyslice_length] k',
                  sh_node, bordernode, p, v).
    entailer!. split.
    + rewrite field_address_offset by auto with field_compatible.
      reflexivity.
    + unfold get_suffix.
      rewrite Zlength_sublist by rep_lia.
      reflexivity.
    + unfold key_rep.
      Exists k'.
      rewrite (cstring_len_split _ key k' keyslice_length) by rep_lia.
      unfold BorderNode.put_value.
      rewrite if_false by rep_lia.
      (* the type differs as string and list byte *)
      change (list Byte.int) with string.
      unfold get_suffix.
      entailer!.
  - forward.
    assert_PROP (0 < Zlength key). {
      unfold key_rep.
      unfold cstring_len.
      entailer!.
    }
    forward_call (sh_node, Zlength key, bordernode, p, v).
    split; [rep_lia | auto].
    unfold BorderNode.put_value.
    rewrite if_true by rep_lia.
    fold_keyrep.
    entailer!.
  - forward.
Qed.
