(** * verif_util.v: Correctness proof of utilities *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Require Import DB.functional.keyslice.

Require Import DB.representation.string.

Require Import DB.specs.

Definition Gprog: funspecs :=
  ltac:(with_library prog [
                       UTIL_StrEqual_spec; UTIL_GetNextKeySlice_spec
       ]).

Lemma body_UTIL_GetNextSlice: semax_body Vprog Gprog f_UTIL_GetNextKeySlice UTIL_GetNextKeySlice_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_while (EX i:Z, EX res: Z, EX str':val,
    PROP (0 <= i <= keyslice_length;
          res = get_keyslice_aux (sublist 0 i key) (Z.to_nat i) 0;
          str' = (field_address0 (Tarray tschar (Zlength key) noattr) [ArraySubsc (Z.min i (Zlength key))] str))
    LOCAL (temp _i (Vint (Int.repr i));
           temp _res (Vint (Int.repr res));
           temp _str str';
           temp _len (Vint (Int.repr (Zlength key))))
    SEP (cstring_len sh key str)).
  Exists 0.
  Exists 0.
  Exists str.
  unfold cstring_len.
  Intros.
  rewrite Z.min_l by rep_omega.
  entailer!.
  rewrite field_address0_offset by (auto with field_compatible).
  rewrite isptr_offset_val_zero; auto.
  - entailer!.
  - forward.
    unfold cstring_len.
    Intros.
    forward_if (
     PROP ()
     LOCAL (temp _res (Vint (Int.repr (get_keyslice_aux (sublist 0 (i + 1) key) (Z.to_nat (i + 1)) 0)));
     temp _i (Vint (Int.repr i));
     temp _str (field_address0 (Tarray tschar (Zlength key) noattr)
                               [ArraySubsc (Z.min (i + 1) (Zlength key))]
                               str);
     temp _len (Vint (Int.repr (Zlength key))))
     SEP (data_at sh (tarray tschar (Zlength key)) (map Vbyte key) str)).
    + assert (0 <= Z.min i (Zlength key) < Zlength key)
        by (split; [apply Z.min_glb; list_solve | rewrite Z.min_l; rep_omega]).
      assert_PROP (str' = field_address (tarray tschar (Zlength key)) [ArraySubsc (Z.min i (Zlength key))] str). {
        entailer!.
        unfold field_address0.
        unfold field_address.
        do 2 rewrite if_true by auto with field_compatible.
        reflexivity.
      }
      rewrite H5.
      forward.
      forward.
      forward.
      rewrite ?Z.min_l in * by rep_omega.
      entailer!.
      split.
      * rewrite Int.shifted_or_is_add; [ | rep_omega | ].
        -- f_equal.
           f_equal.
           change (8) with (Byte.zwordsize).
           rewrite <- Byte.modulus_power.
           rewrite sublist_split with (mid := i) by list_solve.
           rewrite sublist_len_1 by list_solve.
           replace i with (Zlength (sublist 0 i key)) at 3 by (rewrite Zlength_sublist; list_solve).
           rewrite get_keyslice_snoc.
           rewrite Int.unsigned_repr by (apply get_keyslice_aux_inrange; rep_omega).
           change 255 with (Z.ones 8).
           rewrite Z.land_ones by omega.
           change (2 ^ 8) with 256.
           pose proof (Z.mod_pos_bound (Byte.signed (Znth i key)) 256 ltac:(rep_omega)).
           rewrite Int.unsigned_repr by rep_omega.
           rewrite Zlength_sublist by list_solve.
           rewrite Z.sub_0_r.
           f_equal.
           rewrite <- (Zdiv.Zmod_small) with (n := 256) at 1 by rep_omega.
           apply Byte.eqmod_mod_eq; [omega | ].
           replace 256 with Byte.modulus by rep_omega.
           apply Byte.eqmod_sym.
           apply Byte.eqm_signed_unsigned.
        -- change 255 with (Z.ones 8).
           rewrite Z.land_ones by omega.
           change (2 ^ 8) with 256.
           pose proof (Z.mod_pos_bound (Byte.signed (Znth i key)) 256 ltac:(rep_omega)).
           rewrite Int.unsigned_repr by rep_omega.
           change (two_p 8) with 256.
           omega.
      * rewrite sem_add_pi_ptr_special.
        -- simpl.
           rewrite field_address0_offset by auto with field_compatible.
           rewrite field_address_offset by auto with field_compatible.
           simpl.
           rewrite offset_offset_val.
           f_equal.
           rep_omega.
        -- apply field_address_isptr.
           auto with field_compatible.
    + forward.
      rewrite ?Z.min_r in * by rep_omega.
      entailer!.
      * f_equal.
        rewrite Int.shl_mul.
        rewrite ?sublist_same_gen by rep_omega.
        rewrite get_keyslice_padding by list_solve.
        change (Int.shl Int.one (Int.repr 8)) with (Int.repr 256).
        rewrite mul_repr.
        f_equal.
    + forward.
      Exists (i + 1, (get_keyslice_aux (sublist 0 (i + 1) key) (Z.to_nat (i + 1)) 0), (field_address0 (Tarray tschar (Zlength key) noattr) [ArraySubsc (Z.min (i + 1) (Zlength key))] str)).
      entailer!.
      fold_cstring_len.
      cancel.
  - forward.
    entailer!.
    unfold get_keyslice.
    assert (i = keyslice_length) by rep_omega.
    subst.
    rewrite <- get_keyslice_aux_gen by rep_omega.
    reflexivity.
Qed.

Lemma body_UTIL_StrEqual: semax_body Vprog Gprog f_UTIL_StrEqual UTIL_StrEqual_spec.
  start_function.
  unfold cstring_len in *.
  Intros.
  forward_if (Zlength str1 = Zlength str2).
  - forward.
    assert (str1 <> str2) by (intro; apply H1; do 2 f_equal; assumption).
    rewrite if_false by auto.
    entailer!.
  - forward.
    entailer!.
  - Intros.
    unfold Sfor.
    forward.
    forward_loop (EX i:Z,
      PROP (0 <= i <= Zlength str1;
            sublist 0 i str1 = sublist 0 i str2)
      LOCAL (temp _i (Vint (Int.repr i));
             temp _a s1;
             temp _lenA (Vint (Int.repr (Zlength str1)));
             temp _b s2;
             temp _lenB (Vint (Int.repr (Zlength str2))))
      SEP (cstring_len sh1 str1 s1; cstring_len sh2 str2 s2))
    break: (
      PROP (str1 = str2)
      LOCAL (temp _a s1;
             temp _lenA (Vint (Int.repr (Zlength str1)));
             temp _b s2;
             temp _lenB (Vint (Int.repr (Zlength str2))))
      SEP (cstring_len sh1 str1 s1; cstring_len sh2 str2 s2));
      unfold cstring_len in *.
    Exists 0.
    do 2 rewrite sublist_nil.
    entailer!.
    + Intros i.
      forward_if (i < Zlength str1); [forward; entailer! | |].
      * forward.
        assert (i = Zlength str1) by omega.
        do 2 rewrite sublist_same in H3 by list_solve.
        entailer!.
      * Intros.
        forward.
        forward.
        forward_if (Znth i str1 = Znth i str2).
        -- forward.
           assert (str1 <> str2) by (intro; subst str1; contradiction).
           rewrite if_false by auto.
           entailer!.
        -- forward.
           entailer!.
        -- forward.
           Exists (i + 1).
           entailer!.
           do 2 rewrite sublist_last_1 by list_solve.
           f_equal; [assumption | f_equal; assumption].
    + Intros.
      forward.
      rewrite if_true by auto.
      entailer!.
Qed.
