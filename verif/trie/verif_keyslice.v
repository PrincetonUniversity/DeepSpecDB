(** * verif_newrel.v: Correctness proof of NewRelation *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import util.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import keyslice.

(* a length-parametrized string *)
Definition cstring_len (sh: share) (str: string) (s: val) (len: Z) :=
  data_at sh (tarray tschar len) (map Vbyte (str)) s.

(* platform dependent return value type [tuint] *)
Definition UTIL_GetNextKeySlice_spec: ident * funspec :=
  DECLARE _UTIL_GetNextKeySlice
  WITH str: val, key: string, len: Z, sh: share
  PRE [ _str OF tptr tschar, _len OF tint ]
  PROP (readable_share sh;
        0 <= len <= keyslice_length)
  LOCAL (temp _str str;
         temp _len (Vint (Int.repr len)))
  SEP (cstring_len sh key str len)
  POST [ (if Archi.ptr64 then tulong else tuint) ]
  PROP ()
  LOCAL (temp ret_temp (Vint (Int.repr (get_keyslice key)))) (* machine dependent spec *)
  SEP (cstring_len sh key str len).

Definition Gprog: funspecs :=
  ltac:(with_library prog [
                       UTIL_GetNextKeySlice_spec
       ]).

Lemma body_UTIL_GetNextSlice: semax_body Vprog Gprog f_UTIL_GetNextKeySlice UTIL_GetNextKeySlice_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_if (True); [(forward; entailer) | rep_omega | ]; Intros.
  forward_if (True); [(forward; entailer) | rep_omega | ]; Intros.
  assert_PROP (Zlength key = len). {
    unfold cstring_len.
    entailer!.
    rewrite Zlength_map.
    reflexivity.
  }
  forward_while (EX i:Z, EX res: Z, EX str':val,
    PROP (0 <= i <= len;
          res = get_keyslice_aux (sublist 0 i key) (Z.to_nat i) 0;
          str' = (field_address0 (Tarray tschar len noattr) [ArraySubsc i] str))
    LOCAL (temp _i (Vint (Int.repr i));
           temp _res (Vint (Int.repr res));
           temp _str str';
           temp _len (Vint (Int.repr len)))
    SEP (cstring_len sh key str (Zlength key))).
  Exists 0.
  Exists 0.
  Exists str.
  unfold cstring_len.
  entailer!.
  rewrite field_address0_offset by (auto with field_compatible).
  rewrite isptr_offset_val_zero; auto.
  - entailer!.
  - forward.
    unfold cstring_len.
    assert_PROP (str' = field_address (tarray tschar len) [ArraySubsc i] str). {
      entailer!.
      unfold field_address0.
      unfold field_address.
      rewrite if_true by auto with field_compatible.
      rewrite if_true by auto with field_compatible.
      reflexivity.
    }
    rewrite H0.
    forward.
    forward.
    forward.
    forward.
    Exists (i + 1, get_keyslice_aux (sublist 0 (i + 1) key) (Z.to_nat (i + 1)) 0, (field_address0 (Tarray tschar len noattr) [ArraySubsc (i + 1)] str)).
    unfold cstring_len. entailer!.
    split.
    + rewrite Int.shifted_or_is_add.
      * f_equal.
        f_equal.
        change (8) with (Byte.zwordsize).
        rewrite <- Byte.modulus_power.
        rewrite sublist_split with (mid := i) by list_solve.
        rewrite sublist_len_1 by list_solve.
        replace i with (Zlength (sublist 0 i key)) at 3 by (rewrite Zlength_sublist; list_solve).
        rewrite get_keyslice_snoc.
        f_equal.
        -- rewrite Int.unsigned_repr by (apply get_keyslice_aux_inrange; omega).
           rewrite Zlength_sublist by list_solve.
           rewrite Z.sub_0_r.
           reflexivity.
        -- change 255 with (Z.ones 8).
           rewrite Z.land_ones by omega.
           change (2 ^ 8) with 256.
           pose proof (Z.mod_pos_bound (Byte.signed (Znth i key)) 256).
           assert (0 < 256) by (omega).
           apply H2 in H4.
           rewrite Int.unsigned_repr by rep_omega.
           rewrite <- (Zdiv.Zmod_small) with (n := 256) at 1 by rep_omega.
           apply Byte.eqmod_mod_eq.
           ++ omega.
           ++ replace 256 with Byte.modulus by rep_omega.
              apply Byte.eqmod_sym.
              apply Byte.eqm_signed_unsigned.
      * rep_omega.
      * change 255 with (Z.ones 8).
        rewrite Z.land_ones by omega.
        change (2 ^ 8) with 256.
        pose proof (Z.mod_pos_bound (Byte.signed (Znth i key)) 256).
        assert (0 < 256) by (omega).
        apply H2 in H4.
        rewrite Int.unsigned_repr by rep_omega.
        change (two_p 8) with 256.
        rep_omega.
    + rewrite sem_add_pi_ptr_special by (apply field_address_isptr; auto with field_compatible).
      unfold field_address0.
      unfold field_address.
      rewrite if_true by auto with field_compatible.
      rewrite if_true by auto with field_compatible.
      rewrite offset_offset_val.
      simpl; f_equal; rep_omega.
  - assert (i = len) by rep_omega.
    subst i.
    clear H1 HRE.
    forward_while (EX i:Z, EX res: Z,
      PROP (len <= i <= 4;
            res = get_keyslice_aux key (Z.to_nat i) 0)
      LOCAL (temp _i (Vint (Int.repr i));
             temp _res (Vint (Int.repr res));
             temp _str str';
             temp _len (Vint (Int.repr len)))
      SEP (cstring_len sh key str (Zlength key))).
    Exists len.
    Exists res.
    entailer!.
    rewrite sublist_same by list_solve.
    reflexivity.
    + entailer!.
    + forward.
      forward.
      Exists (i + 1, get_keyslice_aux key (Z.to_nat (i + 1)) 0).
      entailer!.
      rewrite Int.shl_mul.
      rewrite get_keyslice_padding by list_solve.
      change (Int.shl Int.one (Int.repr 8)) with (Int.repr 256).
      rewrite mul_repr.
      f_equal.
    + forward.
      entailer!.
      unfold get_keyslice.
      assert (i = keyslice_length) by rep_omega.
      subst i.
      reflexivity.
Qed.
