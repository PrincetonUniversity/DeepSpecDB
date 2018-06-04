Require Import VST.floyd.proofauto.
Require Import common.

Definition cstring_len {cs: compspecs} (sh: share) (str: string) (s: val) :=
  data_at sh (tarray tschar (Zlength str)) (map Vbyte str) s && !! (0 < Zlength str <= Int.max_unsigned).

Lemma cstring_len_local_facts {cs: compspecs} (sh: share) (str: string) (s: val):
  cstring_len sh str s |-- !! isptr s.
Proof.
  unfold cstring_len.
  entailer!.
Qed.

Hint Resolve cstring_len_local_facts: saturate_local.

Lemma cstring_len_valid_pointer {cs: compspecs} (sh: share) (str: string) (s: val):
  sepalg.nonidentity sh ->
  cstring_len sh str s |-- valid_pointer s.
Proof.
  unfold cstring_len.
  entailer!.
  apply data_at_valid_ptr; [auto | simpl; rewrite ?Z.max_r; rep_omega].
Qed.

Lemma cstring_len_split {cs: compspecs} (sh: share) (str: string) (s: val) (k: Z):
  0 < k < Zlength str ->
  cstring_len sh str s = !! (Zlength str <= Int.max_unsigned) && cstring_len sh (sublist 0 k str) s * cstring_len sh (sublist k (Zlength str) str) (field_address (tarray tschar (Zlength str)) [ArraySubsc k] s).
Proof.
  intros.
  unfold cstring_len.
  apply pred_ext.
  - assert_PROP (field_address (tarray tschar (Zlength str)) [ArraySubsc k] s = field_address0 (tarray tschar (Zlength str)) [ArraySubsc k] s). {
      entailer!.
      rewrite field_address_offset by auto with field_compatible.
      rewrite field_address0_offset by auto with field_compatible.
      reflexivity.
    }
    erewrite (split2_data_at_Tarray sh tschar (Zlength str) k (map Vbyte str)) with (v' := (map Vbyte str));
      [ | rep_omega
        | list_solve
        | autorewrite with sublist; auto
        | eauto
        | eauto
      ].
    entailer!.
    + split3; rewrite ?Zlength_sublist; list_solve.
    + rewrite ?sublist_map.
      rewrite ?Zlength_sublist by rep_omega.
      rewrite Z.sub_0_r.
      rewrite H0.
      cancel.
  - entailer!.
    erewrite (split2_data_at_Tarray sh tschar (Zlength str) k (map Vbyte str)) with (v' := (map Vbyte str));
      [ | rep_omega
        | list_solve
        | autorewrite with sublist; auto
        | eauto
        | eauto
      ].
    rewrite ?sublist_map.
    rewrite ?Zlength_sublist by rep_omega.
    rewrite Z.sub_0_r.
    rewrite field_address_offset by auto with field_compatible.
    rewrite field_address0_offset by auto with field_compatible.
    cancel.
Qed.

Lemma cstring_len_fold {cs: compspecs} (sh: share) (str: string) (s: val):
  0 < Zlength str <= Int.max_unsigned ->
  data_at sh (tarray tschar (Zlength str)) (map Vbyte str) s |-- cstring_len sh str s.
Proof.
  intros.
  unfold cstring_len.
  entailer!.
Qed.

Ltac fold_cstring_len :=
  match goal with
  | |- context [data_at ?sh (tarray tschar ?len) (map Vbyte ?str) ?s] =>
    replace len with (Zlength str) by list_solve;
    sep_apply (cstring_len_fold sh str s ltac:(list_solve))
  | _ => fail "please make sure that the length is solvable by list_solve"
  end.

Lemma fold_cstring_len_example {cs: compspecs} (sh: share) (str1 str2: string) (s: val):
  0 < Zlength str1 + Zlength str2 <= Int.max_unsigned ->
  data_at sh (tarray tschar (Zlength (str1 ++ str2))) (map Vbyte str1 ++ map Vbyte str2) s |-- cstring_len sh (str1 ++ str2) s.
Proof.
  intros.
  rewrite <- map_app.
  fold_cstring_len.
  cancel.
Abort.
