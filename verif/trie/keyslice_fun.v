(** * keyslice_fun.v : Functional model of Key and Keyslices *)
Require Import VST.floyd.functional_base.
Import Coq.Lists.List.ListNotations.

Definition string := list byte.
Instance EqDec_string: EqDec string := list_eq_dec Byte.eq_dec.

Definition keyslice_length := Ptrofs.zwordsize / Byte.zwordsize.
Lemma keyslice_length_32: Archi.ptr64 = false -> keyslice_length = 4.
Proof.
  intros H; first [discriminate H | reflexivity].
Qed.
Hint Rewrite keyslice_length_32 using reflexivity: rep_omega.
Lemma keyslice_length_64: Archi.ptr64 = true -> keyslice_length = 8.
Proof.
  intros H; first [discriminate H | reflexivity].
Qed.
Hint Rewrite keyslice_length_64 using reflexivity: rep_omega.

Global Opaque keyslice_length.

Definition keyslice: Set := Z.
Instance EqDec_keyslice: EqDec keyslice := Z.eq_dec.
Definition keyslice_with_len: Set := Z * Z.
Instance EqDec_keyslice_with_len: EqDec keyslice_with_len.
Proof.
  unfold EqDec.
  intros.
  destruct a.
  destruct a'.
  destruct (eq_dec z z1); destruct (eq_dec z0 z2); subst; auto; right; intro; inversion H; auto.
Qed.

Fixpoint get_keyslice_aux (key: string) (n: nat) (result: Z): keyslice :=
  match key, n with
  | _, O => result
  | [], S n' => get_keyslice_aux [] n' (result * Byte.modulus)
  | ch :: key', S n' => get_keyslice_aux key' n' (result * Byte.modulus + (Byte.unsigned ch))
  end.

Definition get_keyslice (key: string): keyslice :=
  get_keyslice_aux key (Z.to_nat keyslice_length) 0.

Definition get_suffix (key: string): string :=
  sublist keyslice_length (Zlength key) key.

Definition get_keyslice_with_len (key: string): keyslice_with_len :=
  (get_keyslice key, Z.min keyslice_length (Zlength key)).

(* A keypath is a sequence of keyslice with an optional suffix *)
Definition keypath_pred (keypath: list keyslice_with_len * option string) :=
  let (keyslice_list, suffix) := keypath in
  Zlength keyslice_list > 0 /\
  if suffix then
    Forall (fun k => snd k = 8) keyslice_list
  else
    Forall (fun k => snd k = 8) (sublist 0 (Zlength keyslice_list - 1) keyslice_list).

Definition keypath := sig keypath_pred.

Function reconstruct_keyslice_aux (slice: Z) (len: Z) {measure Z.to_nat len} :=
  if Z_gt_dec len 0 then
    reconstruct_keyslice_aux (slice / Byte.modulus) (len - 1) ++ [Byte.repr slice]
  else
    [].
Proof.
  intros.
  rewrite <- Z2Nat.inj_lt; omega.
Defined.

Definition reconstruct_keyslice (slice_with_len: keyslice_with_len) :=
  let (slice, len) := slice_with_len in
  reconstruct_keyslice_aux (Z.shiftr slice (keyslice_length - len) * Byte.zwordsize) len.

Definition reconstruct_keypath (keypath: keypath): string :=
  let (keyslice_list, suffix) := proj1_sig keypath in
  match suffix with
  | Some s =>
    concat (map reconstruct_keyslice keyslice_list) ++ s
  | None =>
    concat (map reconstruct_keyslice keyslice_list)
  end.

Definition keypath_rep (keypath: keypath) (key: string): Prop :=
  reconstruct_keypath keypath = key.

Lemma get_keyslice_snoc: forall (key: string) (snoc: byte) (init: Z),
    get_keyslice_aux (key ++ [snoc]) (Z.to_nat (Zlength key + 1)) init = get_keyslice_aux (key) (Z.to_nat (Zlength key)) init * Byte.modulus + (Byte.unsigned snoc).
Proof.
  intros.
  rewrite (ZtoNat_Zlength key).
  generalize dependent init.
  induction key; intros.
  - simpl.
    reflexivity.
  - simpl.
    rewrite Z2Nat.inj_add by list_solve.
    rewrite Nat.add_1_r.
    simpl.
    rewrite Zlength_cons.
    rewrite Z.add_1_r in IHkey.
    rewrite IHkey.
    reflexivity.
Qed.

Lemma get_keyslice_padding_aux: forall (init mult: Z) (i: nat),
    get_keyslice_aux [] i (init * mult) = get_keyslice_aux [] i init * mult.
Proof.
  intros.
  generalize dependent mult.
  generalize dependent init.
  induction i; intros.
  - simpl.
    reflexivity.
  - simpl.
    repeat rewrite IHi.
    rewrite <- Z.mul_assoc.
    rewrite (Z.mul_comm mult Byte.modulus).
    rewrite Z.mul_assoc.
    reflexivity.
Qed.

Lemma get_keyslice_padding: forall (key: string) (init: Z) (i: Z),
    Zlength key <= i ->
    get_keyslice_aux (key) (Z.to_nat (i + 1)) init = get_keyslice_aux (key) (Z.to_nat i) init * Byte.modulus.
Proof.
  intros.
  remember (Z.to_nat i) as n.
  replace (Z.to_nat (i + 1)) with (n + 1)%nat by (rewrite Heqn; rewrite Z2Nat.inj_add by rep_omega; reflexivity).
  assert (length key <= n)%nat. {
    rewrite Zlength_correct in H.
    rewrite <- Z2Nat.id in H by rep_omega.
    rewrite <- Heqn in H.
    apply Nat2Z.inj_le in H.
    assumption.
  }
  clear Heqn.
  clear H.
  generalize dependent key.
  generalize dependent init.
  induction n; intros.
  - destruct key; simpl.
    + reflexivity.
    + simpl in H0.
      list_solve.
  - simpl.
    rewrite IHn by (simpl; omega).
    destruct key.
    + reflexivity.
    + rewrite IHn.
      * reflexivity.
      * simpl in H0.
        omega.
Qed.

Lemma get_keyslice_aux_inrange_aux: forall (key: string) (len: nat) (init: Z),
    0 <= init ->
    0 <= get_keyslice_aux key len init < (init + 1) * Byte.modulus ^ (Z.of_nat len).
Proof.
  intros.
  generalize dependent init.
  generalize dependent key.
  induction len; intros.
  - rewrite Z.pow_0_r.
    simpl.
    destruct key; omega.
  - destruct key.
    + simpl.
      assert (0 <= init * Byte.modulus) by rep_omega.
      specialize (IHlen [] (init * Byte.modulus) H0).
      split; try omega.
      destruct IHlen.
      apply (Z.lt_le_trans _ _ _ H2).
      rewrite Z.mul_add_distr_r.
      rewrite Z.mul_add_distr_r.
      apply Z.add_le_mono.
      * rewrite <- Z.mul_assoc.
        rewrite <- Z.pow_succ_r by apply Nat2Z.is_nonneg.
        rewrite <- Zpos_P_of_succ_nat.
        reflexivity.
      * rewrite Z.pow_pos_fold.
        rewrite Zpos_P_of_succ_nat.
        rewrite Z.pow_succ_r by apply Nat2Z.is_nonneg.
        rewrite (Z.mul_comm Byte.modulus).
        rewrite Z.mul_assoc.
        apply Z.le_mul_diag_r.
        -- rewrite Z.mul_1_l.
           apply Z.pow_pos_nonneg; [rep_omega | apply Nat2Z.is_nonneg].
        -- rep_omega.
    + simpl.
      simpl in IHlen.
      assert (0 <= (init * Byte.modulus + Byte.unsigned i)) by (rep_omega).
      specialize (IHlen key _ H0).
      split; try omega.
      destruct IHlen.
      apply (Z.lt_le_trans _ _ _ H2).
      rewrite <- Z.add_assoc.
      rewrite Z.mul_add_distr_r.
      rewrite (Z.mul_add_distr_r init 1).
      apply Z.add_le_mono.
      * rewrite <- Z.mul_assoc.
        rewrite <- Z.pow_succ_r by apply Nat2Z.is_nonneg.
        rewrite <- Zpos_P_of_succ_nat.
        reflexivity.
      * assert (Byte.unsigned i + 1 <= Byte.modulus). {
          pose proof (Byte.unsigned_range i).
          rep_omega.
        }
        rewrite Z.pow_pos_fold.
        rewrite Zpos_P_of_succ_nat.
        rewrite Z.pow_succ_r by apply Nat2Z.is_nonneg.
        rewrite Z.mul_assoc.
        rewrite Z.mul_1_l.
        apply Z.mul_le_mono_nonneg; try rep_omega.
        apply Z.pow_nonneg.
        rep_omega.
Qed.

Lemma get_keyslice_aux_inrange: forall (key: string) (len: Z),
    0 <= len <= keyslice_length ->
    0 <= get_keyslice_aux key (Z.to_nat len) 0 <= Ptrofs.max_unsigned.
Proof.
  intros.
  pose proof (get_keyslice_aux_inrange_aux key (Z.to_nat len) 0 (Z.le_refl 0)).
  vm_compute (0 + 1) in H0.
  pose proof (Z.pow_le_mono_r Byte.modulus len keyslice_length).
  assert (0 < Byte.modulus) by rep_omega.
  assert (len <= keyslice_length) by omega.
  specialize (H1 H2 H3).
  rewrite Z2Nat.id in H0 by omega.
  change (Byte.modulus ^ keyslice_length) with Ptrofs.modulus in H1.
  rep_omega.
Qed.

Lemma get_keyslice_inrange: forall (key: string),
    0 <= get_keyslice key <= Ptrofs.max_unsigned.
Proof.
  intros.
  unfold get_keyslice.
  simpl (Z.to_nat keyslice_length).
  pose proof (get_keyslice_aux_inrange_aux key (Z.to_nat keyslice_length) 0 (Z.le_refl 0)).
  change ((0 + 1) * _) with Ptrofs.modulus in H.
  rep_omega.
Qed.

