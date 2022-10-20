(** * keyslice_fun.v : Functional model of Key and Keyslices *)
Require Import VST.floyd.functional_base.
Import Coq.Lists.List.ListNotations.
Require Import DB.common.

Definition keyslice_length := Ptrofs.zwordsize / Byte.zwordsize.
Lemma keyslice_length_32: Archi.ptr64 = false -> keyslice_length = 4.
Proof using.
  intros H; first [discriminate H | reflexivity].
Qed.
Hint Rewrite keyslice_length_32 using reflexivity: rep_lia.
Lemma keyslice_length_64: Archi.ptr64 = true -> keyslice_length = 8.
Proof using.
  intros H; first [discriminate H | reflexivity].
Qed.
Hint Rewrite keyslice_length_64 using reflexivity: rep_lia.
Global Opaque keyslice_length.

Definition keyslice: Set := Z.
Instance EqDec_keyslice: EqDec keyslice := Z.eq_dec.
Definition keyslice_with_len: Set := Z * Z.
Instance EqDec_keyslice_with_len: EqDec keyslice_with_len.
Proof using.
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
Proof using.
  intros.
  rewrite <- Z2Nat.inj_lt; lia.
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
Proof using.
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

Lemma get_keyslice_aux_gen: forall (key: string) (len: Z) (init: Z),
    0 <= len ->
    get_keyslice_aux key (Z.to_nat len) init = get_keyslice_aux (sublist 0 len key) (Z.to_nat len) init.
Proof using.
  induction key; intros; simpl.

  - unfold sublist. rewrite skipn_0.
    rewrite firstn_nil.
(*or perhaps:
  - unfold sublist.
    rewrite firstn_nil. rewrite skipn_nil.*)

    reflexivity.
  - destruct (Z_lt_dec len (Zlength (a :: key))); destruct (eq_dec len 0).
    + subst.
      reflexivity.
    + rewrite Zlength_cons in l.
      rewrite sublist_split with (mid := 1) by list_solve.
      rewrite sublist_len_1 by list_solve.
      rewrite Znth_0_cons.
      simpl.
      destruct (Z.to_nat len) eqn:Heqn.
      * assert (len = 0). {
          rewrite <- (Z2Nat.id len) by rep_lia.
          rewrite <- (Z2Nat.id 0) by rep_lia.
          f_equal.
          apply Heqn.
        }
        congruence.
      * simpl.
        rewrite sublist_1_cons.
        assert (n0 = Z.to_nat (len - 1)). {
          rewrite <- Nat2Z.id at 1.
          rewrite Z2Nat.inj_sub by rep_lia.
          rewrite Heqn.
          simpl.
          rewrite Nat.sub_0_r.
          rewrite Nat2Z.id.
          reflexivity.
        }
        rewrite H0.
        rewrite IHkey by list_solve.
        reflexivity.
    + subst.
      reflexivity.
    + rewrite sublist_same_gen by rep_lia.
      destruct (Z.to_nat len) eqn:Heqn.
      * assert (len = 0). {
          rewrite <- (Z2Nat.id len) by rep_lia.
          rewrite <- (Z2Nat.id 0) by rep_lia.
          f_equal.
          apply Heqn.
        }
        congruence.
      * reflexivity.
Qed.

Lemma get_keyslice_padding_aux: forall (init mult: Z) (i: nat),
    get_keyslice_aux [] i (init * mult) = get_keyslice_aux [] i init * mult.
Proof using.
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
Proof using.
  intros.
  remember (Z.to_nat i) as n.
  replace (Z.to_nat (i + 1)) with (n + 1)%nat by (rewrite Heqn; rewrite Z2Nat.inj_add by rep_lia; reflexivity).
  assert (length key <= n)%nat. {
    rewrite Zlength_correct in H.
    rewrite <- Z2Nat.id in H by rep_lia.
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
    rewrite IHn by (simpl; lia).
    destruct key.
    + reflexivity.
    + rewrite IHn.
      * reflexivity.
      * simpl in H0.
        lia.
Qed.

Lemma get_keyslice_aux_init_lt: forall k1 k2 init1 init2 len,
    init1 < init2 ->
    get_keyslice_aux k1 len init1 < get_keyslice_aux k2 len init2.
Proof using.
  intros.
  generalize dependent init1.
  generalize dependent init2.
  generalize dependent k1.
  generalize dependent k2.
  induction len; intros.
  - destruct k1; destruct k2; simpl; lia.
  - destruct k1; destruct k2; simpl;
      apply IHlen; rep_lia.
Qed.

Lemma get_keyslice_cons_inv: forall c1 c2 k1 k2 init len,
    0 < len ->
    get_keyslice_aux (c1 :: k1) (Z.to_nat len) init = get_keyslice_aux (c2 :: k2) (Z.to_nat len) init ->
    Byte.unsigned c1 = Byte.unsigned c2.
Proof using.
  intros.
  remember (Z.to_nat len) as n.
  assert (0 < n)%nat. {
    apply Nat2Z.inj_lt.
    rewrite Heqn.
    rewrite Z2Nat.id by rep_lia.
    rep_lia.
  }
  clear H Heqn len.
  generalize dependent k1.
  generalize dependent k2.
  generalize dependent c1.
  generalize dependent c2.
  generalize dependent init.
  induction n; intros.
  - rep_lia.
  - simpl in H0.
    destruct (eq_dec (Byte.unsigned c1) (Byte.unsigned c2)).
    + auto.
    + assert (Byte.unsigned c1 < Byte.unsigned c2 \/ Byte.unsigned c1 > Byte.unsigned c2) by rep_lia.
      destruct H;
        first [
            pose proof (get_keyslice_aux_init_lt
                          k1 k2
                          (init * Byte.modulus + Byte.unsigned c1) (init * Byte.modulus + Byte.unsigned c2) n
                          ltac:(rep_lia))
          | pose proof (get_keyslice_aux_init_lt
                          k2 k1
                          (init * Byte.modulus + Byte.unsigned c2) (init * Byte.modulus + Byte.unsigned c1) n
                          ltac:(rep_lia))
          ];
        rep_lia.
Qed.

Lemma get_keyslice_aux_eq_inv: forall k1 k2 init1 init2 len,
    get_keyslice_aux k1 len init1 = get_keyslice_aux k2 len init1 ->
    get_keyslice_aux k1 len init2 = get_keyslice_aux k2 len init2.
Proof using.
  intros.
  generalize dependent k1.
  generalize dependent k2.
  generalize dependent init1.
  generalize dependent init2.
  induction len; intros.
  - destruct k1; destruct k2; reflexivity.
  - destruct k1; destruct k2; simpl in H; simpl;
      first [
          eapply IHlen; apply H
        | let Heqn := fresh "Heqn" in
          destruct (eq_dec (init1 * Byte.modulus + Byte.unsigned i) (init1 * Byte.modulus)) as [Heqn | Heqn];
          first [
              let Hzero := fresh "Hzero" in
              assert (Hzero: Byte.unsigned i = 0) by rep_lia;
              rewrite Hzero in *;
              rewrite Z.add_0_r in *;
              eapply IHlen;
              apply H
            | let Hnzero := fresh "Hnzero" in
              assert (Hnzero: Byte.unsigned i <> 0) by rep_lia;
              match goal with
              | [H : get_keyslice_aux ?k2 _ (_ + _) = get_keyslice_aux ?k1 _ _ |- _] =>
                pose proof (get_keyslice_aux_init_lt
                              k1 k2 (init1 * Byte.modulus) (init1 * Byte.modulus + Byte.unsigned i) len
                              ltac:(rep_lia)); rep_lia
              | [H : get_keyslice_aux ?k1 _ _ = get_keyslice_aux ?k2 _ (_ + _) |- _] =>
                pose proof (get_keyslice_aux_init_lt
                              k1 k2 (init1 * Byte.modulus) (init1 * Byte.modulus + Byte.unsigned i) len
                              ltac:(rep_lia)); rep_lia
              end
            ]
        | let Heqn := fresh "Heqn" in
          destruct (eq_dec (Byte.unsigned i) (Byte.unsigned i0)) as [Heqn | ];
          first [
              rewrite Heqn in *;
              eapply IHlen;
              apply H
            | assert (Byte.unsigned i < Byte.unsigned i0 \/ Byte.unsigned i > Byte.unsigned i0) by rep_lia;
              destruct H0;
              first [
                  pose proof (get_keyslice_aux_init_lt
                                k1 k2
                                (init1 * Byte.modulus + Byte.unsigned i) (init1 * Byte.modulus + Byte.unsigned i0) len
                                ltac:(rep_lia))
                | pose proof (get_keyslice_aux_init_lt
                                k2 k1
                                (init1 * Byte.modulus + Byte.unsigned i0) (init1 * Byte.modulus + Byte.unsigned i) len
                                ltac:(rep_lia))
                ];
              rep_lia
            ]
        ].
Qed.

Lemma get_keyslice_aux_inrange_aux: forall (key: string) (len: nat) (init: Z),
    0 <= init ->
    0 <= get_keyslice_aux key len init < (init + 1) * Byte.modulus ^ (Z.of_nat len).
Proof using.
  intros.
  generalize dependent init.
  generalize dependent key.
  induction len; intros.
  - rewrite Z.pow_0_r.
    simpl.
    destruct key; lia.
  - destruct key.
    + simpl.
      assert (0 <= init * Byte.modulus) by rep_lia.
      specialize (IHlen [] (init * Byte.modulus) H0).
      split; try lia.
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
           apply Z.pow_pos_nonneg; [rep_lia | apply Nat2Z.is_nonneg].
        -- rep_lia.
    + simpl.
      simpl in IHlen.
      assert (0 <= (init * Byte.modulus + Byte.unsigned i)) by (rep_lia).
      specialize (IHlen key _ H0).
      split; try lia.
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
          rep_lia.
        }
        rewrite Z.pow_pos_fold.
        rewrite Zpos_P_of_succ_nat.
        rewrite Z.pow_succ_r by apply Nat2Z.is_nonneg.
        rewrite Z.mul_assoc.
        rewrite Z.mul_1_l.
        apply Z.mul_le_mono_nonneg; try rep_lia.
        apply Z.pow_nonneg.
        rep_lia.
Qed.

Lemma get_keyslice_aux_inrange: forall (key: string) (len: Z),
    0 <= len <= keyslice_length ->
    0 <= get_keyslice_aux key (Z.to_nat len) 0 <= Ptrofs.max_unsigned.
Proof using.
  intros.
  pose proof (get_keyslice_aux_inrange_aux key (Z.to_nat len) 0 (Z.le_refl 0)).
  vm_compute (0 + 1) in H0.
  pose proof (Z.pow_le_mono_r Byte.modulus len keyslice_length).
  assert (0 < Byte.modulus) by rep_lia.
  assert (len <= keyslice_length) by lia.
  specialize (H1 H2 H3).
  rewrite Z2Nat.id in H0 by lia.
  change (Byte.modulus ^ keyslice_length) with Ptrofs.modulus in H1.
  rep_lia.
Qed.

Lemma get_keyslice_inrange: forall (key: string),
    0 <= get_keyslice key <= Ptrofs.max_unsigned.
Proof using.
  intros.
  unfold get_keyslice.
  simpl (Z.to_nat keyslice_length).
  pose proof (get_keyslice_aux_inrange_aux key (Z.to_nat keyslice_length) 0 (Z.le_refl 0)).
  change ((0 + 1) * _) with Ptrofs.modulus in H.
  rep_lia.
Qed.

Lemma get_keyslice_aux_len_eq: forall k1 k2 len init ,
    0 <= len ->
    get_keyslice_aux k1 (Z.to_nat len) init = get_keyslice_aux k2 (Z.to_nat len) init ->
    Zlength k1 = Zlength k2 ->
    Zlength k1 <= len ->
    k1 = k2.
Proof using.
  intros.
  remember (Z.to_nat len) as n.
  generalize dependent k1.
  generalize dependent k2.
  generalize dependent init.
  generalize dependent len.
  induction n; intros.
  - assert (len = 0). {
      rewrite <- (Nat2Z.id 0%nat) in Heqn.
      apply Z2Nat.inj in Heqn; rep_lia.
    }
    assert (k1 = []) by (apply Zlength_nil_inv; rep_lia).
    assert (k2 = []) by (apply Zlength_nil_inv; rep_lia).
    subst; reflexivity.
  - remember (len - 1) as len'.
    assert (n = Z.to_nat len'). {
      replace n with (S n - 1)%nat by lia.
      rewrite Heqn.
      rewrite Heqlen'.
      rewrite Z2Nat.inj_sub by rep_lia.
      reflexivity.
    }
    assert (1 <= len). {
      replace len with (Z.of_nat (S n)).
      - rewrite Nat2Z.inj_succ.
        rep_lia.
      - rewrite Heqn.
        rewrite Z2Nat.id; rep_lia.
    }
    specialize (IHn len' ltac:(rep_lia) ltac:(assumption)).
    destruct k1; destruct k2;
      first [
          reflexivity
        | replace (Zlength []) with 0 in H1 by list_solve;
          rewrite Zlength_cons in H1;
          rep_lia
        | idtac
        ].
    pose proof H0.
    rewrite Heqn in H0.
    apply get_keyslice_cons_inv in H0; [ | rep_lia].
    simpl in H5.
    rewrite H0 in H5.
    rewrite ?Zlength_cons in H2.
    rewrite ?Zlength_cons in H1.
    specialize (IHn _ _ _ H5 ltac:(list_solve) ltac:(list_solve)).
    f_equal; [ | assumption].
    assert (Byte.repr (Byte.unsigned i) = Byte.repr (Byte.unsigned i0)). {
      rewrite H0.
      reflexivity.
    }
    rewrite ?Byte.repr_unsigned in H6.
    trivial.
Qed.

Lemma keyslice_inj1: forall (k1 k2: string),
    k1 <> k2 ->
    get_keyslice k1 = get_keyslice k2 ->
    Zlength k1 <= keyslice_length \/ Zlength k2 <= keyslice_length ->
    Zlength k1 <> Zlength k2.
Proof using.
  intros.
  destruct (Z_le_dec (Zlength k2) keyslice_length).
  - intro.
    unfold get_keyslice in H0.
    pose proof (get_keyslice_aux_len_eq k1 k2 keyslice_length 0 ltac:(rep_lia) H0 H2 ltac:(lia)).
    auto.
  - destruct H1; lia.
Qed.

Lemma keyslice_inj2_aux: forall (k1 k2: string) init n,
    0 <= n ->
    get_keyslice_aux k1 (Z.to_nat n) init = get_keyslice_aux k2 (Z.to_nat n) init ->
    Zlength k1 > n /\ Zlength k2 > n ->
    sublist 0 n k1 = sublist 0 n k2.
Proof using.
  intros.
  generalize dependent k1.
  generalize dependent k2.
  generalize dependent init.
  remember (Z.to_nat n) as k.
  generalize dependent n.
  induction k; intros.
  - assert (n = 0). {
      rewrite <- Z2Nat.id by lia.
      simpl (Z.to_nat 0).
      rewrite Heqk.
      rewrite Z2Nat.id; rep_lia.
    }
    rewrite H2.
    rewrite ?sublist_nil.
    reflexivity.
  - destruct k1; destruct k2; subst; try (rewrite Zlength_nil in H1; rep_lia).
    pose proof H0.
    assert (0 < n). {
      destruct (eq_dec n 0).
      - subst.
        inversion Heqk.
      - lia.
    }
    rewrite Heqk in H2.
    apply get_keyslice_cons_inv in H2; [ | rep_lia].
    assert (i = i0). {
      rewrite <- (Byte.repr_unsigned i).
      rewrite <- (Byte.repr_unsigned i0).
      rewrite H2.
      reflexivity.
    }
    subst.
    simpl in H0.
    remember (n - 1) as n'.
    assert (k = Z.to_nat n'). {
      rewrite Heqn'.
      rewrite Z2Nat.inj_sub by rep_lia.
      rewrite <- Heqk.
      simpl.
      rewrite Nat.sub_0_r.
      reflexivity.
    }
    subst.
    rewrite ?Zlength_cons in H1.
    apply IHk with (n0 := n - 1) in H0; first [rep_lia | auto | idtac].
    rewrite sublist_split with (mid := 1) by list_solve.
    rewrite sublist_split with (mid := 1) (al := i0 :: k2) by list_solve.
    rewrite ?sublist_1_cons.
    rewrite H0.
    rewrite ?sublist_len_1 by list_solve.
    rewrite ?Znth_0_cons.
    reflexivity.
Qed.

Lemma keyslice_inj2: forall (k1 k2: string),
    get_keyslice k1 = get_keyslice k2 ->
    Zlength k1 > keyslice_length /\ Zlength k2 > keyslice_length ->
    sublist 0 keyslice_length k1 = sublist 0 keyslice_length k2.
Proof using.
  intros.
  unfold get_keyslice in H.
<<<<<<< HEAD
  destruct (zlt keyslice_length 0).
   rewrite !sublist_nil_gen by lia. auto.
=======
>>>>>>> origin/master
  apply keyslice_inj2_aux in H; first [rep_lia | auto].
Qed.

Lemma keyslice_inj3: forall (k1 k2: string),
    k1 <> k2 ->
    get_keyslice k1 = get_keyslice k2 ->
    Zlength k1 > keyslice_length /\ Zlength k2 > keyslice_length ->
    get_suffix k1 <> get_suffix k2.
Proof using.
  intros.
  assert (sublist 0 keyslice_length k1 = sublist 0 keyslice_length k2)
    by (apply keyslice_inj2; auto; rep_lia).
  unfold get_suffix.
  intro.
  assert (k1 = k2). {
    rewrite <- sublist_same with (lo := 0) (hi := Zlength k1) (al := k1) by rep_lia.
    rewrite <- sublist_same with (lo := 0) (hi := Zlength k2) (al := k2) by rep_lia.
<<<<<<< HEAD
    destruct (zlt keyslice_length 0).
    unfold sublist in H3.
    replace (Z.to_nat keyslice_length) with (Z.to_nat 0) in H3
     by (rewrite (Z2Nat_neg keyslice_length) by auto; auto).
    fold (sublist 0 (Zlength k1) k1) in H3.
    fold (sublist 0 (Zlength k2) k2) in H3.
    auto.
=======
>>>>>>> origin/master
    rewrite sublist_split with (mid := keyslice_length) by first [rep_lia | list_solve].
    rewrite sublist_split with (mid := keyslice_length) (al := k2) by first [rep_lia | list_solve].
    congruence.
  }
  auto.
Qed.
