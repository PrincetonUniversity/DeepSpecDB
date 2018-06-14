Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.

Lemma iter_sepcon_split3 {A: Type} {Inh: Inhabitant A} (l: list A) (P: A -> mpred) (k: Z):
  0 <= k < Zlength l ->
  iter_sepcon l P = iter_sepcon (sublist 0 k l) P * P (Znth k l) * iter_sepcon (sublist (k + 1) (Zlength l) l) P.
Proof.
  intros.
  rewrite <- (sublist_same 0 (Zlength l) l) at 1 by reflexivity.
  rewrite (sublist_split 0 k (Zlength l) l) by list_solve.
  rewrite (sublist_split k (k + 1) (Zlength l) l) by list_solve.
  rewrite ?iter_sepcon_app.
  rewrite sublist_len_1 by list_solve.
  simpl.
  rewrite sepcon_emp.
  rewrite <- sepcon_assoc.
  reflexivity.
Qed.

Lemma iter_sepcon_upd_Znth {A: Type} {Inh: Inhabitant A} (l: list A) (P: A -> mpred) (a: A) (k: Z):
  0 <= k < Zlength l ->
  iter_sepcon l P * P a = iter_sepcon (upd_Znth k l a) P * P (Znth k l).
Proof.
  intros.
  rewrite <- (sublist_same 0 (Zlength l) l) by reflexivity.
  rewrite sublist_same at 3 by reflexivity.
  rewrite (sublist_split 0 k (Zlength l) l) by list_solve.
  rewrite (sublist_split k (k + 1) (Zlength l) l) by list_solve.
  rewrite upd_Znth_app2 by list_solve.
  rewrite upd_Znth_app1 by list_solve.
  rewrite ?iter_sepcon_app.
  rewrite sublist_len_1 by list_solve.
  rewrite Zlength_sublist by list_solve.
  replace (k - (k - 0)) with 0 by omega.
  rewrite upd_Znth0.
  simpl.
  rewrite ?sepcon_emp.
  rewrite <- ?sepcon_assoc.
  pull_right (P a); f_equal;
    pull_right (P (Znth k l)); f_equal.
Qed.

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

Lemma Z_induction (P: Z -> Prop) (lower_bound: Z) (n: Z):
  P lower_bound ->
  (forall n', (forall n'', lower_bound <= n'' < n' -> P n'') -> P n') ->
  lower_bound <= n ->
  P n.
Proof.
  intros.
  assert (forall d d', (0 <= d' < d)%nat -> P (lower_bound + Z.of_nat d')). {
    induction d; intros.
    + omega.
    + destruct H2.
      apply H0.
      intros.
      replace (n'') with (lower_bound + (n'' - lower_bound)) by omega.
      rewrite <- (Z2Nat.id (n'' - lower_bound)) by omega.
      apply IHd.
      split.
      * apply Nat2Z.inj_le.
        rewrite Z2Nat.id by omega.
        simpl.
        omega.
      * apply Nat2Z.inj_lt.
        rewrite Z2Nat.id by omega.
        omega.
  }
  specialize (H2 (Z.to_nat (n - lower_bound + 1)) (Z.to_nat (n - lower_bound))).
  rewrite Z2Nat.id in H2 by omega.
  replace (lower_bound + (n - lower_bound)) with n in H2 by omega.
  apply H2.
  split.
  - apply Nat2Z.inj_le.
    rewrite Z2Nat.id by omega.
    simpl.
    omega.
  - apply Nat2Z.inj_lt.
    rewrite ?Z2Nat.id by omega.
    omega.
Qed.
