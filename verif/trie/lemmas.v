Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import VST.msl.wand_frame.

Lemma iter_sepcon_split3 {A: Type} {Inh: Inhabitant A} (l: list A) (P: A -> mpred) (k: Z):
  0 <= k < Zlength l ->
  iter_sepcon P l = iter_sepcon P (sublist 0 k l) * P (Znth k l) * iter_sepcon P (sublist (k + 1) (Zlength l) l).
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
  iter_sepcon P l * P a = iter_sepcon P (upd_Znth k l a) * P (Znth k l).
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

Lemma iter_in_wand {A: Type} (a: A) (l: list A) (P: A -> mpred):
  In a l ->
  iter_sepcon P l = P a * (P a -* iter_sepcon P l).
Proof.
  intros.
  apply pred_ext.
  - induction l.
    + inv H.
    + inv H.
      * simpl.
        cancel.
        apply wand_frame_intro.
      * simpl.
        sep_apply (IHl H0).
        cancel.
        rewrite <- wand_sepcon_adjoint.
        cancel.
        sep_apply (wand_frame_elim (P a) (iter_sepcon P l)).
        cancel.
  - sep_apply (wand_frame_elim (P a) (iter_sepcon P l)).
    cancel.
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
