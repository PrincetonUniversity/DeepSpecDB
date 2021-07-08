Require Import VST.msl.sepalg.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.

Import ListNotations.

Inductive list_join {A} {JA: Join A} {SA: Sep_alg A} {SI: Sing_alg A}:
  list A -> A -> Prop :=
| join_nil: forall it: A, list_join [] the_unit
| join_cons: forall l lj it c,
    list_join l lj -> join it lj c -> list_join (it :: l) c.

Lemma list_join_perm {A} {JA: Join A} {PA: Perm_alg A}
      {SA: Sep_alg A} {SI: Sing_alg A}:
  forall l1 l2 c, Permutation l1 l2 -> list_join l1 c -> list_join l2 c.
Proof.
  intros until c. intro. revert c. induction H; intros; auto.
  - inversion H0; subst. apply (join_cons l' lj); auto.
  - inversion H. subst; clear H. inversion H2; subst; clear H2.
    apply join_comm in H4. destruct (join_assoc H5 H4) as [lj0y [? ?]].
    apply join_cons with lj0y; auto. apply join_cons with lj0; auto.
Qed.

Lemma list_join_single {A} {JA: Join A} {PA: Perm_alg A}
      {SA: Sep_alg A} {SI: Sing_alg A}:
  forall x l c, In x l -> list_join l c ->
                exists l1 l2 y, l = l1 ++ x :: l2 /\
                                list_join (l1 ++ l2) y /\ join x y c.
Proof.
  intros until l. induction l; intros. 1: inversion H. simpl in H. destruct H.
  - subst. inversion H0; subst. exists [], l, lj. simpl; auto.
  - inversion H0; subst; clear H0. specialize (IHl _ H H3).
    destruct IHl as [l1 [l2 [y [? [? ?]]]]]. subst. apply join_comm in H5.
    destruct (join_assoc H2 H5) as [al1l2 [? ?]]. exists (a :: l1), l2, al1l2.
    repeat split; auto. simpl. apply join_cons with y; auto.
Qed.
