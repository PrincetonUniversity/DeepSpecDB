Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope Z_scope.

Section TREES.
  Context { V : Type }.
  Variable default: V.

  Definition key := Z.

  Inductive tree : Type :=
  | E : tree
  | T: tree -> key -> V -> tree -> tree.

  Inductive In (k : key) : tree -> Prop :=
  | InRoot l r x v:  (k = x) -> In k (T l x v r )
  | InLeft l r x v': In k l -> In k (T l x v' r)
  | InRight l r x v': In k r -> In k (T l x v' r).

  Definition lt (t: tree) (k: key) := forall x : key, In x t -> k < x .
  Definition gt (t: tree) (k: key) := forall x : key, In x t -> k > x .

  Inductive sorted_tree : tree -> Prop :=
  | Sorted_Empty : sorted_tree E
  | Sorted_Tree x v l r : sorted_tree l -> sorted_tree r ->
                          gt l x -> lt r x -> sorted_tree (T l x v r ).

  Definition empty_tree : tree := E.

  Fixpoint lookup (x: key) (t : tree) : V :=
    match t with
    | E => default
    | T tl k v tr => if x <? k then lookup x tl
                     else if k <? x then lookup x tr
                          else v
    end.

  Fixpoint insert (x: key) (v: V) (s: tree) : tree :=
    match s with
    | E => T E x v E
    | T a y v' b => if  x <? y then T (insert x v a) y v' b
                    else if y <? x then T a y v' (insert x v b)
                         else T a x v b
    end.

  Fixpoint pushdown_left (a: tree) (bc: tree) : tree :=
    match bc with
    | E => a
    | T b y vy c => T (pushdown_left a b) y vy c
    end.

  Fixpoint delete (x: key) (s: tree) : tree :=
    match s with
    | E => E
    | T a y v' b => if  x <? y then T (delete x a) y v' b
                    else if y <? x then T a y v' (delete x b)
                         else pushdown_left a b
    end.

  Lemma pushdown_left_In: forall (t1 t2: tree) (x: key),
      In x (pushdown_left t1 t2) -> In x t1 \/ In x t2.
  Proof.
    intros. revert t2 H. induction t2; intros; simpl in *; auto. inversion H; subst.
    - right. now apply InRoot.
    - apply IHt2_1 in H1. destruct H1; [left | right]; auto. now apply InLeft.
    - right. now apply InRight.
  Qed.

  Lemma delete_In: forall (x: key) (t: tree) (y: key), In y (delete x t) -> In y t.
  Proof.
    intros. revert t H. induction t; intros; simpl in *; auto. destruct (x <? k).
    - inversion H; subst;
        try ((now apply InLeft) || (now apply InRoot) || (now apply InRight)).
      apply IHt1 in H1. now apply InLeft.
    - destruct (k <? x).
      + inversion H; subst;
          try ((now apply InLeft) || (now apply InRoot) || (now apply InRight)).
        apply IHt2 in H1. now apply InRight.
      + apply pushdown_left_In in H. destruct H; [apply InLeft | apply InRight]; easy.
  Qed.

  Lemma pushdown_left_sorted: forall (t1 t2: tree),
      sorted_tree t1 -> sorted_tree t2 -> (forall x y, In x t1 -> In y t2 -> x < y) ->
      sorted_tree (pushdown_left t1 t2).
  Proof.
    intros. revert t2 H0 H1. induction t2; intros; simpl in H0 |-* ; auto.
    inversion H0; subst; constructor; auto.
    - apply IHt2_1; auto. intros. apply H1; auto. now apply InLeft.
    - intros z ?. apply pushdown_left_In in H2. destruct H2.
      + apply Z.lt_gt, H1; auto. now apply InRoot.
      + now specialize (H8 _ H2).
  Qed.

  Lemma delete_sorted: forall (x: key) (t: tree),
      sorted_tree t -> sorted_tree (delete x t).
  Proof.
    intros. revert t H. induction t; intros; simpl; auto. inversion H; subst.
    destruct (x <? k) eqn: ?.
    - apply Z.ltb_lt in Heqb. constructor; auto. intros y ?.
      apply delete_In in H0. now apply H6.
    - apply Z.ltb_ge in Heqb. destruct (k <? x) eqn: ?.
      + apply Z.ltb_lt in Heqb0. constructor; auto. intros y ?.
        apply delete_In in H0. now apply H7.
      + apply pushdown_left_sorted; auto. intros y z ? ?.
        apply H6 in H0. apply H7 in H1. lia.
  Qed.

  Lemma value_in_tree: forall x v k (t: tree),
      In k (insert x v t) -> (x = k) \/ In k t.
  Proof.
    intros. induction t; simpl in H. 1: inversion H; subst; auto.
    destruct (x <? k0) eqn: Heqn.
    - inversion H; subst.
      + right. apply InRoot. auto.
      + specialize (IHt1 H1). destruct IHt1. left. auto. right. apply InLeft. auto.
      + right. apply InRight. auto.
    - destruct (k0 <? x) eqn: Heqn'.
      + inversion H; subst.
        * right. apply InRoot. auto.
        * right. apply InLeft. auto.
        * specialize (IHt2 H1). destruct IHt2. left. auto. right. apply InRight. auto.
      + assert (k0 = x).
        { apply Z.ltb_nlt in Heqn'. apply Z.ltb_nlt in Heqn. lia. }
        subst. right. inversion H; subst.
        * apply InRoot. auto.
        * apply InLeft. auto.
        * apply InRight. auto.
  Qed.

  Lemma lookup_not_in: forall t x, ~ In x t -> lookup x t = default.
  Proof.
    induction t; intros; simpl; auto. destruct (x <? k) eqn: ?.
    - apply IHt1. intro. now apply H, InLeft.
    - destruct (k <? x) eqn: ?.
      + apply IHt2. intro. now apply H, InRight.
      + exfalso. apply H. apply Z.ltb_ge in Heqb. apply Z.ltb_ge in Heqb0.
        assert (x = k) by lia. subst. now apply InRoot.
  Qed.

  Lemma delete_not_in: forall t x, ~ In x t -> delete x t = t.
  Proof.
    intros. revert t H. induction t; intros; simpl; auto. destruct (x <? k) eqn: ?.
    - rewrite IHt1; auto. intro. now apply H, InLeft.
    - destruct (k <? x) eqn: ?.
      + rewrite IHt2; auto. intro. now apply H, InRight.
      + exfalso. apply H. apply Z.ltb_ge in Heqb. apply Z.ltb_ge in Heqb0.
        assert (x = k) by lia. subst. now apply InRoot.
  Qed.

  Lemma insert_sorted : forall x v (t: tree),
      sorted_tree t -> sorted_tree (insert x v t).
  Proof.
    intros. induction t.
    - simpl. apply Sorted_Tree; auto; [unfold gt | unfold lt]; intros; easy.
    - simpl. destruct (x <? k)  eqn: Heqn.
      + constructor.
        * apply IHt1. inversion H; auto.
        * inversion H; auto.
        * unfold gt. intros. apply value_in_tree in H0. destruct H0. subst.
          apply Z.ltb_lt in Heqn. lia.  inversion H;subst. auto.
        * unfold lt. intros. inversion H; subst. auto.
      + destruct (k <? x) eqn: Heqn'.
        * apply Sorted_Tree.
          -- inversion H; subst. auto.
          -- apply IHt2. inversion H. auto.
          -- unfold gt. intros. inversion H; subst. auto.
          -- unfold lt. intros. apply value_in_tree in H0. destruct H0.
             ++ subst. apply Z.ltb_lt in Heqn'. lia.
             ++ inversion H; subst. auto.
        * assert (k = x).
          {apply Z.ltb_nlt in Heqn'. apply Z.ltb_nlt in Heqn. lia. }
          subst. apply Sorted_Tree; inversion H; subst; auto.
  Qed.

  Definition insert_seq (s: list (key * V)) (tr: tree) :=
    fold_left (fun t x => insert (fst x) (snd x) t) s tr.

  Definition insert_seq_opt (b: bool) (v: V) l1 l2 :=
    if b
    then insert_seq (l1 ++ (1, v) :: l2) E
    else insert_seq (l1 ++ l2) E.

  Lemma insert_seq_assoc: forall k v l,
      insert k v (insert_seq l E) = insert_seq (l ++ [(k, v)]) E.
  Proof.
    intros.
    change (insert k v (insert_seq l E)) with (insert_seq [(k ,v)] (insert_seq l E)).
    unfold insert_seq. now rewrite <- fold_left_app.
  Qed.

  Lemma insert_seq_opt_assoc:
    forall (k : key) (v : V) (b : bool) (v0 : V) (l1 l2 : list (key * V)),
      insert k v (insert_seq_opt b v0 l1 l2) = insert_seq_opt b v0 l1 (l2 ++ [(k, v)]).
  Proof.
    intros. destruct b; unfold insert_seq_opt; rewrite insert_seq_assoc.
    - f_equal. rewrite <- app_assoc. f_equal.
    - f_equal. rewrite <- app_assoc. easy.
  Qed.

  Lemma insert_seq_sorted: forall l tr,
      sorted_tree tr -> sorted_tree (insert_seq l tr).
  Proof.
    induction l. intros. 1: now simpl.
    change (a :: l) with ([a] ++ l). unfold insert_seq in *.
    intros. rewrite fold_left_app. fold insert_seq. apply IHl. simpl.
    now apply insert_sorted.
  Qed.

  Lemma insert_seq_opt_sorted: forall b v l1 l2,
      sorted_tree (insert_seq_opt b v l1 l2).
  Proof. intros. destruct b; simpl; apply insert_seq_sorted; constructor. Qed.

End TREES.

Arguments E {V}.
Arguments T {V} _ _ _ _.
Arguments insert {V} x v s.
Arguments lookup {V} default x t.
Arguments pushdown_left {V} a bc.
Arguments delete {V} x s.
