Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope Z_scope.

(* ranges *)
Inductive number : Type :=
 | Finite_Integer (n : Z)
 | Neg_Infinity
 | Pos_Infinity.

Definition min_number a b : number :=
 match a with
 | Finite_Integer a1 => match b with
                                          | Finite_Integer b1 => Finite_Integer (Z.min a1 b1)
                                          | Neg_Infinity => b
                                          | Pos_Infinity => a
                                          end
 | Neg_Infinity => a
 | Pos_Infinity => b
 end.

Definition max_number a b : number :=
 match a with
 | Finite_Integer a1 => match b with
                                          | Finite_Integer b1 => Finite_Integer (Z.max a1 b1)
                                          | Neg_Infinity => a
                                          | Pos_Infinity => b
                                          end
 | Neg_Infinity => b
 | Pos_Infinity => a
 end.

Lemma min_min_number: forall a b, min_number a (min_number a b) = min_number a b.
Proof.
  intros. destruct a, b; simpl; try rewrite Z.min_id; auto. f_equal.
  destruct (Z.min_dec n n0); rewrite e; try rewrite Z.min_id; easy.
Qed.

Lemma max_max_number: forall a b, max_number a (max_number a b) = max_number a b.
Proof.
  intros. destruct a, b; simpl; try rewrite Z.max_id; auto. f_equal.
  destruct (Z.max_dec n n0); rewrite e; try rewrite Z.max_id; easy.
Qed.

Lemma min_number_comm : forall a b, min_number a b = min_number b a.
Proof.
  destruct a, b; auto; simpl.
  rewrite Z.min_comm; auto.
Qed.

Lemma max_number_comm : forall a b, max_number a b = max_number b a.
Proof.
  destruct a, b; auto; simpl.
  rewrite Z.max_comm; auto.
Qed.

Lemma min_number_assoc : forall a b c, min_number a (min_number b c) = min_number (min_number a b) c.
Proof.
  destruct a, b, c; auto; simpl.
  rewrite Z.min_assoc; reflexivity.
Qed.

Lemma max_number_assoc : forall a b c, max_number a (max_number b c) = max_number (max_number a b) c.
Proof.
  destruct a, b, c; auto; simpl.
  rewrite Z.max_assoc; reflexivity.
Qed.

Definition less_than_equal a b: bool :=
    match a with
 | Finite_Integer a1 => match b with
                                          | Finite_Integer b1 => (a1 <=? b1)
                                          | Neg_Infinity => false
                                          | Pos_Infinity => true
                                          end
 | Neg_Infinity => true
 | Pos_Infinity => match b with
                                  | Pos_Infinity => true
                                  | _ => false
                                  end
 end.

Definition less_than a b: bool :=
    match a with
 | Finite_Integer a1 => match b with
                                          | Finite_Integer b1 => (a1 <? b1)
                                          | Neg_Infinity => false
                                          | Pos_Infinity => true
                                          end
 | Neg_Infinity => match b with
                                          | Neg_Infinity => false
                                          | _ => true
                                          end
 | Pos_Infinity => false
 end.
Arguments less_than _ _ : simpl nomatch.
Arguments less_than_equal _ _ : simpl nomatch.

Definition range := (number * number)%type.

Definition range_incl (r1 r2 : range) : bool :=
  match r1, r2 with (a1,a2), (b1,b2) => less_than_equal b1 a1 && less_than_equal a2 b2 end.

Definition key_in_range (k : Z) (r : range) : bool :=
 match r with (a1, a2) => less_than a1 (Finite_Integer k) && less_than (Finite_Integer k)  a2 end.

Definition merge_range (a b : range) : range :=
  match a, b with (a1,a2), (b1, b2) => (min_number a1 b1, max_number a2 b2) end.

Lemma merge_assoc: forall a b c, merge_range (merge_range a b) c = merge_range a (merge_range b c ).
Proof.
  intros; unfold merge_range.
  destruct a, b, c.
  rewrite min_number_assoc, max_number_assoc; reflexivity.
 Qed.

Lemma merge_comm: forall a b , merge_range a b = merge_range b a .
Proof.
  intros; unfold merge_range.
  destruct a, b.
  rewrite min_number_comm, max_number_comm; reflexivity.
Qed.

 Lemma merge_id: forall a, merge_range a a = a.
Proof.
  intros; unfold merge_range.
  destruct a.
  destruct n, n0; auto; simpl; rewrite ?Z.min_id, ?Z.max_id; reflexivity.
Qed.

Lemma merge_again: forall a b c, merge_range a b = c -> merge_range a c = c.
Proof.
   intros. destruct a, b, c. unfold merge_range in *. inversion H; subst.
   rewrite min_min_number. rewrite max_max_number. easy.
 Qed.

Lemma leq_min_number: forall a b, less_than_equal (min_number a b) a = true.
Proof. intros. destruct a, b; simpl; auto; rewrite Z.leb_le; lia. Qed.

Lemma leq_max_number: forall a b, less_than_equal a (max_number a b) = true.
Proof. intros. destruct a, b; simpl; auto; rewrite Z.leb_le; lia. Qed.

Lemma merge_range_incl: forall a b c,
    merge_range a b = c -> range_incl a c = true.
Proof.
  intros. destruct a, b, c. unfold merge_range in H. inversion H; subst.
  simpl. rewrite Bool.andb_true_iff. split; [apply leq_min_number | apply leq_max_number].
Qed.

Lemma merge_infinity : forall r, merge_range r (Neg_Infinity, Pos_Infinity) = (Neg_Infinity, Pos_Infinity).
Proof.
  destruct r; unfold merge_range, min_number, max_number.
  destruct n, n0; auto.
Qed.

Lemma leq_min_number1: forall a b, less_than_equal (min_number a b) b = true.
Proof. intros. destruct a, b; simpl; auto; rewrite Z.leb_le; lia. Qed.

Lemma leq_max_number1: forall a b, less_than_equal b (max_number a b) = true.
Proof. intros. destruct a, b; simpl; auto; rewrite Z.leb_le; lia. Qed.

Lemma leq_entail_min_number: forall a b, less_than_equal a b = true -> a = min_number a b.
Proof.
intros. destruct a, b; simpl; auto;simpl in H. apply Z.leb_le in H. rewrite  Z.min_l. auto. auto. discriminate. discriminate. discriminate.
Qed.

Lemma leq_entail_max_number: forall a b, less_than_equal b a = true -> a = max_number a b.
Proof.
intros. destruct a, b; simpl; auto;simpl in H. apply Z.leb_le in H. rewrite  Z.max_l. auto. auto. discriminate. discriminate. discriminate.
Qed.

Lemma merge_range_incl' : forall a b, range_incl a b = true -> merge_range a b = b.
Proof.
  destruct a, b; simpl in *; intros.
  apply Bool.andb_true_iff in H as [].
  rewrite -> min_number_comm, <- leq_entail_min_number by auto.
  rewrite -> max_number_comm, <- leq_entail_max_number by auto; auto.
Qed.

Lemma less_than_equal_trans : forall a b c, less_than_equal a b = true -> less_than_equal b c = true -> less_than_equal a c = true.
Proof.
  destruct a, b, c; auto; try discriminate; simpl; lia.
Qed.

Lemma range_incl_trans : forall a b c, range_incl a b = true -> range_incl b c = true -> range_incl a c = true.
Proof.
  destruct a, b, c; intros; simpl in *.
  rewrite -> Bool.andb_true_iff in *.
  destruct H, H0; split; eapply less_than_equal_trans; eauto.
Qed.

Lemma less_than_equal_less_than_trans: forall a b c, less_than_equal a b = true ->  less_than b c = true -> less_than a c = true .
Proof.
  destruct a, b, c; auto; try discriminate; simpl; lia.
Qed.

Lemma less_than_less_than_equal_trans: forall a b c,
    less_than a b = true -> less_than_equal b c = true -> less_than a c = true .
Proof.
  destruct a, b, c; auto; try discriminate; simpl; lia.
Qed.

Lemma less_than_irrefl: forall a, less_than a a = false.
Proof. intros. destruct a; simpl; auto. apply Z.ltb_irrefl. Qed.

Lemma less_than_trans: forall a b c, less_than a b = true ->  less_than b c = true -> less_than a c = true .
Proof.
  destruct a, b, c; auto; try discriminate; simpl; lia.
Qed.

Lemma less_than_equal_refl: forall a, less_than_equal a a = true.
Proof.
  destruct a; auto; simpl; lia.
Qed.

Lemma range_incl_refl : forall r, range_incl r r = true.
Proof.
  destruct r; simpl.
  rewrite !less_than_equal_refl; reflexivity.
Qed.

Lemma less_than_to_less_than_equal: forall a b, less_than a b = true -> less_than_equal a b = true.
Proof.
  destruct a, b; auto; simpl; lia.
Qed.

Lemma less_than_equal_antisym : forall a b, less_than_equal a b = true -> less_than_equal b a = true -> a = b.
Proof.
  destruct a, b; auto; try discriminate; simpl; intros.
  f_equal; lia.
Qed.

Lemma range_incl_antisym : forall a b, range_incl a b = true -> range_incl b a = true -> a = b.
Proof.
  destruct a, b; simpl; intros.
  apply Bool.andb_true_iff in H as [].
  apply Bool.andb_true_iff in H0 as [].
  f_equal; apply less_than_equal_antisym; auto.
Qed.

Lemma key_in_range_incl : forall k r r', key_in_range k r = true -> range_incl r r' = true -> key_in_range k r' = true.
Proof.
  unfold key_in_range, range_incl; destruct r, r'; intros.
  apply andb_prop in H as [].
  apply andb_prop in H0 as [].
  rewrite Bool.andb_true_iff; split.
  - eapply less_than_equal_less_than_trans; eauto.
  - eapply less_than_less_than_equal_trans; eauto.
Qed.

Lemma range_incl_infty:
  forall r, range_incl r (Neg_Infinity, Pos_Infinity) = true.
Proof. intros. destruct r. simpl. destruct n0; now simpl. Qed.
Global Hint Resolve range_incl_infty : core.

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

Inductive EmptyRange (rn : range) : tree -> range -> Prop :=
 | InEmptyTree : EmptyRange rn E rn
 | InLeftSubTree l x v r n1 n2 : EmptyRange rn l (n1, Finite_Integer x) -> EmptyRange rn (T l x v r) (n1, n2)
 | InRightSubTree l x v r n1 n2 :  EmptyRange rn r (Finite_Integer x, n2) -> EmptyRange rn (T l x v r) (n1, n2).

Definition keys_in_range t r := forall k, In k t -> key_in_range k r = true.

Lemma keys_in_range_subtrees : forall t1 t2 k v r, keys_in_range (T t1 k v t2) r -> sorted_tree (T t1 k v t2) ->
  key_in_range k r = true /\ keys_in_range t1 (fst r, Finite_Integer k) /\ keys_in_range t2 (Finite_Integer k, snd r).
Proof.
  intros. inversion H0; subst. split; [|split].
  - apply H; constructor; auto.
  - intros ??.
    specialize (H k0 (InLeft _ _ _ _ _ H1)).
    apply H7 in H1.
    unfold key_in_range in *.
    destruct r; simpl; apply andb_prop in H as [->]; lia.
  - intros ??.
    specialize (H k0 (InRight _ _ _ _ _ H1)).
    apply H8 in H1.
    unfold key_in_range in *.
    destruct r; simpl; apply andb_prop in H as [? H2].
    simpl in *; rewrite H2; lia.
Qed.

Lemma in_range_infty:
  forall t, keys_in_range t (Neg_Infinity, Pos_Infinity).
Proof. repeat intro; auto. Qed.

Lemma range_inside_range : forall r r_root t, EmptyRange r t r_root -> keys_in_range t r_root -> sorted_tree t -> range_incl r r_root = true.
Proof.
  intros; revert dependent r_root.
  induction t; intros; inversion H; subst.
  - apply range_incl_refl.
  - apply keys_in_range_subtrees in H0 as (? & ? & ?); [|auto].
    inversion H1; subst.
    eapply range_incl_trans; [apply IHt1; eauto 1|].
    unfold key_in_range in H.
    unfold range_incl.
    rewrite less_than_equal_refl.
    apply less_than_to_less_than_equal.
    apply andb_prop in H0 as [_ ->]; auto.
  - apply keys_in_range_subtrees in H0 as (? & ? & ?); [|auto].
    inversion H1; subst.
    eapply range_incl_trans; [apply IHt2; eauto 1|].
    unfold key_in_range in H.
    unfold range_incl.
    rewrite less_than_equal_refl, Bool.andb_true_r.
    apply less_than_to_less_than_equal.
    apply andb_prop in H0 as [-> _]; auto.
Qed.

End TREES.

Arguments E {V}.
Arguments T {V} _ _ _ _.
Arguments insert {V} x v s.
Arguments lookup {V} default x t.
Arguments pushdown_left {V} a bc.
Arguments delete {V} x s.

Global Hint Resolve in_range_infty : core.
