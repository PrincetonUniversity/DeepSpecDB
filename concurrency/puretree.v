Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope Z_scope.

(* Not sure whether we need ranges, but we definitely don't need pure trees in order to prove that
  trees satisfy map specs. If we keep this file, rename it. *)

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

Lemma range_incl_infty:
  forall r, range_incl r (Neg_Infinity, Pos_Infinity) = true.
Proof. intros. destruct r. simpl. destruct n0; now simpl. Qed.
Global Hint Resolve range_incl_infty : core.

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

Lemma key_in_range_l : forall k r, key_in_range k r = true -> range_incl (fst r, Finite_Integer k) r = true.
Proof.
  destruct r; unfold key_in_range; intros; simpl.
  rewrite less_than_equal_refl; simpl.
  apply less_than_to_less_than_equal.
  apply andb_prop in H as [_ ->]; auto.
Qed.

Lemma key_in_range_r : forall k r, key_in_range k r = true -> range_incl (Finite_Integer k, snd r) r = true.
Proof.
  destruct r; unfold key_in_range; intros; simpl.
  rewrite less_than_equal_refl, Bool.andb_true_r.
  apply less_than_to_less_than_equal.
  apply andb_prop in H as [->]; auto.
Qed.

Arguments range_incl _ _ : simpl nomatch.
