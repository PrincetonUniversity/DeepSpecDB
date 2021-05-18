Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import VST.progs.ghosts.
Import ListNotations.

Local Open Scope Z_scope.

Section TREES.
  Context { V : Type }.
  Variable default: V.

  Definition key := Z.

 (* trees labeled with ghost names *)

Inductive ghost_tree: Type :=
 | E_ghost : ghost_tree
 | T_ghost : ghost_tree ->gname -> key -> V  -> ghost_tree -> gname -> ghost_tree.

Inductive In_ghost (k : key) : ghost_tree -> Prop :=
  | InRoot_ghost l g1 r g2 x v :
       (k = x) -> In_ghost k (T_ghost l g1 x v r g2 )
  | InLeft_ghost l g1 r g2 x v' :
      In_ghost k l -> In_ghost k (T_ghost l g1 x v' r g2)
  | InRight_ghost l g1 r g2 x v' :
      In_ghost k r -> In_ghost k (T_ghost l g1 x v' r g2).

Definition lt_ghost (t: ghost_tree) (k: key) := forall x : key, In_ghost x t -> k < x .
Definition gt_ghost (t: ghost_tree) (k: key) := forall x : key, In_ghost x t -> k > x .

Inductive sorted_ghost_tree : ghost_tree -> Prop :=
    | Sorted_Empty_Ghost : sorted_ghost_tree E_ghost
    | Sorted_Ghost_Tree x v l g1 r g2 : sorted_ghost_tree l -> sorted_ghost_tree r -> gt_ghost l x -> lt_ghost r x -> sorted_ghost_tree (T_ghost l g1 x v r g2 ).

 Fixpoint insert_ghost (x: key) (v: V) (s: ghost_tree) (g1:gname) (g2:gname) : ghost_tree :=
 match s with
 | E_ghost => T_ghost E_ghost g1 x v E_ghost g2
 | T_ghost a ga y v' b gb => if  x <? y then T_ghost (insert_ghost x v a g1 g2) ga y v' b gb
                        else if (y <? x) then T_ghost a ga y v' (insert_ghost x v b g1 g2) gb else T_ghost a ga x v b gb

 end.

End TREES.

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

Definition range := (number * number)%type.

Definition range_included (r1 r2 : range) : bool :=
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
    merge_range a b = c -> range_included a c = true.
Proof.
  intros. destruct a, b, c. unfold merge_range in H. inversion H; subst.
  simpl. rewrite Bool.andb_true_iff. split; [apply leq_min_number | apply leq_max_number].
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

Lemma merge_range_incl' : forall a b, range_included a b = true -> merge_range a b = b.
Proof.
  destruct a, b; simpl in *; intros.
  apply Bool.andb_true_iff in H as [].
  rewrite -> min_number_comm, <- leq_entail_min_number by auto.
  rewrite -> max_number_comm, <- leq_entail_max_number by auto; auto.
Qed.

Lemma less_than_equal_trans : forall a b c, less_than_equal a b = true -> less_than_equal b c = true -> less_than_equal a c = true.
Proof.
  destruct a, b, c; auto; try discriminate; simpl; intros.
  rewrite -> Z.leb_le in *; lia.
Qed.

Lemma range_included_trans : forall a b c, range_included a b = true -> range_included b c = true -> range_included a c = true.
Proof.
  destruct a, b, c; intros; simpl in *.
  rewrite -> Bool.andb_true_iff in *.
  destruct H, H0; split; eapply less_than_equal_trans; eauto.
Qed.

Lemma less_than_equal_antisym : forall a b, less_than_equal a b = true -> less_than_equal b a = true -> a = b.
Proof.
  destruct a, b; auto; try discriminate; simpl; intros.
  f_equal; lia.
Qed.

Lemma range_included_antisym : forall a b, range_included a b = true -> range_included b a = true -> a = b.
Proof.
  destruct a, b; simpl; intros.
  apply Bool.andb_true_iff in H as [].
  apply Bool.andb_true_iff in H0 as [].
  f_equal; apply less_than_equal_antisym; auto.
Qed.

Program Instance range_ghost : Ghost :=
  { G := (number*number); valid g := True; Join_G a b c := c =  merge_range a b }.
Next Obligation.
  exists (fun _ => (Pos_Infinity,Neg_Infinity)).
  + intros; hnf.
      destruct t; auto.
  + auto.
Defined.
Next Obligation.
 constructor.
 + intros; hnf in *. subst; auto.
 + intros; hnf in *. exists (merge_range b c); split; hnf. auto. rewrite H0. rewrite H. apply merge_assoc.
 + intros; hnf in *. rewrite merge_comm. apply H.
 + intros; hnf in *.
    symmetry in H; apply merge_range_incl in H.
    symmetry in H0; apply merge_range_incl in H0.
    apply range_included_antisym; auto.
Qed.
Next Obligation.
 constructor.
Qed.
