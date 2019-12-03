(** * verif_splitnode.v : Correctness proof of splitnode *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import relation_mem.
Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.
Require Import btrees.
Require Import btrees_sep.
Require Import btrees_spec.
Require Import verif_newnode.
Require Import verif_findindex.
Require Import index.

Lemma upd_Znth_twice: forall (A:Type) l i (x:A) x',
          0 <= i < Zlength l -> 
          upd_Znth i (upd_Znth i l x) x' = upd_Znth i l x'.
Proof.
  intros.
  unfold upd_Znth.
  autorewrite with sublist. f_equal. f_equal.
  change (x :: ?A) with ([x] ++ A).
  unfold Z.succ.
  autorewrite with sublist.
  auto.
Qed.

Lemma nth_first_sublist: forall le i,
    le_to_list (nth_first_le le (Z.to_nat i)) = sublist 0 i (le_to_list le).
Proof.
Admitted.

Lemma key_repr_k: forall key1 key2,
    key_repr key1 = key_repr key2 ->
    k_ key1 = k_ key2.
Proof.
  intros. unfold key_repr in H.
Admitted.

Lemma Some_inj: forall A (a:A) b, Some a = Some b -> a = b.
Proof.
  intros. inv H. auto.
Qed.

Lemma integrity_leaf_insert: forall X (le:listentry X) k v x i e,
    leaf_le le ->
    nth_entry_le i (insert_le le (keyval X k v x)) = Some e ->
    exists ki vi xi, e = keyval X ki vi xi.
Proof.
Admitted.

(*
Lemma integrity_intern_insert: forall X (le:listentry X) k c i e,
    intern_le le ->
    nth_entry_le i (insert_le le (keychild X k c)) = Some e ->
    exists ki ci, e = keychild X ki ci.
Proof.
Admitted. 
*)

Lemma FRI_next: forall X (le:listentry X) key i,
    next_index(findRecordIndex' le key i) = findRecordIndex' le key (next_index i).
Proof.
  intros.
  generalize dependent i.
  induction le; intros.
  - simpl. auto.
  - simpl. destruct e.
    + destruct (k_ key <=? k_ k). auto. rewrite IHle. auto.
    + destruct (k_ key <=? k_ k). auto. rewrite IHle. auto.
Qed.

Lemma FRI_repr: forall X (le:listentry X) key1 key2 i,
    key_repr key1 = key_repr key2 ->
    findRecordIndex' le key1 i = findRecordIndex' le key2 i.
Proof.
  intros. generalize dependent i. induction le; intros.
  - simpl. auto.
  - simpl. destruct e.
    + rewrite IHle. rewrite key_repr_k with (key2:=key2) by auto. auto.
    + rewrite IHle. rewrite key_repr_k with (key2:=key2) by auto. auto.
Qed.

Lemma insert_fri: forall X (le:listentry X) e fri key,
    key = entry_key e ->
    ip fri = findRecordIndex' le key (ip O) ->
    insert_le le e = le_app (nth_first_le le fri) (cons X e (skipn_le le fri)).
Proof.
  intros. generalize dependent fri.
  induction le; intros.
  - simpl. destruct fri; simpl; auto.
  - destruct fri.
    + simpl. simpl in H0.
      destruct e0.
      * rewrite <- H. simpl.
        destruct (k_ key <=? k_ k). auto.
        assert(idx_to_Z (ip 1) <= idx_to_Z(findRecordIndex' le key (ip 1))) by apply FRI_increase.
        rewrite <- H0 in H1. simpl in H1. omega.
      * rewrite <- H. simpl.
        destruct (k_ key <=? k_ k). auto.
        assert(idx_to_Z (ip 1) <= idx_to_Z(findRecordIndex' le key (ip 1))) by apply FRI_increase.
        rewrite <- H0 in H1. simpl in H1. omega.
    + simpl. simpl in H0.
      destruct e0.
      * rewrite <- H. simpl.
        destruct (k_ key <=? k_ k). inv H0.
        rewrite <- IHle. auto. replace (ip 1) with (next_index (ip O)) in H0 by (simpl; auto).
        rewrite <- FRI_next in H0.
        destruct (findRecordIndex' le key (ip 0)).
        simpl in H0. inv H0. simpl in H0. inv H0. auto.
      * rewrite <- H. simpl.
        destruct (k_ key <=? k_ k). inv H0.
        rewrite <- IHle. auto. replace (ip 1) with (next_index (ip O)) in H0 by (simpl; auto).
        rewrite <- FRI_next in H0.
        destruct (findRecordIndex' le key (ip 0)).
        simpl in H0. inv H0. simpl in H0. inv H0. auto.
Qed.

Lemma suble_skip: forall X (le:listentry X) i f,
    f = numKeys_le le ->
    suble i f le = skipn_le le i.
Proof.
  intros. generalize dependent f. generalize dependent i.
  destruct le; intros.
  - simpl. destruct i. simpl in H. rewrite H. rewrite suble_nil. auto.
    simpl in H. rewrite H. rewrite suble_nil'. auto. omega.
  - destruct f. inv H. simpl in H. inversion H.
    simpl. destruct i.
    + unfold suble. simpl. rewrite nth_first_same. auto. auto.
    + unfold suble. simpl. rewrite nth_first_same. auto.
      rewrite numKeys_le_skipn. auto.
Qed.

Lemma nth_first_le_app1: forall X (l1:listentry X) l2 i,
    (i <= numKeys_le l1)%nat ->
    nth_first_le (le_app l1 l2) i = nth_first_le l1 i.
Proof.
  intros. generalize dependent i. induction l1; intros.
  - simpl. simpl in H. destruct i. simpl. auto. omega.
  - destruct i.
    + simpl. auto.
    + simpl. rewrite IHl1. auto.
      simpl in H. omega.
Qed.

Lemma le_split: forall X (le:listentry X) i,
    (i <= numKeys_le le)%nat ->
    le = le_app (nth_first_le le i) (skipn_le le i).
Proof.
  intros. generalize dependent i. induction le; intros.
  - destruct i; simpl; auto.
  - simpl. destruct i.
    + simpl. auto.
    + simpl. rewrite <- IHle with (i:=i). auto. simpl in H. omega.
Qed.

Lemma insert_rep: forall le (e:entry val),
    le_iter_sepcon le * entry_rep e = le_iter_sepcon (insert_le le e).
Proof.
  intros.
  induction le.
  - apply pred_ext.
    + simpl. entailer!.
    + simpl. entailer!.
  - apply pred_ext.
    + simpl. destruct (k_ (entry_key e) <=? k_ (entry_key e0)).
      * simpl. entailer!.
      * simpl. rewrite <- IHle. entailer!.
    + simpl. destruct (k_ (entry_key e) <=? k_ (entry_key e0)).
      * simpl. entailer!.
      * simpl. rewrite <- IHle. entailer!.
Qed.

Lemma le_iter_sepcon_app: forall le1 le2,
    le_iter_sepcon (le_app le1 le2) = le_iter_sepcon le1 * le_iter_sepcon le2.
Proof.
  intros. induction le1.
  - simpl. apply pred_ext; entailer!.
  - simpl. rewrite IHle1. apply pred_ext; entailer!.
Qed.

Lemma nth_first_insert: forall X (le:listentry X) e k m,
    k = entry_key e ->
    Z.of_nat m <= idx_to_Z (findRecordIndex' le k (ip O)) ->
    nth_first_le (insert_le le e) m = nth_first_le le m.
Proof.
  intros. generalize dependent m. induction le; intros.
  - simpl in H0. destruct m. simpl. auto. rewrite Z2Nat.inj_le in H0.
    rewrite Nat2Z.id in H0. simpl in H0. omega.
    omega. omega.
  - simpl. simpl in H0. rewrite <- H. destruct e0.
    + simpl. destruct (k_ k <=? k_ k0).
      * destruct m. simpl. auto. rewrite Z2Nat.inj_le in H0.
        rewrite Nat2Z.id in H0. simpl in H0. omega.
        omega. omega.
      * destruct m. simpl. auto. simpl.
        rewrite IHle. auto. replace (ip 1) with (next_index(ip O)) in H0.
        rewrite <- FRI_next in H0. rewrite next_idx_to_Z in H0.
        rewrite Nat2Z.inj_succ in H0. omega.
        simpl. auto.
    + simpl. destruct (k_ k <=? k_ k0).
      * destruct m. simpl. auto. rewrite Z2Nat.inj_le in H0.
        rewrite Nat2Z.id in H0. simpl in H0. omega.
        omega. omega.
      * destruct m. simpl. auto. simpl.
        rewrite IHle. auto. replace (ip 1) with (next_index(ip O)) in H0.
        rewrite <- FRI_next in H0. rewrite next_idx_to_Z in H0.
        rewrite Nat2Z.inj_succ in H0. omega.
        simpl. auto.
Qed.

Lemma nth_first_app_same1: forall X (le1:listentry X) le2 i,
    i = numKeys_le le1 ->
    nth_first_le (le_app le1 le2) i = le1.
Proof.
  intros. generalize dependent i.
  induction le1; intros.
  - simpl in H. subst. simpl. auto.
  - destruct i.
    + simpl in H. inv H.
    + simpl. simpl in H. rewrite IHle1. auto. inv H. auto.
Qed.

Set Nested Proofs Allowed.

Definition splitnode_main_if_then : statement :=
 ltac:(let x := constr:(fn_body f_splitnode) in
         let x := eval simpl in x in
         match x with context [Sifthenelse (Ebinop Oeq (Etempvar _ tint)
                                                       (Econst_int (Int.repr 1) tint) tint) ?s1 _] =>
         apply s1
         end).

Definition splitnode_main_if_else : statement := 
 ltac:(let x := constr:(fn_body f_splitnode) in
         let x := eval simpl in x in
         match x with context [Sifthenelse (Ebinop Oeq (Etempvar _ tint)
                                                       (Econst_int (Int.repr 1) tint) tint) _ ?s2] =>
         apply s2
         end).

Definition splitnode_main_if_part2 : statement :=
 ltac:(let x := constr:(splitnode_main_if_then) in
         let x := eval hnf in x in
         match x with context [Ssequence (Sassign   (Efield
                          (Ederef
                            (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                            (Tstruct _BtNode noattr)) _numKeys tint)
                        (Econst_int (Int.repr ?M) tint)) ?S] =>
          exact (Ssequence (Sassign   (Efield
                          (Ederef
                            (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                            (Tstruct _BtNode noattr)) _numKeys tint)
                        (Econst_int (Int.repr M) tint)) S)
         end).



