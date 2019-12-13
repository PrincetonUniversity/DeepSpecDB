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
    0 <= i ->
    le_to_list (nth_first_le le i) = sublist 0 i (le_to_list le).
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
    ip fri = findRecordIndex' le key (ip 0) ->
    insert_le le e = le_app (nth_first_le le fri) (cons X e (skipn_le le fri)).
Proof.
  intros.
  set (i := 0) in *.
  replace (fri) with (fri-i) by omega. 
  pose proof (FRI_increase X le key (ip i)). rewrite <- H0 in H1. simpl in H1.
  clearbody i.
  revert i H1 H0.
  subst.  
  induction le; intros.
  - simpl. if_tac; auto.
  - simpl in *.
     destruct e0.
    + simpl. destruct (k_ (entry_key e) <=? k_ k) eqn:?H. inv H0.
        rewrite Z.sub_diag. simpl. auto.
        pose proof (FRI_increase X le (entry_key e) (ip (Z.succ i))). rewrite <- H0 in H2.
        simpl in H2. rewrite !zle_false by omega. simpl.
       f_equal. rewrite (IHle (Z.succ i)); auto; try omega.
       f_equal. f_equal. omega. f_equal. f_equal. omega.
    + simpl. destruct (k_ (entry_key e) <=? k_ k) eqn:?H. inv H0.
        rewrite Z.sub_diag. simpl. auto.
        pose proof (FRI_increase X le (entry_key e) (ip (Z.succ i))). rewrite <- H0 in H2.
        simpl in H2. rewrite !zle_false by omega. simpl.
       f_equal. rewrite (IHle (Z.succ i)); auto; try omega.
       f_equal. f_equal. omega. f_equal. f_equal. omega.
Qed.

Lemma suble_skip: forall X (le:listentry X) i f,
    0 <= i <= f ->
    f = numKeys_le le ->
    suble i f le = skipn_le le i.
Proof.
  intros.
  unfold suble. subst.
  generalize dependent i.
  destruct le; intros.
  - simpl.  if_tac; auto. assert (i=0) by omega. subst. simpl. auto.
     unfold nth_first_le. rewrite zle_true by omega. auto.
  - simpl. if_tac. assert (i=0) by omega. subst. simpl.
     pose (numKeys_le_nonneg le). rewrite zle_false by omega.
     rewrite Z.sub_0_r, Z.pred_succ. rewrite nth_first_same; auto.
     rewrite nth_first_same; auto. simpl in H.
      rewrite numKeys_le_skipn. omega. omega. 
Qed.

Lemma nth_first_le_app1: forall X (l1:listentry X) l2 i,
    0 <= i <= numKeys_le l1 ->
    nth_first_le (le_app l1 l2) i = nth_first_le l1 i.
Proof.
  intros. generalize dependent i. induction l1; intros.
  - simpl. simpl in H. assert (i=0) by omega. subst. simpl.
      destruct l2; simpl; auto.
  - simpl. if_tac. auto. f_equal. apply IHl1.
     simpl in H.  omega.
Qed.

Lemma le_split: forall X (le:listentry X) i,
    0 <= i <= numKeys_le le ->
    le = le_app (nth_first_le le i) (skipn_le le i).
Proof.
  intros. generalize dependent i. induction le; intros.
  - simpl; if_tac; auto.
  - simpl. if_tac. auto. simpl. f_equal. apply IHle. simpl in H; omega.
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
    0 <= m <= idx_to_Z (findRecordIndex' le k (ip 0)) ->
    nth_first_le (insert_le le e) m = nth_first_le le m.
Proof.
  intros. subst.
  generalize dependent m. induction le; intros.
  - simpl in H0. simpl. rewrite !zle_true by omega. auto.
  - simpl. simpl in H0. destruct e0.
    + simpl. destruct (k_ (entry_key e) <=? k_ k).
      * simpl in H0. assert (m=0) by omega; subst m; simpl; auto.
      * if_tac. assert (m=0) by omega. subst; simpl; auto.
         simpl. rewrite zle_false by omega. f_equal. apply IHle.
         pose proof (FRI'_next_index le (entry_key e) (ip 0)). simpl in H1.
         rewrite H1 in H0.
         destruct ((findRecordIndex' le (entry_key e) (ip 0))). simpl in H0. omega.
         simpl in *. omega.
    + simpl. destruct (k_ (entry_key e) <=? k_ k).
      * simpl in H0. assert (m=0) by omega; subst m; simpl; auto.
      * if_tac. assert (m=0) by omega. subst; simpl; auto.
         simpl. rewrite zle_false by omega. f_equal. apply IHle.
         pose proof (FRI'_next_index le (entry_key e) (ip 0)). simpl in H1.
         rewrite H1 in H0.
         destruct ((findRecordIndex' le (entry_key e) (ip 0))). simpl in H0. omega.
         simpl in *. omega.
Qed.

Lemma nth_first_app_same1: forall X (le1:listentry X) le2 i,
    i = numKeys_le le1 ->
    nth_first_le (le_app le1 le2) i = le1.
Proof.
  intros. subst.
  induction le1.  
  -  simpl.  destruct le2; simpl; auto.
  -  simpl. pose proof (numKeys_le_nonneg le1). rewrite zle_false by omega.
      f_equal. rewrite Z.pred_succ. auto.
Qed.

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



