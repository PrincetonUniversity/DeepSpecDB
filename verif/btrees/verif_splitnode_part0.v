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

(*
Lemma nth_first_sublist: forall X (le: list (entry X)) i,
    0 <= i ->
    sublist 0 i le = sublist 0 i le.
Proof.
intros.
unfold nth_first_le.
auto.
Qed.
*)

Lemma key_repr_k: forall key1 key2,
    key_repr key1 = key_repr key2 ->
    k_ key1 = k_ key2.
Proof.
  intros. unfold key_repr in H.
  unfold k_.
  unfold Vptrofs in H.
  destruct Archi.ptr64 eqn:Hp.
  assert (Ptrofs.to_int64 key1 = Ptrofs.to_int64 key2) by congruence.
  rewrite <- ?int64_unsigned_ptrofs_toint by auto.
  f_equal; auto.
  assert (Ptrofs.to_int key1 = Ptrofs.to_int key2) by congruence.
  rewrite <- ?int_unsigned_ptrofs_toint by auto.
  f_equal; auto.
Qed.

Lemma Some_inj: forall A (a:A) b, Some a = Some b -> a = b.
Proof.
  intros. inv H. auto.
Qed.

Lemma integrity_leaf_insert: forall X {d: Inhabitant X} (le:list (entry X)) k v x i e,
    leaf_le le ->
    nth_entry_le i (insert_le le (keyval X k v x)) = Some e ->
    exists ki vi xi, e = keyval X ki vi xi.
Proof.
intros.
unfold nth_entry_le, Znth_option in *.
repeat if_tac in H0; inv H0.
autorewrite with sublist in *.
rewrite Znth_map in H4 by omega.
inv H4.
generalize dependent i; induction H; intros.
simpl in *.
autorewrite with sublist in *.
assert (i=0) by omega.
subst.
autorewrite with sublist in *.
eauto.
simpl in *.
destruct (k_ k <=? k_ k0).
-
clear - H H1 H2.
destruct (zeq i 0).
subst.
autorewrite with sublist. eauto.
autorewrite with sublist.
destruct (zeq i 1).
subst.
autorewrite with sublist. eauto.
autorewrite with sublist in *.
assert (0 <= i-1-1 < Zlength le) by omega.
forget (i-1-1) as j.
clear - H H0.
revert j H0; induction H; intros.
autorewrite with sublist in H0; omega.
autorewrite with sublist in H0.
destruct (zeq j 0).
subst.
autorewrite with sublist. eauto.
autorewrite with sublist.
eapply IHleaf_le; eauto.
omega.
-
destruct (zeq i 0).
subst.
autorewrite with sublist in *.
eauto.
autorewrite with sublist in *.
eapply IHleaf_le; eauto; omega.
Qed.

Lemma integrity_intern_insert: forall X {d: Inhabitant X} (le:list (entry X)) k c i e n0,
    intern_le le (@node_depth X n0)->
    nth_entry_le i (insert_le le (keychild X k c)) = Some e ->
    exists ki ci, e = keychild X ki ci.
Proof.
intros.
unfold nth_entry_le, Znth_option in *.
repeat if_tac in H0; inv H0.
autorewrite with sublist in *.
rewrite Znth_map in H4 by omega.
inv H4.
generalize dependent i; induction H; intros.
simpl in *.
destruct (k_ k <=? k_ k0); autorewrite with sublist in *.
-
destruct (zeq i 0).
subst.
autorewrite with sublist. eauto.
autorewrite with sublist.
destruct (zeq i 1).
subst.
autorewrite with sublist. eauto.
autorewrite with sublist in *.
omega.
-
destruct (zeq i 0).
subst.
autorewrite with sublist. eauto.
autorewrite with sublist.
destruct (zeq i 1).
subst.
autorewrite with sublist. eauto.
autorewrite with sublist in *.
omega.
-
simpl in *.
destruct (k_ k <=? k_ k0); autorewrite with sublist in *.
destruct (zeq i 0).
subst.
autorewrite with sublist. eauto.
autorewrite with sublist.
destruct (zeq i 1).
subst.
autorewrite with sublist. eauto.
autorewrite with sublist in *.
assert (0 <= i-1-1 < Zlength le) by omega.
forget (i-1-1) as j.
clear - H H3.
revert j H3; induction H; intros.
autorewrite with sublist in *.
assert (j=0) by omega.
subst. 
autorewrite with sublist in *.
eauto.
destruct (zeq j 0).
subst.
autorewrite with sublist. eauto.
autorewrite with sublist.
eapply IHintern_le; eauto.
autorewrite with sublist in H3.
omega.
destruct (zeq i 0).
subst.
autorewrite with sublist in *.
eauto.
autorewrite with sublist in *.
eapply IHintern_le; eauto; omega.
Qed.

Lemma FRI_next: forall X (le:list (entry X)) key i,
    Z.succ(findRecordIndex' le key i) = findRecordIndex' le key (Z.succ i).
Proof.
  intros.
  generalize dependent i.
  induction le; intros.
  - simpl. auto.
  - simpl.
     destruct (k_ key <=? k_ _). auto. rewrite IHle. auto.
Qed.

Lemma FRI_repr: forall X (le:list (entry X)) key1 key2 i,
    key_repr key1 = key_repr key2 ->
    findRecordIndex' le key1 i = findRecordIndex' le key2 i.
Proof.
  intros. generalize dependent i. induction le; intros.
  - simpl. auto.
  - simpl. 
    rewrite IHle. rewrite key_repr_k with (key2:=key2) by auto. auto.
Qed.

Lemma FRI_bound:
  forall X (le: list (entry X)) key i,
     findRecordIndex' le key i <= Zlength le + i.
Proof.
intros.
revert i; induction le; intros. simpl. list_solve.
autorewrite with sublist.
simpl.
destruct (k_ key <=? k_ (entry_key a)).
rep_omega.
specialize (IHle (Z.succ i)).
omega.
Qed.

Lemma insert_fri: forall X {d: Inhabitant X} (le:list (entry X)) e fri key,
    key = entry_key e ->
    fri = findRecordIndex' le key 0 ->
    insert_le le e =  sublist 0 fri le ++ e :: sublist fri (Zlength le) le.
Proof.
  intros.
  set (i := 0) in *.
  assert (0 <= i <= fri /\ fri-i <= Zlength le).
    {  split. split. omega. subst. apply (FRI_increase X le _ i).
       pose proof (FRI_bound _ le key i). omega.
 }
  replace fri with (fri-i) by omega.
  unfold i at 1.
  clearbody i.
  destruct H1.
  revert i H2 H1 H0.
  subst.  
  induction le; intros.
  - simpl in *. subst. autorewrite with sublist in H2. 
      autorewrite with sublist. auto.
  - simpl in *. autorewrite with sublist in H2.
     destruct (k_ (entry_key e) <=? k_ _) eqn:?H;
        subst. autorewrite with sublist. auto.
        pose proof (FRI_increase X le (entry_key e) (Z.succ i)).
       pose proof (FRI_bound _ le (entry_key e) (Z.succ i)).
       set (j := findRecordIndex' le (entry_key e) (Z.succ i)) in *.
        rewrite (IHle (Z.succ i)) by list_solve.
       autorewrite with sublist.
       rewrite (sublist_split 0 (j-Z.succ i) (j-i)) by list_solve.
       rewrite app_ass.
       symmetry.
       destruct (zeq j (Z.succ i)).
       + autorewrite with sublist.
          rewrite (sublist_one (j-Z.succ i) (j-i)) by list_solve.
          rewrite e0, Z.sub_diag.
          autorewrite with sublist. simpl. f_equal. f_equal.
          replace (Z.succ i - i) with 1 by omega.
          rewrite sublist_1_cons. f_equal. omega.
      + rewrite (sublist_split 0 1) by list_solve.
          rewrite app_ass.
          rewrite sublist_1_cons, (sublist_one 0 1) by list_solve.
          simpl.
          autorewrite with sublist. f_equal.
          rewrite (sublist_split 0 (j-Z.succ i - 1) (j-Z.succ i)) by list_solve.
          rewrite app_ass. f_equal. f_equal.
          change (a::le) with ([a]++le).
          autorewrite with sublist. f_equal. omega.
          f_equal. 
          change (a::le) with ([a]++le).
          autorewrite with sublist. f_equal. omega. omega.
Qed.

(*
Lemma suble_skip: forall X (le:list (entry X)) i f,
    0 <= i <= f ->
    f = Zlength le ->
    suble i f le = skipn_le le i.
Proof.
  intros.
  unfold suble, skipn_le. subst. auto.
Qed.


Lemma nth_first_le_app1: forall X (l1:list (entry X)) l2 i,
    0 <= i <= Zlength l1 ->
    nth_first_le (l1 ++ l2) i = nth_first_le l1 i.
Proof.
  intros.
  unfold nth_first_le. autorewrite with sublist. auto.
Qed.

Lemma le_split: forall X (le:list (entry X)) i,
    0 <= i <= Zlength le ->
    le = nth_first_le le i ++ skipn_le le i.
Proof.
  intros.
 unfold nth_first_le, skipn_le. autorewrite with sublist. auto.
Qed.
*)

Lemma insert_rep: forall le (e:entry val),
    iter_sepcon entry_rep le * entry_rep e = iter_sepcon entry_rep (insert_le le e).
Proof.
  intros.
  pose proof (insert_fri _ le e _ _ (eq_refl _) (eq_refl _)).
  pose proof (FRI_bound _ le (entry_key e) 0).
  pose proof (FRI_increase _ le (entry_key e) 0).
  forget (findRecordIndex' le (entry_key e) 0) as i.
  rewrite H; clear H.
  rewrite iter_sepcon_app_comm. simpl.
  rewrite sepcon_comm. f_equal.
  rewrite iter_sepcon_app_comm.
  autorewrite with sublist. auto.
Qed.

Lemma nth_first_insert: forall X {d: Inhabitant X} (le:list (entry X)) e k m,
    k = entry_key e ->
    0 <= m <= findRecordIndex' le k 0 ->
    sublist 0 m (insert_le le e) = sublist 0 m le.
Proof.
  intros. subst.
  rewrite (insert_fri _ le e _ _ (eq_refl _) (eq_refl _)).
  pose proof (FRI_bound _ le (entry_key e) 0).
  forget (findRecordIndex' le (entry_key e) 0) as i.
  autorewrite with sublist. auto.
Qed.

(*
Lemma nth_first_app_same1: forall X (le1:list (entry X)) le2 i,
    i = Zlength le1 ->
    nth_first_le (le1 ++ le2) i = le1.
Proof.
  intros. unfold nth_first_le. autorewrite with sublist. auto.
Qed.
*)

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



