(** * verif_splitnode.v : Correctness proof of splitnode *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import relation_mem.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

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
  unfold upd_Znth. rewrite sublist0_app1. rewrite sublist_app2.
  rewrite semax_lemmas.cons_app with (x:=x).
  rewrite sublist_app2. rewrite Zlength_sublist. rewrite Zlength_cons. simpl.
  replace (i + 1 - (i - 0) - 1) with 0 by omega.
  rewrite sublist_same with (al:=(sublist (i + 1) (Zlength l) l)).
  rewrite sublist_same. auto.
  auto. rewrite Zlength_sublist. omega. omega. omega. auto.
  rewrite Zlength_sublist. rewrite Zlength_app. rewrite Zlength_sublist.
  rewrite Zlength_cons. rewrite Zlength_sublist. omega.
  omega. omega. omega. omega. omega. omega. omega. omega.
  rewrite Zlength_cons. rewrite Zlength_sublist. simpl. omega.
  omega. omega. rewrite Zlength_sublist. omega. omega. omega.
  rewrite Zlength_sublist. omega. omega. omega.
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

Lemma integrity_intern_insert: forall X (le:listentry X) k c i e,
    intern_le le ->
    nth_entry_le i (insert_le le (keychild X k c)) = Some e ->
    exists ki ci, e = keychild X ki ci.
Proof.
Admitted. 

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

Lemma body_splitnode: semax_body Vprog Gprog f_splitnode splitnode_spec.
Proof.
  start_function.
  rename H1 into LEAFENTRY.
  destruct n as [ptr0 le isLeaf First Last nval].
  pose(n:=btnode val ptr0 le isLeaf First Last nval).
  destruct(entry_val_rep e) as [keyrepr coprepr] eqn:HEVR.
  assert(exists k, keyrepr = key_repr k).
  { destruct e; exists k; simpl; simpl in HEVR; inv HEVR; auto. }
  destruct H1 as [k HK].
  forward.                      (* t'28=entry->key *)
  forward_call(n,k).            (* t'1=findrecordindex(node,t'28) *)
  { fold n. cancel. }
  { split; auto. unfold node_wf. fold n in H0. omega. }
  forward.                      (* tgtIdx=t'1 *)
  assert(INRANGE: 0 <= index.idx_to_Z (findRecordIndex n k) <= Z.of_nat (numKeys n)) by apply FRI_inrange.
  fold n in H0. rewrite H0 in INRANGE.
  rewrite unfold_btnode_rep. unfold n. Intros ent_end.
  forward.                      (* t'27=node->Last *)
  { destruct Last; entailer!. }
  forward_call(isLeaf, false, Last, gv). (* t'2=createNewNode(isLeaf,0,t'27 *)
  Intros vnewnode.
  forward.                      (* newnode=t'2 *)
  gather_SEP (malloc_token _ _ _) (data_at _ _ _ _)
             (match ptr0 with
              | Some n' => btnode_rep n'
              | None => emp
              end) (le_iter_sepcon le).
  replace_SEP 0 (btnode_rep n).
  { entailer!. simpl. rewrite unfold_btnode_rep with (n:=n). unfold n. Exists ent_end. cancel.
    apply derives_refl. }
  clear ent_end.
  forward_if(PROP (vnewnode<>nullval)
     LOCAL (temp _newNode vnewnode; temp _t'2 vnewnode; temp _t'27 (Val.of_bool Last);
     temp _tgtIdx (Vint (Int.repr (rep_index (findRecordIndex' le k (index.ip 0)))));
     temp _t'1 (Vint (Int.repr (rep_index (findRecordIndex' le k (index.ip 0))))); 
     temp _t'28 keyrepr; lvar _allEntries (tarray (Tstruct _Entry noattr) 16) v_allEntries;
     temp _node nval; temp _entry pe; temp _isLeaf (Val.of_bool isLeaf))
     SEP (mem_mgr gv; btnode_rep n; btnode_rep (empty_node isLeaf false Last vnewnode);
     data_at_ Tsh (tarray (Tstruct _Entry noattr) 16) v_allEntries; entry_rep e;
     data_at Ews tentry (keyrepr, coprepr) pe)).
  { apply denote_tc_test_eq_split. replace vnewnode with (getval (empty_node isLeaf false Last vnewnode)).
    entailer!. simpl. auto. entailer!. }
  { forward.                    (* skip *)
    entailer!. }
  { assert_PROP(False). entailer!. contradiction. }
  rewrite unfold_btnode_rep with (n:=n). unfold n. Intros ent_end.
  forward.                      (* node->Last = 0 *)
  forward.                      (* t'3=node->isLeaf *)

  forward_if.

  -                             (* Leaf Node *)
    assert(LEAF: isLeaf=true).
    { destruct isLeaf; auto. simpl in H2. inv H2. }
    destruct (findRecordIndex n k) as [|fri] eqn:HFRI.
    { simpl in INRANGE. omega. }
    replace (findRecordIndex' le k (index.ip 0)) with (index.ip fri). simpl.
    Print btnode_rep.
    gather_SEP (malloc_token Ews tbtnode nval)
               (data_at Ews tbtnode  _ nval)
               (match ptr0 with
                | Some n' => btnode_rep n'
                | None => emp
                end)
               (le_iter_sepcon le).
    pose (nleft := btnode val ptr0 le true First false nval).
    replace_SEP 0 (btnode_rep nleft).
    { entailer!. rewrite unfold_btnode_rep with (n:=nleft). unfold nleft.
      Exists ent_end. cancel. } clear ent_end. fold tentry.
    assert(ENTRY: exists ke ve xe, e = keyval val ke ve xe). (* the entry to be inserted at a leaf must be keyval *)
    { destruct e. eauto. simpl in LEAFENTRY.
      rewrite LEAF in LEAFENTRY. exfalso. rewrite LEAFENTRY. auto. }
    destruct ENTRY as [ke [ve [xe ENTRY]]].
    assert_PROP(isptr xe).
    { rewrite ENTRY. unfold entry_rep. entailer!. }
    rename H3 into PTRXE.
    
    forward_for_simple_bound (Z.of_nat fri)
    (EX i:Z, EX allent_end:list (val*(val+val)),
     (PROP (length allent_end = (Fanout + 1 - Z.to_nat(i))%nat)
      LOCAL (temp _t'3 (Val.of_bool isLeaf); temp _newNode vnewnode; temp _t'2 vnewnode;
      temp _t'27 (Val.of_bool Last); temp _tgtIdx (Vint (Int.repr (Z.of_nat fri)));
      temp _t'1 (Vint (Int.repr (Z.of_nat fri))); temp _t'28 keyrepr;
      lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe;
      temp _isLeaf (Val.of_bool isLeaf))
      SEP (mem_mgr gv; btnode_rep nleft; btnode_rep (empty_node isLeaf false Last vnewnode);
           data_at Tsh (tarray tentry 16) (le_to_list (nth_first_le le (Z.to_nat i))++ allent_end) v_allEntries; entry_rep e; data_at Ews tentry (keyrepr, coprepr) pe)))%assert.
    { simpl in INRANGE. rewrite Fanout_eq in INRANGE.
      replace (Z.of_nat 15) with 15 in INRANGE. rep_omega. simpl. auto. }
    { entailer!.
      Exists (default_val (nested_field_type (tarray (Tstruct _Entry noattr) 16) [])).
      entailer!. unfold data_at_, field_at_. simpl.  entailer!. }
    {                           (* loop body *)
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft.
      Intros ent_end.
      assert(HENTRY: exists e, nth_entry_le (Z.to_nat i) le = Some e).
      { apply nth_entry_le_in_range. simpl in INRANGE. rewrite Fanout_eq in INRANGE.
        unfold n in H0. simpl in H0. rewrite H0. rewrite Fanout_eq. apply Nat2Z.inj_lt.
        simpl. rewrite Z2Nat.id. simpl in INRANGE. omega. omega. }
      destruct HENTRY as [ei HENTRY].
      assert (HEI: exists ki vi xi, ei = keyval val ki vi xi).
      { eapply integrity_nth_leaf. eauto. rewrite LEAF. simpl. auto. eauto. }
      destruct HEI as [ki [vi [xi HEI]]]. subst ei.
      assert_PROP(isptr xi).
      { apply le_iter_sepcon_split in HENTRY. rewrite HENTRY. simpl entry_rep. entailer!. }
      rename H5 into XIPTR.
      assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (le_to_list le ++ ent_end) = entry_val_rep (keyval val ki vi xi)).
      { intros. rewrite <- Z2Nat.id with (n:=i). apply Znth_to_list. auto. omega. }
      assert(HIRANGE: (0 <= i < 15)).
      { clear -INRANGE H3. simpl in INRANGE. rewrite Fanout_eq in INRANGE.
        replace (Z.of_nat 15) with 15 in INRANGE by auto. omega. }  
      forward.                  (* t'26 = node->entries[i].key *) 
      { entailer!. rewrite HZNTH. simpl; auto. }
      rewrite HZNTH. simpl.
      Opaque Znth.
      forward.                 (* allEntries[i].key = t'26 *)
      forward.                 (* t'25=node->entries[i]->ptr.record *)
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* allEntries[i]->ptr.record=t'25 *)
      entailer!.
      rename allent_end into x.
      assert(XEMP: Zlength x > 0).
      { destruct x. clear - H4 HIRANGE. simpl in H4. rewrite Fanout_eq in H4.
        apply eq_sym in H4. apply NPeano.Nat.sub_0_le in H4. apply inj_le in H4.
        replace (Z.of_nat (15 + 1)) with 16 in H4. rewrite Z2Nat.id in H4. rep_omega.
        omega. simpl. auto.
        rewrite Zlength_cons. rep_omega. }
      Exists (sublist 1 (Zlength x) x). entailer!.
      { clear -H4 H3 XEMP.
        destruct x.
        - rewrite Zlength_nil in XEMP. omega.
        - rewrite sublist_1_cons. rewrite Zlength_cons. rewrite Zsuccminusone.
          rewrite sublist_same by omega. simpl in H4. rewrite Z2Nat.inj_add by omega.
          simpl.
          assert((Fanout + 1 - Z.to_nat i)%nat = S(Fanout + 1 - (Z.to_nat i + 1))) by omega.
          rewrite H in H4. inv H4. omega. }
      assert(INUM: (Z.to_nat i <= numKeys_le le)%nat).
      { unfold n  in H0. simpl in H0. rewrite H0. clear -INRANGE H3.
        simpl in INRANGE. apply Nat2Z.inj_le.
        simpl. rewrite Z2Nat.id. simpl in INRANGE. omega. omega. }
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft. Exists ent_end. cancel.      
      rewrite upd_Znth_twice.
      rewrite app_Znth2. rewrite le_to_list_length. rewrite numKeys_nth_first. rewrite Z2Nat.id.
      replace (i-i) with 0 by omega.
      rewrite upd_Znth_app2.
      rewrite le_to_list_length. rewrite numKeys_nth_first. rewrite Z2Nat.id.
      replace (i-i) with 0 by omega.
      rewrite upd_Znth_same.
      unfold upd_Znth. rewrite sublist_nil. simpl.
      rewrite nth_first_sublist. rewrite nth_first_sublist.
      rewrite sublist_split with (lo:=0) (mid:=i) (hi:=i+1).
      erewrite sublist_len_1. rewrite <- app_nil_r with (l:=le_to_list le). rewrite HZNTH. simpl.
      rewrite app_nil_r. rewrite <- app_assoc. simpl. cancel.
      rewrite le_to_list_length. unfold n in H0. simpl in H0. rewrite H0. rewrite Fanout_eq.
      replace (Z.of_nat 15) with 15. omega. simpl. auto. omega.
      rewrite le_to_list_length. unfold n in H0. simpl in H0. rewrite H0. rewrite Fanout_eq.
      replace (Z.of_nat 15) with 15. omega. simpl. auto.
      rewrite Zlength_app. rewrite le_to_list_length. rewrite numKeys_nth_first.
      rewrite Z2Nat.id. omega. 
      omega. omega.
      omega. omega.
      rewrite le_to_list_length. rewrite numKeys_nth_first.
      rewrite Z2Nat.id. omega.
      omega. omega.
      omega. omega.
      rewrite le_to_list_length. rewrite numKeys_nth_first. rewrite Z2Nat.id. omega. omega.
      omega.
      rewrite Zlength_app. rewrite le_to_list_length. rewrite numKeys_nth_first. rewrite Z2Nat.id.
      omega. omega. omega. }
    Intros allent_end.
    forward.                    (* t'24=entry->key *)
    rewrite HK. unfold key_repr.

    assert(FRIRANGE: (0 <= fri < 16)%nat).
    { simpl in INRANGE. rewrite Fanout_eq in INRANGE. split. omega.
      replace (Z.of_nat 15) with 15 in INRANGE.
      apply Nat2Z.inj_lt. destruct INRANGE. eapply Z.le_lt_trans with (m:=15). rep_omega.
      simpl. omega. simpl. auto. }
    rewrite ENTRY in HEVR. simpl in HEVR. inv HEVR.

    Opaque Znth.
    forward.                    (* allEntries[tgtIdx]->key = t'24 *)
    forward.                    (* t'23=entry->ptr.record *)
    forward.                    (* allEntries[tgtIdx]->ptr.record = t'23 *)
    assert(0 <= Z.of_nat fri < Zlength (le_to_list (nth_first_le le (Z.to_nat (Z.of_nat fri))) ++ allent_end)).
    { split. omega. rewrite Zlength_app. rewrite le_to_list_length.
      rewrite numKeys_nth_first. rewrite Z2Nat.id. rewrite Zlength_correct.
      rewrite H3. rewrite Nat2Z.id.
      assert(Z.of_nat(Fanout + 1 - fri) > 0).
      { rewrite Fanout_eq. simpl in INRANGE. rewrite Nat2Z.inj_sub.
        simpl. omega. rewrite Fanout_eq in INRANGE. simpl in INRANGE. omega. }
      omega. omega.
      rewrite Nat2Z.id. unfold n in H0. simpl in H0. rewrite H0. rewrite Fanout_eq. omega. }
    rewrite upd_Znth_twice by auto. rewrite upd_Znth_same by auto.
    deadvars!.
    assert(FRILENGTH: Zlength (le_to_list (nth_first_le le (Z.to_nat (Z.of_nat fri)))) = Z.of_nat fri).
    { rewrite le_to_list_length. rewrite numKeys_nth_first. rewrite Nat2Z.id. auto.
      rewrite Nat2Z.id. unfold n in H0. simpl in H0. rewrite H0. simpl in INRANGE. omega. }
    unfold upd_Znth. rewrite sublist_app1 by (try rep_omega; rewrite FRILENGTH; rep_omega).
    rewrite sublist_same by (try rep_omega; rewrite FRILENGTH; rep_omega).
    rewrite sublist_app2 by (rewrite FRILENGTH; rep_omega).
    repeat rewrite FRILENGTH.
    replace (Z.of_nat fri + 1 - Z.of_nat fri) with 1 by rep_omega. rewrite Zlength_app.
    rewrite FRILENGTH.
    replace (Z.of_nat fri + Zlength allent_end - Z.of_nat fri) with (Zlength allent_end) by rep_omega.

    forward_for_simple_bound (Z.of_nat(Fanout)) ( EX i:Z, EX ent_end:list (val * (val+val)),
                                                                     PROP(Z.of_nat fri <= i <= Z.of_nat Fanout; length ent_end = (Fanout - Z.to_nat(i))%nat) LOCAL(temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr (Z.of_nat fri))); lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe)
                                                                         SEP(mem_mgr gv; btnode_rep nleft; btnode_rep (empty_node true false Last vnewnode); data_at Ews tentry (Vint (Int.repr (k_ k)), inr xe) pe; data_at Tsh (tarray tentry 16) (le_to_list (nth_first_le le (Z.to_nat (Z.of_nat fri))) ++ (Vint (Int.repr (k_ k)), inr (force_val (sem_cast_pointer xe))) :: le_to_list(suble (fri) (Z.to_nat i) le) ++ ent_end) v_allEntries; entry_rep(keyval val ke ve xe)))%assert.

    { simpl in INRANGE. rewrite Fanout_eq in INRANGE.
      replace (Z.of_nat 15) with 15 in INRANGE.
      rewrite Fanout_eq. simpl. rep_omega. simpl. auto. }
    abbreviate_semax.
    {                           (* second loop *)
      forward.                  (* i=tgtidx *)
      Exists (Z.of_nat(fri)). Exists ( sublist 1 (Zlength allent_end) allent_end).
      entailer!.
      simpl in INRANGE. split3; try rep_omega.
      { clear -H3 INRANGE. destruct allent_end.
        - simpl in H3. rewrite Nat2Z.id in H3.
          assert((fri <= Fanout)%nat). apply Nat2Z.inj_le. omega. omega.
        - rewrite sublist_1_cons. rewrite Zlength_cons. rewrite Zsuccminusone.
          rewrite sublist_same; auto. simpl in H3. omega. }
      rewrite Nat2Z.id. rewrite suble_nil. cancel. }
    {                           (* loop body *)
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft.
      rename ent_end into x.
      Intros ent_end.
      assert(HENTRY: exists e, nth_entry_le (Z.to_nat i) le = Some e).
      { apply nth_entry_le_in_range. simpl in H0. rewrite H0. apply Nat2Z.inj_lt.
        rewrite Z2Nat.id. omega. omega. }
      destruct HENTRY as [ei HENTRY].
      assert (HEI: exists ki vi xi, ei = keyval val ki vi xi).
      { eapply integrity_nth_leaf. eauto. simpl. auto. eauto. }
      destruct HEI as [ki [vi [xi HEI]]]. subst ei.
      assert_PROP(isptr xi).
      { apply le_iter_sepcon_split in HENTRY. rewrite HENTRY. simpl entry_rep. entailer!. }
      rename H9 into XIPTR.
      rename H7 into IRANGE.
      assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (le_to_list le ++ ent_end) = entry_val_rep (keyval val ki vi xi)).
      { intros. rewrite <- Z2Nat.id with (n:=i). apply Znth_to_list. auto. omega. }
      assert(HIRANGE: (0 <= i < 15)).
      { split. rep_omega. rewrite Fanout_eq in H6. simpl in H6. rep_omega. }
      forward.                  (* t'22=node->entries[i].key *)
      { entailer!. rewrite HZNTH. simpl; auto. }
      rewrite HZNTH. simpl.
      Opaque Znth.
      forward.                  (* allEntries[i+1].key=t'26 *)
      forward.                  (* t'21=node->entries[i].ptr.record *)
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* allEntries[i+1]->ptr.record=t'21 *)
      entailer!.
      assert(XEMP: Zlength x > 0).
      { destruct x. clear -H8 HIRANGE. rewrite Fanout_eq in H8.
        apply eq_sym in H8. apply NPeano.Nat.sub_0_le in H8. apply inj_le in H8.
        simpl in H8. rewrite Z2Nat.id in H8. rep_omega. omega.
        rewrite Zlength_cons. rep_omega. }
      Exists (sublist 1 (Zlength x) x). entailer!.
      { clear -IRANGE H8 XEMP.
        destruct x.
        - rewrite Zlength_nil in XEMP. omega.
        - rewrite sublist_1_cons. rewrite Zlength_cons. rewrite Zsuccminusone.
          rewrite sublist_same by omega. simpl in H8. rewrite Z2Nat.inj_add by omega.
          simpl. omega. }
      assert(INUM: (Z.to_nat i <= numKeys_le le)%nat).
      { unfold n  in H0. simpl in H0. rewrite H0. clear -HIRANGE.
        rewrite Fanout_eq. destruct HIRANGE. apply Z2Nat.inj_lt in H0.
        simpl in H0. omega. auto. omega. }
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft. Exists ent_end. cancel.
      rewrite Nat2Z.id.
      rewrite upd_Znth_twice.
      (* rewrite upd_Znth_app2. *)
      rewrite upd_Znth_same.
      assert((upd_Znth (i + 1) (le_to_list (nth_first_le le fri) ++ (Vint (Int.repr (k_ k)), inr xe) :: le_to_list (suble (fri) ((Z.to_nat i)) le) ++ x) (key_repr ki, inr xi)) = (le_to_list (nth_first_le le fri) ++ (Vint (Int.repr (k_ k)), inr xe) :: le_to_list (suble (fri) ((Z.to_nat (i + 1))) le) ++ sublist 1 (Zlength x) x)).
      { rewrite upd_Znth_app2. rewrite le_to_list_length. rewrite numKeys_nth_first.
        rewrite semax_lemmas.cons_app. rewrite upd_Znth_app2. simpl. rewrite Zlength_cons. simpl.
        rewrite upd_Znth_app2. rewrite le_to_list_length.
        assert(i + 1 - Z.of_nat fri - 1 - Z.of_nat (numKeys_le (suble (fri) ((Z.to_nat i)) le)) = 0).
        { rewrite numKeys_suble. simpl.
          rewrite Nat2Z.inj_sub. rewrite Z2Nat.id. omega. omega.
          rep_omega.
          split. assert(fri <= Z.to_nat i)%nat.
          rep_omega. omega.
          simpl in H0. rewrite H0. clear -H6 HIRANGE. destruct H6.
          rewrite Z2Nat.inj_lt in H0. rewrite Nat2Z.id in H0. omega.
          omega. rep_omega. }
        rewrite H17.
        rewrite upd_Znth0.
        assert(le_to_list (suble (fri) ((Z.to_nat i)) le) ++ [(key_repr ki, (inr xi):(val+val))] = le_to_list (suble (fri) ((Z.to_nat (i + 1))) le)).
        { rewrite Z2Nat.inj_add. simpl. rewrite NPeano.Nat.add_1_r.
          rewrite suble_increase with (e:=keyval val ki vi xi).
          rewrite le_to_list_app. simpl. auto.
          split. destruct IRANGE. clear -H18 HIRANGE. rewrite Nat2Z.inj_le. rewrite Z2Nat.id. auto.
          omega.
          simpl in H0. rewrite H0. apply Nat2Z.inj_lt.
          rewrite Z2Nat.id. omega. omega.
          auto. omega. omega. }
        rewrite <- H18. rewrite <- app_assoc. simpl. auto.
        
        assert(Z.to_nat i < Z.to_nat (Z.of_nat Fanout))%nat. 
        rewrite Nat2Z.id. apply Nat2Z.inj_lt. rewrite Z2Nat.id. omega. omega.
        rewrite le_to_list_length. rewrite numKeys_suble. rep_omega.
        simpl in H0. rewrite H0. split. apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
        apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
        rewrite Zlength_cons. simpl.
        rewrite Zlength_app.
        rewrite le_to_list_length. rewrite numKeys_suble.
        rewrite Zlength_correct. rewrite H8.
        split. omega. rep_omega.
        simpl in H0. rewrite H0. split. apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
        apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
        simpl in H0. rewrite H0. apply Nat2Z.inj_le. omega.
        rewrite Zlength_cons. rewrite Zlength_app. rewrite le_to_list_length. rewrite le_to_list_length.
        rewrite numKeys_nth_first. rewrite numKeys_suble. split. omega.
        rep_omega.
        simpl in H0. rewrite H0. split. apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
        apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
        simpl in H0. rewrite H0. apply Nat2Z.inj_le. omega.
      }
      rewrite H17. cancel.
      rewrite Zlength_app. rewrite Zlength_cons. rewrite le_to_list_length.
      rewrite numKeys_nth_first. rewrite Zlength_app. rewrite le_to_list_length.
      rewrite numKeys_suble. split. omega. rep_omega.
      simpl in H0. rewrite H0. split. apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
        apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
      simpl in H0. rewrite H0. apply Nat2Z.inj_le. omega.
      rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_app.
      rewrite le_to_list_length. rewrite le_to_list_length.
      rewrite numKeys_nth_first. rewrite numKeys_suble. split. omega. rep_omega.
      simpl in H0. rewrite H0. split. apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
        apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
      simpl in H0. rewrite H0. apply Nat2Z.inj_le. omega.
    } 
        
    Intros ent_end.
    deadvars!.
    pose (e:=keyval val ke ve xe).
    rewrite unfold_btnode_rep with (n:=nleft).
    unfold nleft. Intros ent_end0.
    forward.                    (* node->numKeys=8 *)
    Print le_iter_sepcon.
    gather_SEP (le_iter_sepcon le) (entry_rep (keyval val ke ve xe)).
    replace_SEP 0 (le_iter_sepcon (insert_le le e)).
    { entailer!. rewrite <- insert_rep. simpl. entailer!. }
    rewrite le_split with (le0:=insert_le le e) (i:=Middle) by
        (simpl in H0; rewrite numKeys_le_insert; rewrite H0; rewrite Middle_eq; rewrite Fanout_eq; omega).
    rewrite le_iter_sepcon_app.
    
    forward_if (PROP ( )
    LOCAL (temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr (Z.of_nat fri)));
           lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe)
    SEP (mem_mgr gv; btnode_rep (splitnode_left n e); btnode_rep (empty_node true false Last vnewnode);
         data_at Ews tentry (Vint (Int.repr (k_ k)), inr xe) pe;
         data_at Tsh (tarray tentry 16) (le_to_list (nth_first_le le (Z.to_nat (Z.of_nat fri))) ++ (Vint (Int.repr (k_ k)), inr (force_val (sem_cast_pointer xe))) :: le_to_list (suble (fri) ((Z.to_nat (Z.of_nat Fanout))) le) ++ ent_end) v_allEntries; le_iter_sepcon (skipn_le (insert_le le e) Middle))).
    {                           (* fri < 8 *)
      Intros.
      unfold Sfor.              (* both forward_loop and forward_for_simple_bound fail here *)
      forward.                  (* i=tgtIdx *)
      forward_loop (EX i:Z, EX le_end:list(val*(val+val)), PROP(Z.of_nat fri <= i <= Z.of_nat Middle)
LOCAL (temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr (Z.of_nat fri)));
       lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe;
      temp _i (Vint (Int.repr i)))
SEP (mem_mgr gv; le_iter_sepcon (nth_first_le (insert_le le e) Middle);
          le_iter_sepcon (skipn_le (insert_le le e) Middle); malloc_token Ews tbtnode nval;
     data_at Ews tbtnode
       (Val.of_bool true,
       (Val.of_bool First,
       (Val.of_bool false,
       (Vint (Int.repr 8),
       (match ptr0 with
        | Some n' => getval n'
        | None => nullval
        end, le_to_list (nth_first_le (insert_le le e) (Z.to_nat i)) ++ le_end))))) nval;
     match ptr0 with
     | Some n' => btnode_rep n'
     | None => emp
     end; btnode_rep (empty_node true false Last vnewnode);
     data_at Ews tentry (Vint (Int.repr (k_ k)), inr xe) pe;
     data_at Tsh (tarray tentry 16)
       (le_to_list (nth_first_le le (Z.to_nat (Z.of_nat fri))) ++
        (Vint (Int.repr (k_ k)), inr (force_val (sem_cast_pointer xe)))
        :: le_to_list (suble fri (Z.to_nat (Z.of_nat Fanout)) le) ++ ent_end) v_allEntries))%assert.
      - Exists (Z.of_nat fri).
        Exists (le_to_list(skipn_le le fri) ++ ent_end0).
        entailer!.
        { split. omega.  rewrite Middle_eq. simpl. omega. }
        rewrite le_split with (i:=fri) (le0:=le) at 1.
        rewrite le_to_list_app.
        rewrite Nat2Z.id. 
        replace (nth_first_le (insert_le le e) fri) with (nth_first_le le fri).
        rewrite app_assoc. cancel. apply derives_refl.
        rewrite insert_fri with (fri:=fri) (key0:=ke).
        rewrite nth_first_app_same1. auto.
        rewrite numKeys_nth_first. auto.
        simpl in H0. rewrite H0. omega. unfold e. simpl. auto.
        simpl in HFRI. rewrite <- HFRI. apply FRI_repr. auto.
        simpl in H0. rewrite H0. omega.
      -                         (* loop body *)
        Intros i.
        Intros le_end.             
        forward_if.
        + assert(HINSERT: (le_to_list (nth_first_le le (Z.to_nat (Z.of_nat fri))) ++ (Vint (Int.repr (k_ k)), inr (force_val (sem_cast_pointer xe))) :: le_to_list (suble (fri) ((Z.to_nat (Z.of_nat Fanout))) le) ++ ent_end) = le_to_list (insert_le le e) ++ ent_end).
          { rewrite insert_fri with (fri:=fri) (key0:=ke).
            rewrite le_to_list_app.
            simpl. rewrite Nat2Z.id. rewrite H5. rewrite Nat2Z.id.
            rewrite suble_skip. unfold key_repr.
            apply force_val_sem_cast_neutral_isptr in PTRXE.
            replace (force_val (sem_cast_pointer xe)) with xe.
            rewrite <- app_assoc. auto.
            apply Some_inj in PTRXE. auto.
            unfold n in H0. simpl in H0. auto.      
            unfold e. simpl. auto. unfold findRecordIndex in HFRI. unfold n in HFRI.
            rewrite FRI_repr with (key2:=k) by auto. rewrite HFRI. auto.
          } 
          rewrite HINSERT.
          assert(HENTRY: exists ei, nth_entry_le (Z.to_nat i) (insert_le le e) = Some ei).
          { apply nth_entry_le_in_range. simpl in H0. rewrite numKeys_le_insert. rewrite H0.
            rewrite Fanout_eq. rewrite Middle_eq in H9.
            destruct H9. apply Z2Nat.inj_le in H11. rewrite Nat2Z.id in H11.
            omega. omega. omega. }
          destruct HENTRY as [ei HENTRY].  
          assert (HEI: exists ki vi xi, ei = keyval val ki vi xi).
          { eapply integrity_leaf_insert. simpl in H. destruct H. eauto. unfold e in HENTRY.
            eauto. }
          destruct HEI as [ki [vi [xi HEI]]]. subst ei.
          assert_PROP(isptr xi).
          { apply le_iter_sepcon_split in HENTRY.
            gather_SEP (le_iter_sepcon (nth_first_le (insert_le le e) Middle))
                       (le_iter_sepcon (skipn_le (insert_le le e) Middle)).
            replace_SEP 0 ( le_iter_sepcon (insert_le le e)).
            { entailer!. rewrite le_split with (i:=Middle) (le0:= (insert_le le e)) at 3.
              rewrite le_iter_sepcon_app. entailer!. simpl in H0. rewrite numKeys_le_insert.
              rewrite H0. rewrite Middle_eq. rewrite Fanout_eq. omega. }
            rewrite HENTRY. simpl entry_rep. entailer!. }
          rename H11 into XIPTR.
          assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (le_to_list (insert_le le e) ++ ent_end) = entry_val_rep (keyval val ki vi xi)).
          { intros. rewrite <- Z2Nat.id with (n:=i). apply Znth_to_list. auto. omega. }
          assert(0 <= i < 8).
          { split. omega. rewrite Int.signed_repr in H10. auto.
            rewrite Middle_eq in H9. simpl in H9. rep_omega. }
          assert_PROP(Zlength le_end > 0).
          { entailer!.
            clear - H14 H11 H0. simplify_value_fits in H14.
            destruct H14, H1, H2, H3, H4.
            simplify_value_fits in H5. destruct H5.
            rewrite Zlength_app in H5. rewrite le_to_list_length in H5.
            rewrite numKeys_nth_first in H5. rewrite Z2Nat.id in H5. omega. omega.
            simpl in H0. rewrite numKeys_le_insert. rewrite H0. rewrite Fanout_eq.
            destruct H11. rewrite Z2Nat.inj_lt in H8. simpl in H8. omega. omega. omega. }            
          rename H12 into LEEND.
          forward.              (* t'20=allEntries[i]->key *)
          { rewrite HZNTH. entailer!. }
          rewrite HZNTH.
          forward.              (* node->entries[i]->key=t'20 *)
          forward.              (* t'19=allEntries[i]->ptr.record *)
          { rewrite HZNTH. entailer!. }
          rewrite HZNTH.
          forward.              (* node->entries[i]->ptr.record = t'19 *)
          forward.              (* i=i+1 *)
          Exists (i+1).
          Exists (sublist 1 (Zlength le_end) le_end). entailer!.
          { rewrite Middle_eq. simpl. omega. }
          
          rewrite upd_Znth_twice.
          rewrite upd_Znth_same.
          rewrite upd_Znth_app2.
          rewrite le_to_list_length.
          rewrite numKeys_nth_first.
          rewrite Z2Nat.id. replace(i-i) with 0 by omega.
          rewrite upd_Znth0. replace (Z.to_nat (i+1)) with (S (Z.to_nat i)).
          rewrite nth_first_increase with (e:=(keyval val ki vi xi)).
          rewrite le_to_list_app. simpl. rewrite <- app_assoc.
          cancel.
          (* rewrite insert_fri with (fri:=fri) at 1. rewrite le_to_list_app. simpl. *)
          (* rewrite Nat2Z.id. unfold suble. *)
          (* rewrite Nat2Z.id. *)
          (* rewrite nth_first_same with (m:=(Fanout - fri)%nat). *)
          (* rewrite <- app_assoc. simpl. rewrite H5. unfold key_repr. cancel. *)
          (* rewrite numKeys_le_skipn. simpl in H0. rewrite H0. auto. *)
          (* auto. rewrite <- HFRI. simpl. apply FRI_repr. auto. *)
          rewrite numKeys_le_insert. simpl in H0. rewrite H0. destruct H11.
          rewrite Z2Nat.inj_lt in H22. simpl in H22. rewrite Fanout_eq. omega.
          omega. omega.
          auto.
          rewrite Z2Nat.inj_add. simpl. omega. omega. omega. omega.
          rewrite numKeys_le_insert. simpl in H0. rewrite H0. destruct H11.
          rewrite Z2Nat.inj_lt in H22. simpl in H22. rewrite Fanout_eq. omega.
          omega. omega.
          rewrite le_to_list_length. rewrite numKeys_nth_first. rewrite Z2Nat.id.
          rep_omega. omega.
          rewrite numKeys_le_insert. simpl in H0. rewrite H0. destruct H11.
          rewrite Z2Nat.inj_lt in H22. simpl in H22. rewrite Fanout_eq. omega.
          omega. omega.
          rewrite Zlength_app. rewrite le_to_list_length. rewrite numKeys_nth_first.
          rewrite Z2Nat.id. split. omega. omega. omega.
          rewrite numKeys_le_insert. simpl in H0. rewrite H0. destruct H11.
          rewrite Z2Nat.inj_lt in H22. simpl in H22. rewrite Fanout_eq. omega.
          omega. omega.
          rewrite Zlength_app. rewrite le_to_list_length. rewrite numKeys_nth_first.
          rewrite Z2Nat.id. split. omega. omega. omega.
          rewrite numKeys_le_insert. simpl in H0. rewrite H0. destruct H11.
          rewrite Z2Nat.inj_lt in H22. simpl in H22. rewrite Fanout_eq. omega.
          omega. omega.
        + rewrite Middle_eq in H9. simpl in H9. rewrite Int.signed_repr in H10 by rep_omega.
          assert(i=8) by omega.
          forward.              (* break *)
          entailer!.
          unfold n, splitnode_left.
          rewrite unfold_btnode_rep with (n:=btnode val ptr0 (nth_first_le (insert_le le e) Middle) true First false nval).
          Exists le_end.
          cancel. Opaque nth_first_le. simpl.
          rewrite numKeys_nth_first. rewrite Middle_eq. simpl. cancel.
          apply derives_refl.
          simpl in H0. rewrite numKeys_le_insert. rewrite H0.
          rewrite Middle_eq. rewrite Fanout_eq. omega.
    } 
    {                           (* fri >= 8 *)
      forward.                  (* skip *)
      entailer!.
      assert((Middle <=? fri)%nat = true).
      { clear -H8. rewrite Middle_eq. apply leb_correct.
        assert(8 <= Z.of_nat fri) by omega. apply Z2Nat.inj_le in H. simpl in H.
        rewrite Nat2Z.id in H. auto. omega. omega. }
      unfold splitnode_left, n.
      rewrite unfold_btnode_rep with (n:=btnode val ptr0 (nth_first_le (insert_le le e) Middle) true First false nval).
      assert(SPLITLE: le_to_list le = le_to_list (nth_first_le le Middle) ++ le_to_list (skipn_le le Middle)).
      { rewrite le_split with (i:=Middle) at 1. rewrite le_to_list_app. auto.
        simpl in H0. rewrite H0. rewrite Middle_eq, Fanout_eq. omega. }
      rewrite SPLITLE.
      rewrite <- app_assoc.
      Exists (le_to_list (skipn_le le Middle) ++ ent_end0).
      simpl. rewrite numKeys_nth_first.
      rewrite nth_first_insert with (k:=ke). cancel.
      unfold e. simpl. auto. simpl in HFRI.
      rewrite FRI_repr with (key2:=k). rewrite HFRI. simpl. rewrite Middle_eq. simpl. omega.
      auto. simpl in H0. rewrite numKeys_le_insert. rewrite H0. rewrite Middle_eq.
      rewrite Fanout_eq. omega.
    }
    rewrite unfold_btnode_rep with (n:=empty_node true false Last vnewnode).
    simpl. Intros ent_empty.
    assert(HINSERT: (le_to_list (nth_first_le le (Z.to_nat (Z.of_nat fri))) ++ (Vint (Int.repr (k_ k)), inr xe) :: le_to_list (suble (fri) ((Z.to_nat (Z.of_nat Fanout))) le) ++ ent_end) = le_to_list (insert_le le e) ++ ent_end).
    { rewrite insert_fri with (fri:=fri) (key0:=ke).
      rewrite le_to_list_app.
      simpl. rewrite Nat2Z.id. rewrite H5. rewrite Nat2Z.id.
      rewrite suble_skip. unfold key_repr.
      unfold n in H0. simpl in H0. rewrite <- app_assoc. simpl. reflexivity.
      simpl in H0. rewrite H0. auto.
      unfold e. simpl. auto. unfold findRecordIndex in HFRI. unfold n in HFRI. 
      rewrite FRI_repr with (key2:=k) by auto. rewrite HFRI. auto.
    } 
    rewrite HINSERT.
    
    forward_for_simple_bound (Z.of_nat (Fanout) + 1)
(EX i:Z, EX ent_right:list(val*(val+val)), (PROP (Zlength ent_right + i - 8 = Z.of_nat Fanout)
     LOCAL (temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr (Z.of_nat fri)));
     lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe)
     SEP (mem_mgr gv; btnode_rep (splitnode_left n e);
     malloc_token Ews tbtnode vnewnode;
     data_at Ews tbtnode
       (Vtrue, (Vfalse, (Val.of_bool Last, (Vint (Int.repr 0), (nullval, le_to_list(suble Middle (Z.to_nat i) (insert_le le e)) ++ ent_right))))) vnewnode;
     data_at Ews tentry (Vint (Int.repr (k_ k)), inr xe) pe;
     data_at Tsh (tarray tentry 16) (le_to_list (insert_le le e) ++ ent_end) v_allEntries;
     le_iter_sepcon (skipn_le (insert_le le e) Middle))))%assert.                             
    
    { rewrite Fanout_eq. simpl. rep_omega. }
    { rewrite Fanout_eq. simpl. rep_omega. }
    { entailer!. rewrite Middle_eq. rewrite suble_nil. Exists ent_empty. entailer!.
      - simplify_value_fits in H11. destruct H11, H18, H19, H20, H21.
        clear - H22. assert (value_fits (tarray tentry 15) ent_empty). auto.
        simplify_value_fits in H. destruct H.
        rewrite Fanout_eq. replace (Zlength ent_empty + 8 - 8) with (Zlength ent_empty) by omega.
        auto.
      - apply derives_refl. }
    {                           (* loop body *)
      assert(HENTRY: exists ei, nth_entry_le (Z.to_nat i) (insert_le le e) = Some ei).
      { apply nth_entry_le_in_range. simpl in H0. rewrite numKeys_le_insert. rewrite H0.
        rewrite Fanout_eq in H8. simpl in H8. rewrite Fanout_eq. destruct H8.
        apply Z2Nat.inj_lt in H9. simpl in H9. auto. omega. omega. }
      destruct HENTRY as [ei HENTRY].  
      assert (HEI: exists ki vi xi, ei = keyval val ki vi xi).
      { eapply integrity_leaf_insert. simpl in H. destruct H. eauto. unfold e in HENTRY.
        eauto. }
      destruct HEI as [ki [vi [xi HEI]]]. subst ei.
      assert_PROP(isptr xi).
      { apply le_iter_sepcon_split in HENTRY.
        rewrite unfold_btnode_rep with (n:=splitnode_left n e).
        unfold splitnode_left. unfold n. Intros ent_left.
        gather_SEP (le_iter_sepcon (nth_first_le (insert_le le e) Middle)) (le_iter_sepcon (skipn_le (insert_le le e) Middle)).
        replace_SEP 0 ( le_iter_sepcon (insert_le le e)).
        { entailer!. rewrite le_split with (i:=Middle) (le0:= (insert_le le e)) at 3.
          rewrite le_iter_sepcon_app. entailer!. simpl in H0. rewrite numKeys_le_insert.
          rewrite H0. rewrite Middle_eq. rewrite Fanout_eq. omega. }
        rewrite HENTRY. simpl entry_rep. entailer!. }
      rename H9 into XIPTR.
      assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (le_to_list (insert_le le e) ++ ent_end) = entry_val_rep (keyval val ki vi xi)).
      { intros. rewrite <- Z2Nat.id with (n:=i). apply Znth_to_list. auto. omega. }

      rewrite Fanout_eq in H8. simpl in H8.
      forward.                  (* t'18=allEntries[i]->key *)
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* newnode->entries[i-8]->key=t'18 *)
      forward.                  (* t'17=allEntries[i]->ptr.record *)
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* newnode->entries[i-8]->ptr.record=t'17 *)
      entailer!.
      rename ent_right into x.
      rewrite Fanout_eq in H9. simpl in H9. assert(Zlength x = 23 - i) by omega.
      Exists (sublist 1 (Zlength x) x). entailer!.
      { rewrite Fanout_eq. simpl.
        rewrite Zlength_sublist. omega. omega. omega. }
      assert(8 <= Z.to_nat i < 16)%nat.
      { clear - H8.
      destruct H8. apply Z2Nat.inj_lt in H0. apply Z2Nat.inj_le in H.
      simpl in H, H0. omega. omega. omega. omega. omega. }
      
      rewrite upd_Znth_twice.
      rewrite upd_Znth_same.
      rewrite upd_Znth_app2.
      rewrite le_to_list_length.
      rewrite numKeys_suble.
      rewrite Nat2Z.inj_sub.
      rewrite Z2Nat.id. rewrite Middle_eq.
      simpl. replace (i - 8 - (i - 8)) with 0 by omega.
      rewrite upd_Znth0. replace (Z.to_nat (i+1)) with (S (Z.to_nat i)).
      rewrite suble_increase with (e:=(keyval val ki vi xi)).
      rewrite le_to_list_app. simpl. rewrite <- app_assoc.
      cancel.
       
      rewrite numKeys_le_insert. simpl in H0. rewrite H0.
      rewrite Fanout_eq. omega. auto.      
      rewrite Z2Nat.inj_add. simpl. omega. omega. omega.
      omega.
      rewrite Middle_eq. omega.
      rewrite numKeys_le_insert. simpl in H0. rewrite H0. rewrite Middle_eq. rewrite Fanout_eq. omega.
      rewrite le_to_list_length. rewrite numKeys_suble.
      rewrite Middle_eq. rewrite Nat2Z.inj_sub. rewrite Z2Nat.id. simpl.
      omega. omega. omega.
      rewrite numKeys_le_insert. simpl in H0. rewrite H0.
      rewrite Middle_eq. rewrite Fanout_eq. omega.
      rewrite Zlength_app. rewrite le_to_list_length. rewrite numKeys_suble. rewrite H19.
      rewrite Middle_eq. rep_omega. rewrite numKeys_le_insert. simpl in H0. rewrite H0.
      rewrite Middle_eq. rewrite Fanout_eq. omega. 
      rewrite Zlength_app. rewrite le_to_list_length. rewrite numKeys_suble. rewrite H19.
      rewrite Middle_eq. rep_omega. rewrite numKeys_le_insert. simpl in H0. rewrite H0.
      rewrite Middle_eq. rewrite Fanout_eq. omega.
    }
    Intros ent_right.
    forward.
    gather_SEP (malloc_token Ews tbtnode vnewnode) (data_at Ews tbtnode _ vnewnode)
               (le_iter_sepcon (skipn_le (insert_le le e) Middle)).
    replace_SEP 0 (btnode_rep (splitnode_leafnode le e vnewnode Last)).
    { entailer!. rewrite unfold_btnode_rep with (n:=splitnode_leafnode le e vnewnode Last).
      simpl.
      Exists ent_right.
      replace(Z.to_nat (Z.of_nat Fanout + 1)) with (S Fanout).
      rewrite numKeys_le_skipn. rewrite numKeys_le_insert. simpl in H0. rewrite H0.
      assert(HSUB: suble Middle (S Fanout) (insert_le le e) = skipn_le (insert_le le e) Middle).
      { apply suble_skip. rewrite numKeys_le_insert. unfold n in H0. simpl in H0. rewrite H0.
        auto.  }
      rewrite HSUB.
      rewrite Fanout_eq. rewrite Middle_eq.
      replace (Z.of_nat(16 - 8)) with 8 by (simpl; omega). cancel.
      apply derives_refl.
      rewrite Fanout_eq. simpl. auto.
      }
      
    assert(NTHENTRY: exists emid, nth_entry_le Middle (insert_le le e) = Some emid).
    { apply nth_entry_le_in_range. unfold n in H0. simpl in H0. rewrite numKeys_le_insert.
      rewrite H0. rewrite Middle_eq.
      rewrite Fanout_eq. omega. }
    destruct NTHENTRY as [emid NTHENTRY].
    assert(HZNTH: nth_entry_le Middle (insert_le le e) = Some emid) by auto.
    eapply Znth_to_list with (endle:=ent_end) in HZNTH.
    rewrite Middle_eq in HZNTH. simpl in HZNTH.
    
    forward.                    (* t'16=allEntries[8]->key *)
    { entailer!. rewrite HZNTH.
      destruct emid; simpl; auto. }
    rewrite HZNTH.
    forward.                    (* entry->key=t'16 *)
    forward.                    (* entry->ptr.child=newnode *)
    forward.                    (* return *)
    Exists vnewnode. fold e. entailer!. rewrite NTHENTRY. entailer!.
    simpl. unfold splitnode_leafnode. cancel.
    destruct emid; simpl; cancel.
  -                             (* intern node *)
    assert(INTERN: isLeaf=false).
    { destruct isLeaf; auto. simpl in H2. inv H2. }
    destruct (findRecordIndex n k) as [|fri] eqn:HFRI.
    { simpl in INRANGE. omega. }
    replace (findRecordIndex' le k (index.ip 0)) with (index.ip fri). simpl.
    gather_SEP 0 1 2 3.
    pose (nleft := btnode val ptr0 le false First false nval).
    replace_SEP 0 (btnode_rep nleft).
    { entailer!. rewrite unfold_btnode_rep with (n:=nleft). unfold nleft.
      Exists ent_end. cancel. } clear ent_end. fold tentry.
    assert(ENTRY: exists ke ce, e = keychild val ke ce). (* the entry to be inserted at an intern node must be keychild *)
    { destruct e. simpl in LEAFENTRY.
      rewrite INTERN in LEAFENTRY. exfalso. rewrite <- LEAFENTRY. auto. eauto. }
    destruct ENTRY as [ke [ce ENTRY]].
    assert_PROP(isptr (getval ce)).
    { rewrite ENTRY. unfold entry_rep. entailer!. }
    rename H3 into PTRCE.
    
    forward_for_simple_bound (Z.of_nat fri)
    (EX i:Z, EX allent_end:list (val*(val+val)),
     (PROP (length allent_end = (Fanout + 1 - Z.to_nat(i))%nat)
      LOCAL (temp _t'3 (Val.of_bool isLeaf); temp _newNode vnewnode; temp _t'2 vnewnode;
      temp _t'27 (Val.of_bool Last); temp _tgtIdx (Vint (Int.repr (Z.of_nat fri)));
      temp _t'1 (Vint (Int.repr (Z.of_nat fri))); temp _t'28 keyrepr;
      lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe;
      temp _isLeaf (Val.of_bool isLeaf))
      SEP (btnode_rep nleft; btnode_rep (empty_node isLeaf false Last vnewnode);
           data_at Ews (tarray tentry 16) (le_to_list (nth_first_le le (Z.to_nat i))++ allent_end) v_allEntries; entry_rep e; data_at Ews tentry (keyrepr, coprepr) pe)))%assert.
    { simpl in INRANGE. rewrite Fanout_eq in INRANGE.
      replace (Z.of_nat 15) with 15 in INRANGE. rep_omega. simpl. auto. }
    { entailer!.
      Exists (default_val (nested_field_type (tarray (Tstruct _Entry noattr) 16) [])).
      entailer!. unfold data_at_, field_at_. entailer!. }
    {                           (* loop body *)
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft.
      Intros ent_end.
      assert(HENTRY: exists e, nth_entry_le (Z.to_nat i) le = Some e).
      { apply nth_entry_le_in_range. simpl in INRANGE. rewrite Fanout_eq in INRANGE.
        unfold n in H0. simpl in H0. rewrite H0. rewrite Fanout_eq. apply Nat2Z.inj_lt.
        simpl. rewrite Z2Nat.id. simpl in INRANGE. omega. omega. }
      destruct HENTRY as [ei HENTRY].
      assert (HEI: exists ki ci, ei = keychild val ki ci).
      { eapply integrity_nth. eauto. rewrite INTERN. simpl. auto. eauto. }
      destruct HEI as [ki [ci HEI]]. subst ei.
      assert_PROP(isptr (getval ci)).
      { apply le_iter_sepcon_split in HENTRY. rewrite HENTRY. simpl entry_rep. entailer!. }
      rename H5 into CIPTR.
      assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (le_to_list le ++ ent_end) = entry_val_rep (keychild val ki ci)).
      { intros. rewrite <- Z2Nat.id with (n:=i). apply Znth_to_list. auto. omega. }
      assert(HIRANGE: (0 <= i < 15)).
      { clear -INRANGE H3. simpl in INRANGE. rewrite Fanout_eq in INRANGE.
        replace (Z.of_nat 15) with 15 in INRANGE by auto. omega. }  
      forward.                  (* t'26 = node->entries[i].key *) 
      { entailer!. rewrite HZNTH. simpl; auto. }
      rewrite HZNTH. simpl.
      Opaque Znth.
      forward.                 (* allEntries[i].key = t'26 *)
      forward.                 (* t'25=node->entries[i]->ptr.record *)
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* allEntries[i]->ptr.record=t'25 *)
      entailer!.
      rename allent_end into x.
      assert(XEMP: Zlength x > 0).
      { destruct x. clear - H4 HIRANGE. simpl in H4. rewrite Fanout_eq in H4.
        apply eq_sym in H4. apply NPeano.Nat.sub_0_le in H4. apply inj_le in H4.
        replace (Z.of_nat (15 + 1)) with 16 in H4. rewrite Z2Nat.id in H4. rep_omega.
        omega. simpl. auto.
        rewrite Zlength_cons. rep_omega. }
      Exists (sublist 1 (Zlength x) x). entailer!.
      { clear -H4 H3 XEMP.
        destruct x.
        - rewrite Zlength_nil in XEMP. omega.
        - rewrite sublist_1_cons. rewrite Zlength_cons. rewrite Zsuccminusone.
          rewrite sublist_same by omega. simpl in H4. rewrite Z2Nat.inj_add by omega.
          simpl.
          assert((Fanout + 1 - Z.to_nat i)%nat = S(Fanout + 1 - (Z.to_nat i + 1))) by omega.
          rewrite H in H4. inv H4. omega. }
      assert(INUM: (Z.to_nat i <= numKeys_le le)%nat).
      { unfold n  in H0. simpl in H0. rewrite H0. clear -INRANGE H3.
        simpl in INRANGE. apply Nat2Z.inj_le.
        simpl. rewrite Z2Nat.id. simpl in INRANGE. omega. omega. }
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft. Exists ent_end. cancel.      
      rewrite upd_Znth_twice.
      rewrite app_Znth2. rewrite le_to_list_length. rewrite numKeys_nth_first. rewrite Z2Nat.id.
      replace (i-i) with 0 by omega.
      rewrite upd_Znth_app2.
      rewrite le_to_list_length. rewrite numKeys_nth_first. rewrite Z2Nat.id.
      replace (i-i) with 0 by omega.
      rewrite upd_Znth_same.
      unfold upd_Znth. rewrite sublist_nil. simpl.
      rewrite nth_first_sublist. rewrite nth_first_sublist.
      rewrite sublist_split with (lo:=0) (mid:=i) (hi:=i+1).
      erewrite sublist_len_1. rewrite <- app_nil_r with (l:=le_to_list le). rewrite HZNTH. simpl.
      rewrite app_nil_r. rewrite <- app_assoc. simpl. cancel.
      rewrite le_to_list_length. unfold n in H0. simpl in H0. rewrite H0. rewrite Fanout_eq.
      replace (Z.of_nat 15) with 15. omega. simpl. auto. omega.
      rewrite le_to_list_length. unfold n in H0. simpl in H0. rewrite H0. rewrite Fanout_eq.
      replace (Z.of_nat 15) with 15. omega. simpl. auto.
      rewrite Zlength_app. rewrite le_to_list_length. rewrite numKeys_nth_first.
      rewrite Z2Nat.id. omega. 
      omega. omega.
      omega. omega.
      rewrite le_to_list_length. rewrite numKeys_nth_first.
      rewrite Z2Nat.id. omega.
      omega. omega.
      omega. omega.
      rewrite le_to_list_length. rewrite numKeys_nth_first. rewrite Z2Nat.id. omega. omega.
      omega.
      rewrite Zlength_app. rewrite le_to_list_length. rewrite numKeys_nth_first. rewrite Z2Nat.id.
      omega. omega. omega. }
    Intros allent_end.
    forward.                    (* t'24=entry->key *)
    rewrite HK. unfold key_repr.

    assert(FRIRANGE: (0 <= fri < 16)%nat).
    { simpl in INRANGE. rewrite Fanout_eq in INRANGE. split. omega.
      replace (Z.of_nat 15) with 15 in INRANGE.
      apply Nat2Z.inj_lt. destruct INRANGE. eapply Z.le_lt_trans with (m:=15). rep_omega.
      simpl. omega. simpl. auto. }
    rewrite ENTRY in HEVR. simpl in HEVR. inv HEVR.

    Opaque Znth.
    forward.                    (* allEntries[tgtIdx]->key = t'24 *)
    forward.                    (* t'23=entry->ptr.record *)
    forward.                    (* allEntries[tgtIdx]->ptr.record = t'23 *)
    assert(0 <= Z.of_nat fri < Zlength (le_to_list (nth_first_le le (Z.to_nat (Z.of_nat fri))) ++ allent_end)).
    { split. omega. rewrite Zlength_app. rewrite le_to_list_length.
      rewrite numKeys_nth_first. rewrite Z2Nat.id. rewrite Zlength_correct.
      rewrite H3. rewrite Nat2Z.id.
      assert(Z.of_nat(Fanout + 1 - fri) > 0).
      { rewrite Fanout_eq. simpl in INRANGE. rewrite Nat2Z.inj_sub.
        simpl. omega. rewrite Fanout_eq in INRANGE. simpl in INRANGE. omega. }
      omega. omega.
      rewrite Nat2Z.id. unfold n in H0. simpl in H0. rewrite H0. rewrite Fanout_eq. omega. }
    rewrite upd_Znth_twice by auto. rewrite upd_Znth_same by auto.
    deadvars!.
    assert(FRILENGTH: Zlength (le_to_list (nth_first_le le (Z.to_nat (Z.of_nat fri)))) = Z.of_nat fri).
    { rewrite le_to_list_length. rewrite numKeys_nth_first. rewrite Nat2Z.id. auto.
      rewrite Nat2Z.id. unfold n in H0. simpl in H0. rewrite H0. simpl in INRANGE. omega. }
    unfold upd_Znth. rewrite sublist_app1 by (try rep_omega; rewrite FRILENGTH; rep_omega).
    rewrite sublist_same by (try rep_omega; rewrite FRILENGTH; rep_omega).
    rewrite sublist_app2 by (rewrite FRILENGTH; rep_omega).
    repeat rewrite FRILENGTH.
    replace (Z.of_nat fri + 1 - Z.of_nat fri) with 1 by rep_omega. rewrite Zlength_app.
    rewrite FRILENGTH.
    replace (Z.of_nat fri + Zlength allent_end - Z.of_nat fri) with (Zlength allent_end) by rep_omega.

    forward_for_simple_bound (Z.of_nat(Fanout)) ( EX i:Z, EX ent_end:list (val * (val+val)), PROP(Z.of_nat fri <= i <= Z.of_nat Fanout; length ent_end = (Fanout - Z.to_nat(i))%nat) LOCAL(temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr (Z.of_nat fri))); lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe) SEP(btnode_rep nleft; btnode_rep (empty_node false false Last vnewnode);data_at Ews tentry (Vint (Int.repr (k_ k)), inl (getval ce)) pe; data_at Ews (tarray tentry 16) (le_to_list (nth_first_le le (Z.to_nat (Z.of_nat fri))) ++ (Vint (Int.repr (k_ k)), inl (getval ce)) :: le_to_list(suble (fri) (Z.to_nat i) le) ++ ent_end) v_allEntries; entry_rep(keychild val ke ce)))%assert.

    { simpl in INRANGE. rewrite Fanout_eq in INRANGE.
      replace (Z.of_nat 15) with 15 in INRANGE.
      rewrite Fanout_eq. simpl. rep_omega. simpl. auto. }
    abbreviate_semax.
    {                           (* second loop *)
      forward.                  (* i=tgtidx *)
      Exists (Z.of_nat(fri)). Exists ( sublist 1 (Zlength allent_end) allent_end).
      entailer!.
      simpl in INRANGE. split3; try rep_omega.
      { clear -H3 INRANGE. destruct allent_end.
        - simpl in H3. rewrite Nat2Z.id in H3.
          assert((fri <= Fanout)%nat). apply Nat2Z.inj_le. omega. omega.
        - rewrite sublist_1_cons. rewrite Zlength_cons. rewrite Zsuccminusone.
          rewrite sublist_same; auto. simpl in H3. omega. }
      rewrite Nat2Z.id. rewrite suble_nil. cancel. }
    {                           (* loop body *)
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft.
      rename ent_end into x.
      Intros ent_end.
      assert(HENTRY: exists e, nth_entry_le (Z.to_nat i) le = Some e).
      { apply nth_entry_le_in_range. simpl in H0. rewrite H0. apply Nat2Z.inj_lt.
        rewrite Z2Nat.id. omega. omega. }
      destruct HENTRY as [ei HENTRY].
      assert (HEI: exists ki ci, ei = keychild val ki ci).
      { eapply integrity_nth. eauto. simpl. auto. eauto. }
      destruct HEI as [ki [ci HEI]]. subst ei.
      assert_PROP(isptr (getval ci)).
      { apply le_iter_sepcon_split in HENTRY. rewrite HENTRY. simpl entry_rep. entailer!. }
      rename H9 into CIPTR.
      rename H7 into IRANGE.
      assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (le_to_list le ++ ent_end) = entry_val_rep (keychild val ki ci)).
      { intros. rewrite <- Z2Nat.id with (n:=i). apply Znth_to_list. auto. omega. }
      assert(HIRANGE: (0 <= i < 15)).
      { split. rep_omega. rewrite Fanout_eq in H6. simpl in H6. rep_omega. }
      forward.                  (* t'22=node->entries[i].key *)
      { entailer!. rewrite HZNTH. simpl; auto. }
      rewrite HZNTH. simpl.
      Opaque Znth.
      forward.                  (* allEntries[i+1].key=t'26 *)
      forward.                  (* t'21=node->entries[i].ptr.record *)
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* allEntries[i+1]->ptr.record=t'21 *)
      entailer!.
      assert(XEMP: Zlength x > 0).
      { destruct x. clear -H8 HIRANGE. rewrite Fanout_eq in H8.
        apply eq_sym in H8. apply NPeano.Nat.sub_0_le in H8. apply inj_le in H8.
        simpl in H8. rewrite Z2Nat.id in H8. rep_omega. omega.
        rewrite Zlength_cons. rep_omega. }
      Exists (sublist 1 (Zlength x) x). entailer!.
      { clear -IRANGE H8 XEMP.
        destruct x.
        - rewrite Zlength_nil in XEMP. omega.
        - rewrite sublist_1_cons. rewrite Zlength_cons. rewrite Zsuccminusone.
          rewrite sublist_same by omega. simpl in H8. rewrite Z2Nat.inj_add by omega.
          simpl. omega. }
      assert(INUM: (Z.to_nat i <= numKeys_le le)%nat).
      { unfold n  in H0. simpl in H0. rewrite H0. clear -HIRANGE.
        rewrite Fanout_eq. destruct HIRANGE. apply Z2Nat.inj_lt in H0.
        simpl in H0. omega. auto. omega. }
      rewrite unfold_btnode_rep with (n:=nleft). unfold nleft. Exists ent_end. cancel.
      rewrite Nat2Z.id.
      rewrite upd_Znth_twice.
      (* rewrite upd_Znth_app2. *)
      rewrite upd_Znth_same.
      assert((upd_Znth (i + 1) (le_to_list (nth_first_le le fri) ++ (Vint (Int.repr (k_ k)), inl (getval ce)) :: le_to_list (suble (fri) ((Z.to_nat i)) le) ++ x) (key_repr ki, inl (getval ci))) = (le_to_list (nth_first_le le fri) ++ (Vint (Int.repr (k_ k)), inl (getval ce)) :: le_to_list (suble (fri) ((Z.to_nat (i + 1))) le) ++ sublist 1 (Zlength x) x)).
      { rewrite upd_Znth_app2. rewrite le_to_list_length. rewrite numKeys_nth_first.
        rewrite semax_lemmas.cons_app. rewrite upd_Znth_app2. simpl. rewrite Zlength_cons. simpl.
        rewrite upd_Znth_app2. rewrite le_to_list_length.
        assert(i + 1 - Z.of_nat fri - 1 - Z.of_nat (numKeys_le (suble (fri) ((Z.to_nat i)) le)) = 0).
        { rewrite numKeys_suble. simpl.
          rewrite Nat2Z.inj_sub. rewrite Z2Nat.id. omega. omega.
          rep_omega.
          split. assert(fri <= Z.to_nat i)%nat.
          rep_omega. omega.
          simpl in H0. rewrite H0. clear -H6 HIRANGE. destruct H6.
          rewrite Z2Nat.inj_lt in H0. rewrite Nat2Z.id in H0. omega.
          omega. rep_omega. }
        rewrite H18.
        rewrite upd_Znth0.
        assert(le_to_list (suble (fri) ((Z.to_nat i)) le) ++ [(key_repr ki, (inl (getval ci)):(val+val))] = le_to_list (suble (fri) ((Z.to_nat (i + 1))) le)).
        { rewrite Z2Nat.inj_add. simpl. rewrite NPeano.Nat.add_1_r.
          rewrite suble_increase with (e:=keychild val ki ci).
          rewrite le_to_list_app. simpl. auto.
          split. destruct IRANGE. clear -H19 HIRANGE. rewrite Nat2Z.inj_le. rewrite Z2Nat.id. auto.
          omega.
          simpl in H0. rewrite H0. apply Nat2Z.inj_lt.
          rewrite Z2Nat.id. omega. omega.
          auto. omega. omega. }
        rewrite <- H19. rewrite <- app_assoc. simpl. auto.
        
        assert(Z.to_nat i < Z.to_nat (Z.of_nat Fanout))%nat. 
        rewrite Nat2Z.id. apply Nat2Z.inj_lt. rewrite Z2Nat.id. omega. omega.
        rewrite le_to_list_length. rewrite numKeys_suble. rep_omega.
        simpl in H0. rewrite H0. split. apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
        apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
        rewrite Zlength_cons. simpl.
        rewrite Zlength_app.
        rewrite le_to_list_length. rewrite numKeys_suble.
        rewrite Zlength_correct. rewrite H8.
        split. omega. rep_omega.
        simpl in H0. rewrite H0. split. apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
        apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
        simpl in H0. rewrite H0. apply Nat2Z.inj_le. omega.
        rewrite Zlength_cons. rewrite Zlength_app. rewrite le_to_list_length. rewrite le_to_list_length.
        rewrite numKeys_nth_first. rewrite numKeys_suble. split. omega.
        rep_omega.
        simpl in H0. rewrite H0. split. apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
        apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
        simpl in H0. rewrite H0. apply Nat2Z.inj_le. omega.
      }
      rewrite H18. cancel.
      rewrite Zlength_app. rewrite Zlength_cons. rewrite le_to_list_length.
      rewrite numKeys_nth_first. rewrite Zlength_app. rewrite le_to_list_length.
      rewrite numKeys_suble. split. omega. rep_omega.
      simpl in H0. rewrite H0. split. apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
        apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
      simpl in H0. rewrite H0. apply Nat2Z.inj_le. omega.
      rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_app.
      rewrite le_to_list_length. rewrite le_to_list_length.
      rewrite numKeys_nth_first. rewrite numKeys_suble. split. omega. rep_omega.
      simpl in H0. rewrite H0. split. apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
        apply Nat2Z.inj_le. rewrite Z2Nat.id. omega. omega.
      simpl in H0. rewrite H0. apply Nat2Z.inj_le. omega.
    } 
        
    Intros ent_end.
    deadvars!.
    pose (e:=keychild val ke ce).
    rewrite unfold_btnode_rep with (n:=nleft).
    unfold nleft. Intros ent_end0.
    forward.                    (* node->numKeys=8 *)
    gather_SEP 3 7.
    replace_SEP 0 (le_iter_sepcon (insert_le le e)).
    { entailer!. rewrite <- insert_rep. simpl. entailer!. }
    rewrite le_split with (le0:=insert_le le e) (i:=Middle) by
        (simpl in H0; rewrite numKeys_le_insert; rewrite H0; rewrite Middle_eq; rewrite Fanout_eq; omega).
    rewrite le_iter_sepcon_app.
    
    forward_if (PROP ( )
    LOCAL (temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr (Z.of_nat fri)));
           lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe)
    SEP (btnode_rep (splitnode_left n e); btnode_rep (empty_node false false Last vnewnode);
         data_at Ews tentry (Vint (Int.repr (k_ k)), inl (getval ce)) pe;
         data_at Ews (tarray tentry 16) (le_to_list (nth_first_le le (Z.to_nat (Z.of_nat fri))) ++ (Vint (Int.repr (k_ k)), inl (getval ce)) :: le_to_list (suble (fri) ((Z.to_nat (Z.of_nat Fanout))) le) ++ ent_end) v_allEntries; le_iter_sepcon (skipn_le (insert_le le e) Middle))).
    {                           (* fri < 8 *)
      Intros.
      unfold Sfor.              (* both forward_loop and forward_for_simple_bound fail here *)
      forward.                  (* i=tgtIdx *)
      forward_loop (EX i:Z, EX le_end:list(val*(val+val)), PROP(Z.of_nat fri <= i <= Z.of_nat Middle)
LOCAL (temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr (Z.of_nat fri)));
       lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe;
      temp _i (Vint (Int.repr i)))
SEP (le_iter_sepcon (nth_first_le (insert_le le e) Middle);
          le_iter_sepcon (skipn_le (insert_le le e) Middle); malloc_token Ews tbtnode nval;
     data_at Ews tbtnode
       (Val.of_bool false,
       (Val.of_bool First,
       (Val.of_bool false,
       (Vint (Int.repr 8),
       (match ptr0 with
        | Some n' => getval n'
        | None => nullval
        end, le_to_list (nth_first_le (insert_le le e) (Z.to_nat i)) ++ le_end))))) nval;
     match ptr0 with
     | Some n' => btnode_rep n'
     | None => emp
     end; btnode_rep (empty_node false false Last vnewnode);
     data_at Ews tentry (Vint (Int.repr (k_ k)), inl (getval ce)) pe;
     data_at Ews (tarray tentry 16)
       (le_to_list (nth_first_le le (Z.to_nat (Z.of_nat fri))) ++
        (Vint (Int.repr (k_ k)), inl (getval ce))
        :: le_to_list (suble fri (Z.to_nat (Z.of_nat Fanout)) le) ++ ent_end) v_allEntries))%assert.
      - Exists (Z.of_nat fri).
        Exists (le_to_list(skipn_le le fri) ++ ent_end0).
        entailer!.
        { split. omega.  rewrite Middle_eq. simpl. omega. }
        rewrite le_split with (i:=fri) (le0:=le) at 1.
        rewrite le_to_list_app.
        rewrite Nat2Z.id. 
        replace (nth_first_le (insert_le le e) fri) with (nth_first_le le fri).
        rewrite app_assoc. cancel. apply derives_refl.
        rewrite insert_fri with (fri:=fri) (key0:=ke).
        rewrite nth_first_app_same1. auto.
        rewrite numKeys_nth_first. auto.
        simpl in H0. rewrite H0. omega. unfold e. simpl. auto.
        simpl in HFRI. rewrite <- HFRI. apply FRI_repr. auto.
        simpl in H0. rewrite H0. omega.
      -                         (* loop body *)
        Intros i.
        Intros le_end.             
        forward_if.
        + assert(HINSERT: (le_to_list (nth_first_le le (Z.to_nat (Z.of_nat fri))) ++ (Vint (Int.repr (k_ k)), inl (getval ce)) :: le_to_list (suble (fri) ((Z.to_nat (Z.of_nat Fanout))) le) ++ ent_end) = le_to_list (insert_le le e) ++ ent_end).
          { rewrite insert_fri with (fri:=fri) (key0:=ke).
            rewrite le_to_list_app.
            simpl. rewrite Nat2Z.id. rewrite H5. rewrite Nat2Z.id.
            rewrite suble_skip. unfold key_repr.
            rewrite <- app_assoc. auto.
            unfold n in H0. simpl in H0. auto.      
            unfold e. simpl. auto. unfold findRecordIndex in HFRI. unfold n in HFRI.
            rewrite FRI_repr with (key2:=k) by auto. rewrite HFRI. auto.
          } 
          rewrite HINSERT.
          assert(HENTRY: exists ei, nth_entry_le (Z.to_nat i) (insert_le le e) = Some ei).
          { apply nth_entry_le_in_range. simpl in H0. rewrite numKeys_le_insert. rewrite H0.
            rewrite Fanout_eq. rewrite Middle_eq in H9.
            destruct H9. apply Z2Nat.inj_le in H11. rewrite Nat2Z.id in H11.
            omega. omega. omega. }
          destruct HENTRY as [ei HENTRY].  
          assert (HEI: exists ki ci, ei = keychild val ki ci).
          { eapply integrity_intern_insert. simpl in H. destruct ptr0. eauto. inv H. unfold e in HENTRY.
            eauto. }
          destruct HEI as [ki [ci HEI]]. subst ei.
          assert_PROP(isptr (getval ci)).
          { apply le_iter_sepcon_split in HENTRY.
            gather_SEP 0 1.
            replace_SEP 0 ( le_iter_sepcon (insert_le le e)).
            { entailer!. rewrite le_split with (i:=Middle) (le0:= (insert_le le e)) at 3.
              rewrite le_iter_sepcon_app. entailer!. simpl in H0. rewrite numKeys_le_insert.
              rewrite H0. rewrite Middle_eq. rewrite Fanout_eq. omega. }
            rewrite HENTRY. simpl entry_rep. entailer!. }
          rename H11 into CIPTR.
          assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (le_to_list (insert_le le e) ++ ent_end) = entry_val_rep (keychild val ki ci)).
          { intros. rewrite <- Z2Nat.id with (n:=i). apply Znth_to_list. auto. omega. }
          assert(0 <= i < 8).
          { split. omega. rewrite Int.signed_repr in H10. auto.
            rewrite Middle_eq in H9. simpl in H9. rep_omega. }
          assert_PROP(Zlength le_end > 0).
          { entailer!.
            clear - H14 H11 H0. simplify_value_fits in H14.
            destruct H14, H1, H2, H3, H4.
            simplify_value_fits in H5. destruct H5.
            rewrite Zlength_app in H5. rewrite le_to_list_length in H5.
            rewrite numKeys_nth_first in H5. rewrite Z2Nat.id in H5. omega. omega.
            simpl in H0. rewrite numKeys_le_insert. rewrite H0. rewrite Fanout_eq.
            destruct H11. rewrite Z2Nat.inj_lt in H8. simpl in H8. omega. omega. omega. }            
          rename H12 into LEEND.
          forward.              (* t'20=allEntries[i]->key *)
          { rewrite HZNTH. entailer!. }
          rewrite HZNTH.
          forward.              (* node->entries[i]->key=t'20 *)
          forward.              (* t'19=allEntries[i]->ptr.record *)
          { rewrite HZNTH. entailer!. }
          rewrite HZNTH.
          forward.              (* node->entries[i]->ptr.record = t'19 *)
          forward.              (* i=i+1 *)
          Exists (i+1).
          Exists (sublist 1 (Zlength le_end) le_end). entailer!.
          { rewrite Middle_eq. simpl. omega. }
          
          rewrite upd_Znth_twice.
          rewrite upd_Znth_same.
          rewrite upd_Znth_app2.
          rewrite le_to_list_length.
          rewrite numKeys_nth_first.
          rewrite Z2Nat.id. replace(i-i) with 0 by omega.
          rewrite upd_Znth0. replace (Z.to_nat (i+1)) with (S (Z.to_nat i)).
          rewrite nth_first_increase with (e:=(keychild val ki ci)).
          rewrite le_to_list_app. simpl. rewrite <- app_assoc.
          cancel.
          (* rewrite insert_fri with (fri:=fri) at 1. rewrite le_to_list_app. simpl. *)
          (* rewrite Nat2Z.id. unfold suble. *)
          (* rewrite Nat2Z.id. *)
          (* rewrite nth_first_same with (m:=(Fanout - fri)%nat). *)
          (* rewrite <- app_assoc. simpl. rewrite H5. unfold key_repr. cancel. *)
          (* rewrite numKeys_le_skipn. simpl in H0. rewrite H0. auto. *)
          (* auto. rewrite <- HFRI. simpl. apply FRI_repr. auto. *)
          rewrite numKeys_le_insert. simpl in H0. rewrite H0. destruct H11.
          rewrite Z2Nat.inj_lt in H22. simpl in H22. rewrite Fanout_eq. omega.
          omega. omega.
          auto.
          rewrite Z2Nat.inj_add. simpl. omega. omega. omega. omega.
          rewrite numKeys_le_insert. simpl in H0. rewrite H0. destruct H11.
          rewrite Z2Nat.inj_lt in H22. simpl in H22. rewrite Fanout_eq. omega.
          omega. omega.
          rewrite le_to_list_length. rewrite numKeys_nth_first. rewrite Z2Nat.id.
          rep_omega. omega.
          rewrite numKeys_le_insert. simpl in H0. rewrite H0. destruct H11.
          rewrite Z2Nat.inj_lt in H22. simpl in H22. rewrite Fanout_eq. omega.
          omega. omega.
          rewrite Zlength_app. rewrite le_to_list_length. rewrite numKeys_nth_first.
          rewrite Z2Nat.id. split. omega. omega. omega.
          rewrite numKeys_le_insert. simpl in H0. rewrite H0. destruct H11.
          rewrite Z2Nat.inj_lt in H22. simpl in H22. rewrite Fanout_eq. omega.
          omega. omega.
          rewrite Zlength_app. rewrite le_to_list_length. rewrite numKeys_nth_first.
          rewrite Z2Nat.id. split. omega. omega. omega.
          rewrite numKeys_le_insert. simpl in H0. rewrite H0. destruct H11.
          rewrite Z2Nat.inj_lt in H22. simpl in H22. rewrite Fanout_eq. omega.
          omega. omega.
        + rewrite Middle_eq in H9. simpl in H9. rewrite Int.signed_repr in H10 by rep_omega.
          assert(i=8) by omega.
          forward.              (* break *)
          entailer!.
          rewrite unfold_btnode_rep with (n:=btnode val ptr0 (nth_first_le (insert_le le e) Middle) false First false nval).
          Exists le_end.
          cancel. Opaque nth_first_le. simpl.
          rewrite numKeys_nth_first. rewrite Middle_eq. simpl. cancel.
          apply derives_refl.
          simpl in H0. rewrite numKeys_le_insert. rewrite H0.
          rewrite Middle_eq. rewrite Fanout_eq. omega.
    } 
    {                           (* fri >= 8 *)
      forward.                  (* skip *)
      entailer!.
      assert((Middle <=? fri)%nat = true).
      { clear -H8. rewrite Middle_eq. apply leb_correct.
        assert(8 <= Z.of_nat fri) by omega. apply Z2Nat.inj_le in H. simpl in H.
        rewrite Nat2Z.id in H. auto. omega. omega. }
      rewrite unfold_btnode_rep with (n:=btnode val ptr0 (nth_first_le (insert_le le e) Middle) false First false nval).
      assert(SPLITLE: le_to_list le = le_to_list (nth_first_le le Middle) ++ le_to_list (skipn_le le Middle)).
      { rewrite le_split with (i:=Middle) at 1. rewrite le_to_list_app. auto.
        simpl in H0. rewrite H0. rewrite Middle_eq, Fanout_eq. omega. }
      rewrite SPLITLE.
      rewrite <- app_assoc.
      Exists (le_to_list (skipn_le le Middle) ++ ent_end0).
      simpl. rewrite numKeys_nth_first.
      rewrite nth_first_insert with (k:=ke). cancel.
      unfold e. simpl. auto. simpl in HFRI.
      rewrite FRI_repr with (key2:=k). rewrite HFRI. simpl. rewrite Middle_eq. simpl. omega.
      auto. simpl in H0. rewrite numKeys_le_insert. rewrite H0. rewrite Middle_eq.
      rewrite Fanout_eq. omega.
    }
    rewrite unfold_btnode_rep with (n:=empty_node false false Last vnewnode).
    simpl. Intros ent_empty.
    assert(HINSERT: (le_to_list (nth_first_le le (Z.to_nat (Z.of_nat fri))) ++ (Vint (Int.repr (k_ k)), inl (getval ce)) :: le_to_list (suble (fri) ((Z.to_nat (Z.of_nat Fanout))) le) ++ ent_end) = le_to_list (insert_le le e) ++ ent_end).
    { rewrite insert_fri with (fri:=fri) (key0:=ke).
      rewrite le_to_list_app.
      simpl. rewrite Nat2Z.id. rewrite H5. rewrite Nat2Z.id.
      rewrite suble_skip. unfold key_repr.
      unfold n in H0. simpl in H0. rewrite <- app_assoc. simpl. reflexivity.
      simpl in H0. rewrite H0. auto.
      unfold e. simpl. auto. unfold findRecordIndex in HFRI. unfold n in HFRI. 
      rewrite FRI_repr with (key2:=k) by auto. rewrite HFRI. auto.
    } 
    rewrite HINSERT.
    
    forward_for_simple_bound (Z.of_nat (Fanout) + 1)
(EX i:Z, EX ent_right:list(val*(val+val)),
(PROP (Zlength ent_right + i - 9 = Z.of_nat Fanout; 9 <= i <= 16)
     LOCAL (temp _newNode vnewnode; temp _tgtIdx (Vint (Int.repr (Z.of_nat fri)));
     lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe)
     SEP (btnode_rep (splitnode_left n e);
     malloc_token Ews tbtnode vnewnode;
     data_at Ews tbtnode
       (Vfalse, (Vfalse, (Val.of_bool Last, (Vint (Int.repr 0), (nullval, le_to_list(suble (S Middle) (Z.to_nat i) (insert_le le e)) ++ ent_right))))) vnewnode;
     data_at Ews tentry (Vint (Int.repr (k_ k)), inl (getval ce)) pe;
     data_at Ews (tarray tentry 16) (le_to_list (insert_le le e) ++ ent_end) v_allEntries;
     le_iter_sepcon (skipn_le (insert_le le e) Middle))))%assert.                             
    
    { rewrite Fanout_eq. simpl. rep_omega. }
    { abbreviate_semax.
      forward.                  (* i=9 *)
      Exists 9. Exists ent_empty. entailer!.
      split. rewrite Fanout_eq. simpl. rep_omega.
      rewrite Fanout_eq. simpl.
      simplify_value_fits in H11. destruct H11, H17, H18, H19, H20.
      clear - H21. assert (value_fits (tarray tentry 15) ent_empty). auto.
      simplify_value_fits in H. destruct H.
      replace (Zlength ent_empty + 9 - 9) with (Zlength ent_empty) by omega.
      auto.
      apply derives_refl. }
    {                           (* loop body *)
      Intros.
      assert(HENTRY: exists ei, nth_entry_le (Z.to_nat i) (insert_le le e) = Some ei).
      { apply nth_entry_le_in_range. simpl in H0. rewrite numKeys_le_insert. rewrite H0.
        rewrite Fanout_eq in H8. simpl in H8. rewrite Fanout_eq. destruct H8.
        apply Z2Nat.inj_lt in H11. simpl in H11. auto. omega. omega. }
      destruct HENTRY as [ei HENTRY].  
      assert (HEI: exists ki ci, ei = keychild val ki ci).
      { eapply integrity_intern_insert. simpl in H. destruct ptr0. eauto. inv H. unfold e in HENTRY.
        eauto. }
      destruct HEI as [ki [ci HEI]]. subst ei.
      assert_PROP(isptr (getval ci)).
      { apply le_iter_sepcon_split in HENTRY.
        rewrite unfold_btnode_rep with (n:=splitnode_left n e).
        unfold splitnode_left. unfold n. Intros ent_left.
        gather_SEP 3 8.
        replace_SEP 0 ( le_iter_sepcon (insert_le le e)).
        { entailer!. rewrite le_split with (i:=Middle) (le0:= (insert_le le e)) at 3.
          rewrite le_iter_sepcon_app. entailer!. simpl in H0. rewrite numKeys_le_insert.
          rewrite H0. rewrite Middle_eq. rewrite Fanout_eq. omega. }
        rewrite HENTRY. simpl entry_rep. entailer!. }
      rename H9 into CIPTR.
      assert(HZNTH: forall ent_end, Znth (d:=(Vundef,inl Vundef)) i (le_to_list (insert_le le e) ++ ent_end) = entry_val_rep (keychild val ki ci)).
      { intros. rewrite <- Z2Nat.id with (n:=i). apply Znth_to_list. auto. omega. }

      rewrite Fanout_eq in H8. simpl in H8.
      forward.                  (* t'18=allEntries[i]->key *)
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* newnode->entries[i-8]->key=t'18 *)
      forward.                  (* t'17=allEntries[i]->ptr.record *)
      { rewrite HZNTH. entailer!. }
      rewrite HZNTH. simpl.
      forward.                  (* newnode->entries[i-8]->ptr.record=t'17 *)
      entailer!.
      rename ent_right into x.
      rewrite Fanout_eq in CIPTR. simpl in CIPTR. assert(Zlength x = 24 - i) by omega.
      Exists (sublist 1 (Zlength x) x). entailer!.
      { rewrite Fanout_eq. simpl. 
        rewrite Zlength_sublist. omega. omega. omega. }
      assert(9 <= Z.to_nat i < 16)%nat.
      { clear - H10 H8. assert(HH: 9 <= i <= 16) by auto.
        destruct H10. apply Z2Nat.inj_le in H0. apply Z2Nat.inj_le in H.
        destruct H8. apply Z2Nat.inj_lt in H2.
        simpl in H, H0, H1, H2. split. omega. omega. omega. omega. omega. omega. omega. omega. }
      
      rewrite upd_Znth_twice.
      rewrite upd_Znth_same.
      rewrite upd_Znth_app2.
      rewrite le_to_list_length.
      rewrite numKeys_suble.
      rewrite Nat2Z.inj_sub.
      rewrite Z2Nat.id. rewrite Middle_eq.
      simpl. replace (i - 9 - (i - 9)) with 0 by omega.
      rewrite upd_Znth0. replace (Z.to_nat (i+1)) with (S (Z.to_nat i)).
      rewrite suble_increase with (e:=(keychild val ki ci)).
      rewrite le_to_list_app. simpl. rewrite <- app_assoc.
      cancel.
       
      rewrite numKeys_le_insert. simpl in H0. rewrite H0.
      rewrite Fanout_eq. omega. auto.      
      rewrite Z2Nat.inj_add. simpl. omega. omega. omega.
      omega.
      rewrite Middle_eq. omega.
      rewrite numKeys_le_insert. simpl in H0. rewrite H0. rewrite Middle_eq. rewrite Fanout_eq. omega.
      rewrite le_to_list_length. rewrite numKeys_suble.
      rewrite Middle_eq. rewrite Nat2Z.inj_sub. rewrite Z2Nat.id. simpl.
      omega. omega. omega.
      rewrite numKeys_le_insert. simpl in H0. rewrite H0.
      rewrite Middle_eq. rewrite Fanout_eq. omega.
      rewrite Zlength_app. rewrite le_to_list_length. rewrite numKeys_suble. rewrite H21.
      rewrite Middle_eq. rep_omega. rewrite numKeys_le_insert. simpl in H0. rewrite H0.
      rewrite Middle_eq. rewrite Fanout_eq. omega. 
      rewrite Zlength_app. rewrite le_to_list_length. rewrite numKeys_suble. rewrite H21.
      rewrite Middle_eq. rep_omega. rewrite numKeys_le_insert. simpl in H0. rewrite H0.
      rewrite Middle_eq. rewrite Fanout_eq. omega.
    }
    Intros ent_right.
    forward.                    (* newnode->numKeys=7 *)
    assert(NTHENTRY: exists emid, nth_entry_le Middle (insert_le le e) = Some emid).
    { apply nth_entry_le_in_range. unfold n in H0. simpl in H0. rewrite numKeys_le_insert.
      rewrite H0. rewrite Middle_eq.
      rewrite Fanout_eq. omega. }
    destruct NTHENTRY as [emid NTHENTRY].
    assert (HEMID: exists ki ci, emid = keychild val ki ci).
    { eapply integrity_intern_insert. simpl in H. destruct ptr0. eauto. inv H. unfold e in NTHENTRY.
      eauto. }
    destruct HEMID as [ki [ci HEMID]].
    assert_PROP(isptr (getval ci)).
    { apply le_iter_sepcon_split in NTHENTRY.
      rewrite unfold_btnode_rep with (n:=splitnode_left n e).
      simpl (splitnode_left n e). destruct (btnode val ptr0 (nth_first_le (insert_le le e) Middle) false First false nval) eqn:HDES. Intros ent_end1. inv HDES.
      gather_SEP 3 8.
      replace_SEP 0 (le_iter_sepcon (insert_le le e)).
      { entailer!. rewrite le_split with (i:=Middle) (le0:=insert_le le e) at 3.
        rewrite le_iter_sepcon_app. entailer!.
        simpl in H0. rewrite numKeys_le_insert. rewrite H0. rewrite Fanout_eq. rewrite Middle_eq.
        omega. }
      rewrite NTHENTRY. simpl entry_rep. entailer!. }
    assert(HZNTH: nth_entry_le Middle (insert_le le e) = Some emid) by auto.
    eapply Znth_to_list with (endle:=ent_end) in HZNTH.
    rewrite Middle_eq in HZNTH. simpl in HZNTH.
    forward.                    (* t'5=allEntries[8]->ptr.child *)
     { entailer!. rewrite HZNTH.
       simpl. apply isptr_is_pointer_or_null. auto. }
     rewrite HZNTH. rewrite HEMID. simpl.
     forward.                   (* nenode->ptr0=t'5 *)
     rewrite skipn_increase with (n:=Middle) (e:=emid). simpl. Intros.
     
     gather_SEP 1 2 5 6.
     replace_SEP 0 (btnode_rep (splitnode_internnode le e vnewnode Last ci)).
     { entailer!. rewrite unfold_btnode_rep with (n:=splitnode_internnode le e vnewnode Last ci).
       simpl.
       Exists ent_right.
       replace(Z.to_nat (Z.of_nat Fanout + 1)) with (S Fanout).
       rewrite numKeys_le_skipn. rewrite numKeys_le_insert. simpl in H0. rewrite H0.
       assert(HSUB: suble (S Middle) (S Fanout) (insert_le le e) = skipn_le (insert_le le e) (S Middle)).
       { apply suble_skip. rewrite numKeys_le_insert. unfold n in H0. simpl in H0. rewrite H0.
         auto.  }
       rewrite HSUB.
       rewrite Fanout_eq. rewrite Middle_eq.
      replace (Z.of_nat(16 - 9)) with 7 by (simpl; omega). cancel.
      apply derives_refl.
      rewrite Fanout_eq. simpl. auto. }
     
     forward.                    (* t'16=allEntries[8]->key *)
     { entailer!. rewrite HZNTH. simpl. auto. }
     rewrite HZNTH.
     forward.                    (* entry->key=t'16 *)
     forward.                    (* entry->ptr.child=newnode *)
     forward.                    (* return *)
     Exists vnewnode. fold e. rewrite NTHENTRY. entailer!.
     simpl. apply derives_refl.
     rewrite numKeys_le_insert. simpl in H0. rewrite H0. rewrite Fanout_eq. rewrite Middle_eq. omega.
     auto.
Qed.
