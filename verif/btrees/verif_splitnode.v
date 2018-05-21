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

Lemma numKeys_nth_first: forall (X:Type) (le:listentry X) i,
    (i <= numKeys_le le)%nat ->
    numKeys_le (nth_first_le le i) = i.
Proof.
  intros. generalize dependent i.
  induction le; intros.
  - destruct i; simpl. auto. simpl in H. omega.
  - destruct i.
    + simpl. auto.
    + simpl. apply f_equal. apply IHle. simpl in H. omega.
Qed.

Lemma length_to_list: forall le,
    Zlength (le_to_list le) = Z.of_nat (numKeys_le le).
Proof.
  intros. induction le.
  - simpl. apply Zlength_nil.
  - simpl. rewrite Zlength_cons. rewrite Zpos_P_of_succ_nat. apply f_equal. auto.
Qed.

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

Lemma body_splitnode: semax_body Vprog Gprog f_splitnode splitnode_spec.
Proof.
  start_function.
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
  forward_call(isLeaf, false, Last). (* t'2=createNewNode(isLeaf,0,t'27 *)
  Intros vnewnode.
  forward.                      (* newnode=t'2 *)
  gather_SEP 1 2 3 4.
  replace_SEP 0 (btnode_rep n).
  { entailer!. rewrite unfold_btnode_rep with (n:=n). unfold n. Exists ent_end. cancel.
    change_compspecs CompSpecs. cancel. } clear ent_end.
  forward_if(PROP (vnewnode<>nullval)
     LOCAL (temp _newNode vnewnode; temp _t'2 vnewnode; temp _t'27 (Val.of_bool Last);
     temp _tgtIdx (Vint (Int.repr (rep_index (findRecordIndex' le k (index.ip 0)))));
     temp _t'1 (Vint (Int.repr (rep_index (findRecordIndex' le k (index.ip 0))))); 
     temp _t'28 keyrepr; lvar _allEntries (tarray (Tstruct _Entry noattr) 16) v_allEntries;
     temp _node nval; temp _entry pe; temp _isLeaf (Val.of_bool isLeaf))
     SEP (btnode_rep n; btnode_rep (empty_node isLeaf false Last vnewnode);
     data_at_ Tsh (tarray (Tstruct _Entry noattr) 16) v_allEntries; entry_rep e;
     data_at Tsh tentry (keyrepr, coprepr) pe)).
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
    gather_SEP 0 1 2 3.
    pose (nright := btnode val ptr0 le true First false nval).
    replace_SEP 0 (btnode_rep nright).
    { entailer!. rewrite unfold_btnode_rep with (n:=nright). unfold nright.
      Exists ent_end. cancel. } clear ent_end. fold tentry.
    assert(ENTRY: exists ke ve xe, e = keyval val ke ve xe). (* the entry to be inserted at a leaf must be keyval *)
    { admit. }
    destruct ENTRY as [ke [ve [xe ENTRY]]].
    
    forward_for_simple_bound (Z.of_nat fri)
    (EX i:Z, EX allent_end:list (val*(val+val)),
     (PROP (length allent_end = (Fanout + 1 - Z.to_nat(i))%nat)
      LOCAL (temp _t'3 (Val.of_bool isLeaf); temp _newNode vnewnode; temp _t'2 vnewnode;
      temp _t'27 (Val.of_bool Last); temp _tgtIdx (Vint (Int.repr (Z.of_nat fri)));
      temp _t'1 (Vint (Int.repr (Z.of_nat fri))); temp _t'28 keyrepr;
      lvar _allEntries (tarray tentry 16) v_allEntries; temp _node nval; temp _entry pe;
      temp _isLeaf (Val.of_bool isLeaf))
      SEP (btnode_rep nright; btnode_rep (empty_node isLeaf false Last vnewnode);
           data_at Tsh (tarray tentry 16) (le_to_list (nth_first_le le (Z.to_nat i))++ allent_end) v_allEntries; entry_rep e; data_at Tsh tentry (keyrepr, coprepr) pe)))%assert.
    { simpl in INRANGE. rewrite Fanout_eq in INRANGE.
      replace (Z.of_nat 15) with 15 in INRANGE. rep_omega. simpl. auto. }
    { entailer!.
      Exists (default_val (nested_field_type (tarray (Tstruct _Entry noattr) 16) [])).
      entailer!. unfold data_at_, field_at_. entailer!. }
    {                           (* loop body *)
      rewrite unfold_btnode_rep with (n:=nright). unfold nright.
      Intros ent_end.
      assert(HENTRY: exists e, nth_entry_le (Z.to_nat i) le = Some e).
      { apply nth_entry_le_in_range. simpl in INRANGE. rewrite Fanout_eq in INRANGE.
        unfold n in H0. simpl in H0. rewrite H0. rep_omega. }
      destruct HENTRY as [ei HENTRY].
      assert (HEI: exists ki vi xi, ei = keyval val ki vi xi).
      { eapply integrity_nth_leaf. eauto. rewrite LEAF. simpl. auto. eauto. }
      destruct HEI as [ki [vi [xi HEI]]]. subst ei.        
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
      { rewrite HZNTH. entailer!. admit. }
      rewrite HZNTH. simpl.
      forward.                  (* allEntries[i]->ptr.record=t'25 *)
      entailer!.
      Exists (sublist 1 (Zlength x) x). entailer!.
      { clear -H4. admit. }
      rewrite unfold_btnode_rep with (n:=nright). unfold nright. Exists ent_end. cancel.
      
      rewrite upd_Znth_twice.
      rewrite app_Znth2. rewrite length_to_list. rewrite numKeys_nth_first. rewrite Z2Nat.id.
      replace (i-i) with 0 by omega.
      rewrite upd_Znth_app2.
      rewrite length_to_list. rewrite numKeys_nth_first. rewrite Z2Nat.id.
      replace (i-i) with 0 by omega.
      rewrite upd_Znth_same.
      unfold upd_Znth. rewrite sublist_nil. simpl.
      rewrite nth_first_sublist. rewrite nth_first_sublist.
      rewrite sublist_split with (lo:=0) (mid:=i) (hi:=i+1).
      erewrite sublist_len_1. rewrite <- app_nil_r with (l:=le_to_list le). rewrite HZNTH. simpl.
      rewrite app_nil_r. rewrite <- app_assoc. simpl. cancel.
      rewrite length_to_list. unfold n in H0. simpl in H0. rewrite H0. rewrite Fanout_eq.
      replace (Z.of_nat 15) with 15. omega. simpl. auto. omega.
      rewrite length_to_list. unfold n in H0. simpl in H0. rewrite H0. rewrite Fanout_eq.
      replace (Z.of_nat 15) with 15. omega. simpl. auto.
      rewrite Zlength_app. rewrite length_to_list. rewrite numKeys_nth_first.
      rewrite Z2Nat.id. admit.
      omega. admit.
      omega. admit.
      rewrite length_to_list. rewrite numKeys_nth_first.
      rewrite Z2Nat.id. admit.
      omega. admit.
      omega. admit.
      rewrite length_to_list. rewrite numKeys_nth_first. rewrite Z2Nat.id. omega. omega.
      admit.
      admit. }
    Intros allent_end.
    forward.                    (* t'24=entry->key *) rewrite HK. unfold key_repr.

    assert(FRIRANGE: (0 <= fri < 16)%nat).
    { simpl in INRANGE. rewrite Fanout_eq in INRANGE. split. omega.
      replace (Z.of_nat 15) with 15 in INRANGE. admit. simpl. auto. }
    rewrite ENTRY in HEVR. simpl in HEVR. inv HEVR.

    Opaque Znth.
    forward.                    (* allEntries[tgtIdx]->key = t'24 *)
    forward.                    (* t'23=entry->ptr.record *)
    { entailer!. admit. }    
    forward.                    (* allEntries[tgtIdx]->ptr.record = t'23 *)
    assert(0 <= Z.of_nat fri < Zlength (le_to_list (nth_first_le le (Z.to_nat (Z.of_nat fri))) ++ allent_end)).
    { split. omega. rewrite Zlength_app. rewrite length_to_list.
      rewrite numKeys_nth_first. rewrite Z2Nat.id. rewrite Zlength_correct.
      rewrite H3. admit.
      omega. rewrite Nat2Z.id. unfold n in H0. simpl in H0. rewrite H0. rewrite Fanout_eq. omega. }

      rewrite upd_Znth_twice by auto. rewrite upd_Znth_same by auto.

    admit.                      (* second loop *)

  -                             (* intern node *)
    admit.
Admitted.