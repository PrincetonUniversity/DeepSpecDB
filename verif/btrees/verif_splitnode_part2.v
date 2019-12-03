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
Require Import verif_splitnode_part0.


(* Could be useful in refactoring splitnode_main_if_then_proof *)
Definition splitnode_main_if_part1 : statement :=
 ltac:(let x := constr:(splitnode_main_if_then) in
         let x := eval hnf in x in
         match x with context C [Ssequence (Sassign   (Efield
                          (Ederef
                            (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                            (Tstruct _BtNode noattr)) _numKeys tint)
                        (Econst_int (Int.repr _) tint)) _] =>
           let y :=context C[Sskip]
            in exact y
         end).




Require Import verif_splitnode_part1.

Opaque Znth.

Lemma splitnode_main_if_then_proof:
 forall (Espec : OracleKind)
   (ptr0 : option (node val))  (le : listentry val) (isLeaf First Last : bool)
   (nval : val) (e : entry val) (pe : val) (gv : globals) (v_allEntries : val)
  (H : node_integrity (btnode val ptr0 le isLeaf First Last nval)),
  let n := btnode val ptr0 le isLeaf First Last nval : node val in
  forall (H0 : numKeys n = Fanout)
  (LEAFENTRY : LeafEntry e = LeafNode (btnode val ptr0 le isLeaf First Last nval))
  (keyrepr : val) (coprepr : val + val)
  (HEVR : entry_val_rep e = (keyrepr, coprepr))
  (k : key) (HK : keyrepr = key_repr k)
  (INRANGE : 0 <= idx_to_Z (findRecordIndex n k) <= Z.of_nat Fanout)
  (vnewnode : val)
  (H1 : vnewnode <> nullval)
  (ent_end : list (val * (val + val)))
  (H2 : typed_true tint
       (force_val
          (both_int
             (fun n1 n2 : int => Some (Val.of_bool (Int.eq n1 n2)))
             sem_cast_pointer sem_cast_pointer 
             (Val.of_bool isLeaf) (Vint (Int.repr 1))))),

semax (func_tycontext f_splitnode Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _t'3 (Val.of_bool isLeaf); temp _newNode vnewnode;
   temp _t'2 vnewnode; temp _t'27 (Val.of_bool Last);
   temp _tgtIdx
     (Vint (Int.repr (rep_index (findRecordIndex' le k (ip 0)))));
   temp _t'1
     (Vint (Int.repr (rep_index (findRecordIndex' le k (ip 0)))));
   temp _t'28 keyrepr;
   lvar _allEntries (tarray (Tstruct _Entry noattr) 16) v_allEntries;
   temp _node nval; temp _entry pe;
   temp _isLeaf (Val.of_bool isLeaf))
   SEP (mem_mgr gv; malloc_token Ews tbtnode nval;
   data_at Ews tbtnode
     (Val.of_bool isLeaf,
     (Val.of_bool First,
     (Vint (Int.repr 0),
     (Vint
        (Int.repr
           (Z.of_nat
              (numKeys (btnode val ptr0 le isLeaf First Last nval)))),
     (match ptr0 with
      | Some n' => getval n'
      | None => nullval
      end, le_to_list le ++ ent_end))))) nval;
   match ptr0 with
   | Some n' => btnode_rep n'
   | None => emp
   end; le_iter_sepcon le;
   btnode_rep (empty_node isLeaf false Last vnewnode);
   data_at_ Tsh (tarray (Tstruct _Entry noattr) 16) v_allEntries;
   entry_rep e; data_at Ews tentry (keyrepr, coprepr) pe))
  splitnode_main_if_then
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (EX newx : val,
         PROP ( )
         LOCAL ()
         SEP (mem_mgr gv;
         btnode_rep
           (splitnode_left (btnode val ptr0 le isLeaf First Last nval)
              e);
         entry_rep
           (splitnode_right
              (btnode val ptr0 le isLeaf First Last nval) e newx);
         data_at Ews tentry
           (key_repr
              (splitnode_key
                 (btnode val ptr0 le isLeaf First Last nval) e),
           inl newx) pe))%assert) (stackframe_of f_splitnode)).
Proof.
 intros.
 abbreviate_semax.
    assert(LEAF: isLeaf=true).
    { destruct isLeaf; auto. simpl in H2. inv H2. }
   clear H2; pose (H2:=True).
    destruct (findRecordIndex n k) as [|fri] eqn:HFRI.
    { simpl in INRANGE. omega. }
    replace (findRecordIndex' le k (index.ip 0)) with (index.ip fri). simpl.
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
        change (?A::?B) with ([A]++B).
        rewrite upd_Znth_app2. simpl. rewrite Zlength_cons. simpl.
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

    match goal with |- semax _ _ ?c _ => change c with splitnode_main_if_part2 end.
    change Delta with (func_tycontext f_splitnode Vprog Gprog []).
    subst POSTCONDITION; unfold abbreviate.
    clear MORE_COMMANDS.
    clear - FRILENGTH H4 H5 FRIRANGE H3 PTRXE H1 INRANGE HFRI H H0 LEAFENTRY.
    eapply splitnode_main_if_part2_proof; eassumption.
Qed.
