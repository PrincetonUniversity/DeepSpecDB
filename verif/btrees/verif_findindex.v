(** * verif_findindex.v : Correctness proof of findChildIndex and findRecordIndex *)

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

(* Move this to floyd/forward.v? *)
Lemma ltu_false_inv64:
 forall x y, Int64.ltu x y = false -> Int64.unsigned x >= Int64.unsigned y.
Proof.
intros.
unfold Int64.ltu in H. if_tac in H; inv H; auto.
Qed.


Lemma body_findChildIndex: semax_body Vprog Gprog f_findChildIndex findChildIndex_spec.
Proof.
  start_function.
  forward.                      (* i=0 *)
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:= btnode val ptr0 le isLeaf First Last pn). fold n.
  rewrite unfold_btnode_rep. unfold n. Intros ent_end.
  forward.                      (* t'4=node->numKeys *)
  simpl in H. destruct isLeaf; try inv H.
  sep_apply (fold_btnode_rep ptr0).  fold n.
 
  forward_if True.
  - forward.                    (* skip *)
    entailer!.
  - elimtype False.
     destruct (intern_le_cons _ _ _ _ _ _ H0 I) as [le' [l2'' ?]].
     subst. simpl in H. apply node_wf_numKeys in H1. simpl in H1. 
     normalize in H. autorewrite with sublist in H. rep_omega.
  - destruct le as [|e le'] eqn:HLE.
    { apply intern_le_cons in H0. destruct H0. destruct H. inv H. simpl. auto. }
    destruct e eqn:HE.
    simpl in H0.
    destruct ptr0; try inv H0.  (* keyval isn't possible in an intern node *)
    rewrite unfold_btnode_rep. unfold n. simpl. Intros ent_end0.
    forward.                    (* t'6=node->entries[0]->key *)
    change (?A :: ?B ++ ?C) with ((A::B)++C).
    change ((key_repr k, inl (getval n0)) :: _) with
        (map entry_val_rep (keychild val k n0 :: le')).
   change (btnode_rep n0) with (entry_rep (keychild val k n0)).
    sep_apply cons_le_iter_sepcon.
    change Vfalse with (Val.of_bool false).
    sep_apply (fold_btnode_rep ptr0). fold n.
    deadvars!.
{  forward_loop (EX i:Z, PROP(0 <= i <= numKeys n;
                                              findChildIndex' le key (-1) = findChildIndex' (sublist i (Zlength le) le) key (Z.pred i)) 
                                     LOCAL(temp _i (Vint(Int.repr i)); temp _node pn; temp _key (key_repr key))
                                     SEP(btnode_rep n))
                   break:(EX i:Z, PROP(i=numKeys n; findChildIndex' le key (-1) = Z.pred i)
                                        LOCAL(temp _i (Vint(Int.repr i)); temp _node pn; temp _key (key_repr key))
                                        SEP(btnode_rep n)).

  - Exists 0. autorewrite with sublist.
    entailer!. split. omega. apply Zlength_nonneg.
  - Intros i. clear ent_end ent_end0.
    rewrite unfold_btnode_rep. unfold n. Intros ent_end.
    forward.                    (* t'5=node->numKeys *)
    sep_apply (fold_btnode_rep ptr0 (keychild val k n0 :: le')  false). fold n.
    forward_if.
    + clear ent_end. rewrite unfold_btnode_rep. unfold n. Intros ent_end.
      assert(HRANGE: 0 <= i < Zlength le).
      { apply node_wf_numKeys in H1. simpl in H1.
        unfold n in H; simpl in H. rewrite HLE. simpl.
        rewrite !Int.signed_repr in H3 by rep_omega. omega. }
      assert(NTHENTRY: exists ei, nth_entry_le i le = Some ei).
      { apply nth_entry_le_in_range. auto. }
      destruct NTHENTRY as [ei NTHENTRY].
      assert(ZNTH: nth_entry_le i le = Some ei) by auto.
      apply Znth_to_list' with (endle:=ent_end) in ZNTH. 
      assert (H99: 0 <= Zlength le <= Fanout). {
         clear - HLE H1. subst le. apply (node_wf_numKeys _ H1).
     }
      forward.                  (* t'2=node->entries+i->key *)
      { apply prop_right. rep_omega. }
      { entailer!. simpl in ZNTH. fold Inhabitant_entry_val_rep.
        rewrite ZNTH. destruct ei; simpl; auto. }
      rewrite HLE in ZNTH.  fold Inhabitant_entry_val_rep. rewrite ZNTH.
      forward_if.
      * forward.                (* return i-1 *)
        entailer!.
        { simpl cast_int_int.  normalize. f_equal. f_equal.
          change (i-1 = findChildIndex' (keychild val k n0 :: le') key (-1)).
          rewrite H2.
          set (le:=keychild val k n0 :: le') in NTHENTRY|-*.
          clear -NTHENTRY H4 HRANGE.
          assert(k_ key <? k_ (entry_key ei) = true).
          { assert(-1 < k_ key < Ptrofs.modulus) by (unfold k_; rep_omega).
            destruct ei; simpl in H4; simpl;
            apply typed_true_of_bool in H4;
            apply Int64.ltu_inv in H4; apply Zaux.Zlt_bool_true;
            rewrite ?int_unsigned_ptrofs_toint in H4 by reflexivity;
            rewrite ?int64_unsigned_ptrofs_toint in H4 by reflexivity;
            apply H4. } clear H4.
          apply nth_entry_skipn in NTHENTRY.
          destruct (sublist i (Zlength le) le); inv NTHENTRY. 
           autorewrite with sublist in H1. inv H1.
          destruct ei; simpl in H; simpl; rewrite H; normalize; f_equal. }
          rewrite unfold_btnode_rep with (n:= btnode val ptr0 (keychild val k n0 :: le') false First Last pn).
        Exists ent_end. cancel.
      * forward.                (* i++ *)
        Exists (Z.succ i). entailer!. split.
        { clear - HRANGE H1. subst n. simpl in *. omega. }
        { rewrite H2.
          pose (le:= keychild val k n0 :: le').
          fold le. fold le in NTHENTRY. clear -NTHENTRY H4 HRANGE.
          assert(k_ key <? k_ (entry_key ei) = false).
          { assert(-1 < k_ key < Int64.modulus) by (unfold k_; rep_omega).
            apply Zaux.Zlt_bool_false; unfold k_.
            destruct ei; simpl in H4; simpl;
              apply typed_false_of_bool in H4;  apply ltu_false_inv64 in H4;
              rewrite ?int_unsigned_ptrofs_toint in H4 by reflexivity;
              rewrite ?int64_unsigned_ptrofs_toint in H4 by reflexivity;
              omega. }
          autorewrite with sublist in HRANGE.
          apply nth_entry_skipn in NTHENTRY.
          replace (sublist (Z.succ i) (Zlength le) le)
                        with (sublist 1 (Zlength le - i ) (sublist i (Zlength le) le))
          by (subst le; autorewrite with sublist; f_equal; omega).
          destruct (sublist i (Zlength le) le) eqn:H9; autorewrite with sublist in NTHENTRY; inv NTHENTRY.
          assert (H19: Zlength l = Zlength le - Z.succ i). {
                subst le.
                apply (f_equal (@Zlength _)) in H9.
                autorewrite with sublist in H9. list_solve.
          } clear H9.
          assert(findChildIndex' (ei :: l) key (Z.pred i) = findChildIndex' l key (Z.succ (Z.pred i))).
          { simpl; destruct ei; simpl in H; rewrite H; simpl; auto. } rewrite H0.
          simpl. f_equal. change (ei::l) with ([ei]++l). autorewrite with sublist; auto.
           omega. }
        do 2 f_equal. replace 1 with (Z.of_nat 1) by reflexivity.
        rewrite unfold_btnode_rep with (n:=n). unfold n. Exists ent_end.
        cancel.
    + forward.                  (* break *)
      unfold n in H. unfold node_wf in H1. simpl in H, H1.
      rewrite Int.signed_repr in H3 by rep_omega.
      rewrite Int.signed_repr in H3 by rep_omega.
      autorewrite with sublist in H3,H.
      assert( i = Z.succ (Zlength le')) by omega.
      Exists i. entailer!.
      split. simpl. autorewrite with sublist. auto.
      rewrite H2.     
      rewrite Z.pred_succ.
      replace (Z.succ (Zlength le')) with (Zlength (keychild val k n0 :: le')).
      autorewrite with sublist. simpl. auto.
      list_solve.
  - Intros i. clear ent_end ent_end0.
    rewrite unfold_btnode_rep. unfold n. Intros ent_end.
    forward.                     (* t'1=node->numKeys *)
    forward.                     (* return t'1-1 *)
    + entailer!. unfold node_wf in H1. simpl in H1.
      pose proof (Zlength_nonneg le').
      rewrite Int.signed_repr by rep_omega.
      rewrite Int.signed_repr by rep_omega.
      rep_omega.
    + entailer!.
      * simpl cast_int_int; normalize.
        do 2 f_equal.
        unfold findChildIndex. rewrite H2. simpl numKeys. omega.
      * rewrite unfold_btnode_rep with (n:=btnode val ptr0 (keychild val k n0 :: le') false First Last pn).
        Exists ent_end. cancel.  }
Qed.

Lemma body_findRecordIndex: semax_body Vprog Gprog f_findRecordIndex findRecordIndex_spec.
Proof.
  start_function.
  forward.                      (* i=0 *)
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:= btnode val ptr0 le isLeaf First Last pn). fold n.
  rewrite unfold_btnode_rep. unfold n. Intros ent_end.
  forward.                      (* t'5=node->numKeys *)
  simpl.
  sep_apply (fold_btnode_rep ptr0). fold n.
  clear ent_end.
  forward_if True.
  { forward. entailer!. }
  { exfalso. apply node_wf_numKeys in H0. simpl in H0.
    rewrite Int.signed_repr in H1; rep_omega. }
  rewrite unfold_btnode_rep. unfold n. Intros ent_end.
  forward.                      (* t'4=node->numKeys *)
  forward_if.
  { forward.                    (* return 0 *)
    entailer!. simpl cast_int_int. f_equal. rewrite <- H1.
    apply node_wf_numKeys in H0. simpl in H0.
    apply (f_equal Int.unsigned) in H1.  normalize in H1.
    f_equal. destruct le. simpl; auto. simpl in H1.
    autorewrite with sublist in H1; rep_omega.
    rewrite unfold_btnode_rep with (n:=btnode val ptr0 le isLeaf First Last pn).
    Exists ent_end. entailer!. }
  forward.                    (* i=0 *)
  simpl.
  sep_apply (fold_btnode_rep ptr0). fold n.
  clear ent_end. deadvars!.
{ forward_loop (EX i:Z, PROP(0<=i<=numKeys n; findRecordIndex' le key 0 = findRecordIndex' (sublist i (Zlength le) le) key i)
                                    LOCAL (temp _i (Vint (Int.repr i)); temp _node pn; temp _key (key_repr key))
                                    SEP (btnode_rep n))
               break:(EX i:Z, PROP(i=numKeys n; findRecordIndex' le key 0 = i) 
                                    LOCAL (temp _i (Vint (Int.repr i)); temp _node pn; temp _key (key_repr key))
                                    SEP (btnode_rep n)).
  - Exists 0. entailer!.
    split. split. omega. apply Zlength_nonneg. autorewrite with sublist. auto.
  - Intros i. rewrite unfold_btnode_rep. unfold n. Intros ent_end.
    forward.                    (* t'3=node->numKeys *)
    forward_if.
    + entailer!.
      apply node_wf_numKeys in H0. simpl in H0.
      rewrite Int.signed_repr by rep_omega.
      rewrite Int.signed_repr by rep_omega.
      rep_omega.
    + apply node_wf_numKeys in H0; simpl in H0. unfold n in H2; simpl in H2.
        assert(HRANGE: 0 <= i < Zlength le).
      { rewrite !Int.signed_repr in H4 by rep_omega. omega. }
      assert(NTHENTRY: exists ei, nth_entry_le i le = Some ei).
      { apply nth_entry_le_in_range. auto. }
      destruct NTHENTRY as [ei NTHENTRY].
      assert(ZNTH: nth_entry_le i le = Some ei) by auto.
      apply Znth_to_list' with (endle:=ent_end) in ZNTH.
      forward.                  (* t'2=node->entries[i]->key *)
      { entailer!. }
      { entailer!. 
        fold Inhabitant_entry_val_rep. rewrite ZNTH. destruct ei; simpl; auto. }
      fold Inhabitant_entry_val_rep. rewrite ZNTH.
      forward_if.
      * forward.                (* return i *)
        entailer!. unfold findRecordIndex. rewrite H3.
        f_equal. f_equal.
        destruct (sublist i (Zlength le) le) eqn:HSKIP.
        { simpl. auto. }
        apply nth_entry_skipn in NTHENTRY.
        simpl in  NTHENTRY. rewrite HSKIP in NTHENTRY.
        autorewrite with sublist in NTHENTRY.
        inv NTHENTRY.
        assert(k_ key <=? k_ (entry_key ei) = true).
        { assert(-1 < k_ key < Int64.modulus) by (unfold k_; rep_omega).
          destruct ei; simpl in H5; simpl;
            apply typed_true_of_bool in H5;
            apply binop_lemmas3.negb_true in H5;
            apply ltu_false_inv64 in H5;
              rewrite ?int_unsigned_ptrofs_toint in H5 by reflexivity;
              rewrite ?int64_unsigned_ptrofs_toint in H5 by reflexivity;
            try apply Zaux.Zle_bool_true; unfold k_; omega. }
        simpl. rewrite H10. auto.
        rewrite unfold_btnode_rep with (n:=btnode val ptr0 le isLeaf First Last pn).
        Exists ent_end. entailer!.
      * forward.                (* i=i+1 *)
        Exists (Z.succ i). entailer!.
        split.
        { unfold n; simpl; omega. }
        { rewrite H3. clear -NTHENTRY H5 HRANGE.
          assert(k_ key <=? k_ (entry_key ei) = false).
          { assert(-1 < k_ key < Int64.modulus) by (unfold k_; rep_omega).
            destruct ei; simpl in H5; simpl;
              apply typed_false_of_bool in H5;
              apply negb_false_iff in H5;
              apply Int64.ltu_inv in H5;
              rewrite ?int_unsigned_ptrofs_toint in H5 by reflexivity;
              rewrite ?int64_unsigned_ptrofs_toint in H5 by reflexivity;
              try apply Zaux.Zle_bool_false; unfold k_; omega. }
          apply nth_entry_skipn in NTHENTRY.
          replace (sublist (Z.succ i) (Zlength le) le)
                        with (sublist 1 (Zlength le - i ) (sublist i (Zlength le) le)) 
               by (rewrite sublist_sublist; try list_solve; f_equal; omega).
          destruct (sublist i (Zlength le) le) eqn:?H; autorewrite with sublist in NTHENTRY; inv NTHENTRY.
          simpl. rewrite H. f_equal.
          apply (f_equal (@Zlength _)) in H0. autorewrite with sublist in H0.
          rewrite H0.
          change (ei::l) with ([ei]++l). autorewrite with sublist. auto.  }
        rewrite unfold_btnode_rep with (n:=n). unfold n.
        Exists ent_end. entailer!.
    + forward.                  (* break *)
      Exists (Zlength le).
      entailer!.
      assert(i=Zlength le).
      { unfold n in H2. simpl in H2.
      apply node_wf_numKeys in H0. simpl in H0.
        rewrite !Int.signed_repr in H4 by rep_omega.
        rep_omega. }
      subst. split.
      * rewrite H3. autorewrite with sublist.
        simpl. auto.
      * auto.
      * rewrite unfold_btnode_rep with (n:=n).
        unfold n. Exists ent_end. entailer!.
  - Intros i. subst.
    rewrite unfold_btnode_rep. unfold n. Intros ent_end.
    forward.                    (* t'1=node->numkeys *)
    forward.                    (* return t'1 *)
    entailer!.
    + f_equal. f_equal. unfold findRecordIndex. rewrite H3. simpl. auto.
    + rewrite unfold_btnode_rep with (n:=btnode val ptr0 le isLeaf First Last pn).
      Exists ent_end. entailer!. }
Qed.
