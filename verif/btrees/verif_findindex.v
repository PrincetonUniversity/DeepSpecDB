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
  set (n:= btnode val ptr0 le isLeaf First Last pn) in *.
  red in H1; simpl in H1.
  simpl in H. destruct isLeaf; inv H.
  rewrite unfold_btnode_rep. unfold n. Intros ent_end.
  forward.                      (* t'4=node->numKeys *)
  sep_apply (fold_btnode_rep ptr0).  fold n.
 
  forward_if True.
  - forward.                    (* skip *)
    entailer!.
  - elimtype False.
     destruct (intern_le_cons _ _ _ _ _ _ H0 I) as [le' [l2'' ?]].
     subst. autorewrite with sublist in H. rep_lia.
  - destruct le as [|[|] le'] (*eqn:HLE*).
    { destruct (intern_le_cons _ _ _ _ _ _ H0 I) as [? [? H]]. inv H. }
    destruct ptr0; try inv H0.  (* keyval isn't possible in an intern node *)
    rewrite unfold_btnode_rep. unfold n. simpl. Intros ent_end0.
    forward.                    (* t'6=node->entries[0]->key *)
    change (?A :: ?B ++ ?C) with ((A::B)++C).
    change ((Vptrofs k, inl (getval n0)) :: _) with
        (map entry_val_rep (keychild val k n0 :: le')).
   change (btnode_rep n0) with (entry_rep (keychild val k n0)).
    sep_apply cons_le_iter_sepcon.
    change Vfalse with (Val.of_bool false).
    sep_apply (fold_btnode_rep ptr0). fold n.
    deadvars!.
{  forward_loop (EX i:Z, PROP(0 <= i <= Zlength (node_le n);
                                              findChildIndex n key = findChildIndex' (sublist i (Zlength (node_le n)) (node_le n)) key (Z.pred i)) 
                                     LOCAL(temp _i (Vint(Int.repr i)); temp _node pn; temp _key (Vptrofs key))
                                     SEP(btnode_rep n))
                   break:(PROP(findChildIndex n key = Z.pred (Zlength (node_le n)))
                                        LOCAL(temp _node pn; temp _key (Vptrofs key))
                                        SEP(btnode_rep n)).

  - Exists 0. autorewrite with sublist.
    entailer!.
  - Intros i. clear ent_end ent_end0.
    rewrite unfold_btnode_rep. unfold n. Intros ent_end.
    forward.                    (* t'5=node->numKeys *)
    sep_apply (fold_btnode_rep ptr0 (keychild val k n0 :: le')  false). fold n.
    forward_if.
    + clear ent_end. rewrite unfold_btnode_rep. unfold n. Intros ent_end.
      assert(HRANGE: 0 <= i < Zlength (node_le n)).
      { clear - H H3 H1. simpl in *. 
        rewrite !Int.signed_repr in H3 by rep_lia. lia. }
      assert(NTHENTRY: exists ei, Znth_option i (node_le n) = Some ei).
      { apply Znth_option_in_range. auto. }
      destruct NTHENTRY as [ei NTHENTRY].
      assert(ZNTH: Znth_option i (node_le n) = Some ei) by auto.
      apply Znth_to_list' with (endle:=ent_end) in ZNTH. 
      assert (H99: 0 <= Zlength (node_le n) <= Fanout). {
         clear - H1. simpl.  rep_lia. 
     }
      forward.                  (* t'2=node->entries+i->key *)
      { apply prop_right. rep_lia. }
      { entailer!. simpl in ZNTH.
        change (Vlong (Ptrofs.to_int64 k)) with (Vptrofs k).
        fold Inhabitant_entry_val_rep.
        rewrite ZNTH. destruct ei; simpl; auto. }
      fold Inhabitant_entry_val_rep. simpl node_le in ZNTH. rewrite ZNTH.
      forward_if.
      * forward.                (* return i-1 *)
        entailer!.
        { simpl cast_int_int.  normalize. f_equal. f_equal.
          rewrite H2.
          clear -NTHENTRY H4 HRANGE.
          assert(Ptrofs.ltu key (entry_key ei) = true).
          { destruct ei; simpl in H4; simpl;
            apply typed_true_of_bool in H4;
            unfold Ptrofs.ltu;
            unfold Ptrofs.to_int64, Int64.ltu in H4;
            rewrite !Int64.unsigned_repr in H4 by rep_lia; auto. } clear H4.
          apply nth_entry_skipn in NTHENTRY.
          destruct (sublist i (Zlength (node_le n)) (node_le n)); inv NTHENTRY.
          destruct ei; simpl in H; simpl; rewrite H; normalize; f_equal. }
          simpl node_le. unfold n.
          rewrite unfold_btnode_rep with (n:= btnode val ptr0 (keychild val k n0 :: le') false First Last pn).
        Exists ent_end. cancel.
      * forward.                (* i++ *)
        Exists (Z.succ i). entailer!.
        { rewrite H2.
          set (le:= keychild val k n0 :: le') in *.
          clear -NTHENTRY H4 HRANGE.
          assert(Ptrofs.ltu key (entry_key ei) = false).
          { destruct ei; simpl in H4; simpl;
            apply typed_false_of_bool in H4;
            unfold Ptrofs.ltu;
            unfold Ptrofs.to_int64, Int64.ltu in H4;
            rewrite !Int64.unsigned_repr in H4 by rep_lia; auto. } 
          autorewrite with sublist in HRANGE.
          apply nth_entry_skipn in NTHENTRY.
          change (node_le n) with le in *.
          rewrite Z.pred_succ.
          replace (sublist (Z.succ i) (Zlength le) le)
                        with (sublist 1 (Zlength le - i ) (sublist i (Zlength le) le))
           by (subst le; autorewrite with sublist in *; autorewrite with sublist;
                  f_equal; lia).
          destruct (sublist i (Zlength le) le) eqn:H9; autorewrite with sublist in NTHENTRY; inv NTHENTRY.
          assert (H19: Zlength l = Zlength le - Z.succ i). {
                subst le.
                apply (f_equal (@Zlength _)) in H9.
                autorewrite with sublist in HRANGE,H9. list_solve.
          } clear H9.
          assert(findChildIndex' (ei :: l) key (Z.pred i) = findChildIndex' l key (Z.succ (Z.pred i))).
          { simpl; destruct ei; simpl in H; rewrite H; simpl; auto. } rewrite H0.
          simpl. f_equal. change (ei::l) with ([ei]++l). autorewrite with sublist; auto.
           lia. }
        do 2 f_equal. replace 1 with (Z.of_nat 1) by reflexivity.
        rewrite unfold_btnode_rep with (n:=n). unfold n. Exists ent_end.
        cancel.
    + forward.                  (* break *)
       entailer!.
      simpl in H,H1.
      rewrite!Int.signed_repr in H3 by rep_lia.
      autorewrite with sublist in H3,H.
      assert( i = Z.succ (Zlength le')) by lia.
      clear H3 H. subst i.
      rewrite H2. simpl. autorewrite with sublist. reflexivity.
  -  clear ent_end ent_end0.
    rewrite unfold_btnode_rep. unfold n. Intros ent_end.
    forward.                     (* t'1=node->numKeys *)
    forward.                     (* return t'1-1 *)
    entailer!.
      * simpl cast_int_int; normalize.
        do 2 f_equal. fold n in H. rewrite H. simpl. lia.
      * rewrite unfold_btnode_rep with (n:=n).
        Exists ent_end. cancel.  }
Qed.

Lemma body_findRecordIndex: semax_body Vprog Gprog f_findRecordIndex findRecordIndex_spec.
Proof.
  start_function.
  forward.                      (* i=0 *)
  destruct n as [ptr0 le isLeaf First Last pn].
  set (n:= btnode val ptr0 le isLeaf First Last pn).
  rewrite unfold_btnode_rep. unfold n. Intros ent_end.
  red in H0; simpl in H0.
  forward.                      (* t'5=node->numKeys *)
  simpl.
  sep_apply (fold_btnode_rep ptr0). fold n.
  clear ent_end.
  forward_if True.
  { forward. entailer!. }
  { rep_lia. }
  rewrite unfold_btnode_rep. unfold n. Intros ent_end.
  forward.                      (* t'4=node->numKeys *)
  forward_if.
  { forward.                    (* return 0 *)
    entailer!. simpl cast_int_int. f_equal. rewrite <- H1.
(*    apply (f_equal Int.unsigned) in H1.  normalize in H1. *)
    f_equal. rewrite H1. destruct le. simpl; auto.
    autorewrite with sublist in H1; rep_lia.
    rewrite unfold_btnode_rep with (n:=btnode val ptr0 le isLeaf First Last pn).
    Exists ent_end. cancel. }
  forward.                    (* i=0 *)
  simpl.
  sep_apply (fold_btnode_rep ptr0). fold n.
  clear ent_end. deadvars!.
{ forward_loop (EX i:Z, PROP(0<=i<=Zlength (node_le n); 
                                             findRecordIndex n key = findRecordIndex' (sublist i (Zlength (node_le n)) (node_le n)) key i)
                                    LOCAL (temp _i (Vint (Int.repr i)); temp _node pn; temp _key (Vptrofs key))
                                    SEP (btnode_rep n))
               break:(PROP(findRecordIndex n key = Zlength (node_le n)) 
                          LOCAL (temp _node pn; temp _key (Vptrofs key))
                          SEP (btnode_rep n)).
  - Exists 0. entailer!. autorewrite with sublist. auto.
  - Intros i. rewrite unfold_btnode_rep. unfold n. Intros ent_end.
    forward.                    (* t'3=node->numKeys *)
    forward_if.
    + simpl in H2.
        assert(HRANGE: 0 <= i < Zlength le).
      { rewrite !Int.signed_repr in H4 by rep_lia. lia. }
      assert(NTHENTRY: exists ei, Znth_option i le = Some ei).
      { apply Znth_option_in_range. auto. }
      destruct NTHENTRY as [ei NTHENTRY].
      assert(ZNTH: Znth_option i le = Some ei) by auto.
      apply Znth_to_list' with (endle:=ent_end) in ZNTH.
      forward.                  (* t'2=node->entries[i]->key *)
      { entailer!. }
      { entailer!. 
        fold Inhabitant_entry_val_rep. rewrite ZNTH. destruct ei; simpl; auto. }
      fold Inhabitant_entry_val_rep. rewrite ZNTH.
      forward_if.
      * forward.                (* return i *)
        entailer!. fold n. simpl cast_int_int. rewrite H3.
        f_equal. f_equal. simpl node_le.
        destruct (sublist i (Zlength le) le) eqn:HSKIP.
        { simpl. auto. }
        apply nth_entry_skipn in NTHENTRY.
        simpl in  NTHENTRY. rewrite HSKIP in NTHENTRY.
        autorewrite with sublist in NTHENTRY.
        inv NTHENTRY.
        assert(Ptrofs.cmpu Cle key (entry_key ei) = true).
        { 
          destruct ei; simpl in H5; simpl;
            apply typed_true_of_bool in H5;
            apply binop_lemmas3.negb_true in H5;
            rewrite negb_true_iff;
            unfold Ptrofs.to_int64, Int64.ltu in H5; unfold Ptrofs.ltu;
            rewrite !Int64.unsigned_repr in H5 by rep_lia; auto. }
        simpl. simpl in H10. rewrite H10. auto.
        rewrite unfold_btnode_rep with (n:=btnode val ptr0 le isLeaf First Last pn).
        Exists ent_end. cancel.
      * forward.                (* i=i+1 *)
        Exists (Z.succ i). entailer!.
        split.
        { unfold n; simpl; lia. }
        { rewrite H3. clear -NTHENTRY H5 HRANGE.
          assert(Ptrofs.cmpu Cle key (entry_key ei) = false).
        { 
          destruct ei; simpl in H5; simpl;
            apply typed_false_of_bool in H5;
            rewrite negb_false_iff in H5 |- *;
            unfold Ptrofs.to_int64, Int64.ltu in H5; unfold Ptrofs.ltu;
            rewrite !Int64.unsigned_repr in H5 by rep_lia; auto. }
          apply nth_entry_skipn in NTHENTRY.
          simpl node_le.
          replace (sublist (Z.succ i) (Zlength le) le)
                        with (sublist 1 (Zlength le - i ) (sublist i (Zlength le) le)) 
               by (rewrite sublist_sublist; try list_solve; f_equal; lia).
          destruct (sublist i (Zlength le) le) eqn:?H; autorewrite with sublist in NTHENTRY; inv NTHENTRY.
          simpl. simpl in H; rewrite H. f_equal.
          apply (f_equal (@Zlength _)) in H0. autorewrite with sublist in H0.
          rewrite H0.
          change (ei::l) with ([ei]++l). autorewrite with sublist. auto.  }
        rewrite unfold_btnode_rep with (n:=n). unfold n.
        Exists ent_end. cancel.
    + forward.                  (* break *)
      entailer!.
      assert(i=Zlength le).
      { simpl in H2.
        rewrite !Int.signed_repr in H4 by rep_lia.
        rep_lia. }
      * rewrite H3. simpl. autorewrite with sublist.
        simpl. auto.
      * rewrite unfold_btnode_rep with (n:=n).
        unfold n. Exists ent_end. cancel.
  - rewrite unfold_btnode_rep. unfold n. Intros ent_end.
    forward.                    (* t'1=node->numkeys *)
    forward.                    (* return t'1 *)
    entailer!.
    + f_equal. f_equal. rewrite H2. simpl. auto.
    + rewrite unfold_btnode_rep with (n:=btnode val ptr0 le isLeaf First Last pn).
      Exists ent_end. cancel. }
Qed.
