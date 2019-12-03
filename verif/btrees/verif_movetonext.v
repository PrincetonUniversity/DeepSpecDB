(** * verif_movetonext.v : Correctness proof of firstpointer, moveToNext and RL_MoveToNext *)

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
Require Import index.
Require Import btrees_sep.
Require Import btrees_spec.
Require Import verif_movetofirst.

Lemma body_lastpointer: semax_body Vprog Gprog f_lastpointer lastpointer_spec.
Proof.
  start_function.
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:=btnode val ptr0 le isLeaf First Last pn).
  rewrite unfold_btnode_rep. Intros ent_end.
  forward.                      (* t'1=node->isLeaf *)
  { entailer!. destruct isLeaf; simpl; auto. }
  forward_if.
  - forward.                    (* t'3=node->numKeys *)
    forward.                    (* return *)
    destruct isLeaf.
    + unfold rep_index. entailer!. fold n. rewrite unfold_btnode_rep with (n:=n). unfold n.
      Exists ent_end. entailer!.
    + simpl in H0. inv H0.
  - forward.                    (* t'2=node->numKeys *)
    forward.                    (* return *)
    { entailer!. unfold node_wf in H.
      simpl in H. clear -H. rewrite Int.signed_repr. rewrite Int.signed_repr.
      rep_omega. rep_omega. rep_omega. }
    destruct isLeaf.
    + simpl in H0. inv H0.
    + destruct (numKeys_le le) eqn:HNUM.
      * unfold rep_index. simpl. entailer!.
        rewrite HNUM. reflexivity.
        Exists ent_end. fold le_iter_sepcon. fold btnode_rep. entailer.
      * replace (Z.of_nat (S n0) -1) with (Z.of_nat n0).
        unfold rep_index. entailer!. fold n.
        simpl. rewrite HNUM. do 2 f_equal. replace 1 with (Z.of_nat 1) by reflexivity.
        rewrite <- Nat2Z.inj_sub. f_equal. omega. omega.
        Exists ent_end. entailer!. fold le_iter_sepcon. fold btnode_rep. apply derives_refl.
        
        { rewrite Nat2Z.inj_succ. rewrite Zsuccminusone. auto. }
Qed.

Instance Inhabitant_index: Inhabitant index := ip 0.
Instance Inhabitant_node {X: Type} (x: Inhabitant X): Inhabitant (node X) :=
  btnode X None (nil X) true true true x.

Lemma partial_cursor_correct_cons {X} (c: cursor X) (r: relation X) (n: node X) (i: index): 
  partial_cursor_correct_rel ((n, i)::c) r -> partial_cursor_correct_rel c r.
Proof.
  intro h. 
  unfold partial_cursor_correct_rel in h|-*. destruct c. easy.
  destruct p as [n0 i0]; case_eq (nth_node i0 n0); case_eq (nth_node i n).
  + intros n1 h1 n2 h2. rewrite h1 in h. simpl in h|-*. easy.
  + intros hnone n1 h1. rewrite hnone in h. contradiction.
  + intros n1 h1 hnone. rewrite h1 in h. simpl in h.
    destruct h as [[_ h] _]. rewrite h in hnone. discriminate.
  + intros hnone1 hnone2.
    rewrite hnone1 in h. contradiction.
Qed.

Lemma complete_sublist_partial: forall (X:Type) {_: Inhabitant X} (c:cursor X) r i,
    i >= 1 ->
    complete_cursor_correct_rel c r ->
    partial_cursor_correct_rel (sublist i (Zlength c) c) r.
Proof.
  intros X inhx c r i hi hcomplete.
  destruct c as [|[n [|ii]]]; try easy.
  unfold complete_cursor_correct_rel in hcomplete. simpl in hcomplete.
  case_eq (nth_entry ii n); [| intro hnone; rewrite hnone in hcomplete; contradiction].
  intros e he. rewrite he in hcomplete. destruct e; [| easy]. destruct hcomplete as [hcomplete _].
  rewrite Zlength_cons.
  destruct (Z_ge_dec i (Z.succ (Zlength c))) as [hge | hnge].
  - unfold sublist.
    rewrite Z_to_nat_neg. easy.
    omega.
  - apply Znot_ge_lt in hnge.
    assert (hi': 1 <= i <= Zlength c) by omega. clear hi hnge. pose proof hi' as hi''.
    revert hi'. apply Z_lt_induction with (x := i);[|omega].
  clear hi'' i.
  intros i hind hi.
  destruct (eq_dec i 1) as [he1 | he1]. rewrite he1.
  rewrite sublist_1_cons. replace (Z.succ (Zlength c) - 1) with (Zlength c) by omega.
  rewrite sublist_same by omega. unfold partial_cursor_correct_rel.
  destruct c; try easy. destruct p as [n' i']. simpl in hcomplete |-*.
  rewrite (proj2 hcomplete). easy.
  assert (h: partial_cursor_correct_rel (sublist (i-1) (Z.succ (Zlength c)) ((n, ip ii) :: c)) r).
  apply hind; omega.
  rewrite sublist_split with (mid := i) in h; [|omega|rewrite Zlength_cons; omega].
  remember (i-1) as j. replace i with (j+1) in h by omega.
  rewrite sublist_len_1 in h; [|rewrite Zlength_cons; omega]. unfold app in h.
  destruct (Znth j ((n, ip ii) :: c)). apply partial_cursor_correct_cons in h.
  replace (j+1) with i in h by omega. auto.
Qed.

Lemma sublist_tl: forall (A:Type) (a0: Inhabitant A) c i (a:A) c',
    0 <= i < Zlength c ->
    sublist i (Zlength c) c = a :: c' ->
    c' = sublist (i+1) (Zlength c) c.
Proof.
  intros A a0 c i a c' hi hsub.
  rewrite sublist_split with (mid := i+1) in hsub.
  rewrite sublist_len_1 in hsub.
  unfold app in hsub. inversion hsub. auto.
  omega. omega. omega.
Qed.

Lemma up_at_last_range: forall (X:Type) (c:cursor X) m,
    0 <= Zlength c - 1 < m ->
    0 <= Zlength (up_at_last c) - 1 < m.
Proof.
  intros.
  induction c.
  - simpl in H. omega.
  - destruct a as [n i]. simpl. destruct c.
    + simpl. omega.
    + destruct(index_eqb i (lastpointer n)).
      * apply IHc. split. rewrite Zlength_cons. rewrite Zsuccminusone. apply Zlength_nonneg.
        rewrite Zlength_cons in H. omega.
      * auto.
Qed.

Lemma complete_partial_upatlast: forall (X:Type) (c:cursor X) r,
    partial_cursor_correct_rel c r \/ complete_cursor_correct_rel c r ->
    partial_cursor_correct_rel (up_at_last c) r \/ complete_cursor_correct_rel (up_at_last c) r.
Proof.
  intros.
  induction c.
  - simpl. left. auto.
  - simpl. destruct a as [n i].
    destruct c.
    + auto.
    + destruct(index_eqb i (lastpointer n)).
      * apply IHc. destruct H.
        { left. apply partial_cursor_correct_cons with (n0 := n) (i0 := i). auto. }
        { left. unfold complete_cursor_correct_rel, complete_cursor_correct, getCEntry in H.
          destruct i. easy.
          case_eq (nth_entry n0 n). intros e h. destruct e.
          - rewrite h in H. destruct H as [H _].
            destruct p as [n1 i1].
            unfold partial_cursor_correct_rel.
            simpl in H. rewrite (proj2 H). easy.            
          - rewrite h in H. contradiction.
          - intro hnone. rewrite hnone in H. contradiction.
        }
      * auto.
Qed.

Lemma nth_entry_some':
  forall (X : Type) (n : node X) (i : nat),  (i < numKeys n)%nat -> exists e, nth_entry i n = Some e.
Proof.
  intros X n i h.
  destruct n as [ptr0 [|e le] isLeaf First Last x].
  simpl in h. omega.
  simpl in h|-*.
  generalize dependent i. generalize dependent e.
  induction le.
  - intros e i hi. simpl in hi. replace i with 0%nat by omega.
    now exists e.
  - intros e0 i hi.
    destruct i. exists e0. reflexivity.
    apply lt_S_n in hi. simpl in hi.
    apply IHle. auto.
Qed.

Lemma index_eqb_false: forall i1 i2,
    i1 <> i2 <-> index_eqb i1 i2 = false.
Proof.
  intros i1 i2.
  destruct i1, i2; try easy.
  unfold index_eqb. rewrite Nat.eqb_neq. split; intro h. intro hcontr. now subst.
  intro hcontr. now inversion hcontr.
Qed.

Lemma movetonext_correct: forall c r,
    complete_cursor c r -> isValid c r = true ->
    root_integrity (get_root r) ->
    ne_partial_cursor (next_cursor (up_at_last c)) r \/ complete_cursor (next_cursor(up_at_last c)) r.
Proof.
  intros c r hcomplete hvalid hint.
  unfold ne_partial_cursor.
  remember (next_cursor (up_at_last c)) as nxt.
  unfold complete_cursor in hcomplete|-*.
  unshelve epose proof (complete_partial_upatlast val c r _) as hual. now right.
  destruct c as [|[n i] c]. easy.
  destruct i as [|i]. easy.
  assert (hleaf: LeafNode n) by now apply (complete_leaf n (ip i) c r).
  assert (hcomplete' := hcomplete).
  unfold complete_cursor_correct_rel, complete_cursor_correct, getCEntry in hcomplete.
  case_eq (nth_entry i n); [|intros hnone; now rewrite hnone in hcomplete].
  intros e he; rewrite he in hcomplete. destruct e; try easy.
  case_eq (index_eqb (ip i) (lastpointer n)); intro h; unfold up_at_last in Heqnxt, hual; fold (@up_at_last val) in Heqnxt, hual.
  - left.
    rewrite h in Heqnxt, hual.
    induction c. simpl in Heqnxt. rewrite Heqnxt. simpl.
    split; [ | auto].
    admit. admit.
  - right. rewrite h in Heqnxt.
    assert (hnxt : nxt = (n, ip (S i)) :: c).
    { rewrite Heqnxt. now destruct c. }
    rewrite hnxt. split; [|easy].
    unfold complete_cursor_correct_rel, getCEntry.
    unshelve eassert (h1 := nth_entry_some' _ n (S i) _).
    -- destruct n as [ptr0 le [] First Last x]; try easy.
       simpl in h |- *.
       apply beq_nat_false in h.
       admit.
    -- destruct h1 as [e' he'].
       rewrite he'.
       unshelve eassert (h2 := integrity_nth_leaf _ _ _ _ _ hleaf he').
       { apply hint.
         replace n with (currNode ((n, ip i) :: c) r) by reflexivity.
         now apply complete_cursor_subnode. }
       destruct h2 as [k' [v' [x' he'']]]. rewrite he''.
       simpl. rewrite he'' in he'. easy.
Admitted.

Lemma length_next_cursor: forall (X:Type) (c:cursor X),
    Zlength (next_cursor c) = Zlength c.
Proof.
  intros. destruct c. simpl. auto. simpl. destruct p.
  rewrite Zlength_cons. rewrite Zlength_cons. auto.
Qed.

Lemma fst_next_cursor: forall (X:Type) (c:cursor X),
    map fst c = map fst (next_cursor c).
Proof.
  intros. destruct c. simpl. auto. destruct p. simpl. auto.
Qed.

Lemma upd_Znth_rev: forall (X:Type) (l:list X) v,
    l <> [] ->
    upd_Znth (Zlength l -1) (rev l) v = rev(upd_Znth 0 l v).
Proof.
  intros. destruct l.
  - exfalso. apply H. auto.
  - simpl. rewrite Zlength_cons. rewrite Zsuccminusone.
    rewrite upd_Znth_app2. rewrite Zlength_rev.
    replace (Zlength l - Zlength l) with 0.
    rewrite upd_Znth0. rewrite Zlength_cons. simpl. rewrite sublist_nil.
    rewrite sublist_1_cons. rewrite Zsuccminusone. rewrite sublist_same. auto.
    auto. auto. omega. rewrite Zlength_rev. rewrite Zlength_cons.
    simpl. omega.
Qed.

Lemma body_moveToNext: semax_body Vprog Gprog f_moveToNext moveToNext_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)). fold r.
  destruct c as [|[n i] c']. { inv H. inv H3. }
  pose (c:=(n,i)::c'). fold c.
  unfold cursor_rep. Intros anc_end. Intros idx_end. unfold r.
  forward_call(r,c,pc,numrec).         (* t'1=isValid(cursor) *)
  { unfold relation_rep, cursor_rep. unfold r. Exists anc_end. Exists idx_end. cancel. }
  forward_if.                              (* if t'1 == 0 *)
  { forward.                    (* return *)
    destruct (isValid c r) eqn:INVALID. inv H3. fold c. fold r.
    replace (moveToNext c r) with c.
    entailer!.
    unfold moveToNext; rewrite INVALID; auto. }
  assert (VALID: isValid c r = true).
  { destruct (isValid c r). auto. inv H3. } rewrite VALID.
  forward_loop
    (EX i:Z, PROP(up_at_last c = up_at_last (sublist i (Zlength c) c); 0 <= i <= Zlength c)
             LOCAL (temp _t'1 (Val.of_bool true); temp _cursor pc)
             SEP (relation_rep r numrec; cursor_rep (sublist i (Zlength c) c) r pc))
    break:(EX i:Z, PROP(up_at_last c = sublist i (Zlength c) c)
           LOCAL (temp _t'1 (Val.of_bool true); temp _cursor pc)
           SEP (relation_rep r numrec; cursor_rep (up_at_last c) r pc)).
  - Exists 0. entailer!.
    + rewrite sublist_same. simpl. auto. auto. omega.
    + rewrite sublist_same. cancel. auto. omega.
  - Intros i0.
    pose (subc:=sublist i0 (Zlength c) c). fold subc.
    unfold cursor_rep.
    Intros anc_end0. Intros idx_end0. unfold r.
    forward.                    (* t'16 = cursor->level *)
    gather_SEP 1 2. replace_SEP 0 (cursor_rep subc r pc).
    { entailer!. unfold cursor_rep. Exists anc_end0. Exists idx_end0. unfold r. cancel. }
    forward_if (PROP ( )
     LOCAL (temp _t'16 (Vint (Int.repr (Zlength subc - 1))); temp _t'1 (Val.of_bool true);
            temp _cursor pc;
            temp _t'2 (Val.of_bool (andb (Z.gtb (Zlength subc - 1) 0) (index_eqb (entryIndex subc) (lastpointer (currNode subc r)))))) 
     SEP (cursor_rep subc r pc; relation_rep (root, prel) numrec)).
    + assert(PARTIAL: ne_partial_cursor subc r \/ complete_cursor subc r).
      { destruct (eq_dec i0 0) as [heq|hneq].
        replace ((n, i) :: c') with subc in H.
        right. assumption. unfold subc. now rewrite heq, sublist_same.
        left. unfold complete_cursor in H. destruct H as [CORRECT BALANCED].
        unfold ne_partial_cursor. split.
        - unfold subc. apply complete_sublist_partial. auto.
          omega. assumption.
        - destruct subc. simpl in H6. inv H6. simpl. omega. }
      forward_call(r,subc,pc,numrec).     (* t'3=entryIndex(cursor) *)
      { fold r. cancel. }       
      forward_call(r,subc,pc,numrec).                (* t'4 = curnode(cursor) *)
      destruct subc as [|[currnode i'] subc'] eqn:HSUBC.
      { simpl in H6. inv H6. }
      simpl. assert (SUBNODE: subnode currnode root).
      {
        destruct PARTIAL as [PARTIAL | PARTIAL].
        unfold ne_partial_cursor in PARTIAL. destruct PARTIAL.
        apply partial_cursor_subnode in H7. simpl in H7. auto.
        destruct PARTIAL as [PARTIAL _].
        apply complete_cursor_subnode in PARTIAL. simpl in PARTIAL. assumption. }
      assert(CURRNODE: currnode = currNode subc r). { rewrite HSUBC. simpl. auto. }
      forward_call(currNode subc r). (* 't'5=lastpointer t'4 *)
      { entailer!. }
      { apply subnode_rep in SUBNODE. rewrite SUBNODE. rewrite CURRNODE. cancel. }
      { unfold get_root in H1. unfold root_wf in H1. simpl in H1. rewrite <- CURRNODE.
        apply H1. apply SUBNODE. }
      forward.                  (* t'2= (t'3==t'5) *)
      entailer!.
      { rewrite Zlength_cons. rewrite Zsuccminusone. 
        pose (lastp:=(lastpointer (currNode (sublist i0 (Zlength c) c) r))).
        rewrite Zlength_cons in H6. rewrite Zsuccminusone in H6.
        assert(LENGTH: Zlength subc' >? 0 = true).
        { destruct(subc'). rewrite Zlength_nil in H6. rewrite Int.signed_repr in H6.
          omega. rep_omega. rewrite Zlength_cons. apply Z.gtb_lt. rep_omega. }
        rewrite LENGTH. simpl.
        destruct(index_eqb i' lastp) eqn:HEQ.
        + destruct i' as [|i''].
          * fold lastp. rewrite HEQ. destruct lastp;  simpl. reflexivity.
            simpl in HEQ. inversion HEQ.
          * fold lastp. rewrite HEQ. destruct lastp; simpl. simpl in HEQ. inv HEQ.
            inv HEQ. rewrite Nat.eqb_eq in H14. rewrite H14, Int.eq_true. auto.
        + unfold Int.eq.
          unfold ne_partial_cursor in PARTIAL.
          (* apply partial_correct_rel_index in H13. *)
          unfold root_wf in H1.
          apply H1 in SUBNODE. unfold node_wf in SUBNODE.
          assert(idx_to_Z lastp <= Z.of_nat (numKeys (currNode (sublist i0 (Zlength c) c) r))).
          { unfold lastpointer in lastp. destruct (currNode (sublist i0 (Zlength c) c) r).
            destruct b. unfold lastp. simpl. omega. simpl.
            destruct (numKeys_le l). unfold lastp. simpl. omega.
            unfold lastp. simpl. rewrite Zpos_P_of_succ_nat. omega. }
          clear -PARTIAL SUBNODE H13 HEQ. fold lastp.
          destruct i' as [|ii]; destruct lastp as [|pp]; unfold rep_index; unfold idx_to_Z in H13;
            simpl in H13; unfold index_eqb in HEQ; simpl in HEQ.
          * inv HEQ.
          * rewrite if_false. simpl. auto. unfold not. intros.
            apply eq_sym in H. autorewrite with norm in H.
            assert(Z.of_nat pp <= Z.of_nat Fanout).
            { apply inj_le  in SUBNODE. rep_omega. }
            rewrite H in H0. rewrite Fanout_eq in H0. simpl in H0. compute in H0. apply H0. auto.
          * rewrite if_false. simpl. auto. unfold not. intros. apply inj_le in SUBNODE. 
            destruct PARTIAL as [[parcor _] | comp].
            ++ apply partial_correct_rel_index in parcor. simpl in parcor. pose proof (Z.lt_le_trans _ _ _ parcor SUBNODE) as H0.
               rewrite Int.unsigned_repr in H. 
               rewrite Fanout_eq, H in H0. compute in H0. inversion H0.
               split. apply Nat2Z.is_nonneg. transitivity (Z.of_nat 15). rewrite <- Fanout_eq. omega.
            compute. intro inveq ; inversion inveq.
            ++ destruct comp as [comp _]. apply complete_correct_rel_index in comp.
               simpl in comp. pose proof (Z.lt_le_trans _ _ _ comp SUBNODE).
               rewrite Int.unsigned_repr in H. 
               rewrite Fanout_eq, H in H0. compute in H0. inversion H0.
               split. apply Nat2Z.is_nonneg. transitivity (Z.of_nat 15). rewrite <- Fanout_eq. omega.
            compute. intro inveq ; inversion inveq.
          * rewrite if_false. simpl. rewrite HEQ. auto. unfold not. intros.
            rewrite Int.unsigned_repr in H. rewrite Int.unsigned_repr in H by rep_omega.
            apply Nat2Z.inj in H. subst. rewrite <- beq_nat_refl in HEQ. inv HEQ.
            split. apply Nat2Z.is_nonneg.
            apply inj_le in SUBNODE.
            transitivity ( Z.of_nat (numKeys (currNode (sublist i0 (Zlength c) c) r))).
            { destruct PARTIAL as [[par _]|[comp _]].
              apply partial_correct_rel_index in par. simpl in par. omega.
              apply complete_correct_rel_index in comp. simpl in comp. omega. }
              transitivity (Z.of_nat Fanout). omega. rewrite Fanout_eq. compute. intro inveq ; inversion inveq.
      }
      unfold relation_rep. cancel.
      sep_apply (wand_frame_elim (btnode_rep (currNode (sublist i0 (Zlength c) c) r))).
      apply derives_refl.
    + forward.                  (* t'2=0 *)
      entailer!.
      rewrite Int.signed_repr in H6.
      replace (Zlength subc -1 >? 0) with false. simpl. auto.
      { destruct subc. auto. destruct subc. auto. rewrite Zlength_cons in H6.
        rewrite Zlength_cons in H6. rewrite Zsuccminusone in H6. rewrite Zlength_correct in H6.
        omega. }
      
      split. rep_omega. assert(0 <= Zlength c - 1 < 20).
      { eapply partial_complete_length. right. eauto. auto. }
      unfold subc. rewrite Zlength_sublist. rep_omega.
      split. omega. rep_omega. rep_omega.
    + forward_if.
      * unfold cursor_rep. unfold r. Intros anc_end1. Intros idx_end1.
        forward.                (* t'15=cursor->level *)
        forward.                (* cursor->level = t'15-1 *)
        { entailer!. unfold subc.
          assert(0 <= Zlength c - 1 < 20).
          { eapply partial_complete_length. right. eauto. auto. }
          rewrite Zlength_sublist.
          rewrite Int.signed_repr. rewrite Int.signed_repr.
          rep_omega. rep_omega. rep_omega. rep_omega. rep_omega. }
        assert(i0 + 1 <= Zlength c).
        { apply andb_true_iff in H6. destruct H6.
          unfold subc in H6. rewrite Zlength_sublist in H6 by rep_omega.
          apply Zgt_is_gt_bool in H6. omega. }
        Exists (i0+1). entailer!. unfold cursor_rep. unfold r.
        { rewrite H4. fold subc.
          apply andb_true_iff in H6. destruct H6.
          destruct subc as [|[subn subi] subc'] eqn:HSUBC.
          - simpl in H6. apply Z.gtb_lt in H6. omega.
          - unfold subc in HSUBC.
            apply sublist_tl in HSUBC. rewrite HSUBC.
            rewrite Zlength_cons in H6. rewrite Zsuccminusone in H6. rewrite <- HSUBC.
            destruct subc'. rewrite Zlength_nil in H6. apply Z.gtb_lt in H6. omega.
            simpl in H13 |- *. rewrite H13. auto. exact (btnode val None (nil val) true true true nullval, ip 0). omega. }
        Exists ((getval (currNode subc r))::anc_end1).
        Exists ((Vint(Int.repr(rep_index(entryIndex subc))))::idx_end1).
        cancel.
        rewrite Zlength_sublist. unfold subc. rewrite Zlength_sublist. unfold r.
        replace (Zlength c - (i0 + 1) - 1) with  (Zlength c - i0 - 1 - 1) by rep_omega.
        unfold_data_at 1%nat. unfold_data_at 1%nat. cancel. repeat rewrite <- map_rev.
        rewrite sublist_split with (mid:=i0+1) at 1. rewrite rev_app_distr.
        erewrite @sublist_len_1 with (d:=(n,i)). simpl. rewrite list_append_map. rewrite <- app_assoc.
        simpl.
        replace(snd (Znth i0 c)) with (entryIndex (sublist i0 (Zlength c) c)).
        cancel.
        rewrite sublist_split with (mid:=i0+1) at 1. rewrite rev_app_distr.
        erewrite @sublist_len_1 with (d:=(n,i)). simpl. rewrite list_append_map. rewrite list_append_map.
        rewrite <- app_assoc.
        simpl.
        replace(fst(Znth i0 c)) with (currNode (sublist i0 (Zlength c) c) (root,prel)).
        cancel.
        rewrite sublist_split with (mid:=i0+1).
        erewrite @sublist_len_1 with (d:=(n,i)). simpl. unfold fst. auto.
        rep_omega. rep_omega. rep_omega. rep_omega. rep_omega. rep_omega.
        rewrite sublist_split with (mid:=i0+1).
        erewrite @sublist_len_1 with (d:=(n,i)). simpl. unfold snd. auto.
        rep_omega. rep_omega. rep_omega. rep_omega. rep_omega. rep_omega. rep_omega.
        rep_omega. rep_omega. rep_omega.
      * forward.                (* break *)
        entailer!. rewrite H4. fold subc.
        apply andb_false_iff in H6.
        assert(subc = up_at_last subc).
        { destruct H6.
          - destruct subc. simpl. auto. destruct subc. simpl. destruct p. auto.
            repeat rewrite Zlength_cons in H6. rewrite Zsuccminusone in H6.
            rewrite Z.gtb_ltb in H6. apply Z.ltb_ge in H6.
            assert(0 <= Zlength subc) by apply Zlength_nonneg. omega.
          - destruct subc as [|[subn subi] subc'].
            + simpl. auto.
            + simpl. simpl in H6. rewrite H6. destruct subc'. auto. auto. }
        Exists i0.
        fold r. rewrite <- H9.
        entailer!.
  - unfold cursor_rep. Intros uali. Intros anc_end0. Intros idx_end0. unfold r.
    forward.                    (* t'12=cursor->level *)
    forward.                    (* t'13=cursor->level *)
    assert(UPATLAST: up_at_last c = match c' with
            | [] => [(n, i)]
            | _ :: _ => if index_eqb i (lastpointer n) then up_at_last c' else (n, i) :: c'
                                    end). 
   { simpl. auto. }
    assert(RANGE: 0 <= Zlength (up_at_last c) - 1 < 20).
    { apply up_at_last_range. fold c in H. eapply partial_complete_length; eauto. }
    forward.                    (* t'14=cursor->ancidx[t'13] *)
    { entailer!. rewrite <- UPATLAST.
      rewrite app_Znth1. rewrite Znth_rev.
      rewrite Zlength_map. replace (Zlength (up_at_last c) - (Zlength (up_at_last c) - 1) - 1) with 0.
      destruct (up_at_last c).
      - simpl in RANGE. omega.
      - simpl. auto.
      - rep_omega.
      - rewrite Zlength_map. rep_omega.
      - autorewrite with sublist. omega.
    }
    forward.                    (* cursor->ancestors[t'12] = t'14 +1 *)
    { entailer!. rewrite <- UPATLAST.
      rewrite app_Znth1. rewrite Znth_rev. rewrite Zlength_map.
      replace (Zlength (up_at_last c) - (Zlength (up_at_last c) - 1) - 1) with 0.
      destruct (up_at_last c) as [|[n' i'] up'].
      - simpl in RANGE. omega.
      - simpl. entailer!. unfold complete_cursor in H. destruct H.
        assert(SUBNODE: subnode n' root).
        { assert(h : partial_cursor_correct_rel ((n, i) :: c') (root, prel) \/ complete_cursor_correct_rel ((n, i) :: c') (root, prel)) by (right; auto).
          
          apply complete_partial_upatlast in h. simpl in h. rewrite <- UPATLAST in h.
          destruct h as [h1 | h2]. 
          - apply partial_cursor_subnode in h1. simpl in h1. auto.
          - apply complete_cursor_subnode in h2. simpl in h2. auto. }
        assert((numKeys n' <= Fanout)%nat).
        { unfold root_wf in H1. apply H1 in SUBNODE. unfold node_wf in SUBNODE. auto. }
        clear -H UPATLAST H16 H15.
        assert(partial_cursor_correct_rel ((n, i) :: c') (root, prel) \/ complete_cursor_correct_rel ((n, i) :: c') (root, prel)) by (right; auto).
        apply complete_partial_upatlast in H0.
        assert((n',i')::up' = up_at_last((n,i)::c')).
        { simpl. rewrite UPATLAST. auto. } clear UPATLAST.
        destruct i'. simpl. rep_omega. simpl.
        destruct H0.
        + unfold partial_cursor_correct_rel in H0. rewrite <- H1 in H0.
          destruct(nth_node (ip n0) n'); try contradiction.
          apply partial_correct_index in H0. simpl in H0.
          apply inj_le in H16.
          assert (Z.of_nat n0 < 15). replace 15 with (Z.of_nat Fanout) by reflexivity. omega.
          pose proof (Nat2Z.is_nonneg n0).
          rewrite Int.signed_repr.
          rep_omega. rep_omega.
        + unfold complete_cursor_correct_rel in H0.
          destruct(getCEntry (up_at_last ((n, i) :: c'))); try contradiction.
          destruct e; try contradiction.
          rewrite <- H1 in H0.
          apply complete_correct_index in H0. simpl in H0.
          rewrite Int.signed_repr. rep_omega. rep_omega.
      - rep_omega.
      - rewrite Zlength_map. rep_omega.
      - rewrite Zlength_rev. rewrite Zlength_map. rep_omega. } deadvars!. rewrite <- UPATLAST.
    gather_SEP 1 2. pose(cincr := next_cursor (up_at_last c)).
    replace_SEP 0 (cursor_rep cincr r pc).
    {  unfold cursor_rep. entailer!.
       Exists anc_end0. Exists idx_end0. cancel.
       unfold r.
       (* rewrite <- UPATLAST. *)
       unfold cincr.
       rewrite length_next_cursor.
       rewrite upd_Znth_app1.
       rewrite fst_next_cursor. 
       rewrite app_Znth1.
       rewrite Znth_rev. rewrite Zlength_map.
       replace(Zlength (up_at_last c) - (Zlength (up_at_last c) - 1) - 1) with 0.
       destruct (up_at_last c) as [|[upn upi] upc] eqn:HUP.
       { simpl in RANGE. omega. }
       simpl.
       rewrite upd_Znth_app2.
       rewrite Zlength_rev. rewrite Zlength_map. rewrite Zlength_cons.
       rewrite Zsuccminusone. replace (Zlength upc - Zlength upc) with 0.
       rewrite upd_Znth0. rewrite Zlength_cons. simpl. rewrite sublist_nil.
       assert(Vint (Int.add (Int.repr (rep_index upi)) (Int.repr 1)) = Vint (Int.repr (rep_index (next_index upi)))).
       { rewrite add_repr.
         rewrite next_rep. auto. }
       rewrite H8. cancel.
       omega.
       rewrite Zlength_cons. rewrite Zsuccminusone. rewrite Zlength_rev. rewrite Zlength_map.
       rewrite Zlength_cons. simpl. omega.
       omega.
       rewrite Zlength_map. omega.
       rewrite Zlength_rev. rewrite Zlength_map. omega.
       split. destruct(up_at_last c). simpl in RANGE. omega. rewrite Zlength_cons. rewrite Zsuccminusone.
       apply Zlength_nonneg.
       rewrite Zlength_rev. rewrite Zlength_map. omega. }
    forward_call(r,cincr,pc,numrec).       (* t'6=currNode(cursor) *)
    { fold r. cancel. }
    { unfold r. split; auto. now apply movetonext_correct. }
    assert(SUBNODE: subnode (currNode cincr r) root).
    { apply movetonext_correct in H; try easy. fold c cincr in H.
      destruct H. inv H. apply partial_cursor_subnode in H5. simpl in H5. auto.
      inv H. apply complete_cursor_subnode in H5. simpl in H5. assumption. }
    assert(SUBREP: subnode (currNode cincr r) root) by auto.
    pose(currnode:= currNode cincr r). fold currnode.
    destruct currnode eqn:HCURR.
    simpl.
    apply subnode_rep in SUBREP. rewrite SUBREP. Intros. fold currnode.
    rewrite unfold_btnode_rep with (n:=currnode) at 1. rewrite HCURR.
    Intros ent_end.
    forward.                    (* t'11=t'6->isLeaf *)
    { entailer!. destruct b; simpl; auto. }
    sep_apply (fold_btnode_rep o).
    sep_apply modus_ponens_wand.
    forward_if.                 (* if t'11 *)
    + forward.                  (* return *)
      entailer!. fold r. fold c.
      assert(cincr = moveToNext c r).
      { unfold cincr. unfold moveToNext. fold r in H4.
        rewrite VALID. unfold cincr in HCURR.
        destruct(up_at_last c).
        { simpl in RANGE. omega. }
        simpl in cincr. destruct p.
        simpl in HCURR. destruct b.
        rewrite HCURR. simpl. auto.
        apply typed_true_of_bool in H5. inv H5. }
      rewrite H11. unfold relation_rep, r. cancel.
    + forward_call(r,cincr,pc,numrec).     (* t'7=currnode(cursor) *)
      { unfold relation_rep. unfold r.  cancel. }
      { split. unfold cincr. apply movetonext_correct. auto. auto. auto. auto. }
      forward_call(r,cincr,pc,numrec). (* t'8 = entryIndex(cursor) *)
      { split. unfold cincr. apply movetonext_correct. auto. auto. auto. auto. }
      apply movetonext_correct in H. fold c in H.
      assert(CINCRDEF: cincr = next_cursor(up_at_last c)) by auto.
      destruct (up_at_last c) as [|[upn upi] upc] eqn:HUP.
      { simpl in RANGE. omega. } rewrite <- HUP in CINCRDEF.
      simpl in cincr. unfold cincr. simpl.
      assert(exists incri, next_index upi = ip incri).
      { destruct upi. exists O. simpl. auto. exists (S n0). simpl. auto. }
      destruct H6 as [incri HNEXT]. rewrite HNEXT. simpl. Intros.
      unfold cincr in SUBREP, SUBNODE. simpl in SUBREP, SUBNODE.
      rewrite SUBREP.
      rewrite unfold_btnode_rep with (n:=upn) at 1.
      destruct upn eqn:HUPN. Intros ent_end0. simpl.
      assert(INCRI:  idx_to_Z (ip incri) < Z.of_nat (numKeys upn)).
      { simpl in H. rewrite HNEXT in H.
        destruct H.
        - rewrite <- HUPN in H. clear -H. inv H. simpl in H0.
          destruct(nth_node (ip incri) upn) eqn:HNTH; try contradiction.
          destruct H0.
          assert(partial_cursor_correct ((upn,ip incri)::upc) n root).
          { simpl. split; auto. }
          apply partial_correct_index in H2. auto.
        - rewrite <- HUPN in H. clear -H. inv H. unfold complete_cursor_correct_rel in H0.
          destruct(getCEntry((upn, ip incri) :: upc)); try contradiction.
          destruct e; try contradiction.
          apply complete_correct_index in H0. simpl in H0. auto. }
      assert(WF: subnode upn root).
      { rewrite <- HUPN in SUBNODE. auto. }
      unfold root_wf in H1. simpl in H1. apply H1 in WF. unfold node_wf in WF.
      assert(NTH: (incri < numKeys_le l0)%nat).
      { simpl in INCRI. rewrite HUPN in INCRI. simpl in INCRI. omega. }
      apply nth_entry_le_in_range in NTH. destruct NTH as [e NTHH].
      unfold cincr in currnode. simpl in currnode. unfold currnode in HCURR.
      inv HCURR.
      assert(INTERN: b = false).
      { destruct b. simpl in H5. inv H5. auto. }
      assert(INTEGRITY:  subnode (btnode val o l b b0 b1 v) root) by auto.
      unfold root_integrity in H2. simpl in H2. apply H2 in INTEGRITY.
      rewrite INTERN in INTEGRITY.
      apply integrity_nth with (e:=e) (i:=incri) in INTEGRITY; simpl; auto.
      destruct INTEGRITY as [k [child HE]].
      forward.                  (* t'9=t'7 -> entries + t'8 ->ptr.child *)
      { entailer!. split. omega. rewrite Fanout_eq in WF. simpl in INCRI. simpl in WF. rep_omega. }
      { destruct o. assert(subnode child root).
        eapply sub_trans with (m:=(btnode val (Some n0) l false b0 b1 v)).
        apply nth_subnode with (i:=ip incri). simpl. apply nth_entry_child with (k:=k). rewrite HE in NTHH.
        eauto. rewrite INTERN in SUBNODE. auto.
        apply subnode_rep in H6.
        pose(upn:=btnode val (Some n0) l b b0 b1 v).
        sep_apply (fold_btnode_rep (Some n0)). fold upn.
        sep_apply modus_ponens_wand. rewrite HE in NTHH.
        rewrite Znth_to_list with (e:=(keychild val k child)) by auto. rewrite H6. entailer!.
      assert (node_integrity  (btnode val None l b b0 b1 v)). auto. subst. easy. }
      pose(upn:=btnode val o l b b0 b1 v).
      sep_apply (fold_btnode_rep o). fold upn.
      sep_apply modus_ponens_wand.
      unfold cursor_rep. Intros anc_end1. Intros idx_end1. unfold r.
      forward.                  (* t'10=cursor->level *)
      rewrite HE in NTHH.
      rewrite Znth_to_list with (e:=(keychild val k child)) by auto. simpl.
      forward_call(r,cincr,pc,child,numrec). (* movetofirst(t'9,cursor,t'10+1) *)
      { rewrite Zlength_cons. rewrite Zsuccminusone.
        rewrite Zlength_cons, Zsuccminusone in RANGE.
        rewrite Int.signed_repr by rep_omega.
        rewrite Int.signed_repr by rep_omega.
        rep_omega. }
      { entailer!. 
        repeat rewrite Zlength_cons. repeat rewrite Zsuccminusone.
        rewrite Z.add_1_r. auto. }
      { unfold relation_rep. unfold cursor_rep. Exists anc_end1. Exists idx_end1. unfold r.
        cancel. unfold cincr. repeat rewrite Zlength_cons. rewrite HNEXT. simpl.
         cancel. } simpl in H. fold cincr in H.
      { repeat split.
        - destruct H. unfold ne_partial_cursor in H. destruct H as [P L].
          unfold r. auto.
          unfold cincr in H.
          exfalso. apply complete_leaf in H. rewrite INTERN in H. inv H.
          auto.
        - destruct H; destruct H; auto.
        - auto.
        - unfold cincr. simpl. rewrite HNEXT. destruct o, b; try easy. apply nth_entry_child with (k:=k). eauto. assert (node_integrity (btnode val None l false b0 b1 v)). auto. easy. 
        - auto. }
      forward.                  (* return *)
      * unfold moveToNext. fold r in H2. fold r. fold c.
        rewrite VALID. rewrite <- CINCRDEF. simpl. rewrite HNEXT.
        replace (nth_node_le incri l) with (Some child).
        cancel.
        { destruct o. entailer. assert (node_integrity (btnode val None l false b0 b1 v)). auto.
          easy.  }
        symmetry. apply (nth_entry_child _ _ k). auto.
      * auto.
      * auto. 
Qed.

Lemma movetonext_complete : forall c r,
    complete_cursor c r -> complete_cursor (moveToNext c r) r.
Proof.
Admitted.

Lemma body_RL_MoveToNext: semax_body Vprog Gprog f_RL_MoveToNext RL_MoveToNext_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)). fold r.
  destruct c as [|[n i] c'].
  inv H. inv H3. pose (c:=(n,i)::c'). fold c.
  forward_call(r,c,pc,numrec).         (* t'1=entryIndex(cursor) *)
  forward_call(r,c,pc,numrec).         (* t'2=currNode(cursor) *)
  unfold c. simpl.
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:=btnode val ptr0 le isLeaf First Last pn). simpl.
  assert (SUBNODE: subnode n root).
  { unfold complete_cursor in H. destruct H. apply complete_cursor_subnode in H. auto. }
  unfold relation_rep. rewrite subnode_rep with (n:=n) by auto.
  rewrite unfold_btnode_rep at 1. unfold n. Intros ent_end.
  forward.                      (* t'3=t'2->numKeys *)
  simpl.
  sep_apply (fold_btnode_rep ptr0). fold n in H,c|-*.
  sep_apply modus_ponens_wand.
  sep_apply (fold_relation_rep). fold r in H0,H1,H2|-*. fold c in H|-*.
  forward_if(PROP ( )
     LOCAL (temp _t'3 (Vint (Int.repr (Z.of_nat (numKeys_le le)))); temp _t'2 pn;
     temp _t'1 (Vint(Int.repr(rep_index i))); temp _cursor pc)
     SEP (relation_rep r numrec; match (index_eqb i (ip (numKeys n))) with true => cursor_rep (moveToNext c r) r pc | false => cursor_rep c r pc end)).
  - forward_call(c,pc,r,numrec).       (* moveToNext(cursor) *)
    entailer!.
    destruct H. apply complete_correct_rel_index in H.
    unfold root_wf in H1. apply H1 in SUBNODE. unfold node_wf in SUBNODE. fold n  in H.
    assert(Z.of_nat (numKeys_le le) <= Z.of_nat Fanout).
    { simpl in SUBNODE. omega. } simpl in H.
      destruct i as [|ii].
    + simpl in H4. simpl in H. clear -H3 H6. apply (f_equal Int.unsigned) in H3.
      rewrite Fanout_eq in H6. simpl in H6. apply eq_sym in H3. autorewrite with norm in H3.
      rewrite H3 in H6. exfalso. compute in H6. apply H6. auto.
    + simpl in H3. apply (f_equal Int.unsigned) in H3. rewrite Fanout_eq in H6. simpl in H6.
      clear -H3 H6 H. apply eq_sym in H3. simpl in H.
      autorewrite with norm in H3. apply Nat2Z.inj in H3. subst. simpl.
      rewrite Nat.eqb_refl. cancel.
  - forward.                                            (* skip *)
    destruct H. apply complete_correct_rel_index in H.
    unfold root_wf in H1. apply H1 in SUBNODE. unfold node_wf in SUBNODE. fold n  in H.
    assert(Z.of_nat (numKeys_le le) <= Z.of_nat Fanout).
    { simpl in SUBNODE. omega. } simpl in H.
    destruct i as [|ii]; simpl index_eqb.
    { entailer!. } unfold index_eqb, numKeys. unfold n.
    destruct (ii =? numKeys_le le)%nat eqn:HII.
    + exfalso. apply beq_nat_true in HII. subst. simpl in H2. contradiction.
    + entailer!.
  - pose (newc:=if index_eqb i (ip (numKeys n)) then (moveToNext c r) else c).
    forward_call(newc,pc,r,numrec).                               (* moveToNext(cursor) *)
    + unfold newc. destruct (index_eqb i (ip (numKeys n))); cancel.
    + split; auto. unfold newc.
      destruct (index_eqb i (ip (numKeys n))).
      * apply movetonext_complete. auto.
      * auto.
    + Local Ltac entailer_for_return ::= idtac.
        forward.
        entailer!. unfold newc. simpl. fold n. fold c. 
      destruct (index_eqb i (ip (numKeys_le le))); fold c; fold r; cancel.
Qed.
