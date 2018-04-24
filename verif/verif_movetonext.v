(** * verif_movetonext.v : Correctness proof of firstpointer, moveToNext and RL_MoveToNext *)

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
Require Import index.
Require Import btrees_sep.
Require Import btrees_spec.
Require Import verif_movetofirst.

Lemma body_lastpointer: semax_body Vprog Gprog f_lastpointer lastpointer_spec.
Proof.
  start_function.
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:=btnode val ptr0 le isLeaf First Last pn).
  rewrite unfold_btnode_rep. Intros.
  forward.                      (* t'1=node->isLeaf *)
  { entailer!. destruct isLeaf; simpl; auto. }
  forward_if.
  - forward.                    (* t'3=node->numKeys *)
    forward.                    (* return *)
    entailer!.
    destruct isLeaf.
    + unfold rep_index. reflexivity.
    + simpl in H0. inv H0.
  - forward.                    (* t'2=node->numKeys *)
    forward.                    (* return *)
    { entailer!. unfold node_wf in H.
      simpl in H. clear -H. admit. (* OK *) }
    entailer!.
    destruct isLeaf.
    + simpl in H0. inv H0.
    + destruct (numKeys_le le).
      * unfold rep_index. simpl. reflexivity.
      * assert (Z.of_nat (S n0) -1 = Z.of_nat n0).
        { admit. }              (* OK *)
        rewrite H6. unfold rep_index. reflexivity.  
Admitted.

Lemma body_moveToNext: semax_body Vprog Gprog f_moveToNext moveToNext_spec.
Proof.
  start_function.
  destruct r as [[[root numRec] depth] prel].
  pose (r:=(root,numRec,depth,prel)). fold r.
  destruct c as [|[n i] c'].
  inv H0. pose (c:=(n,i)::c'). fold c.
  unfold cursor_rep. Intros anc_end. Intros idx_end. unfold r.
  forward.                      (* t'17=cursor->relation *)
  unfold relation_rep. Intros.
  forward.                      (* t'18=t'17->numRecords *)
  forward_if.
  {  forward.                   (* return *)
     assert (numRec = O) by admit. (* OK by H1 *)
     entailer!.
     unfold moveToNext. simpl. fold c. unfold cursor_rep. Exists anc_end. Exists idx_end. cancel. }
  forward.                      (* skip *)
  forward_call(r,c,pc).         (* t'1=isValid(cursor) *)
  { unfold relation_rep, cursor_rep. unfold r. Exists anc_end. Exists idx_end. cancel.
    change_compspecs CompSpecs. cancel. }
  forward_if.
  { forward.                    (* return *)
    assert (isValid c r = false) by admit. (* OK by H2 *)
    assert (moveToNext c r = c).
    { unfold moveToNext. destruct (get_numrec r). auto. rewrite H8. auto. }
    fold c. fold r. rewrite H9.
    entailer!.  }
  forward.                      (* skip *)
  assert (isValid c r = true).
  { destruct (isValid c r). auto. inv H2. } rewrite H3.
  forward_loop
    (EX i:Z, PROP()
             LOCAL (temp _t'1 (Val.of_bool true); temp _t'18 (Vint (Int.repr (Z.of_nat numRec))); temp _t'17 prel; temp _cursor pc)
             SEP (relation_rep r; cursor_rep (sublist 0 (Zlength c - i) c) r pc))
    break:(PROP()
           LOCAL (temp _t'1 (Val.of_bool true); temp _t'18 (Vint (Int.repr (Z.of_nat numRec))); temp _t'17 prel; temp _cursor pc)
           SEP (relation_rep r; cursor_rep (up_at_last c) r pc)).
  - Exists 0. entailer!. rewrite sublist_same. cancel. auto. omega.
  - Intros i0.
    pose (subc:=sublist 0 (Zlength c - i0) c). fold subc.
    unfold cursor_rep.
    Intros anc_end0. Intros idx_end0. unfold r.
    forward.                    (* t'16 = cursor->level *)
    gather_SEP 1 2. replace_SEP 0 (cursor_rep subc r pc).
    { entailer!. unfold cursor_rep. Exists anc_end0. Exists idx_end0. unfold r. cancel. }
    forward_if (PROP ( )
     LOCAL (temp _t'16 (Vint (Int.repr (Zlength subc - 1))); temp _t'1 (Val.of_bool true);
            temp _t'18 (Vint (Int.repr (Z.of_nat numRec))); temp _t'17 prel; temp _cursor pc;
            temp _t'2 (Val.of_bool (andb (Z.gtb (Zlength subc - 1) 0) (index_eqb i (lastpointer n))))) 
     SEP (cursor_rep subc r pc; relation_rep (root, numRec, depth, prel))).
    + forward_call(r,subc,pc).     (* t'3=entryInde(cursor) *)
      { fold r. cancel. }
      { admit.                  (* todo: cursor_wf preserved *) }
      forward_call(r,subc,pc).
      { admit.                  (* todo: cursor_wf preserved *) }
      forward_call(currNode subc r). (* 't'5=lastpointer t'4 *)
      { admit. }
      { admit.                  (* todo: node_wf preserved *) }
      forward.                  (* t'2= (t'3==t'5) *)
      entailer!.
      admit.
      admit.
    + forward.                  (* t'2=0 *)
      entailer!.
      admit.
    + forward_if.
      * forward.                (* skip *)
        unfold cursor_rep. unfold r. Intros anc_end1. Intros idx_end1.
        forward.                (* t'15=cursor->level *)
        forward.                (* cursor->level = t'15-1 *)
        { admit. }
        Exists (i0+1). entailer!. unfold cursor_rep. unfold r.
        Exists ((getval (currNode subc r))::anc_end1).
        Exists ((rep_index(entryIndex subc))::idx_end1).
        cancel.
        admit.                  (* should be ok *)
      * forward.                (* break *)
        entailer!.
        admit. (* TODO: prove that when the loop stops, we have up_at_last *)
  - unfold cursor_rep. Intros anc_end0. Intros idx_end0. unfold r.
    forward.                    (* t'12=cursor->level *)
    forward.                    (* t'13=cursor->level *)
    forward.                    (* t'14=cursor->ancidx[t'13] *)
    { admit.                    (* cursor in range *) }
    { admit. }
    forward.                    (* cursor->ancestors[t'12] = t'14 +1 *)
    { admit. }
    { admit. }
    gather_SEP 1 2. pose(cincr := next_cursor (up_at_last c)).
    replace_SEP 0 (cursor_rep cincr r pc).
    { unfold cursor_rep. entailer!.
    Exists anc_end0. Exists idx_end0. cancel. admit. }
    forward_call(r,cincr,pc).       (* t'6=currNode(cursor) *)
    { fold r. cancel. }
    { admit. }
    destruct (currNode cincr r).
    simpl. Intros.
    (* here I need a representation for the current node of cincr *)
    admit.
Admitted.

Lemma body_RL_MoveToNext: semax_body Vprog Gprog f_RL_MoveToNext RL_MoveToNext_spec.
Proof.
  start_function.
  destruct r as [[[root numRec] depth] prel].
  pose (r:=(root,numRec,depth,prel)). fold r.
  destruct c as [|[n i] c'].
  inv H0. pose (c:=(n,i)::c'). fold c.
  forward_call(r,c,pc).         (* t'1=entryIndex(cursor) *)
  forward_call(r,c,pc).         (* t'2=currNode(cursor) *)
  unfold c. simpl.
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:=btnode val ptr0 le isLeaf First Last pn). simpl.
  assert (subnode n root) by admit. (* I need a cursor correctness property here *)
  unfold relation_rep. rewrite subnode_rep with (n:=n) by auto.
  rewrite unfold_btnode_rep at 1. unfold n. Intros.
  forward.                      (* t'3=t'2->numKeys *)
  simpl.
  gather_SEP 2 3 4 5. replace_SEP 0 (btnode_rep n).
  { entailer!. } gather_SEP 0 3. replace_SEP 0 (btnode_rep root).
  { entailer!. apply wand_frame_elim. } gather_SEP 0 1 2. replace_SEP 0 (relation_rep r).
  { entailer!. } fold c.
  forward_if(PROP ( )
     LOCAL (temp _t'3 (Vint (Int.repr (Z.of_nat (numKeys_le le)))); temp _t'2 pn;
     temp _t'1 (rep_index i); temp _cursor pc)
     SEP (relation_rep r; match (index_eqb i (ip (numKeys n))) with true => cursor_rep (moveToNext c r) r pc | false => cursor_rep c r pc end)).
  - forward_call(c,pc,r).       (* moveToNext(cursor) *)
    entailer!.
    assert (i = ip (numKeys_le le)) by admit. (* OK by H2 *)
    rewrite H10. simpl. admit.                          (* OK *)
  - forward.                                            (* skip *)
    assert (i <> ip (numKeys n)) by admit. (* OK by H2 *)
    entailer!. admit.                                   (* OK *)
  - forward_call(c,pc,r).                               (* moveToNext(cursor) *)
    + admit.                                            (* false *)
    + forward.                                          (* return *)
      entailer!.
      * admit.                  (* todo: cursor_wf & cursor_correct preservation *)
      * admit.                  (* false *)
Admitted.
(* Why is there no match in the POSTCONDITION? *)
        