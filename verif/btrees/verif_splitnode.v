(** * verif_splitnode.v : Correctness proof of splitnode *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import btrees.relation_mem.
Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.
Require Import btrees.btrees.
Require Import btrees.btrees_sep.
Require Import btrees.btrees_spec. 
Require Import btrees.verif_splitnode_part2. (*For splitnode_main_if_then_proof.*)
Require Import btrees.verif_splitnode_part4. (*For splitnode_main_if_else_proof.*)

Opaque Znth.

Lemma body_splitnode: semax_body Vprog Gprog f_splitnode splitnode_spec.
Proof.
  start_function.
  rename H1 into LEAFENTRY.
  destruct n as [ptr0 le isLeaf First Last nval].
  simpl in H0.
  pose(n:=btnode val ptr0 le isLeaf First Last nval).
  destruct(entry_val_rep e) as [keyrepr coprepr] eqn:HEVR.
  assert(exists k, keyrepr = Vptrofs k).
  { destruct e; exists k; simpl; simpl in HEVR; inv HEVR; auto. }
  destruct H1 as [k HK].
  subst keyrepr.
  forward.                      (* t'28=entry->key *)
  forward_call(n,k).            (* t'1=findrecordindex(node,t'28) *)
  { fold n. cancel. }
  { split; auto.  unfold node_wf. simpl. lia. }
  forward.                      (* tgtIdx=t'1 *)
  assert(INRANGE: 0 <= findRecordIndex n k <= Zlength le) by apply FRI_inrange.
  fold n in H0. rewrite H0 in INRANGE.
  rewrite unfold_btnode_rep. unfold n. Intros ent_end.
  forward.                      (* t'27=node->Last *)
  { destruct Last; entailer!. }
  forward_call(isLeaf, false, Last, gv). (* t'2=createNewNode(isLeaf,0,t'27 *)
  Intros vnewnode.
  forward.                      (* newnode=t'2 *)
  sep_apply (fold_btnode_rep ptr0). fold n.
  clear ent_end.
  forward_if(PROP (vnewnode<>nullval)
     LOCAL (temp _newNode vnewnode; temp _t'2 vnewnode; temp _t'27 (Val.of_bool Last);
     temp _tgtIdx (Vint (Int.repr (findRecordIndex' le k 0)));
     temp _t'1 (Vint (Int.repr (findRecordIndex' le k 0))); 
     temp _t'28 (Vptrofs k); lvar _allEntries (tarray (Tstruct _Entry noattr) 16) v_allEntries;
     temp _node nval; temp _entry pe; temp _isLeaf (Val.of_bool isLeaf))
     SEP (mem_mgr gv; btnode_rep n; btnode_rep (empty_node isLeaf false Last vnewnode);
     data_at_ Tsh (tarray (Tstruct _Entry noattr) 16) v_allEntries; entry_rep e;
     data_at Ews tentry (Vptrofs k, coprepr) pe)).
  { apply denote_tc_test_eq_split. replace vnewnode with (getval (empty_node isLeaf false Last vnewnode)).
    entailer!. simpl. auto. entailer!. }
  { forward.                    (* skip *)
    entailer!. }
  { assert_PROP(False). entailer!. contradiction. }
  rewrite unfold_btnode_rep with (n:=n). unfold n. Intros ent_end.
  forward.                      (* node->Last = 0 *)
  forward.                      (* t'3=node->isLeaf *)
  forward_if.
 - (* leaf node *)
 apply splitnode_main_if_then_proof; auto.
  -   (* intern node *)
 apply splitnode_main_if_else_proof; auto.
Qed.