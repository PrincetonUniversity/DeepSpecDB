(** * verif_getrecord.v : Correctness proof of RL_GetRecord  *)

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
Require Import verif_entryindex.
Require Import verif_currnode.
Require Import verif_isvalid.
Require Import index.

Lemma body_RL_GetRecord: semax_body Vprog Gprog f_RL_GetRecord RL_GetRecord_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)).
  destruct c as [|[n i] c'].
  { destruct H; inv H; inv H2. }
  pose (c:=(n,i)::c').
  forward_call(r,c,pc,numrec).  (* t'1=isValid(cursor) *)
  { unfold r. unfold c. cancel. }
  forward_if (PROP () LOCAL (temp _cursor pc) SEP (relation_rep (root, prel) numrec; cursor_rep ((n, i) :: c') (root, prel) pc)).
  - forward.                    (* skip *)
    unfold r. unfold c. entailer!.
  - assert_PROP(False). fold c r in H1. rewrite H1 in H4. simpl in H4. inv H4. contradiction.
  - forward_call(r,c,pc,numrec). (* t'2=entryIndex(cursor) *)
    { fold r c. cancel. }
    forward_call(r,c,pc,numrec). (* t'3=currnode(cursor) *)
    unfold c. simpl.
    assert(SUBNODE: subnode n root).
    { destruct H. apply complete_cursor_subnode in H. simpl in H. auto. }
    assert(SUBREP: subnode n root) by auto. apply subnode_rep in SUBREP.
    rewrite SUBREP.
    destruct n as [ptr0 le isLeaf First Last pn].
    pose (n:=btnode val ptr0 le isLeaf First Last pn). fold n.
    rewrite unfold_btnode_rep with (n:=n) at 1. unfold n.
    Intros ent_end.
    forward.                    (* t'7=t'3->numKeys *)
    gather_SEP 2 3 4 5. replace_SEP 0 (btnode_rep n).
    { entailer!. rewrite unfold_btnode_rep. unfold n. Exists ent_end. entailer!. }
    gather_SEP 0 3. replace_SEP 0 (btnode_rep root).
    { entailer!. unfold n. apply wand_frame_elim. }
    gather_SEP 0 1 2. replace_SEP 0 (relation_rep r numrec).
    { entailer!. } deadvars!. simpl numKeys. fold n. fold n in c. fold c.
    pose (normc := match index_eqb i (ip (numKeys n)) with
                   | true => moveToNext c r
                   | false => c
                   end).
    forward_if(PROP ( )
     LOCAL (temp _t'7 (Vint (Int.repr (Z.of_nat (numKeys_le le))));
     temp _t'2 (Vint (Int.repr (rep_index i))); temp _cursor pc)
     SEP (relation_rep r numrec; cursor_rep normc r pc; emp)).
    { forward_call(c,pc,r,numrec).
      entailer!. unfold normc. simpl.
      apply (f_equal Int.signed) in H4.
      unfold root_wf, node_wf, n in H2. apply H2 in SUBNODE. simpl in SUBNODE.
      rewrite Int.signed_repr in H4.
      rewrite Int.signed_repr in H4.
      destruct i as [|ii]. simpl in H4. omega.
      simpl in H4. apply Nat2Z.inj in H4. subst. simpl.
      rewrite Nat.eqb_refl. cancel.
      rep_omega. destruct H. apply complete_correct_rel_index in H.
      destruct i. simpl. rep_omega. simpl in H. simpl. rep_omega. }
    { forward.                  (* skip *)
      entailer!. unfold normc.
      admit. }
    forward_call(r,normc,pc,numrec). (* t'4=currnode(cursor) *)
    split. right. admit. auto.
    forward_call(r,normc,pc,numrec). (* t'5=entryIndex(cursor) *)
    split. right. admit. auto.
    unfold relation_rep. unfold r.
    rewrite SUBREP. fold n. rewrite unfold_btnode_rep with (n:=n) at 1. unfold n.
    autorewrite with norm.
    (* Intros ent_end. *)
    admit.
Admitted.