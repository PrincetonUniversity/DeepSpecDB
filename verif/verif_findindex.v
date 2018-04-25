(** * verif_findindex.v : Correctness proof of findChildIndex and findRecordIndex *)

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
Require Import index.

Lemma body_findChildIndex: semax_body Vprog Gprog f_findChildIndex findChildIndex_spec.
Proof.
  start_function.
  forward.                      (* i=0 *)
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:= btnode val ptr0 le isLeaf First Last pn). fold n.
  rewrite unfold_btnode_rep. unfold n. Intros ent_end.
  forward.                      (* t'7=node->numKeys *)
  simpl in H. destruct isLeaf; try inv H.
  gather_SEP 0 1 2 3. replace_SEP 0 (btnode_rep n). { entailer!. Exists ent_end. entailer!. }

  forward_if (PROP ( )
     LOCAL (temp _t'7 (Vint (Int.repr (Z.of_nat (numKeys (btnode val ptr0 le false First Last pn)))));
     temp _i (Vint (Int.repr 0)); temp _node (getval (btnode val ptr0 le false First Last pn));
     temp _key (Vint (Int.repr key)))  SEP (btnode_rep n)).
  - forward.                    (* skip *)
    entailer!.
  - apply intern_le_cons in H0. destruct H0. destruct H0. rewrite H0 in H. simpl in H.
    (* contradiction in H *)
    admit. simpl. auto.
  - destruct le as [|e le'] eqn:HLE.
    { apply intern_le_cons in H0. destruct H0. destruct H. inv H. simpl. auto. }
    destruct e eqn:HE.
    simpl in H0.
    destruct ptr0; try inv H0.  (* keyval isn't possible in an intern node *)
    rewrite unfold_btnode_rep. unfold n. simpl. Intros ent_end0.
    forward.                    (* t'6=node->entries[0]->key *)
    forward_if.
    + forward.                  (* return *)
      entailer!. unfold findChildIndex'. simpl.
      assert (key <? k = true).
      admit.                    (* true because of H *)
      rewrite H5. Exists ent_end0. entailer!.
    + forward.                  (* skip *)
      forward.                  (* i=0 *)
      gather_SEP 0 1 2 3 4 5. replace_SEP 0 (btnode_rep n). { entailer!. Exists ent_end0. entailer!. } deadvars!.
      
{ forward_loop (EX i:Z, PROP(i<=idx_to_Z (findChildIndex n key)) LOCAL(temp _i (Vint(Int.repr i)); temp _node pn; temp _key (Vint(Int.repr key))) SEP(btnode_rep n))
                   break:(EX i:Z, PROP(i=idx_to_Z (findChildIndex n key)) LOCAL(temp _i (Vint(Int.repr i)); temp _node pn; temp _key (Vint(Int.repr key))) SEP(btnode_rep n)).

  - Exists 0. entailer!.
    assert (key <? k = false). admit.   (* true from H *)
    rewrite H1.
    admit.                      (* OK because fCI' is called with ip 0 *)
  - Intros i.
    rewrite unfold_btnode_rep. unfold n. Intros ent_end1.
    forward.                    (* t'5=node->numKeys *)
    gather_SEP 0 1 2 3 4 5 6. replace_SEP 0 (btnode_rep n). { entailer!. Exists ent_end1. entailer!. } 
    assert((numKeys (btnode val ptr0 (cons val (keychild val k n0) le') false First Last pn)) = S (numKeys_le le')). simpl. auto.
    rewrite H2.
    forward_if.
    + entailer!. admit.         (* le not to large *)
    + forward.                  (* skip *)
      admit.                    (* TODO *)
    + forward.                  (* break *)
      Exists (idx_to_Z (findChildIndex n key)). entailer!.
      admit.                    (* TODO *)
  - Intros i.
    admit. }                    (* TODO *)
Admitted.


Lemma body_findRecordIndex: semax_body Vprog Gprog f_findRecordIndex findRecordIndex_spec.
Proof.
  start_function.
  forward.                      (* i=0 *)
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:= btnode val ptr0 le isLeaf First Last pn). fold n.
  forward_if (PROP ( ) LOCAL (temp _i (Vint (Int.repr 0)); temp _node pn; temp _key (Vint (Int.repr key))) SEP (btnode_rep n)).
  - apply denote_tc_test_eq_split.
    admit.                      (* valid pointer *)
    entailer!.
  - forward.                    (* skip *)
    entailer!.
  - assert_PROP(False). unfold btnode_rep. entailer!.
    admit.                      (* offset_val 20 p = nullval should be a contradiction? *)
    contradiction.
  - rewrite unfold_btnode_rep. unfold n. Intros.
    forward.                    (* t'5=node->numKeys *)
    gather_SEP 0 1 2 3. replace_SEP 0 (btnode_rep n). { entailer!. }
    { forward_if(PROP ( ) LOCAL (temp _t'5 (Vint (Int.repr (Z.of_nat (numKeys (btnode val ptr0 le isLeaf First Last pn))))); temp _i (Vint (Int.repr 0)); temp _node pn; temp _key (Vint (Int.repr key))) SEP (btnode_rep n)).
      - forward.                (* skip *)
        entailer!.
      - admit.
        (* contradiction in H1 *)
      - rewrite unfold_btnode_rep. unfold n. Intros.
        forward.                (* t'4=node->numKeys *)
        forward_if.
        + forward.              (* return *)
          entailer!.
          assert(le= nil val). admit. (* true from H1 *)
          rewrite H5. simpl. auto.
        + forward.              (* skip *)
          forward.              (* i=0 *)
          gather_SEP 0 1 2 3. replace_SEP 0 (btnode_rep n). { entailer!. } deadvars!.
{ forward_loop (EX i:Z, (PROP (i<= Z.of_nat (numKeys_le le))
     LOCAL (temp _i (Vint (Int.repr i)); temp _node pn; temp _key (Vint (Int.repr key)))
     SEP (btnode_rep n)))
               break:(EX i:Z, (PROP (i= Z.of_nat(numKeys_le le))
     LOCAL (temp _i (Vint (Int.repr i)); temp _node pn; temp _key (Vint (Int.repr key)))
     SEP (btnode_rep n))).
  - Exists 0. entailer!.
  - Intros i. rewrite unfold_btnode_rep. unfold n. Intros.
    forward.                    (* t'3=node->numKeys *)
    forward_if.
    + entailer!. admit.
    + forward. admit.
    + forward. admit.
  - Intros i. rewrite unfold_btnode_rep. unfold n. Intros.
    forward.                    (* t'1=node->numKeys *)
    forward.                    (* return *)
    entailer!.
    admit.                      (* loop invariant isn't strong enough *) } }
Admitted.