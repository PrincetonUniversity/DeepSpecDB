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

Lemma FCI_increase: forall X (le:listentry X) key i,
    idx_to_Z i <= idx_to_Z (findChildIndex' le key i).
Proof.
  intros. generalize dependent i.
  induction le; intros.
  - simpl. omega.
  - destruct e; simpl.
    * destruct (key.(k_) <? k.(k_)). omega.
      eapply Z.le_trans with (m:=idx_to_Z (next_index i)). rewrite next_idx_to_Z. omega.
      apply IHle.
    * destruct (key.(k_) <? k.(k_)). omega.
      eapply Z.le_trans with (m:=idx_to_Z (next_index i)). rewrite next_idx_to_Z. omega.
      apply IHle.
Qed.

Lemma FRI_increase: forall X (le:listentry X) key i,
    idx_to_Z i <= idx_to_Z (findRecordIndex' le key i).
Proof.
  intros. generalize dependent i.
  induction le; intros.
  - simpl. omega.
  - destruct e; simpl.
    * destruct (key.(k_) <=? k.(k_)). omega.
      eapply Z.le_trans with (m:=idx_to_Z (next_index i)). rewrite next_idx_to_Z. omega.
      apply IHle.
    * destruct (key.(k_) <=? k.(k_)). omega.
      eapply Z.le_trans with (m:=idx_to_Z (next_index i)). rewrite next_idx_to_Z. omega.
      apply IHle.
Qed.

Lemma body_findChildIndex: semax_body Vprog Gprog f_findChildIndex findChildIndex_spec.
Proof.
  start_function.
  forward.                      (* i=0 *)
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:= btnode val ptr0 le isLeaf First Last pn). fold n.
  rewrite unfold_btnode_rep. unfold n. Intros ent_end.
  forward.                      (* t'7=node->numKeys *)
  simpl in H. destruct isLeaf; try inv H.
  gather_SEP 0 1 2 3. replace_SEP 0 (btnode_rep n).
  { rewrite unfold_btnode_rep with (n:=n). entailer!. Exists ent_end. entailer!. }

  forward_if (PROP ( )
     LOCAL (temp _t'7 (Vint (Int.repr (Z.of_nat (numKeys (btnode val ptr0 le false First Last pn)))));
     temp _i (Vint (Int.repr 0)); temp _node (getval (btnode val ptr0 le false First Last pn));
     temp _key (key_repr key))  SEP (btnode_rep n)).
  - forward.                    (* skip *)
    entailer!.
  - apply intern_le_cons in H0. destruct H0. destruct H0. rewrite H0 in H. simpl in H.
    pose (num := numKeys_le x0). fold num in H. rewrite Zpos_P_of_succ_nat in H.
    rewrite Int.signed_repr in H. omega.
    split. rep_omega. unfold node_wf in H1. rewrite H0 in H1. simpl in H1. unfold num.
    rep_omega. simpl. auto.
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
      rewrite key_unsigned_repr in H. rewrite key_unsigned_repr in H.
      apply Fcore_Zaux.Zlt_bool_true in H. rewrite H. simpl. auto.
      rewrite unfold_btnode_rep with (n:=(btnode val ptr0 (cons val (keychild val k n0) le') false First Last pn)).
      Exists ent_end0. entailer!.
    + forward.                  (* skip *)
      forward.                  (* i=0 *)
      gather_SEP 0 1 2 3 4 5. replace_SEP 0 (btnode_rep n).
      { rewrite unfold_btnode_rep with (n:=n). unfold n.
        entailer!. Exists ent_end0. entailer!. } deadvars!.
      
{ forward_loop (EX i:Z, PROP(i<=Z.of_nat(numKeys n) -1) LOCAL(temp _i (Vint(Int.repr i)); temp _node pn; temp _key (key_repr key)) SEP(btnode_rep n))
                   break:(EX i:Z, PROP(i=Z.of_nat(numKeys n) -1) LOCAL(temp _i (Vint(Int.repr i)); temp _node pn; temp _key (key_repr key)) SEP(btnode_rep n)).

  - Exists 0. entailer!.
    destruct (Pos.of_succ_nat (numKeys_le le')).
    apply Pos2Z.is_nonneg. apply Pos2Z.is_nonneg. omega.
    
    (* rewrite key_unsigned_repr in H. rewrite key_unsigned_repr in H. *)
    (* apply Z.ge_le in H. *)
    (* apply Fcore_Zaux.Zlt_bool_false in H. rewrite H. *)
    (* replace 0 with (idx_to_Z (ip O)). *)
    (* apply FCI_increase. auto. *)
  - Intros i.
    rewrite unfold_btnode_rep. unfold n. Intros ent_end1.
    forward.                    (* t'5=node->numKeys *)
    gather_SEP 0 1 2 3 4 5 6. replace_SEP 0 (btnode_rep n).
    { rewrite unfold_btnode_rep with (n:=n). unfold n. entailer!. Exists ent_end1. entailer!. } 
    assert((numKeys (btnode val ptr0 (cons val (keychild val k n0) le') false First Last pn)) = S (numKeys_le le')). { simpl. auto. }
    rewrite H3.
    forward_if.
    + entailer!.
      clear -H1. unfold node_wf in H1. simpl in H1.
      rewrite Zpos_P_of_succ_nat.
      rewrite Int.signed_repr.      
      rewrite Int.signed_repr by rep_omega. rep_omega.
      rep_omega.
    + forward.                  (* rest of the loop *)
      admit.                    (* TODO *)
    + forward.                  (* break *)
      Exists (Z.of_nat (numKeys n) -1). entailer!.      
      admit.                    (* TODO *)
  - Intros i.                   (* after the loop *)
    rewrite unfold_btnode_rep. unfold n. Intros ent_end1.
    forward.                    (* t'2=node->numKeys *)
    forward.                    (* return *)
    + entailer!. rewrite Zpos_P_of_succ_nat. unfold node_wf in H1. simpl in H1. clear -H1.
      rewrite Int.signed_repr. rewrite Int.signed_repr.
      rewrite Zsuccminusone. rep_omega. rep_omega. rep_omega.
    + 
      (* prove that numKeys-1 is FCI *)
      admit. }
Admitted.


Lemma body_findRecordIndex: semax_body Vprog Gprog f_findRecordIndex findRecordIndex_spec.
Proof.
  start_function.
  forward.                      (* i=0 *)
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:= btnode val ptr0 le isLeaf First Last pn). fold n.
  forward_if (PROP ( ) LOCAL (temp _i (Vint (Int.repr 0)); temp _node pn; temp _key (key_repr key)) SEP (btnode_rep n)).
Admitted.