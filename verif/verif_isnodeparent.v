(** * verif_isnodeparent.v : Correctness proof of isNodeParent *)

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
Require Import verif_findindex.

Lemma body_isNodeParent: semax_body Vprog Gprog f_isNodeParent isNodeParent_spec.
Proof.
  start_function.
  destruct n as [ptr0 le isLeaf First Last pn].
  pose (n:=btnode val ptr0 le isLeaf First Last pn).
  rewrite unfold_btnode_rep. Intros ent_end.
  forward.                      (* t'5 = node->isLeaf *)
  { entailer!. destruct isLeaf; simpl; auto. }
  forward_if.
{                               (* Leaf Node *)
  assert(LEAF: isLeaf = true).
  { destruct isLeaf; auto. simpl in H1. inv H1. } subst.
  forward.                       (* t'10 = node->numKeys *)
  gather_SEP 0 1 2 3. replace_SEP 0 (btnode_rep n).
  { entailer!. rewrite unfold_btnode_rep with (n:=n). Exists ent_end. entailer!. }
  forward_if.
  - forward.                    (* return. *)
    entailer!. destruct le as [|e le']. auto.
    simpl in H2. unfold node_wf in H0. simpl in H0. rewrite Fanout_eq in H0. exfalso.
    rewrite Zpos_P_of_succ_nat in H2. apply (f_equal Int.unsigned) in H2.
    autorewrite with norm in H2. omega.
  - forward.                    (* skip *)
    assert(NELE: numKeys_le le <> O).
    { destruct le. simpl in H2. contradiction. simpl. omega. }
    destruct le as [|e le']. simpl in NELE. contradiction.
    pose (le:= cons val e le'). fold le.
    rewrite unfold_btnode_rep. clear ent_end. unfold n. Intros ent_end.
    forward.                    (* lowest=node->entries[0]->key *)
    { unfold le. simpl. rewrite Znth_0_cons. destruct e; simpl; entailer!. }
    forward.                    (* t'9=node->numKeys *)
    forward.                    (* highest=node->entries[t'9-1] *)
    + rewrite Zpos_P_of_succ_nat. entailer!. rewrite Zsuccminusone.
      unfold node_wf in H0. simpl in H0. rewrite Fanout_eq in H0. omega.
    + admit.                    (* should be ok, do we need to split le? *)
    + entailer!. rewrite Zpos_P_of_succ_nat. unfold node_wf in H0. simpl in H0. rewrite Fanout_eq in H0.
      rewrite Int.signed_repr. rewrite Int.signed_repr.
      rewrite Zsuccminusone. 
      rep_omega. rep_omega. rep_omega.
    + admit.
} {                             (* Intern Node *)
  assert(INTERN: isLeaf = false).
  { destruct isLeaf; auto. simpl in H1. inv H1. } subst.
  gather_SEP 0 1 2 3. replace_SEP 0 (btnode_rep n).
  { entailer!. rewrite unfold_btnode_rep with (n:=n). Exists ent_end. entailer!. }
  forward_call(n,key).
  { split3. unfold n. simpl. auto. auto. auto. }
  forward_if(PROP() LOCAL(temp _t'4 (Val.of_bool (negb (isNodeParent n key))); temp _idx (Vint(Int.repr((rep_index (findChildIndex n key))))); temp _node pn; temp _key (key_repr key)) SEP (btnode_rep n)).
  - forward.                    (* t'4=1 *)
    entailer!.
    destruct (findChildIndex n key) eqn:FCI.
    simpl in FCI. rewrite FCI. auto.
    simpl in FCI. rewrite FCI in H2. simpl in H2.
    apply (f_equal Int.unsigned) in H2.
    assert(Z.of_nat n0 < Z.of_nat Fanout).
    { assert(-1 <= idx_to_Z (findChildIndex n key) < Z.of_nat (numKeys n)) by apply FCI_inrange.
      simpl in H4. rewrite FCI in H4. simpl in H4.
      unfold node_wf in H0. simpl in H0. omega. }
    rewrite Fanout_eq in H4. simpl in H4. autorewrite with norm in H2.
    rewrite H2 in H4. compute in H4. inv H4.
  - rewrite unfold_btnode_rep. unfold n. Intros ent_end0.
    forward.                    (* t'6=node->numKeys *)
    forward.                    (* t'4= (idx==t'6-1) *)
    { entailer!. unfold node_wf in H0. simpl in H0. rewrite Fanout_eq in H0.
      rewrite Int.signed_repr. rewrite Int.signed_repr.
      rep_omega. rep_omega. rep_omega. }
    gather_SEP 0 1 2 3. replace_SEP 0 (btnode_rep n).
    { entailer!. rewrite unfold_btnode_rep. Exists ent_end0. entailer!. }
    entailer!.
    destruct (findChildIndex' le key im) eqn:FCI'.
    { simpl in H2. contradiction. }
    rewrite negb_involutive. simpl.
    destruct (S n0 =? numKeys_le le)%nat eqn:HNUM.
    + destruct (numKeys_le le).
      apply beq_nat_true in HNUM. omega.
      apply beq_nat_true in HNUM. inv HNUM.
      replace (Z.of_nat (S n1) -1) with (Z.of_nat n1).
      rewrite Int.eq_true. rewrite Nat.eqb_refl. simpl. auto.
      rewrite Nat2Z.inj_succ. rewrite Zsuccminusone. auto.
    + apply beq_nat_false in HNUM.
      destruct(Int.eq (Int.repr (Z.of_nat n0)) (Int.repr (Z.of_nat (numKeys_le le) - 1))) eqn:HEQ.
      { unfold node_wf in H0. rewrite Fanout_eq in H0. simpl in H0.
        apply eq_sym in HEQ. apply binop_lemmas2.int_eq_true in HEQ. exfalso.
        apply (f_equal Int.unsigned) in HEQ.
        rewrite Int.unsigned_repr in HEQ. rewrite Int.unsigned_repr in HEQ.
        assert(Z.of_nat (S n0) = Z.of_nat (numKeys_le le)) by omega.
        apply Nat2Z.inj in H5. rewrite H5 in HNUM. contradiction.
        split. destruct le. simpl in FCI'. inv FCI'. simpl numKeys_le.
        rewrite Nat2Z.inj_succ. rewrite Zsuccminusone. omega.
        rep_omega.
        split. omega.
        assert(-1 <= idx_to_Z (findChildIndex n key) < Z.of_nat (numKeys n)) by apply FCI_inrange.
        simpl in H5. rewrite FCI' in H5. simpl in H5. rep_omega. }      
      destruct (numKeys_le le).
      simpl. auto. destruct (n0 =? n1)%nat eqn:HEQ2.
      apply beq_nat_true in HEQ2. subst. contradiction. simpl. auto.      
  - forward_if.
    + forward.                  (* return 0 *)
      entailer!.
      rewrite H2. simpl. auto.
    + forward.                  (* skip *)
      forward.                  (* return 1 *)
      rewrite H2. entailer!.
Admitted.    
