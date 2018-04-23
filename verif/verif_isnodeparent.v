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
  forward_call(n,key).
  forward_if(PROP() LOCAL(temp _t'2 (Val.of_bool (negb (isNodeParent n key))); temp _idx (rep_index (findChildIndex n key)); temp _node (getval n); temp _key (Vint (Int.repr key))) SEP (btnode_rep n)).
  - forward.                    (* t'2=1 *)
    entailer!.
    destruct (findChildIndex n key) eqn:FCI.
    unfold isNodeParent. rewrite FCI. simpl. auto.
    inv H1. admit.              (* contradiction in h6 *)
  - destruct n as [ptr0 le isLeaf First Last pn].
    pose (n:=btnode val ptr0 le isLeaf First Last pn).
    rewrite unfold_btnode_rep. simpl. Intros.
    forward.                    (* t'3=node->numKeys *)
    forward.                    (* t'2= (idx==t'3-1) *)
    + admit.                    (* tc_expr *)
    + gather_SEP 0 1 2 3. replace_SEP 0 (btnode_rep n).
      { entailer!. }
      entailer!.
      unfold isNodeParent. fold n.
      destruct (findChildIndex n key) eqn:FCI.
      { unfold findChildIndex, n in FCI. rewrite FCI in H1. simpl in H1. inv H1. }
      rewrite negb_involutive.
      destruct (S n0 =? numKeys n)%nat eqn:Hnum.
      * unfold findChildIndex, n in FCI. rewrite FCI.
        simpl.
        inv Hnum. destruct (numKeys_le le); inv H8.
        assert (Z.of_nat (S n1) -1 = Z.of_nat n1) by admit.
        rewrite H7. admit.      (* true from H9 *)
      * simpl. unfold findChildIndex, n in FCI. rewrite FCI.
        simpl.
        admit.                  (* ok from Hnum *)
  - forward_if.
    + forward.                  (* return *)
      rewrite H1. entailer!.
    + forward.                  (* skip *)
      forward.                  (* return *)
      rewrite H1. entailer!.
Admitted.