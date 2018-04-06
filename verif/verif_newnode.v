(** * verif_newnode.v: Correctness proof of createNewNode *)

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

Lemma body_createNewNode: semax_body Vprog Gprog f_createNewNode createNewNode_spec.
Proof.
  start_function.
  forward_call (tbtnode).
  - split. simpl. rep_omega.
    split; auto.
  - Intros vret.
    forward_if (PROP (vret<>nullval)
     LOCAL (temp _newNode vret; temp _isLeaf (Val.of_bool isLeaf); temp _FirstLeaf (Val.of_bool FirstLeaf); temp _LastLeaf (Val.of_bool LastLeaf))
     SEP (if eq_dec vret nullval
          then emp
          else malloc_token Tsh tbtnode vret * data_at_ Tsh tbtnode vret; emp)).
    + if_tac; entailer.
    + forward. rewrite if_true; auto.
      Exists nullval. entailer!. 
    + forward. rewrite if_false; auto. entailer!.
    + Intros. rewrite if_false; auto. Intros.
      forward.                  (* newNode->numKeys = 0 *)
      unfold default_val. simpl.
      forward.                  (* newnode->isLeaf=isLeaf *)
      forward.                  (* newnode->FirstLeaf=FirstLeaf *)
      forward.                  (* newnode->LastLeaf=LastLeaf *)
      forward.                  (* newnode->ptr0=null *)
      forward.                  (* return newnode *)
      Exists vret. rewrite if_false by auto.
      entailer!. unfold_data_at 1%nat. entailer!. apply derives_refl.
Qed.