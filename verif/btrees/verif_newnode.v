(** * verif_newnode.v: Correctness proof of createNewNode *)

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

Lemma body_createNewNode: semax_body Vprog Gprog f_createNewNode createNewNode_spec.
Proof.
  start_function.
  forward_call (tbtnode, gv).       (* t'1=malloc(sizeof tbtnode) *)
  - split. simpl. rep_lia.
    split; auto.
  - Intros vret.
    forward_if (PROP (vret<>nullval)
     LOCAL (temp _newNode vret; temp _isLeaf (Val.of_bool isLeaf); temp _First (Val.of_bool First); temp _Last (Val.of_bool Last))
     SEP (mem_mgr gv; malloc_token Ews tbtnode vret; data_at_ Ews tbtnode vret; emp)).
    + forward.                  (* return null *)
    + forward. entailer!.
    + Intros. 
      forward.                  (* newNode->numKeys = 0 *)
      unfold default_val. simpl.
      forward.                  (* newnode->isLeaf=isLeaf *)
      forward.                  (* newnode->First=First *)
      forward.                  (* newnode->Last=Last *)
      forward.                  (* newnode->ptr0=null *)
      forward.                  (* return newnode: 2,79 min *)
      Exists vret. entailer!.
      Exists (list_repeat 15 (Vundef, (inl Vundef):(val+val))).
      simpl. cancel.
Qed.
