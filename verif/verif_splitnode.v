(** * verif_splitnode.v : Correctness proof of splitnode *)

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
Require Import verif_newnode.
Require Import verif_findindex.

Lemma body_splitnode: semax_body Vprog Gprog f_splitnode splitnode_spec.
Proof.
  start_function.
  destruct n as [ptr0 le isLeaf First Last nval].
  pose(n:=btnode val ptr0 le isLeaf First Last nval).
  destruct(entry_val_rep e) as [keyrepr coprepr] eqn:HEVR.
  assert(exists k, keyrepr = key_repr k).
  { destruct e; exists k; simpl; simpl in HEVR; inv HEVR; auto. }
  destruct H1 as [k HK].
  forward.                      (* t'8=entry->key *)
  forward_call(n,k).            (* t'1=findrecordindex(node,t'8) *)
  { fold n. cancel. }
  { split; auto. unfold node_wf. fold n in H0. omega. }
  forward.                      (* tgtIdx=t'1 *)
  forward.                      (* j=0 *)
  forward.                      (* inserted=0 *)
  (* forward_loop *)
  admit.
Admitted.