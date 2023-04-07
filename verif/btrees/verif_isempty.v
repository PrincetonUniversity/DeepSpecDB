(** * verif_isvalid.v : Correctness proof of isValid, isFirst and RL_CursorIsValid *)

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

Lemma body_isempty : semax_body Vprog Gprog f_RL_IsEmpty RL_IsEmpty_spec.
Proof.
  start_function. 
  forward_if (PROP ( cursor <> nullval )
                   LOCAL (gvars gv; temp _cursor cursor)
                   SEP (mem_mgr gv; relation_rep r ; cursor_rep c r cursor)).
  + forward. entailer.
  + subst cursor.
    unfold cursor_rep. assert_PROP False.
  - Intros a b. destruct r. rewrite data_at_isptr. entailer.
  - contradiction.
    + unfold cursor_rep. destruct r. Intros anc_end idx_end. forward.
      unfold relation_rep. Intros. forward.
      destruct n. simpl getval. unfold btnode_rep; fold btnode_rep.
      
      Intros ent_end.
      forward.
      Intros. forward_if.
      forward. entailer!. unfold node_le.
      destruct (eq_dec (Int.repr (Zlength le)) (Int.repr 0)).
      auto. contradiction.
      * unfold relation_rep, cursor_rep; entailer!. (* This proof is not so pretty. *)
        Exists anc_end. entailer. Exists idx_end. entailer.
        unfold btnode_rep. fold btnode_rep. Exists ent_end. entailer!.
      * forward. entailer!. unfold node_le.
        destruct (eq_dec (Int.repr (Zlength le)) (Int.repr 0)).
        contradiction. auto.
        unfold cursor_rep, relation_rep. entailer!.
        Exists anc_end. entailer!. Exists idx_end. entailer!.
        unfold btnode_rep. fold btnode_rep. 
        Exists ent_end. entailer!.
Qed.
