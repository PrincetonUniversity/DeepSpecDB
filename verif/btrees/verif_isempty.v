(** * verif_isvalid.v : Correctness proof of isValid, isFirst and RL_CursorIsValid *)

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

Lemma body_isempty : semax_body Vprog Gprog f_RL_IsEmpty RL_IsEmpty_spec.
Proof.
  start_function. 
  forward_if (PROP ( cursor <> nullval )
                   LOCAL (gvars gv; temp _cursor cursor)
                   SEP (mem_mgr gv; relation_rep r (get_numrec r); cursor_rep c r cursor)).
  + forward. entailer.
  + subst cursor.
    unfold cursor_rep. assert_PROP False.
  - Intros a b. destruct r. rewrite data_at_isptr. entailer.
  - contradiction.
    + unfold cursor_rep. destruct r. Intros anc_end idx_end. forward.
      unfold relation_rep. Intros. forward.
      destruct n. simpl getval. unfold btnode_rep; fold btnode_rep; fold le_iter_sepcon.
      Intros ent_end.
      forward.
      Intros. forward_if.
      forward. entailer!. simpl numKeys.
      replace (numKeys_le l) with 0%nat.
      * easy.
      * apply Nat2Z.inj, repr_inj_unsigned.
        easy. split. omega. 
        transitivity (Z.of_nat Fanout).
        -- apply inj_le. replace (numKeys_le l) with (numKeys (btnode val o l b b0 b1 v0)) by reflexivity.
           apply H. apply sub_refl.
        -- easy.
        -- easy.
      * unfold relation_rep, cursor_rep; entailer!. (* This proof is not so pretty. *)
        Exists anc_end. entailer. Exists idx_end. entailer.
        unfold btnode_rep. fold btnode_rep. fold le_iter_sepcon. Exists ent_end. entailer!.
      * forward. entailer!. simpl. 
        destruct (nat_eq_dec (numKeys_le l) 0%nat). 
        destruct l. simpl in H1. contradiction. inversion e. reflexivity.
        unfold cursor_rep, relation_rep. entailer!.
        Exists anc_end. entailer!. Exists idx_end. entailer!.
        unfold btnode_rep. fold btnode_rep. fold le_iter_sepcon.
        Exists ent_end. entailer!.
Qed.
