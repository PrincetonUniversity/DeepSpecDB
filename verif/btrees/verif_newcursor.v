(** * verif_newcursor.v: Correctness proof of newCursor *)

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

Lemma upd_repeat: forall X i (a:X) b m, 0 <= i -> i < m -> m=MaxTreeDepth ->  
    upd_Znth i (list_repeat (Z.to_nat i) a ++ list_repeat (Z.to_nat (m - i)) b) a =
    (list_repeat (Z.to_nat (i+1)) a) ++ list_repeat (Z.to_nat (m - (i+1))) b.
Proof.
  intros.
  pose proof I.
  pose proof I.
  rewrite Z2Nat.inj_add by lia.
  rewrite <- list_repeat_app.
  replace (m-i) with (1 + (m-(i+1))) by lia.
  rewrite Z2Nat.inj_add by lia.
  rewrite <- list_repeat_app.
  rewrite upd_Znth_app2 by list_solve.
  rewrite app_ass. f_equal. 
  autorewrite with sublist.
  f_equal.
Qed.

Lemma body_NewCursor: semax_body Vprog Gprog f_RL_NewCursor RL_NewCursor_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)). fold r.
  forward_if (PROP() LOCAL(gvars gv; temp _relation prel) SEP(relation_rep r; mem_mgr gv))%assert.
  - unfold relation_rep, r.
    apply denote_tc_test_eq_split; entailer!.
  - unfold abbreviate in POSTCONDITION. forward. entailer!.
  - assert_PROP(False).
    entailer!. contradiction.
  - forward_call (tcursor, gv).
    + split. unfold sizeof. simpl. rep_lia. split; auto.
    + Intros vret.
      forward_if.
      * forward. (*entailer!. Exists (Vint (Int.repr 0)). entailer!.*)
      * forward.                (* cursor->relation=relation *)
        forward.                (* cursor->level=0 *)
        unfold relation_rep. unfold r. Intros.
        forward.                  (* t'3=relation->root *)
{       forward_call(r,empty_cursor,vret,root). (* moveToFirst at level 0 *)
        - instantiate (Frame:=[mem_mgr gv]). unfold Frame.
          unfold relation_rep. unfold r. entailer!.
          unfold cursor_rep.
          do 2 Exists (list_repeat (Z.to_nat MaxTreeDepth) Vundef). 
          unfold empty_cursor. simpl fold_right_sepcon. cancel.
        - repeat split.
          + unfold partial_cursor_correct_rel. simpl. auto.
          + unfold empty_cursor. simpl. auto.
          + auto.
        - unfold cursor_rep. Intros anc_end. Intros idx_end. unfold r.
          forward.              (* return *)
          entailer!.
          Exists vret. entailer!. unfold cursor_rep.
          Exists anc_end. Exists idx_end. cancel. }
Qed.
