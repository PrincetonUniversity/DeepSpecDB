(** * verif_curnode.v : Correctness proof of currNode  *)

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

Lemma body_currNode: semax_body Vprog Gprog f_currNode currNode_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)).
  destruct c as [|[n i] c'].
  { destruct H. inv H. inv H2. inv H. inv H1. } (* cursor can't be empty *)
  unfold cursor_rep. Intros anc_end. Intros idx_end.
  assert_PROP( is_pointer_or_null (getval n)).
  { assert(subnode (currNode ((n,i)::c') r) (get_root r)).
    - destruct H.
      + apply partial_cursor_subnode. inv H. auto.
      + apply complete_cursor_subnode. inv H. auto.
    - unfold get_root in H0. simpl in H0.
      unfold relation_rep. rewrite subnode_rep with (n:=n) by auto. entailer!. }
  assert (H99 := partial_complete_length _ _ H H0).
  forward.                      (* t'1=cursor->level *)
  forward.                      (* t'2=cursor->ancestors[t'1] *)
  { entailer!. 
    rewrite app_Znth1. rewrite app_Znth2.
    rewrite Zlength_cons. rewrite Zsuccminusone. rewrite Zlength_rev. rewrite Zlength_map.
    rewrite Zlength_map. replace (Zlength c'-Zlength c') with 0 by lia.
    rewrite Znth_0_cons. auto.
    rewrite Zlength_cons. rewrite Zsuccminusone. rewrite Zlength_rev. rewrite Zlength_map.
    rewrite Zlength_map. lia.
    rewrite Zlength_cons. rewrite Zsuccminusone. rewrite Zlength_app. rewrite Zlength_rev.
    rewrite Zlength_map. rewrite Zlength_map. rewrite Zlength_cons. simpl. lia. }
  forward. entailer!.
  + (*rewrite if_false. rewrite nth_Znth.*)
    rewrite app_Znth1.
    rewrite Zlength_cons.
    simpl.
    replace (Z.succ (Zlength c') - 1) with (Zlength c') by lia.
    rewrite app_Znth2, Zlength_rev, Zlength_map, Zlength_map, Z.sub_diag, Znth_0_cons. auto.
    - rewrite Zlength_rev, Zlength_map, Zlength_map. lia.
    - rewrite Zlength_rev,  map_map, Zlength_cons, Zlength_cons, Zlength_map. lia.
    (*- rewrite Zlength_app, Zlength_rev, map_map, Zlength_cons, Zlength_cons, Zlength_map.
      rewrite Zsuccminusone. split. apply Zlength_nonneg.
      pose proof (Zlength_nonneg anc_end). lia.
    - rewrite Zlength_cons, Zsuccminusone. pose proof (Zlength_nonneg c'). lia. *)
  + unfold cursor_rep. Exists anc_end. Exists idx_end.
    cancel.
Qed.
