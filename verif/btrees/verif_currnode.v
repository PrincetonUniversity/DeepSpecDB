(** * verif_curnode.v : Correctness proof of currNode  *)

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
Require Import verif_entryindex.

Lemma body_currNode: semax_body Vprog Gprog f_currNode currNode_spec.
Proof.
  start_function.
  destruct r as [root prel].
  pose (r:=(root,prel)).
  destruct c as [|[n i] c'].
  { destruct H; inv H; inv H2. inv H. inv H1. } (* cursor can't be empty *)
  unfold cursor_rep. Intros anc_end. Intros idx_end.
  assert_PROP( is_pointer_or_null (getval n)).
  { assert(subnode (currNode ((n,i)::c') r) (get_root r)).
    - destruct H.
      + apply partial_cursor_subnode. inv H. auto.
      + apply complete_cursor_subnode. inv H. auto.
    - unfold get_root in H0. simpl in H0.
      unfold relation_rep. rewrite subnode_rep with (n:=n) by auto. entailer!. }
  forward.                      (* t'1=cursor->level *)
  forward.                      (* t'2=cursor->ancestors[t'1] *)
  { entailer!. apply partial_complete_length with (r:=r). unfold r. auto. auto. }
  { entailer!. 
    rewrite app_Znth1. rewrite app_Znth2.
    rewrite Zlength_cons. rewrite Zsuccminusone. rewrite Zlength_rev. rewrite Zlength_map.
    rewrite Zlength_map. assert(Zlength c'-Zlength c' = 0) by omega. rewrite H9.
    rewrite Znth_0_cons. auto.
    rewrite Zlength_cons. rewrite Zsuccminusone. rewrite Zlength_rev. rewrite Zlength_map.
    rewrite Zlength_map. omega.
    rewrite Zlength_cons. rewrite Zsuccminusone. rewrite Zlength_app. rewrite Zlength_rev.
    rewrite Zlength_map. rewrite Zlength_map. rewrite Zlength_cons. simpl. omega. }
  forward. entailer!.
  + rewrite if_false. rewrite nth_Znth.
    rewrite app_Znth1.
    rewrite Zlength_cons. rewrite app_Znth2.
    rewrite Zlength_rev. rewrite Zlength_map. rewrite Zlength_map.
    assert((Z.succ (Zlength c') - 1 - Zlength c') = 0) by omega. rewrite H10.
    rewrite Znth_0_cons. auto.
    rewrite Zlength_rev. rewrite Zlength_map. rewrite Zlength_map. omega.
    rewrite Zlength_app. rewrite Zlength_rev. rewrite Zlength_map. rewrite Zlength_map.
    rewrite Zlength_cons. rewrite Zsuccminusone. rewrite Zlength_cons. simpl. omega.
    rewrite Zlength_cons. rewrite Zsuccminusone. rewrite Zlength_app. rewrite Zlength_app.
    rewrite Zlength_rev. rewrite Zlength_map. rewrite Zlength_map.
    rewrite Zlength_cons. simpl. assert(0 <= Zlength anc_end) by apply Zlength_nonneg.
    assert(0<=Zlength c') by apply Zlength_nonneg.
    omega. rewrite Zlength_cons. rewrite Zsuccminusone.
    assert(0<=Zlength c') by apply Zlength_nonneg. omega.
  + unfold cursor_rep. Exists anc_end. Exists idx_end.
    cancel.
Qed.