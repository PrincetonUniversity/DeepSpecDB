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
  destruct r as [[[root numRec] depth] prel].
  pose (r:=(root,numRec,depth,prel)).
  unfold cursor_rep. Intros anc_end. Intros idx_end.
  forward.                      (* t'1=cursor->level *)
  forward.                      (* t'2=cursor->ancestors[t'1] *)
  entailer!. inv H. split. omega. rewrite MTD_eq in H9. assert (Z.of_nat 20 = 20). simpl. auto. omega.
  (* TODO: rep_omega? *)
  destruct c as [|[n i] c']. { inv H. inv H0. } assert_PROP( is_pointer_or_null (getval n)).
  { apply cursor_rel_subnode in H0. unfold get_root in H0. simpl in H0.
    unfold relation_rep. rewrite subnode_rep with (n:=n) by auto. entailer!. }
  - entailer!. 
    rewrite app_Znth1.
    assert((Zlength ((n, i) :: c') - 1) = Zlength c').
    rewrite Zlength_cons. rep_omega. rewrite H9.
    rewrite app_Znth2. rewrite Zlength_rev. rewrite Zlength_map. rewrite Zlength_map.
    assert (Zlength c' - Zlength c' = 0) by omega. rewrite H10. rewrite Znth_0_cons. auto.
    rewrite Zlength_rev. rewrite Zlength_map. rewrite Zlength_map. omega.
    rewrite Zlength_app. rewrite Zlength_rev. rewrite Zlength_map. rewrite Zlength_map.
    rewrite Zlength_cons. rewrite Zlength_cons. simpl. omega.
  - forward. entailer!.
    + rewrite app_Znth1. destruct c. inv H. inv H9.
      rewrite Zlength_cons. simpl. destruct p. rewrite app_Znth2. simpl.
      rewrite Zlength_rev. rewrite Zlength_map. rewrite Zlength_map.
      assert((Z.succ (Zlength c) - 1 - Zlength c) = 0) by omega. rewrite H9. rewrite Znth_0_cons. auto.
      rewrite Zlength_rev. rewrite Zlength_map. rewrite Zlength_map. omega.
      rewrite Zlength_rev. rewrite Zlength_map. rewrite Zlength_map. omega.
    + unfold cursor_rep. Exists anc_end. Exists idx_end.
      cancel.
Qed.

