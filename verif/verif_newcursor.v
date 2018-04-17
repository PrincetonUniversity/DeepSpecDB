(** * verif_newcursor.v: Correctness proof of newCursor *)

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
Require Import verif_movetofirst.

Lemma upd_repeat: forall X i (a:X) b m, 0 <= i -> (Z.to_nat i < m)%nat -> m=MaxTreeDepth ->  
    upd_Znth i (list_repeat (Z.to_nat i) a ++ list_repeat (m - Z.to_nat i) b) a =
    (list_repeat (Z.to_nat (i+1)) a) ++ list_repeat (m - Z.to_nat (i+1)) b.
Proof.
  intros. assert (Z.to_nat (i + 1) = ((Z.to_nat i) + S O)%nat).
  rewrite Z2Nat.inj_add; auto. omega.
  rewrite H2.
  rewrite <- list_repeat_app.
  rewrite upd_Znth_app2. 
  rewrite Zlength_list_repeat by auto.
  simpl. assert (i-i=0). omega. rewrite H3.
  unfold upd_Znth. simpl.
  assert ((m - (Z.to_nat i))%nat = Z.to_nat (20-i)). admit.
  assert ((m - (Z.to_nat i + 1))%nat = Z.to_nat (20-i-1)). admit.
  rewrite H4. rewrite H5.
  rewrite sublist_list_repeat.
  rewrite Zlength_list_repeat. rewrite <- app_assoc. auto.
  admit.                        (* OK *)
  omega.
  rewrite Zlength_list_repeat. split; auto.
  admit.                        (* OK *)
  apply Z.le_refl.
  admit.                        (* OK *)
  rewrite Zlength_list_repeat. split. apply Z.le_refl.
  assert ((m - (Z.to_nat i))%nat = Z.to_nat (20-i)). admit.
  rewrite H3. admit.              (* OK *)
  auto.
Admitted.

Lemma body_NewCursor: semax_body Vprog Gprog f_RL_NewCursor RL_NewCursor_spec.
Proof.
  start_function.
  destruct r as [[[root numRec] depth] prel].
  pose (r:=(root,numRec,depth,prel)). fold r.
  forward_if (PROP() LOCAL(temp _relation p) SEP(relation_rep r p))%assert.
  - forward. auto.
  - subst p.
    assert_PROP(False).
    entailer!. contradiction.
  - forward_call tcursor.
    + split. unfold sizeof. simpl. rep_omega. split; auto.
    + Intros vret.
      forward_if.
      * if_tac; entailer!.
      * rewrite if_true; auto.
        forward. Exists nullval. Exists p'. entailer!.
      * rewrite if_false; auto. Intros.
        forward.                (* skip *)
        forward.                (* cursor->relation=relation *)
        forward.                (* cursor->level=0 *)
        unfold relation_rep. unfold r. Intros proot.
        forward.                  (* t'3=relation->root *)
        simpl. entailer!. unfold local. unfold lift1. entailer!.
        admit.
{       forward_call(r,prel,empty_cursor,vret,root,(getval root)).
        - entailer!.
        - unfold relation_rep. unfold r. Exists proot. entailer!.
          change_compspecs CompSpecs. cancel.
          unfold cursor_rep.
          destruct (default_val tcursor) eqn:DEF.
          unfold_data_at 1%nat.
          destruct c eqn:HC.
          Exists (snd c0). Exists (fst c0). unfold empty_cursor. simpl.
          change_compspecs CompSpecs. cancel.
        - split; try split; try split.
          + unfold empty_cursor. unfold Zlength. simpl. omega.
          + unfold empty_cursor. unfold Zlength. simpl. rewrite MTD_eq. simpl. omega.
          + auto.
          + fold r in H0. auto.
        - unfold cursor_rep. Intros anc_end. Intros idx_end. unfold r.
          forward.              (* t'2=cursor->level *)
          forward.              (* i=t'2+1 *)
          + entailer!. unfold empty_cursor.
            admit.              (* after moveToFirst, size of cursor in range *)
          + (* gather_SEP 1 2 3 4 5 6. *)
            (* replace_SEP 0 (cursor_rep (moveToFirst root empty_cursor (length empty_cursor)) r vret). *)
            (* entailer!. unfold cursor_rep. Exists anc_end. Exists idx_end. entailer!. *)
            autorewrite with norm.
{ (* forward_loop ( *)
  (*    EX i:Z,                   *)
  (*    PROP ( i<=20 ) *)
  (*    LOCAL (temp _i (Vint(Int.repr i)); *)
  (*    temp _t'2 (Vint (Int.repr (Zlength (moveToFirst root empty_cursor (length empty_cursor)) - 1))); *)
  (*    temp _t'3 proot; temp _cursor vret; temp _relation p) *)
  (*    SEP (relation_rep (root, numRec, depth, prel) prel; malloc_token Tsh tcursor vret; *)
  (*    field_at Tsh tcursor [StructField _relation] prel vret; *)
  (*    field_at Tsh tcursor [StructField _level] *)
  (*      (Vint (Int.repr (Zlength (moveToFirst root empty_cursor (length empty_cursor)) - 1))) vret; *)
  (*    field_at Tsh tcursor [StructField _ancestorsIdx] *)
  (*      (rev *)
  (*         (map (fun x : node val * index.index => rep_index (snd x)) *)
  (*            (moveToFirst root empty_cursor (length empty_cursor))) ++ idx_end) vret; *)
  (*    field_at Tsh tcursor [StructField _ancestors] *)
  (*      (rev (map getval (map fst (moveToFirst root empty_cursor (length empty_cursor)))) ++ anc_end) *)
  (*      vret; emp)%assert). *)
  (* should we do the loop ?  *)
  admit.
          
Admitted.


(* the proof for the previous loop (that didn't call moveToFirst) *)
(*       autorewrite with norm. simpl. *)
(*       pose (n:=20). *)
(*       pose (Pre:=(EX i:Z, *)
(*             PROP ((0 <= i)%Z; (i <= n)%Z) *)
(*             LOCAL(temp _cursor vret; temp _relation p)          *)
(*             SEP(malloc_token Tsh tcursor vret; *)
(*                 relation_rep r p; *)
(*                 data_at Tsh tcursor *)
(*                (force_val (sem_cast_pointer p), *)
(*                (Vint (Int.repr 0), *)
(*                (list_repeat (Z.to_nat i) (Vint(Int.repr 0)) ++  list_repeat (MaxTreeDepth - (Z.to_nat i)) Vundef, *)
(*                 (list_repeat (Z.to_nat i) nullval ++ list_repeat (MaxTreeDepth - (Z.to_nat i)) Vundef)))) vret))%assert). *)
(*       {  *)
(*         forward_for_simple_bound n Pre. *)
(*         - autorewrite with sublist. entailer!. *)
(*         - Intros. *)
(*           forward.              (* cursor->nextancestorptridx[i]=0 *) *)
(*           forward.              (* cursor->ancestors[i]=null *) *)
(*           assert (MaxTreeDepth = Z.to_nat 20). rewrite MTD_eq. simpl. auto. *)
(*           entailer!. rewrite upd_repeat. rewrite upd_repeat. entailer!. *)
(*           auto. rewrite H3. apply Z2Nat.inj_le. auto. omega. auto. *)
(*           auto. auto. rewrite H3. apply Z2Nat.inj_le. auto. omega. auto. auto. *)
(*         - forward.              (* return *) *)
(*           Exists vret. entailer!. *)
(*           rewrite if_false by auto. *)
(*           unfold cursor_rep.  Exists (list_repeat 20 nullval). Exists (list_repeat 20 (Vint(Int.repr 0))). *)
(*           entailer!. autorewrite with sublist. *)
(*           unfold_data_at 1%nat. simpl. entailer!. *)
(*           rewrite field_at_data_at. entailer!. *)
(*           destruct r. destruct p. *)
(*           rewrite <- field_at_data_at. simpl. cancel. unfold Vtrue. *)
(*           admit.                (* my isValid definition is wrong. add it to the cursor type? *) *)
(*       }  *)
(* Admitted. *)