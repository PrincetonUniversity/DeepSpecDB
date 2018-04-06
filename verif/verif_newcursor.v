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

Lemma upd_repeat: forall X i (a:X) b m, 0 <= i -> (Z.to_nat i <= m)%nat -> m=MaxTreeDepth ->  
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
  assert ((m - (Z.to_nat i))%nat = Z.to_nat (20-i)).
  admit. rewrite H4.
  rewrite sublist_list_repeat.
  admit.
  omega. admit.                  (* false! *)
  rewrite Zlength_list_repeat. split. omega. admit. auto.  
Admitted.

Lemma body_NewCursor: semax_body Vprog Gprog f_RL_NewCursor RL_NewCursor_spec.
Proof.
  start_function.
  forward_if (PROP() LOCAL(temp _relation p) SEP(relation_rep r p))%assert.
  - forward. auto.
  - subst p. SearchPattern(NOTE__Perhaps_you_need_to_Import_floyd_library___See_reference_manual_chapter___with_library).
    (* forward_call tt. *)              (* telling me to import VST.floyd.library, but it has been done *)
    admit.
  - forward_call tcursor.
    + split. unfold sizeof. simpl. rep_omega. split; auto.
    + Intros vret.
      forward_if ((PROP (vret<>nullval)
                        LOCAL (temp _cursor vret; temp _relation p)
                        SEP (if eq_dec vret nullval
                             then emp
                             else malloc_token Tsh tcursor vret * data_at_ Tsh tcursor vret; 
                             relation_rep r p))).
      * if_tac; entailer!.
      * rewrite if_true; auto.
        forward. Exists nullval. entailer!.
      * forward. rewrite if_false; auto. entailer!.
      * Intros. rewrite if_false; auto. Intros.
        forward.                  (* cursor->relation=relation *)
        forward.                  (* cursor->level=0 *)
        unfold relation_rep. destruct r. destruct p0. destruct p0. Intros proot.
        forward.                  (* t'3=relation->root *)
        simpl. entailer!. unfold local. unfold lift1. entailer!.
        admit.
        (* forward_call to MoveToFirst *)
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