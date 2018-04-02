(** * verif_movetonext.v: Correctness proof of MoveToNext *)

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

Lemma body_MoveToNext: semax_body Vprog Gprog f_RL_MoveToNext RL_MoveToNext_spec.
Proof.
start_function.
unfold cursor_rep. Intros anc_end. Intros idx_end.
forward.                        (* t'17=btCursor->currNode *)
- autorewrite with norm.
  entailer!. unfold getCurrVal.
  destruct c. auto. destruct p0. destruct n. admit.
- unfold relation_rep. destruct rel as [[nroot numrec] prel'].
  destruct c as [|[n i] c'].
  +                             (* empty cursor *)
    admit.
  + destruct n as [ptr0n len bn xn].
    simpl.
    unfold cursor_correct_rel in H.
    


  
  admit.
Admitted.