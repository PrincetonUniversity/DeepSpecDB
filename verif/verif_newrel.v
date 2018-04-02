(** * verif_newrel.v: Correctness proof of NewRelation *)

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

Lemma body_NewRelation: semax_body Vprog Gprog f_RL_NewRelation RL_NewRelation_spec.
Proof.
start_function.
forward_call(true).
Intros vret.
forward_if(PROP (vret<>nullval)
     LOCAL (temp _pRootNode vret)
     SEP (if eq_dec vret nullval then emp else btnode_rep (empty_node true vret) vret)).
- if_tac; entailer!.
- subst vret. forward. Exists nullval. Exists nullval. entailer!.
- forward. rewrite if_false by auto. entailer!.
- forward_call trelation.
  + split. unfold sizeof. simpl. rep_omega. split; auto.
  + Intros newrel.
    forward_if(PROP (newrel<>nullval)
     LOCAL (temp _pNewRelation newrel; temp _pRootNode vret)
     SEP (if eq_dec newrel nullval
          then emp
          else malloc_token Tsh trelation newrel * data_at_ Tsh trelation newrel;
          if eq_dec vret nullval then emp else btnode_rep (empty_node true vret) vret)).
    * if_tac; entailer!.
    * rewrite if_true by auto. rewrite if_false by auto. subst newrel.
      forward_call (tbtnode, vret). (* free *)
      { unfold btnode_rep. simpl. Intros. cancel.
        unfold data_at_. unfold field_at_. simpl.
        (* Frame should be empty *)
        (* default val should be the way we instantiated it -> comes from free spec? *)
       admit.
      }
      { forward.
        Exists (Vint(Int.repr 0)). Exists vret. rewrite if_true by auto. entailer!.
        admit. }
    * rewrite if_false; auto.
      forward.
      entailer!. rewrite if_false; auto.
    * Intros. rewrite if_false; auto. Intros.
      forward.                  (* pnewrelation->root = prootnode *)
      forward.                  (* pnewrelation->numrecords=0 *)
      forward.                  (* return pnewrelation *)
      Exists newrel. Exists vret. rewrite if_false by auto. rewrite if_false by auto. Exists vret.
      entailer!. unfold_data_at 1%nat. cancel.
Admitted.