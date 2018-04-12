(** * verif_movetofirst.v : Correctness proof of moveToFirst *)

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
Require Import index.

Lemma body_moveToFirst: semax_body Vprog Gprog f_moveToFirst moveToFirst_spec.
Proof.
  start_function.
  forward_if (
      PROP(pn<>nullval)
      LOCAL(temp _cursor pc; temp _node pn; temp _level (Vint (Int.repr (Zlength c))))
      SEP(relation_rep r pr; cursor_rep c r pc))%assert.
  - apply denote_tc_test_eq_split.
    admit.                       (* valid pointer (getval n) *)
    entailer!.
  - forward.                    (* skip *)
    entailer!.
  - assert_PROP(False).
    entailer!.                  (* contradiction in H2? *)
    admit.
    inv H3.
  - forward_if (
        (PROP (pn <> nullval; pc <> nullval)
         LOCAL (temp _cursor pc; temp _node pn; temp _level (Vint (Int.repr (Zlength c))))
         SEP (relation_rep r pr; cursor_rep c r pc))).
    + forward. entailer!.
    + assert_PROP(False).
      entailer. inv H4.
    + forward_if ((PROP (pn <> nullval; pc <> nullval; (Zlength c) >= 0)
     LOCAL (temp _cursor pc; temp _node pn; temp _level (Vint (Int.repr (Zlength c))))
     SEP (relation_rep r pr; cursor_rep c r pc))).
      * forward. entailer!.
      * assert_PROP(False). entailer.
        (* contradiction in H2. *) admit.
        inv H5.
      * unfold cursor_rep.
        Intros anc_end. Intros idx_end.
        destruct r as [[[root numRec] depth] prel].
Admitted.