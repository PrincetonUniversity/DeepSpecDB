(** * verif_findindex.v : Correctness proof of findChildIndex and findRecordIndex *)

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

Lemma body_findChildIndex: semax_body Vprog Gprog f_findChildIndex findChildIndex_spec.
Proof.
  start_function.
  forward.                      (* i=0 *)
  forward_if (PROP() LOCAL (temp _i (Vint (Int.repr 0)); temp _length (Vint (Int.repr (Z.of_nat (numKeys_le le)))); temp _key (Vint (Int.repr key)); temp _entries p)  SEP (le_iter_sepcon le)).
  - forward.                    (* skip *)
    entailer!. admit.           (* why is valid_pointer gone from the postcondition? *)
  - contradiction.
  - forward_if(PROP ( ) LOCAL (temp _i (Vint (Int.repr 0)); temp _length (Vint (Int.repr (Z.of_nat (numKeys_le le)))); temp _key (Vint (Int.repr key)); temp _entries p)  SEP (le_iter_sepcon le)).
    + forward.                  (* skip *)
      entailer!.
    + destruct le. contradiction. simpl in H1.
      clear -H1. admit.
      (* there's a contradiction in h1. rep_omega takes forever *)
    + destruct le as [|e le']; try contradiction.
      simpl.
      (* _entries+(0) should be e *)
      admit.    
Admitted.


Lemma body_findRecordIndex: semax_body Vprog Gprog f_findRecordIndex findRecordIndex_spec.
Proof.
  start_function.
Admitted.

