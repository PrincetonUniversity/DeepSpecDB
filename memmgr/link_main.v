Require Import VST.floyd.proofauto.
Require Import linking.
Require main.
(*Require verif_main.*)
Require verif_malloc_free. 
Require verif_malloc_large.
Require verif_malloc_small. 
Require verif_free_small. 
Require verif_fill_bin.
Require verif_bin2size2bin. 

Definition allmodules := 
(*  verif_main.module ++ *)
  verif_malloc_free.module ++
  verif_malloc_large.module ++
  verif_malloc_small.module ++
  verif_free_small.module ++
  verif_fill_bin.module ++
  verif_bin2size2bin.module ++ nil.

Definition Gprog := ltac:
  (let x := constr:(merge_Gprogs_of allmodules) in
   let x := eval hnf in x in
   let x := eval simpl in x in 
   exact x).

Lemma prog_correct:
  semax_prog spec_main.linked_prog spec_main.Vprog Gprog.
Proof.
  prove_semax_prog.
  do_semax_body_proofs (SortBodyProof.sort allmodules).
Qed.
