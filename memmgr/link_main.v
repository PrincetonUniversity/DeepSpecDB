Require Import VST.floyd.proofauto.
Require Import linking.
Require main.
Require verif_malloc_free. 
Require verif_malloc_large.
Require verif_malloc_small. 
Require verif_free_large.
Require verif_free_small. 
Require verif_list_from_block.
Require verif_pre_fill.
Require verif_fill_bin.
Require verif_bin2size2bin. 
Require verif_external.
Require spec_main.
Require verif_main.


Definition allmodules := 
  verif_main.module ++ 
  verif_malloc_free.module ++
  verif_malloc_large.module ++
  verif_malloc_small.module ++
  verif_free_large.module ++
  verif_free_small.module ++
  verif_list_from_block.module ++
  verif_pre_fill.module ++
  verif_fill_bin.module ++
  verif_bin2size2bin.module ++ 
  verif_external.module ++ nil.

Definition Gprog := ltac:
  (let x := constr:(merge_Gprogs_of allmodules) in
   let x := eval hnf in x in
   let x := eval simpl in x in 
   exact x).

Lemma prog_correct:
  semax_prog spec_main.linked_prog tt spec_main.Vprog Gprog.
Proof.
unfold Gprog.
  prove_semax_prog.
  do_semax_body_proofs (SortBodyProof.sort allmodules).
Qed.

