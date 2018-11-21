Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.

Require Import malloc_lemmas.
Require Import malloc.
Require Import spec_malloc.


Lemma body_bin2size: semax_body Vprog Gprog f_bin2size bin2size_spec.
Proof. start_function. forward. 
Qed.

Lemma body_size2bin: semax_body Vprog Gprog f_size2bin size2bin_spec.
Proof. start_function. 
  forward_call (BINS-1). rep_omega. 
  forward_if.
  - (* then *) 
    forward. entailer!. f_equal. f_equal. unfold size2binZ; simpl. 
    bdestruct (bin2sizeZ (BINS - 1) <? s); try omega.
  - (* else *)
    forward.  entailer!. f_equal. unfold size2binZ. 
    bdestruct (bin2sizeZ (BINS - 1) <? s); try omega.
    unfold Int.divu. do 2 rewrite Int.unsigned_repr by rep_omega. 
    f_equal. normalize.  f_equal. rep_omega.
Qed.
 
