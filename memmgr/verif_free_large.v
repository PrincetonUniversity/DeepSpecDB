Require Import VST.floyd.proofauto.
Require Import malloc_lemmas.
Require Import malloc.
Require Import spec_malloc.
Require Import linking.


Definition Gprog : funspecs := external_specs ++ private_specs.

Lemma body_free_large:  semax_body Vprog Gprog f_free_large free_large_spec.
Proof. 
start_function. 
forward_call( (offset_val (-(WA+WORD)) p), (s+WA+WORD) ). (*! munmap( p-(WASTE+WORD), s+WASTE+WORD ) !*)
+ entailer!. destruct p; try contradiction; simpl. normalize.
  rewrite Ptrofs.sub_add_opp. reflexivity.
+ (* munmap pre *)
  entailer!. 
  sep_apply (free_large_chunk s p); try rep_omega.
  entailer!.
+ rep_omega.
+ entailer!.   
Qed.


Definition module := [mk_body body_free_large].
