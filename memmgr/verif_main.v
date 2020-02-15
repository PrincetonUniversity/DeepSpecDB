Require Import VST.floyd.proofauto.
Require Import linking.
Require Import malloc.
Require Import main.
Require Import malloc_lemmas.
Require Import spec_malloc.
Require Import spec_main.

Definition Gprog : funspecs := spec_main.specs ++ user_specs_R ++ private_specs.

Definition Vprog : varspecs. mk_varspecs linked_prog. Defined. 

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
sep_apply (create_mem_mgr_R gv); auto.
forward_call(100,gv,emptyResvec). (* t1 = malloc(100) *)
rep_omega.
Intros p.
change (guaranteed emptyResvec 100) with false.
cbv iota.
if_tac.
+ (* p = nullval *)
 subst p.
 forward_call (100,nullval,gv,emptyResvec).  (* free (p); *)
 rewrite if_true by auto. cancel.
 rewrite if_true by auto. forward.
+
 change (100 <=? maxSmallChunk) with true; cbv iota.
 Intros rvec'.
 forward_call (100,p,gv,rvec').  (* free (p); *)
 rewrite if_false by auto. cancel.
 rewrite if_false by auto.
 change (100 <=? maxSmallChunk) with true; cbv iota.
 forward.
Qed.

Definition module := [mk_body body_main].



