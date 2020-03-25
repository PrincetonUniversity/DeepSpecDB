(* Alternate verification of main.c using user_specs, the normal
malloc/free specs without resource tracking.  
By contrast, verif_main.c uses the resource-tracking specs,
which is needed as of Feb 2020 to prove (in link_main.v) correctness
of the linked program, owing to limitations of the linking tactics.
*)

Require Import VST.floyd.proofauto.
Require Import linking.
Require Import malloc.
Require Import main.
Require Import malloc_lemmas.
Require Import spec_malloc.
Require Import spec_main.

Definition Gprog : funspecs := spec_main.specs ++ user_specs.

Definition Vprog : varspecs. mk_varspecs linked_prog. Defined. 

Lemma body_main_alt: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
sep_apply (create_mem_mgr gv); auto.
forward_call(100,gv). (* t1 = malloc(100) *)
rep_omega.
Intros p.
if_tac.
+ (* p = nullval *)
 subst p.
 forward_call (100,nullval,gv).  (* free (p); *)
 entailer!.
 forward. (* return *)
+
 forward_call (100,p,gv).  (* free (p); *)
 rewrite if_false by auto. cancel.
 forward. (* return *)
Qed.



