Require Import VST.floyd.proofauto.
Require Import linking.
Require Import malloc.
Require Import main_R.
Require Import malloc_lemmas.
Require Import spec_malloc.


Definition linked_prog : Clight.program :=
 ltac: (linking.link_progs_list [malloc.prog; main_R.prog]).

Instance CompSpecs : compspecs. make_compspecs linked_prog. Defined.

Definition Vprog : varspecs. mk_varspecs linked_prog. Defined.

Local Open Scope assert.

Definition main_spec :=
 DECLARE _main
 WITH gv: globals
 PRE [ ] main_pre linked_prog tt nil gv
 POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr 0)))
    SEP(TT).

Definition Gprog : funspecs := [main_spec] ++ external_specs ++ user_specs_R.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
change 8 with BINS.
sep_apply (create_mem_mgr_R gv); auto.
forward_call BIGBLOCK.  (*! *m = mmap0(BIGBLOCK ...) !*)  
rep_omega.
Intros m.
forward_if.
{ if_tac; entailer!. }
+ (* m = null *)
  forward. (* return *)
+ (* m <> null *)
  if_tac. contradiction.
  forward_call(50,m,gv,emptyResvec). (* pre_fill(50,m) *)
  split.  rep_omega. auto.
  set (rvec:=add_resvec emptyResvec (size2binZ 50) (chunks_from_block (size2binZ 50))).
  forward_call(50,gv,rvec). (* t1 = malloc(50) --- using malloc_spec_R *)
  rep_omega.
  Intros p.
  change (guaranteed rvec 50) with true.
  cbv iota.
  assert_PROP (p <> nullval) by entailer!.
  forward_call(50,p,gv,(add_resvec rvec (size2binZ 50) (-1))). (* free(p) *)
  rewrite if_false by auto.
  entailer!.
  forward.
Qed.


(* Proof of main using the malloc_spec_R_simple *)

Definition user_specs_R' := 
[pre_fill_spec'; try_pre_fill_spec'; malloc_spec_R_simple'; free_spec_R'].

Definition Gprog' : funspecs := [main_spec] ++ external_specs ++ user_specs_R'.

Lemma body_main': semax_body Vprog Gprog' f_main main_spec.
Proof.
start_function.
change 8 with BINS.
sep_apply (create_mem_mgr_R gv); auto.
forward_call BIGBLOCK.  (*! *m = mmap0(BIGBLOCK ...) !*)  
rep_omega.
Intros m.
forward_if.
{ if_tac; entailer!. }
+ (* m = null *)
  forward. (* return *)
+ (* m <> null *)
  if_tac. contradiction.
  forward_call(50,m,gv,emptyResvec). (* pre_fill(50,m) *)
  split.  rep_omega. auto.
  set (rvec:=add_resvec emptyResvec (size2binZ 50) (chunks_from_block (size2binZ 50))).
  forward_call(50,gv,rvec). (* t1 = malloc(50) *)
  split. rep_omega.  
  change (guaranteed rvec 50) with true; auto.
  Intros p.
  assert_PROP (p <> nullval) by entailer!.
  forward_call(50,p,gv,(add_resvec rvec (size2binZ 50) (-1))). (* free(p) *)
  rewrite if_false by auto.
  entailer!.
  forward.
Qed.





