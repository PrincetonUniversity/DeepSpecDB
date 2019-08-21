Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import malloc_lemmas.
Require Import malloc.
Require Import spec_malloc.
Require Import linking.


Definition Gprog : funspecs := 
 ltac:(with_library prog (user_specs ++ private_specs)).

Lemma body_malloc:  semax_body Vprog Gprog f_malloc malloc_spec'.
Proof. 
start_function. 
forward_call (BINS-1). (*! t'3 = bin2size(BINS-1) !*)
rep_omega. 
forward_if. (*! if nbytes > t'3 !*)
- (* case nbytes > bin2size(BINS-1) *)
  forward_call (n, gv).  (*! t'1 = malloc_large(nbytes) !*)
  { (* precond *) destruct H. split; try assumption. } 
  Intros p.
  forward. (*! return t'1 !*) 
  if_tac.
  + (* case p = null *) Exists nullval. entailer!.
    if_tac; try contradiction. entailer!. 
  + Exists p. if_tac. contradiction. 
    entailer!.  
- (* case nbytes <= bin2size(BINS-1) *)
  forward_call(n, gv).  (*! t'2 = malloc_small(nbytes) !*)
  { (* precond *)  destruct H. split; try rep_omega. }
  Intros p.
  forward. (*! result = t'2 !*)
  Exists p. 
  entailer!.
Qed.

Lemma body_free:  semax_body Vprog Gprog f_free free_spec'.
Proof. 
start_function. 
forward_if (PROP()LOCAL()SEP(mem_mgr gv)). (*! if (p != NULL) !*)
- (* typecheck *) if_tac; entailer!.
- (* case p!=NULL *)
  apply semax_pre with 
   (PROP ( )
     LOCAL (temp _p p; gvars gv)
     SEP (mem_mgr gv;  malloc_token' Ews n p * memory_block Ews n p)).
  { if_tac; entailer!. }
  assert_PROP ( 0 <= n <= Ptrofs.max_unsigned - WORD ) by entailer!. 
  sep_apply (from_malloc_token'_and_block n p); auto.
  Intros s.
  assert_PROP( 
     (force_val
     (sem_add_ptr_int tuint Signed (force_val (sem_cast_pointer p))
        (eval_unop Oneg tint (Vint (Int.repr 1)))) 
    = field_address tuint [] (offset_val (- WORD) p))).
  { entailer!. simpl. unfold field_address. if_tac. normalize. contradiction. }
  forward. (*! t'2 = p[-1] !*)
  forward. (*! s = t'2 !*) 
  forward_call(BINS - 1). (*! t'1 = bin2size(BINS - 1) !*)
  { (* precond *) rep_omega. } 
  deadvars!.
  forward_if (PROP () LOCAL () SEP (mem_mgr gv)). (*! if s <= t'1 !*)
  -- (* case s <= bin2sizeZ(BINS-1) *)
    forward_call(p,s,n,gv). (*! free_small(p,s) !*) 
    { (* preconds *) split3; try omega; try assumption. }
    entailer!. if_tac. entailer. omega.
  -- (* case s > bin2sizeZ(BINS-1) *)
    if_tac; try omega.
    (*! munmap( p-(WASTE+WORD), s+WASTE+WORD ) !*)
    forward_call( (offset_val (-(WA+WORD)) p), (s+WA+WORD) ).
    + entailer!. destruct p; try contradiction; simpl. normalize.
      rewrite Ptrofs.sub_add_opp. reflexivity.
    + (* munmap pre *)
      entailer!. 
      sep_apply (free_large_chunk s p); try rep_omega.
      entailer!.
    + rep_omega.
    + entailer!.
- (* case p == NULL *) 
  forward. (*! skip !*)
  entailer!.
- (* after if *)
  forward. (*! return !*)
Qed.

Definition module := 
  [mk_body body_malloc; mk_body body_free].
