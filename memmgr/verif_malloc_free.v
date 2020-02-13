Require Import VST.floyd.proofauto.
Require Import malloc_lemmas.
Require Import malloc_sep.
Require Import malloc.
Require Import spec_malloc.
Require Import linking.


Definition Gprog : funspecs := user_specs_R ++ private_specs.

Lemma body_malloc:  semax_body Vprog Gprog f_malloc malloc_spec_R'.
Proof. 
start_function. 
forward_call (BINS-1). (*! t'3 = bin2size(BINS-1) !*)
rep_omega. 
forward_if. (*! if nbytes > t'3 !*)
- (* case nbytes > bin2size(BINS-1) *)
  forward_call (n, gv, rvec).  (*! t'1 = malloc_large(nbytes) !*)
  { (* precond *) destruct H. split; try assumption. } 
  Intros p.
  forward. (*! return t'1 !*) 
  Exists p.
  assert (guaranteed rvec n = false) by (apply large_not_guaranteed; auto).
  destruct (guaranteed rvec n).
  discriminate.
  destruct (eq_dec p nullval); entailer!.
  bdestruct (n <=? maxSmallChunk); try rep_omega.
  cancel.
- (* case nbytes <= bin2size(BINS-1) *)
  forward_call(n, gv, rvec).  (*! t'2 = malloc_small(nbytes) !*)
  { (* precond *)  destruct H. split; try rep_omega. }
  Intros p.
  forward. (*! result = t'2 !*)
  Exists p. 
  destruct (eq_dec p nullval); entailer.
  simple_if_tac.  
  entailer!.
  bdestruct (n <=? maxSmallChunk); try rep_omega.
  Intros rvec'.  Exists rvec'.
  entailer!.
Qed.


Lemma body_free:  semax_body Vprog Gprog f_free free_spec_R'.
Proof. 
start_function. 
(* TODO is there a way to refer to post of free_spec_R' which I've copied here? *)
forward_if (PROP()LOCAL()                          (*! if (p != NULL) !*)
                SEP (if eq_dec p nullval
                     then mem_mgr_R gv rvec
                     else if n <=? maxSmallChunk
                          then mem_mgr_R gv (add_resvec rvec (size2binZ n) 1)
                          else mem_mgr_R gv rvec )). 
- (* typecheck *) if_tac; entailer!.
- (* case p!=NULL *)
  apply semax_pre with 
   (PROP ( )
     LOCAL (temp _p p; gvars gv)
     SEP (mem_mgr_R gv rvec;  malloc_token' Ews n p * memory_block Ews n p)).
  { if_tac; entailer!. }
  assert_PROP ( 0 <= n <= Ptrofs.max_unsigned - WORD ) by entailer!. 
  sep_apply (from_malloc_token'_and_block n p); auto.
(* future: preceding exposes not only the size but also the link pointer, though that's 
not needed for large block. *)
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
  forward_if (PROP()LOCAL()               (*! if s <= t'1 !*)
              SEP (if n <=? maxSmallChunk
                   then mem_mgr_R gv (add_resvec rvec (size2binZ n) 1)
                   else mem_mgr_R gv rvec )). 
  -- (* case s <= bin2sizeZ(BINS-1) *)
    forward_call(p,s,n,gv,rvec). (*! free_small(p,s) !*) 
    { (* preconds *) split3; try omega; try assumption. }
    destruct (zle s (bin2sizeZ (BINS - 1))). 
    + bdestruct(n <=? maxSmallChunk); try rep_omega. entailer!.
    + rep_omega.
  -- (* case s > bin2sizeZ(BINS-1) *)
    bdestruct(n <=? maxSmallChunk); try rep_omega.
    if_tac; try omega.
    forward_call(p,s,gv,rvec). (*! free_large(p,s) !*)
    { split3; try rep_omega; auto. }
    entailer.
  -- (* joinpoint spec implies post *)
    destruct (eq_dec p nullval); try contradiction.  entailer.
- (* case p == NULL *) 
  forward. (*! skip !*)
  entailer.
Qed.


Definition module : list semax_body_proof := 
  [mk_body body_malloc; mk_body body_free].



