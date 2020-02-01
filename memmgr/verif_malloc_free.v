Require Import VST.floyd.proofauto.
Require Import malloc_lemmas.
Require Import malloc.
Require Import spec_malloc.
Require Import linking.


Definition Gprog : funspecs := external_specs ++ user_specs_R ++ private_specs.

Lemma body_malloc:  semax_body Vprog Gprog f_malloc malloc_spec_R'.
Proof. 
start_function. 
forward_call (BINS-1). (*! t'3 = bin2size(BINS-1) !*)
rep_omega. 
forward_if. (*! if nbytes > t'3 !*)
- (* case nbytes > bin2size(BINS-1) *)
  forward_call (n, gv, lens).  (*! t'1 = malloc_large(nbytes) !*)
  { (* precond *) destruct H. split; try assumption. } 
  Intros p.
  forward. (*! return t'1 !*) 
  Exists p.
  assert (guaranteed lens n = false) by (apply large_not_guaranteed; auto).
  destruct (guaranteed lens n).
  inversion H1.
  destruct (eq_dec p nullval); entailer!.
  bdestruct (n <=? bin2sizeZ(BINS-1)); try rep_omega.
  cancel.
- (* case nbytes <= bin2size(BINS-1) *)
  forward_call(n, gv, lens).  (*! t'2 = malloc_small(nbytes) !*)
  { (* precond *)  destruct H. split; try rep_omega. }
  Intros p.
  forward. (*! result = t'2 !*)
  Exists p. 
  destruct (eq_dec p nullval); entailer.
  simple_if_tac.  entailer!.
  bdestruct (n <=? bin2sizeZ(BINS-1)); try rep_omega.
  Intros lens'.  Exists lens'.
  entailer. 
Qed.

Lemma body_free:  semax_body Vprog Gprog f_free free_spec_R'.
Proof. 
start_function. 
forward_if (PROP()LOCAL()                          (*! if (p != NULL) !*)
                SEP (if eq_dec p nullval
                     then mem_mgr_R gv lens 
                     else if n <=? bin2sizeZ(BINS-1)
                          then mem_mgr_R gv (incr_lens lens (size2binZ n) 1)
                          else mem_mgr_R gv lens )). 
- (* typecheck *) if_tac; entailer!.
- (* case p!=NULL *)
  apply semax_pre with 
   (PROP ( )
     LOCAL (temp _p p; gvars gv)
     SEP (mem_mgr_R gv lens;  malloc_token' Ews n p * memory_block Ews n p)).
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
  forward_if (PROP()LOCAL()               (*! if s <= t'1 !*)
              SEP (if n <=? bin2sizeZ(BINS-1)
                   then mem_mgr_R gv (incr_lens lens (size2binZ n) 1)
                   else mem_mgr_R gv lens )). 
  -- (* case s <= bin2sizeZ(BINS-1) *)
    forward_call(p,s,n,gv,lens). (*! free_small(p,s) !*) 
    { (* preconds *) split3; try omega; try assumption. }
    destruct (zle s (bin2sizeZ (BINS - 1))). 
    + bdestruct(n <=? bin2sizeZ(BINS-1)); try rep_omega. entailer!.
    + rep_omega.
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
      bdestruct(n <=? bin2sizeZ(BINS-1)); try rep_omega.
      cancel.
  -- (* joinpoint spec implies post *)
    destruct (eq_dec p nullval); try contradiction.  entailer.
- (* case p == NULL *) 
  forward. (*! skip !*)
  entailer.
Qed.


Definition module : list semax_body_proof := 
  [mk_body body_malloc; mk_body body_free].



