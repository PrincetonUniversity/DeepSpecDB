Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import malloc_lemmas.
Require Import malloc.
Require Import spec_malloc.




Definition Gprog : funspecs := 
 ltac:(with_library prog [ 
   mmap0_spec; munmap_spec; bin2size_spec; size2bin_spec; fill_bin_spec;
   malloc_small_spec; malloc_large_spec; free_small_spec]). (* ; malloc_spec; free_spec]).*)


Lemma body_malloc:  semax_body Vprog Gprog f_malloc malloc_spec'.
Proof. 
start_function. 
forward_call (BINS-1). (*! t'3 = bin2size(BINS-1) !*)
rep_omega. 
forward_if. (*! if nbytes > t'3 !*)
- (* case nbytes > bin2size(BINS-1) *)


WORKING HERE - need to change spec of malloc_large

  forward_call (n, gv).  (*! t'1 = malloc_large(nbytes) !*)
  { (* precond *) 
    destruct H. split3; try assumption. split; try rep_omega. 
    assert (0 <= sizeof t) as H' by omega.
    pose proof (unsigned_repr_le (sizeof t) H').
    eapply Z.lt_le_trans. 
    match goal with | HA: bin2sizeZ (BINS-1) < _ |- _ => apply HA end. 
    assumption.
  } 
  Intros p.
  forward. (*! return t'1 !*) 
  if_tac.
  + (* case p = null *) Exists nullval. entailer!.
    if_tac; try contradiction. entailer!. 
  + Exists p. if_tac. contradiction. 
    entailer!.  
- (* case nbytes <= bin2size(BINS-1) *)
  forward_call(t,gv).  (*! t'2 = malloc_small(nbytes) !*)
  { (* precond *)
    destruct H. split3; try assumption. 
    split; try rep_omega. 
    clear H0 H1.
    match goal with | HA: bin2sizeZ (BINS-1) >= _ |- _ => apply Z.ge_le in HA end.
    rewrite max_unsigned_32 in *.
    rewrite Int.unsigned_repr in *; try assumption. 
    split; try omega. 
    assumption.
    assert (0 <= WA+WORD) as HA by rep_omega.
    eapply Z.le_le_sub_lt; try apply HA.
    replace (sizeof t - 0) with (sizeof t).
    assumption.
    rewrite Z.sub_0_r; reflexivity.
  }
  Intros p.
  forward. (*! result = t'2 !*)
  Exists p. 
  entailer!.
Qed.

Lemma body_free:  semax_body Vprog Gprog f_free free_spec'.
Proof. 
start_function. 
set (n:=sizeof t). (* try to avoid entailer or rep_omega issues *)
forward_if (PROP()LOCAL()SEP(mem_mgr gv)). (*! if (p != NULL) !*)
- (* typecheck *) if_tac. entailer!.
  sep_apply (data_at__memory_block Ews t p). 
  entailer!.
- (* case p!=NULL *)
  apply semax_pre with 
   (PROP ( )
     LOCAL (temp _p p; gvars gv)
     SEP (mem_mgr gv;  malloc_token Ews t p * data_at_ Ews t p)).
  { if_tac; entailer!. }
  assert_PROP ( 0 <= n <= Ptrofs.max_unsigned - WORD ) by entailer!. 
  sep_apply (from_malloc_token_and_block t n p); auto.
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
