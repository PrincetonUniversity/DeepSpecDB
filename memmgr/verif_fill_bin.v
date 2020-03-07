Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import Lia.
Require Import malloc_lemmas.
Require Import malloc_sep.
Require Import malloc.
Require Import spec_malloc.
Require Import linking. (* just for mk_body *)

Definition Gprog : funspecs := external_specs ++ private_specs.


Lemma body_fill_bin: semax_body Vprog Gprog f_fill_bin fill_bin_spec.
Proof. 
start_function. 
forward_call b.  (*! s = bin2size(b) !*)
set (s:=bin2sizeZ b).
assert (WORD <= s <= bin2sizeZ(BINS-1)) by (pose proof (bin2size_range b); rep_omega).
forward_call BIGBLOCK.  (*! *p = mmap0(BIGBLOCK ...) !*)  
(* TODO unfunspecs *)
{ rep_omega. }
Intros p.  
if_tac in H1. (* split cases on mmap post *)
- (* case p = nullval *)
  forward_if. (*! if p == NULL, case true  !*)
  forward. (*! return NULL !*)
  Exists nullval. Exists 1. 
  entailer!.  
  if_tac; try contradiction. entailer!. contradiction.
- (* case p <> nullval *)
  assert_PROP (isptr p) by entailer!.
  destruct p; try contradiction. 
  rename b0 into pblk; rename i into poff. (* p as blk+ofs *)
  assert_PROP (Ptrofs.unsigned poff + BIGBLOCK < Ptrofs.modulus) by entailer!.
  forward_if; try contradiction. (*! if p == NULL, case false *)
  forward_call((s,(Vptr pblk poff),nullval,0%nat,b)).  (*! t3 = list_from_block(s,p,null) *)
  { unfold mmlist. entailer!. }
  Intro q.
  forward. (*! return t3 *) 
  Exists q. Exists (chunks_from_block (size2binZ s)).
  if_tac.
  { (* q = null - contradiction *)
    pose proof (chunks_from_block_pos b H).
    assert (q<>nullval).
    { apply (proj1 H7) in H8.
      rewrite Nat.add_0_r in H8.
      rewrite <- Z2Nat.inj_0 in H8.
      apply Z2Nat.inj in H8; try rep_omega.
      subst s.
      rewrite bin2size2bin_id in *; try rep_omega.
      apply chunks_from_block_nonneg.
    }
    contradiction.
  }
  entailer!.
  assert (Hbs: 0 <= s <= bin2sizeZ(BINS-1)) by rep_omega.
  pose proof (size2bin_range s Hbs) as Hs.
  pose proof (chunks_from_block_pos (size2binZ s) Hs).
  rep_omega.
  rewrite Nat.add_0_r. (* ugh *)
  subst s.
  cancel.
Qed.


Definition module := [mk_body body_fill_bin].
