Require Import VST.floyd.proofauto.
Require Import malloc_lemmas.
Require Import malloc_sep.
Require Import malloc.
Require Import spec_malloc.
Require Import linking.

Definition Gprog : funspecs := external_specs ++ user_specs_R ++ private_specs.

Definition try_pre_fill_spec' :=
 DECLARE _try_pre_fill 
   WITH n:Z, req:Z, rvec:resvec, gv:globals
   PRE [ _n OF tuint, _req OF tint ]
       PROP (0 <= n <= maxSmallChunk /\ 0 <= req <= Int.max_signed)
       LOCAL (temp _n (Vint (Int.repr n)); 
              temp _req (Vint (Int.repr req)); gvars gv) 
       SEP (mem_mgr_R gv rvec) 
   POST [ tint ] EX result: Z,
     PROP ()
     LOCAL (temp ret_temp (Vint (Int.repr result)))
     SEP (mem_mgr_R gv (add_resvec rvec (size2binZ n) result)).

Lemma add_resvec_0: 
  forall rvec b, 0 <= b < BINS -> Zlength rvec = BINS -> (add_resvec rvec b 0) = rvec.
Proof.
  intros. unfold add_resvec.
  bdestruct(Zlength rvec =? BINS); [ | rep_omega].
  bdestruct(0 <=? b); [ | rep_omega].
  bdestruct(b <? BINS); [ | rep_omega].
  simpl.
  replace (Znth b rvec + 0) with (Znth b rvec) by omega.
  rewrite upd_Znth_same_val; [auto | rep_omega].
Qed.

Lemma add_resvec_plus: 
  forall rvec b n m, 0 <= b < BINS -> Zlength rvec = BINS -> 
    (add_resvec (add_resvec rvec b n) b m) = (add_resvec rvec b (n+m)).
Proof.
  intros. unfold add_resvec.
  bdestruct(Zlength rvec =? BINS); [ | rep_omega].
  bdestruct(0 <=? b); [ | rep_omega].
  bdestruct(b <? BINS); [ | rep_omega]; simpl.
  rewrite upd_Znth_Zlength.
  bdestruct(Zlength rvec =? BINS); [ | rep_omega]; simpl.
  rewrite upd_Znth_same; try rep_omega.
  rewrite upd_Znth_twice; try rep_omega.
  rewrite Z.add_assoc; reflexivity. rep_omega.
Qed.

Lemma body_try_pre_fill:  semax_body Vprog Gprog f_try_pre_fill try_pre_fill_spec'.
Proof. 
start_function.
destruct H as [[Hnlo Hnhi] [Hreqlo Hreqhi]].
assert_PROP (Zlength rvec = BINS) as Hrvec. {
  unfold mem_mgr_R. entailer. rewrite Zlength_map in H0. entailer!. }
forward_call(BINS-1). (*! t1 = bin2size(BINS-1) *)
rep_omega.
forward_if. (*! if n > t1 *)
(* large case *)
{ forward. (*! return 0 *)
  Exists 0.
  entailer!.
  rewrite add_resvec_0; try rep_omega.
}
(* small case *)
forward_call n; try rep_omega. (*! b = size2bin(n) *)
forward. (*! ful = 0 *)
deadvars!.
set (b:=size2binZ n).
assert (Hb: 0 <= b < BINS) by (apply (size2bin_range n); rep_omega).
forward_call b. (*! t3 = bin2size(b) *)
forward. (*! chunks = (BIGBLOCK - WASTE) / t3 + WORD) *)
entailer!.
admit. (* contradict H0 by 
          pose proof (bin2size_range b Hb) as [Hlo Hhi].
          assert (bin2sizeZ b + 4 <> 0) by rep_omega. *)
forward_while (*! while (req - ful > 0) *)
    (EX ful:_,
    PROP ( 0 <= ful <= Int.max_signed )
     LOCAL (temp _n (Vptrofs (Ptrofs.repr n)); temp _req (Vptrofs (Ptrofs.repr req)); 
            temp _b (Vint (Int.repr b)); temp _ful (Vint (Int.repr ful)); 
            temp _chunks (Vint (Int.repr((BIGBLOCK-WA)/(bin2sizeZ b + WORD)))); 
            gvars gv)
     SEP (mem_mgr_R gv (add_resvec rvec (size2binZ n) ful))).
- (* init *)
Exists 0.
rewrite add_resvec_0; try rep_omega.
entailer!. f_equal.
admit. (* arith (maybe simplify by tweaking the invariant) *)

- (* typecheck guard *)
entailer!.

- (* body preserves *)
forward_if. (*! if (UINT_MAX - ful < chunks) *)
(* case overflow *)
{ forward. (*! return ful *)
  Exists ful.
  entailer!.
}
(* continue *) 
forward_call BIGBLOCK. (*! t3 = mmap(BIGBLOCK) *)
rep_omega.
Intros p.
forward_if. (*! if p==null *)
-- if_tac; entailer!. 
-- (* case p==null *)
if_tac. forward. Exists ful. entailer!. contradiction.
-- (* case p<>null *)
forward_call (n,p,gv,(add_resvec rvec b ful)). (*! pre_fill(n,p) *)
if_tac. contradiction. subst b. entailer!. 
destruct (eq_dec p nullval). contradiction.
split; [rep_omega|auto].
forward. (*! ful += chunks *)
(* restore invar *)
Exists (ful + chunks_from_block b).
entailer!.
split.
admit. (* arith *)
unfold chunks_from_block.
bdestruct(0<=?b); [ | rep_omega].
bdestruct(b<?BINS); [ | rep_omega].
simpl.
reflexivity.
entailer!.
rewrite add_resvec_plus.
subst b.
entailer!.
apply size2bin_range; rep_omega. 
rep_omega.

- (* after loop *) 
forward. (*! return ful *)
Exists ful.
entailer!.
all: fail.
Admitted.


Definition module := [mk_body body_try_pre_fill].
