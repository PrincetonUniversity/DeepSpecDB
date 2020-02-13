Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import Lia. (* for lia tactic (nonlinear integer arithmetic) *) 

Require Import malloc_lemmas. (* background *)
Require Import malloc_shares. (* for comp_Ews *)

Ltac start_function_hint ::= idtac. (* no hint reminder *)

(* Require Import mmap0. (* the shim code *) *)
Require Import malloc. (* the program *)

(* Note about clightgen:
Compiling malloc.c triggers a warning, "Unsupported compiler detected",
from the header file cdefs.h. This is ok.
*)

Instance CompSpecs : compspecs. make_compspecs prog. Defined. 
Definition Vprog : varspecs. mk_varspecs prog. Defined. 

Local Open Scope Z.
Local Open Scope logic.  


(*+ assumed specs *)

(* Specifications for posix mmap0 and munmap as used by this memory manager.
   Using wrapper mmap0 (in malloc.c) which returns 0 on failure, because 
   mmap returns -1, and pointer comparisons with non-zero literals violate 
   the C standard.   Aside from that, mmap0's spec is the same as mmap's.

TODO: The implementation of mmap0 ignores the flags (etc) so it's not essential
for the spec to mimic that of mmap.  Moreover different platforms seem to 
have different values for MAP_PRIVATE or MAP_ANONYMOUS so we've commented-out
the precondition on flags.

   The posix spec says the pointer will be aligned on page boundary.  Our
   spec uses malloc_compatible which says it's on the machine's natural 
   alignment. 
*)

Definition mmap0_spec := 
   DECLARE _mmap0
   WITH n:Z
   PRE [ 1%positive (*_addr*) OF (tptr tvoid), 
         2%positive (*_len*) OF tuint, 
         3%positive (*_prot*) OF tint,
         4%positive (*_flags*) OF tint,
         5%positive (*_fildes*) OF tint,
         6%positive (*_off*) OF tlong ]
     PROP (0 <= n <= Ptrofs.max_unsigned)
     LOCAL (temp 1%positive nullval; 
            temp 2%positive (Vptrofs (Ptrofs.repr n));
            temp 3%positive (Vint (Int.repr 3)); (* PROT_READ|PROT_WRITE *)
(*            temp 4%positive (Vint (Int.repr 4098)); (* MAP_PRIVATE|MAP_ANONYMOUS *) *)
            temp 5%positive (Vint (Int.repr (-1)));
            temp 6%positive (Vlong (Int64.repr 0)))
     SEP ()
   POST [ tptr tvoid ] EX p:_, 
     PROP ( if eq_dec p nullval
            then True else malloc_compatible n p )
     LOCAL (temp ret_temp p)
     SEP ( if eq_dec p nullval
           then emp else memory_block Tsh n p).

Definition munmap_spec := 
   DECLARE _munmap
   WITH p:val, n:Z
   PRE [ 1%positive (*_addr*) OF (tptr tvoid), 
         2%positive (*_len*) OF tuint ]
     PROP (0 <= n <= Ptrofs.max_unsigned)
     LOCAL (temp 1%positive p; 
            temp 2%positive (Vptrofs (Ptrofs.repr n)) )
     SEP ( memory_block Tsh n p )
   POST [ tint ] EX res: Z,
     PROP ()
     LOCAL (temp ret_temp (Vint (Int.repr res)))
     SEP ( emp ).

(*+ malloc token *)

(* Accounts for the size field, alignment padding, 
   and a share of the allocated block so that malloc_token sh n p |- valid_pointer p
   where p is the address returned by malloc.

Unfolding the definition reveals the stored size value s, which 
is not the request size (n = sizeof t) but rather the size of the chunk 
(not counting the size field itself).

The constraint s + WA + WORD <= Ptrofs.max_unsigned caters for 
padding and is used e.g. in proof of body_free.
(The conjunct (malloc_compatible s p) implies (s < Ptrofs.modulus) but 
that's not enough.)

About waste: for small chunks, there is waste at the beginning of each big 
block used by fill_bin, and the module invariant mem_mgr accounts for it. 
In addition, there is waste of size s - n at the end of each small chunk 
(as n gets rounded up to the nearest size2binZ), and each large chunk has 
waste at the start, for alignment; these are accounted for by malloc_token.

About the share: The idea is that one might want to be able to split tokens.
To do so, the API in floyd/library.v would need to include a splitting lemma.
For now, we keep parameter sh but do not provide a splitting lemma. 
Malloc and free are specified to use share Ews, anticipating what would be
needed for splittable token.

The 'retainer' (TODO term?) is needed to validate malloc_token_valid_pointer;
a small share of the user's block.

Notes:

- malloc_spec and free_spec 
  param on cs and on type (yes, free too)
  use malloc_token param'd on cs and type

- malloc_spec' and free_spec' 
  not param'd on anything (except implicit cs in malloc context)
  use malloc_token' param'd on size and not on cs

*)

Definition comp := VST.msl.shares.Share.comp.

Definition malloc_tok (sh: share) (n: Z) (s: Z) (p: val): mpred := 
   !! (0 <= n <= s /\ s + WA + WORD <= Ptrofs.max_unsigned /\ 
       (s <= bin2sizeZ(BINS-1) -> s = bin2sizeZ(size2binZ n)) /\
       (s > bin2sizeZ(BINS-1) -> s = n) /\
       malloc_compatible s p ) &&
    data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p) (* stored size *)
  * memory_block (comp Ews) s p                               (* retainer *)
  * memory_block Ews (s - n) (offset_val n p)                 (* waste at end of small *)
  * (if zle s (bin2sizeZ(BINS-1))  
    then emp
    else memory_block Tsh WA (offset_val (-(WA+WORD)) p)).  (* waste at start of large *)

(* for export *)
Definition malloc_token' (sh: share) (n: Z) (p: val): mpred := 
   EX s:Z, malloc_tok sh n s p.

(* for export *)
Definition malloc_token {cs: compspecs} (sh: share) (t: type) (p: val): mpred := 
   !! field_compatible t [] p && 
   malloc_token' sh (sizeof t) p.


Lemma malloc_token'_valid_pointer_size: 
  forall sh n p, malloc_token sh n p |-- valid_pointer (offset_val (- WORD) p).
Proof.
  intros; unfold malloc_token, malloc_token', malloc_tok; entailer!.
  sep_apply (data_at_valid_ptr Tsh tuint (Vint (Int.repr s)) (offset_val(-WORD) p)).
  apply top_share_nonidentity.
  entailer!.
Qed.


Lemma malloc_token_valid_pointer_size: 
  forall sh t p, malloc_token sh t p |-- valid_pointer (offset_val (- WORD) p).
Proof.
  intros; unfold malloc_token, malloc_token', malloc_tok; entailer!.
  sep_apply (data_at_valid_ptr Tsh tuint (Vint (Int.repr s)) (offset_val(-WORD) p)).
  apply top_share_nonidentity.
  entailer!.
Qed.

(* for export *)
Lemma malloc_token'_local_facts:
  forall sh n p, malloc_token' sh n p 
  |-- !!( malloc_compatible n p /\ 0 <= n <= Ptrofs.max_unsigned - (WA+WORD)).
Proof.
  intros; unfold malloc_token, malloc_token'; Intro s; unfold malloc_tok; entailer!.
  apply (malloc_compatible_prefix n s p); try omega; try assumption.
Qed.

(* for export *)
Lemma malloc_token_local_facts:
  forall {cs: compspecs} sh t p, malloc_token sh t p 
  |-- !!( malloc_compatible (sizeof t) p /\ 
          0 <= (sizeof t) <= Ptrofs.max_unsigned - (WA+WORD) /\
          field_compatible t [] p).
Proof.
  intros; unfold malloc_token, malloc_token'; Intro s; unfold malloc_tok; entailer!.
  apply (malloc_compatible_prefix (sizeof t) s p); try omega; try assumption.
Qed.


(* for export *)
Lemma malloc_token'_valid_pointer:
  forall sh n p, malloc_token' sh n p |-- valid_pointer p.
Proof.
  intros.  unfold malloc_token, malloc_token'.
  entailer!.
  unfold malloc_tok.
  assert_PROP (s > 0). { 
    entailer!. bdestruct(bin2sizeZ (BINS-1) <? s). rep_omega.
    match goal with | HA: not(bin2sizeZ _ < _) |- _ => 
      (apply Znot_lt_ge in HA; apply Z.ge_le in HA; apply H1 in HA) end.
    pose proof (bin2size_range (size2binZ n)). subst.
    pose proof (size2bin_range n). rep_omega.
  }
  sep_apply (memory_block_valid_pointer (comp Ews) s p 0); try omega.
  apply nonidentity_comp_Ews.
  entailer.
Qed.


(* for export *)
Lemma malloc_token_valid_pointer:
  forall {cs: compspecs} sh t p, malloc_token sh t p |-- valid_pointer p.
Proof.
  intros.  unfold malloc_token, malloc_token'.
  entailer!.
  unfold malloc_tok.
  assert_PROP (s > 0). { 
    entailer!. bdestruct(bin2sizeZ (BINS-1) <? s). rep_omega.
    match goal with | HA: not(bin2sizeZ _ < _) |- _ => 
      (apply Znot_lt_ge in HA; apply Z.ge_le in HA; apply H2 in HA) end.
    pose proof (bin2size_range (size2binZ (sizeof t))). subst.
    pose proof (size2bin_range (sizeof t)). rep_omega.
  }
  sep_apply (memory_block_valid_pointer (comp Ews) s p 0); try omega.
  apply nonidentity_comp_Ews.
  entailer.
Qed.

Hint Resolve malloc_token_valid_pointer_size : valid_pointer.
Hint Resolve malloc_token'_valid_pointer_size : valid_pointer.
Hint Resolve malloc_token_valid_pointer : valid_pointer.
Hint Resolve malloc_token'_valid_pointer : valid_pointer.
Hint Resolve malloc_token_local_facts : saturate_local.
Hint Resolve malloc_token'_local_facts : saturate_local.

(*+ free lists *)

(* TODO 'link' versus 'nxt' in the comments *)

(* linked list segment, for free chunks of a fixed size.

p points to a linked list of len chunks, terminated at r.

Chunks are viewed as (sz,nxt,remainder) where nxt points to the
next chunk in the list.  Each chunk begins with the stored size
value sz.  Each pointer, including p, points to the nxt field, 
not to sz.
The value of sz is the number of bytes in (nxt,remainder).

A segment predicate is used, to cater for fill_bin which grows 
the list at its tail. For non-empty segment, terminated at r means 
that r is the value in the nxt field of the last chunk -- which 
may be null or a valid pointer to not-necessarily-initialized memory. 

The definition uses nat, for ease of termination check, at cost 
of Z conversions.  I tried using the Function mechanism, with len:Z
and {measure Z.to_nat len}, but this didn't work.

Note on range of sz:  Since the bins are for moderate sizes,
there's no need for sz > Int.max_unsigned, but the malloc/free API
uses size_t for the size, and jumbo chunks need to be parsed by
free even though they won't be in a bin, so this spec uses 
Ptrofs in conformance with the code's use of size_t.
TODO - parsing of big chunks has nothing to do with mmlist. 

Note: in floyd/field_at.v there's a todo note related to revising
defs assoc'd with malloc_compatible.
*)

Fixpoint mmlist (sz: Z) (len: nat) (p: val) (r: val): mpred :=
 match len with
 | O => !! (0 < sz <= bin2sizeZ(BINS - 1) /\ p = r /\ is_pointer_or_null p) && emp 
 | (S n) => EX q:val, 
         !! (p <> r /\ malloc_compatible sz p) &&  
         data_at Tsh tuint (Vptrofs (Ptrofs.repr sz)) (offset_val (- WORD) p) *
         data_at Tsh (tptr tvoid) q p *
         memory_block Tsh (sz - WORD) (offset_val WORD p) *
         mmlist sz n q r
 end.

(* an uncurried variant, caters for use with iter_sepcon *)
Definition mmlist' (it: nat * val * Z) :=
  mmlist (bin2sizeZ (snd it)) (fst (fst it)) (snd (fst it)) nullval. 



(*+ module invariant mem_mgr *)

(* There is an array, its elements point to null-terminated lists 
of right size chunks, and there is some wasted memory.
*) 

(* with Resource accounting *)
Definition mem_mgr_R (gv: globals) (rvec: resvec): mpred := 
  EX bins: list val, EX idxs: list Z, EX lens: list nat,
    !! (Zlength bins = BINS /\ Zlength lens = BINS /\
        lens = map Z.to_nat rvec /\
        idxs = map Z.of_nat (seq 0 (Z.to_nat BINS)) /\  
        no_neg rvec ) &&
  data_at Ews (tarray (tptr tvoid) BINS) bins (gv _bin) * 
  iter_sepcon mmlist' (zip3 lens bins idxs) * 
  TT. (* waste, which arises due to alignment in bins *)

Definition mem_mgr (gv: globals): mpred := EX rvec: resvec, mem_mgr_R gv rvec.

(*  This is meant to describe the extern global variables of malloc.c,
    as they would appear as processed by CompCert and Floyd. *)
Definition initialized_globals (gv: globals) := 
   !! (headptr (gv malloc._bin)) &&
   data_at Ews (tarray (tptr tvoid) BINS) (repeat nullval (Z.to_nat BINS)) (gv malloc._bin).

Lemma create_mem_mgr_R: 
  forall (gv: globals), initialized_globals gv |-- mem_mgr_R gv emptyResvec.
Proof.
  intros gv.
  unfold initialized_globals; entailer!.
  unfold mem_mgr_R.
  Exists (repeat nullval (Z.to_nat BINS)).
  Exists (Zseq BINS).
  Exists (repeat 0%nat (Z.to_nat BINS)).  
  entailer!.
  { unfold emptyResvec. apply Forall_repeat; rep_omega. }
  unfold mmlist'.
  erewrite iter_sepcon_func_strong with 
    (l := (zip3 (repeat 0%nat (Z.to_nat BINS)) (repeat nullval (Z.to_nat BINS)) (Zseq BINS)))
    (Q := (fun it : nat * val * Z => emp)).
  { rewrite iter_sepcon_emp'. entailer. intros. normalize. }
  intros [[num p] sz] Hin.
  pose proof (In_zip3 ((num,p),sz)
                      (repeat 0%nat (Z.to_nat BINS))
                      (repeat nullval (Z.to_nat BINS))
                      (Zseq BINS)
                      Hin) as [Hff [Hsf Hs]].
  clear H H0 Hin.
  assert (Hn: num = 0%nat) by (eapply repeat_spec; apply Hff). 
  rewrite Hn; clear Hn Hff.
  assert (Hp: p = nullval) by (eapply repeat_spec; apply Hsf). 
  rewrite Hp; clear Hp Hsf.
  assert (Hsz: 0 <= sz < BINS).
  { assert (Hsx: 0 <= sz < BINS). 
    apply in_Zseq; try rep_omega; try assumption. assumption. }
  simpl. unfold mmlist.
  apply pred_ext; entailer!.
  pose proof (bin2size_range sz Hsz). rep_omega.
Qed.

Lemma create_mem_mgr: 
  forall (gv: globals), initialized_globals gv |-- mem_mgr gv.
Proof.  
  intros gv. unfold mem_mgr. Exists emptyResvec. apply (create_mem_mgr_R gv).
Qed.



(*+ code specs *)

(* Notes: 
Resourced specs are designed to subsume the non-resourced specs; so don't strengthen old precondition but rather post, which results in annoying set of cases for malloc.

TODO _R resourced versions so far correspond to malloc_spec' and free_spec' with implicit compspecs; need to add the ones with explicit compspecs, for linking, and prove their subsumptions.
*)

(* public interface *)

(* NOTES on describing the interface.

Standard specs of malloc and free: malloc may return null, indicating failure; the representation invariant mem_mgr exposes nothing to the client about the implementation 

Resourced specs describe the malloc-free system in terms of a standard implementation in which free lists (dubbed buckets) are maintained for a range of 'small' chunk sizes.  The resourced spec for malloc ensures that it succeeds if the requisite bucket is non-empty.  There is a resourced spec for the non-standard function pre_fill that lets a client provide a block of memory to be used for a particular bucket.  The representation invariant mem_mgr_R gives a lower bound on the current bucket sizes, as a list of naturals we dub 'resource vector'.  
For somewhat arbitrary reasons --simplicity and also compatibility with existing proofs of the non-resourced version-- the spec of pre_fill requires a specific fixed size for the 'big block' provided by the caller.

The resource vector corresponds exactly to the free list sizes: freeing a small chunk adds one to its free list, and if an allocation is guaranteed to succeed (because its free list is non-empty) then the size of the free list decreases by one.  However, a non-guaranteed allocation may succeed either because the chunk is available in its free list, thereby decreasing the list size by one, or because the free list has been renewed by a call to the operating system, in which case the bucket may have increased in size.  This is reflected in the postcondition of malloc.  (That postondition could be made slighly stronger, to reflect successful refilling of the bucket, but it doesn't seem worth doing since the situation isn't relevant to clients interested in guaranteed resources.)

The resourced specs say nothing about large chunks which are not stored in buckets.  A client that relies on availability of large chunks needs to allocate these upon initialization, either via the malloc-free system (which in turn relies on mmap), by direct calls to mmap, or using its own bss.    

Resource-sensitive clients will use malloc_spec_R_simple, free_spec_R, and pre_fill_spec.

*)

(* the spec for the code *)
Definition malloc_spec_R' := 
   DECLARE _malloc
   WITH n:Z, gv:globals, rvec:resvec
   PRE [ _nbytes OF size_t ]
       PROP (0 <= n <= Ptrofs.max_unsigned - (WA+WORD))
       LOCAL (temp _nbytes (Vptrofs (Ptrofs.repr n)); gvars gv)
       SEP ( mem_mgr_R gv rvec )
   POST [ tptr tvoid ] EX p:_, 
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( if guaranteed rvec n
             then mem_mgr_R gv (add_resvec rvec (size2binZ n) (-1)) *
                  malloc_token' Ews n p * memory_block Ews n p
             else if eq_dec p nullval 
                  then mem_mgr_R gv rvec
                  else (if n <=? maxSmallChunk 
                        then (EX rvec':_, !!(eq_except rvec' rvec (size2binZ n))
                                            && (mem_mgr_R gv rvec'))
                        else mem_mgr_R gv rvec) *
                       malloc_token' Ews n p * memory_block Ews n p).

(* convenient specs for resource-conscious clients, first draft.
For completeness we need:
- malloc large doesn't change the vector (and may not succeed)
- malloc with guarantee (which implies small)
- free large doesn't change vector, free small decreases
We might also want to eliminate conditional posts in favor of non-null preconditions.
 *)
Definition malloc_spec_R_simple' :=
   DECLARE _malloc
   WITH n:Z, gv:globals, rvec:resvec
   PRE [ _nbytes OF size_t ]
       PROP (0 <= n <= Ptrofs.max_unsigned - (WA+WORD) /\
            guaranteed rvec n = true)
       LOCAL (temp _nbytes (Vptrofs (Ptrofs.repr n)); gvars gv)
       SEP ( mem_mgr_R gv rvec )
   POST [ tptr tvoid ] EX p:_, 
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mem_mgr_R gv (add_resvec rvec (size2binZ n) (-1)) *
             malloc_token' Ews n p * memory_block Ews n p ).


Definition free_spec_R' :=
 DECLARE _free
   WITH n:Z, p:val, gv:globals, rvec:resvec
   PRE [ _p OF tptr tvoid ]
       PROP ()
       LOCAL (temp _p p; gvars gv)
       SEP (mem_mgr_R gv rvec;
            if eq_dec p nullval then emp
            else (malloc_token' Ews n p * memory_block Ews n p))
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (if eq_dec p nullval 
            then mem_mgr_R gv rvec
            else if n <=? maxSmallChunk
                 then mem_mgr_R gv (add_resvec rvec (size2binZ n) 1)
                 else mem_mgr_R gv rvec ).


Definition pre_fill_spec' :=
 DECLARE _pre_fill 
   WITH n:Z, p:val, gv:globals, rvec:resvec
   PRE [ _n OF tuint, _p OF tptr tvoid ]
       PROP (0 <= n <= maxSmallChunk /\ malloc_compatible BIGBLOCK p)
       LOCAL (temp _n (Vptrofs (Ptrofs.repr n)); temp _p p; gvars gv) 
       SEP (mem_mgr_R gv rvec; memory_block Tsh BIGBLOCK p) 
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr_R gv (add_resvec rvec (size2binZ n) 
                                     (chunks_from_block (size2binZ n)))).


Definition malloc_spec' := 
   DECLARE _malloc
   WITH n:Z, gv:globals
   PRE [ _nbytes OF size_t ]
       PROP (0 <= n <= Ptrofs.max_unsigned - (WA+WORD))
       LOCAL (temp _nbytes (Vptrofs (Ptrofs.repr n)); gvars gv)
       SEP ( mem_mgr gv )
   POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mem_mgr gv;
             if eq_dec p nullval then emp
             else (malloc_token' Ews n p * memory_block Ews n p)).


Definition malloc_spec {cs: compspecs} (t: type):= 
   DECLARE _malloc
   WITH gv:globals
   PRE [ _nbytes OF size_t ]
       PROP (0 <= sizeof t <= Ptrofs.max_unsigned - (WA+WORD);
             complete_legal_cosu_type t = true;
             natural_aligned natural_alignment t = true)
       LOCAL (temp _nbytes (Vptrofs (Ptrofs.repr (sizeof t))); gvars gv)
       SEP ( mem_mgr gv )
   POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mem_mgr gv;
             if eq_dec p nullval then emp
             else (malloc_token Ews t p * data_at_ Ews t p)).


Definition free_spec' :=
 DECLARE _free
   WITH n:Z, p:val, gv: globals
   PRE [ _p OF tptr tvoid ]
       PROP ()
       LOCAL (temp _p p; gvars gv)
       SEP (mem_mgr gv;
              if eq_dec p nullval then emp
              else (malloc_token' Ews n p * memory_block Ews n p))
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr gv).

Definition free_spec {cs:compspecs} (t: type) := 
   DECLARE _free
   WITH p:val, gv:globals
   PRE [ _p OF tptr tvoid ]
       PROP ()
       LOCAL (temp _p p; gvars gv)
       SEP (mem_mgr gv; 
            if eq_dec p nullval then emp
            else (malloc_token Ews t p * data_at_ Ews t p))
   POST [ Tvoid ]
       PROP ()
       LOCAL ( )
       SEP (mem_mgr gv).


Lemma malloc_spec_sub:
 forall {cs: compspecs} (t: type), 
   funspec_sub (snd malloc_spec') (snd (malloc_spec t)).
Proof.
intros.
apply NDsubsume_subsume.
split; extensionality x; reflexivity.
split3; auto.
intros gv.
simpl in gv.
Exists (sizeof t, gv) emp.
change (liftx emp) with (@emp (environ->mpred) _ _).
rewrite !emp_sepcon.
apply andp_right.
entailer!.
match goal with |- _ |-- prop ?PP => set (P:=PP) end.
entailer!.
subst P.
Intros p; Exists p.
entailer!.
if_tac; auto.
unfold malloc_token, malloc_token'.
(* preceding copied from pile/spec_stdlib *)
unfold malloc_tok.
Intros s; Exists s.
entailer!.
- apply malloc_compatible_field_compatible; auto;
  apply (malloc_compatible_prefix (sizeof t) s); assumption. 
- rewrite memory_block_data_at_; auto; 
  apply malloc_compatible_field_compatible; auto;
  apply (malloc_compatible_prefix (sizeof t) s); auto.
Qed.


Lemma malloc_spec_R_sub:
 forall {cs: compspecs},
   funspec_sub (snd malloc_spec_R') (snd malloc_spec').
Proof.
intros.
apply NDsubsume_subsume.
split; extensionality x; reflexivity.
split3; auto.
intros [n gv].
unfold mem_mgr.
Intros rvec.
Exists (n, gv, rvec) emp. (* empty frame *)
change (liftx emp) with (@emp (environ->mpred) _ _).
rewrite !emp_sepcon.
apply andp_right.
entailer!.
match goal with |- _ |-- prop ?PP => set (P:=PP) end.
entailer!.
subst P.
destruct (guaranteed rvec n) eqn:guar.
- (* guaranteed success *)
  Intros p; Exists p.
  Exists (add_resvec rvec (size2binZ n) (-1)).
  entailer!.
  if_tac; entailer!.
- (* not guaranteed *)
  bdestruct (n <=? maxSmallChunk).
  Intros p; Exists p.
  destruct (eq_dec p nullval).
  Exists rvec.
  entailer!.
  Intro rvec'.
  Exists rvec'.
  entailer!.
  Intros p; Exists p.
  Exists rvec.
  entailer!.
  destruct (eq_dec p nullval); entailer!.
Qed.

Lemma malloc_spec_R_simple_sub:
 forall {cs: compspecs},
   funspec_sub (snd malloc_spec_R') (snd malloc_spec_R_simple').
Proof.
intros.
apply NDsubsume_subsume.
split; extensionality x; reflexivity.
split3; auto.
intros [[n gv] rvec].
Exists (n, gv, rvec) emp. (* empty frame *)
change (liftx emp) with (@emp (environ->mpred) _ _).
rewrite !emp_sepcon.
apply andp_right.
entailer!.
match goal with |- _ |-- prop ?PP => set (P:=PP) end.
entailer!.
subst P.
destruct H as [[Hn Hn'] Hg].
destruct (guaranteed rvec n) eqn:guar; try inversion Hg.
Intros p; Exists p.
entailer!.
Qed.


Lemma free_spec_sub:
 forall {cs: compspecs} (t: type), 
   funspec_sub (snd free_spec') (snd (free_spec t)).
Proof.
intros.
apply NDsubsume_subsume.
split; extensionality x; reflexivity.
split3; auto.
intros (p,gv).
simpl in gv.
Exists (sizeof t, p, gv) emp.
change (liftx emp) with (@emp (environ->mpred) _ _).
rewrite !emp_sepcon.
apply andp_right.
if_tac.
entailer!.
entailer!. simpl in H0.
unfold malloc_token. entailer!.
apply data_at__memory_block_cancel.
apply prop_right.
entailer!.
Qed.


Lemma free_spec_R_sub:
 forall {cs: compspecs},
   funspec_sub (snd free_spec_R') (snd free_spec').
Proof.
intros.
apply NDsubsume_subsume.
split; extensionality x; reflexivity.
split3; auto.
intros [(n,p) gv].
unfold mem_mgr.
Intros rvec.
Exists (n, p, gv, rvec) emp.
change (liftx emp) with (@emp (environ->mpred) _ _).
rewrite !emp_sepcon.
apply andp_right.
entailer!.
match goal with |- _ |-- prop ?PP => set (P:=PP) end.
entailer!.
simpl in H.
subst P.
if_tac.
Exists rvec.
entailer!.
bdestruct (n <=? maxSmallChunk).
- (* small *)
  Exists (add_resvec rvec (size2binZ n) 1); entailer!.
- (* large *)
  Exists rvec; entailer!.
Qed.



(*! private functions !*)

Definition bin2size_spec :=
 DECLARE _bin2size
  WITH b: Z
  PRE [ _b OF tint ] 
     PROP( 0 <= b < BINS ) 
     LOCAL (temp _b (Vint (Int.repr b))) SEP ()
  POST [ tuint ] 
     PROP() LOCAL(temp ret_temp (Vptrofs (Ptrofs.repr (bin2sizeZ b)))) SEP ().

Definition size2bin_spec :=
 DECLARE _size2bin
  WITH s: Z
  PRE [ _s OF tuint ]    
     PROP( 0 <= s <= Ptrofs.max_unsigned ) 
     LOCAL (temp _s (Vptrofs (Ptrofs.repr s))) SEP ()
  POST [ tint ]
     PROP() LOCAL(temp ret_temp (Vint (Int.repr (size2binZ s)))) SEP ().


Definition list_from_block_spec :=
 DECLARE _list_from_block
  WITH s: Z, p: val, tl: val, tlen: nat, b: Z
  PRE [ _s OF tuint, _p OF tptr tschar, _tl OF tptr tvoid ]    
     PROP( 0 <= b < BINS /\ s = bin2sizeZ b /\ malloc_compatible BIGBLOCK p ) 
     LOCAL (temp _s (Vptrofs (Ptrofs.repr s)); temp _p p; temp _tl tl)
     SEP ( memory_block Tsh BIGBLOCK p; mmlist s tlen tl nullval )
  POST [ tptr tvoid ] EX res:_,
     PROP() 
     LOCAL(temp ret_temp res)
     SEP ( mmlist s (Z.to_nat(chunks_from_block (size2binZ s)) + tlen) res nullval * TT ).


(* The postcondition describes the list returned, together with
   TT for the wasted space at the beginning and end of the big block from mmap. *)

Definition fill_bin_spec :=
 DECLARE _fill_bin
  WITH b: _
  PRE [ _b OF tint ]
     PROP(0 <= b < BINS) LOCAL (temp _b (Vint (Int.repr b))) SEP ()
  POST [ (tptr tvoid) ] EX p:_, EX len:Z,
     PROP( if eq_dec p nullval then True else len > 0 ) 
     LOCAL(temp ret_temp p)
     SEP ( if eq_dec p nullval then emp
           else mmlist (bin2sizeZ b) (Z.to_nat len) p nullval * TT).

Definition malloc_small_spec :=
   DECLARE _malloc_small
   WITH n:Z, gv:globals, rvec:resvec
   PRE [ _nbytes OF size_t ] 
       PROP (0 <= n <= bin2sizeZ(BINS-1))
       LOCAL (temp _nbytes (Vptrofs (Ptrofs.repr n)); gvars gv)
       SEP ( mem_mgr_R gv rvec )
   POST [ tptr tvoid ] EX p:_, 
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( if guaranteed rvec n
             then mem_mgr_R gv (add_resvec rvec (size2binZ n) (-1)) *
                  malloc_token' Ews n p * memory_block Ews n p
             else if eq_dec p nullval 
                  then mem_mgr_R gv rvec 
                  else (EX rvec':_, !!(eq_except rvec' rvec (size2binZ n))
                                 && mem_mgr_R gv rvec' *
                                    malloc_token' Ews n p * memory_block Ews n p) ).


Definition malloc_large_spec :=
   DECLARE _malloc_large
   WITH n:Z, gv:globals, rvec:resvec
   PRE [ _nbytes OF size_t ]
       PROP (bin2sizeZ(BINS-1) < n <= Ptrofs.max_unsigned - (WA+WORD))
       LOCAL (temp _nbytes (Vptrofs (Ptrofs.repr n)); gvars gv)
       SEP ( mem_mgr_R gv rvec )
   POST [ tptr tvoid ] EX p:_, 
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr_R gv rvec;
            if eq_dec p nullval then emp 
            else malloc_token' Ews n p * memory_block Ews n p).

(* TODO needs update for resourced - or avoid the bother and just inline this function *)

(* s is the stored chunk size and n is the original request amount. *)
(* Note: the role of n in free_small_spec is merely to facilitate proof for free itself *)
Definition free_small_spec :=
   DECLARE _free_small
   WITH p:_, s:_, n:_, gv:globals, rvec:resvec
   PRE [ _p OF tptr tvoid, _s OF tuint ]
       PROP (0 <= n <= bin2sizeZ(BINS-1) /\ s = bin2sizeZ(size2binZ n) /\ 
             malloc_compatible s p)
       LOCAL (temp _p p; temp _s (Vptrofs (Ptrofs.repr s)); gvars gv)
       SEP ( data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p); 
            data_at_ Tsh (tptr tvoid) p;
            memory_block Tsh (s - WORD) (offset_val WORD p);
            mem_mgr_R gv rvec)
   POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr_R gv (add_resvec rvec (size2binZ n) 1)).

Definition free_large_spec :=
   DECLARE _free_large
   WITH p:_, s:_, gv:globals, rvec:resvec
   PRE [ _p OF tptr tvoid, _s OF tuint ]
       PROP (malloc_compatible s p /\ maxSmallChunk < s <= Ptrofs.max_unsigned - (WA+WORD))
       LOCAL (temp _p p; temp _s (Vptrofs (Ptrofs.repr s)); gvars gv)
       SEP ( data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p); 
            data_at_ Tsh (tptr tvoid) p;
            memory_block Tsh (s - WORD) (offset_val WORD p);
            memory_block Tsh WA (offset_val (- (WA+WORD)) p);
            mem_mgr_R gv rvec)
   POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr_R gv rvec).


(* TODO
Probably want two different sets of user specs, for resourced and not.
Private specs should just be the resourced ones, so no _R in their names. 
Also - ultimate user will use, e.g., malloc_spec or malloc_spec_R, not malloc_spec'.
*)
Definition external_specs := [mmap0_spec; munmap_spec].
Definition user_specs := [malloc_spec'; free_spec'].
Definition user_specs_R := [pre_fill_spec'; malloc_spec_R'; free_spec_R'].
Definition private_specs := [ malloc_large_spec; malloc_small_spec; free_large_spec; free_small_spec; bin2size_spec; size2bin_spec; list_from_block_spec; fill_bin_spec]. 




