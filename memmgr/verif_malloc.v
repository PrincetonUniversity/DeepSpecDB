Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

(* First draft specs.  Not specifying that chunks are aligned (but they are). 

Alert: overriding the definition of malloc_token, malloc_spec', and free_spec' in floyd.library *)

(* Note re CompCert 3: I'm currently using tuint for what in the code
is size_t.  That works for 32bit mode.  To generalize the proof
to 64bit as well, it may work to replace tuint by t_size_t defined like 
t_size_t := if Archi.ptr64 then tulong else tuint
*)


Require Import malloc.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Local Open Scope Z.
Local Open Scope logic.  

(* TODO 
Initially I imagined the constants would be defined as 
parameters (with suitable assumptions, e.g., BIGBLOCK
needs to be big enough for at least one chunk of the largest size,
because fill_bin unconditionally initializes the last chunk. 
*)
Definition WORD: Z := 4.  (* sizeof(size_t) 4 for 32bit Clight; 8 in clang *)
Definition ALIGN: Z := 2.
Definition BINS: Z := 8. 
Definition BIGBLOCK: Z := ((Z.pow 2 17) * WORD).

Lemma BIGBLOCK_repr: 
Int.repr BIGBLOCK = Int.mul (Int.shl (Int.repr 2) (Int.repr 16)) (Int.repr WORD).
Admitted.

Lemma BIGBLOCK_size: 0 <= BIGBLOCK <= Int.max_unsigned.
Proof. 
Admitted.

Definition bin2sizeZ := fun b: Z => (Z.mul ((Z.mul (b+1) ALIGN)-1) WORD).


Definition size2binZ : Z -> Z := fun s => 
   if zlt (bin2sizeZ(BINS-1)) s then -1 
   else (s+(Z.mul WORD (ALIGN-1))-1) / (Z.mul WORD ALIGN).


(* Require that BIGBLOCK fits at least one block of max size,
   together with the alignment prefix for that size. *)
Lemma BIGBLOCK_enough: bin2sizeZ(BINS-1) + bin2sizeZ(BINS-1) + WORD <= BIGBLOCK.
Admitted. 


(* Some sanity checks; may not be needed for code verification. *)

Lemma claim1: forall s,
0 <= s <= bin2sizeZ(BINS-1) -> s <= bin2sizeZ(size2binZ s).
Proof. intros. unfold bin2sizeZ in *. unfold size2binZ in *. simpl in *.
assert (H1: bin2sizeZ 7 = 60) by normalize. 
rewrite H1. unfold ALIGN, WORD. 
if_tac. omega.
Admitted.


Lemma claim2: forall s, 
0 <= s <= bin2sizeZ(BINS-1) -> 0 <= size2binZ s < BINS.
Admitted.

Lemma claim3: forall s, 0 <= s <= bin2sizeZ(BINS-1) 
    -> size2binZ(bin2sizeZ(size2binZ(s))) = size2binZ(s).
Admitted.

Lemma claim4: forall b,
0 <= b < BINS -> Z.rem (bin2sizeZ b + WORD) (Z.mul WORD ALIGN) = 0.
Proof.
intros.  unfold bin2sizeZ. unfold WORD. unfold ALIGN. 
Admitted.

Lemma claim5: forall b, 
0 <= b < BINS -> size2binZ(bin2sizeZ(b)) = b.
Proof.
  intros. unfold size2binZ.
  assert (H1: (bin2sizeZ (BINS - 1) >= (bin2sizeZ b))) 
    by ( unfold bin2sizeZ; unfold WORD, ALIGN, BINS in *; omega).
  destruct (zlt (bin2sizeZ (BINS - 1)) (bin2sizeZ b)) as [H2|H2]. contradiction.
  unfold bin2sizeZ. 
  assert (H3: 
     (((b + 1) * ALIGN - 1) * WORD + WORD * (ALIGN - 1) - 1) / (WORD * ALIGN)
     = (b*ALIGN*WORD + 2*ALIGN*WORD - 2*WORD -1)/(WORD*ALIGN)).
  (* TODO algebra incl. integer quotient *) admit. admit.
Admitted.


Definition  bin2sizeBINS_eq: 
ltac:(const_equation (bin2sizeZ(BINS-1))) := eq_refl.


Definition sbrk_spec := 
(* like malloc without token;
and I removed the possibility of failure to streamline the proof of fill_bin *)
   DECLARE _sbrk
   WITH n:Z
   PRE [ 1%positive OF tuint ]
       PROP (0 <= n <= Ptrofs.max_unsigned)
       LOCAL (temp 1%positive (Vptrofs (Ptrofs.repr n)))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( (* if eq_dec p nullval then emp else memory_block Tsh n p) *)
             memory_block Tsh n p).


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

(* malloc token: accounts for both the size field and padding.
n is the number of bytes requested.
Unfolding the definition reveals the stored size value and the
actual size of the block. 
The stored size value is not the request n but rather the
size of the block (not counting the size field).

Note that offset_val is in bytes, not like C pointer arith. 
*)
Definition malloc_token (sh: share) (n: Z) (p: val): mpred := 
   !! (0 <= n <= Ptrofs.max_unsigned) &&
   data_at Tsh tuint (offset_val (- WORD) p) 
        (Vptrofs (Ptrofs.repr (bin2sizeZ(size2binZ(n)))))
 * memory_block Tsh (bin2sizeZ(size2binZ(n)) - n) (offset_val n p). 

Lemma malloc_token_valid_pointer:
  forall sh n p, malloc_token sh n p |-- valid_pointer p.
Admitted.

Lemma malloc_token_valid_pointer_size:
  forall sh n p, malloc_token sh n p |-- valid_pointer (offset_val (- WORD) p).
Admitted.

Lemma malloc_token_precise:
  forall sh n p, predicates_sl.precise (malloc_token sh n p).
Admitted.

Lemma malloc_token_local_facts:
  forall sh n p, malloc_token sh n p 
  |-- !!( malloc_compatible n p /\ 0 <= n <= Ptrofs.max_unsigned ).
Admitted.

Hint Resolve malloc_token_valid_pointer : valid_pointer.
Hint Resolve malloc_token_valid_pointer_size : valid_pointer.
Hint Resolve malloc_token_precise : valid_pointer.
Hint Resolve malloc_token_local_facts : saturate_local.

(* linked list segment, for free blocks.
p points to a linked list of len blocks, terminated at r.
Blocks are viewed as (sz,nxt,remainder) where nxt points to the
next block in the list.  Each block begins with the stored size
value sz.  Each pointer, including p, points to the nxt field, 
not to sz.
The value of sz should be the number of bytes in (nxt,remainder)

The definition uses nat, for ease of termination check, at cost 
of Z conversions.  A segment prediicate is needed to cater for
fill_bin which grows the list at its tail.

TODO simplify base case using lemma ptr_eq_is_pointer_or_null ?

Note on range of sz:  Since the bins are for moderate sizes,
there's no need for sz > Int.max_unsigned, but the malloc/free API
uses size_t for the size, and jumbo blocks need to be parsed by
free even though they won't be in a bin, so this spec uses 
Ptrofs in conformance with the code's use of size_t.
*)
Fixpoint mmlist (sz: Z) (len: nat) (p: val) (r: val): mpred :=
 match len with
 | O => !! (0 <= sz <= Ptrofs.max_unsigned 
            /\ is_pointer_or_null p /\ ptr_eq p r) && emp 
 | (S n) => EX q:val, !! is_pointer_or_null q && 
            data_at Tsh tuint (Vptrofs (Ptrofs.repr sz)) (offset_val (- WORD) p) *
            data_at Tsh (tptr tvoid) q p *
            memory_block Tsh (sz - WORD) (offset_val WORD p) *
            mmlist sz n q r
 end.

Lemma mmlist_local_facts:
  forall sz len p r,
   mmlist sz len p r |--
   !! (0 <= sz <= Ptrofs.max_unsigned /\ 
       is_pointer_or_null p /\ is_pointer_or_null r /\ (p=r <-> len=O)).
Proof.
intros. revert p. 
induction len.
- (* 0 *) intros. unfold mmlist. entailer!. split; reflexivity.
- (* N>0 *) intros. entailer!.
Admitted.

Hint Resolve mmlist_local_facts : saturate_local.

Lemma mmlist_ne_valid_pointer:
  forall sz len p r,  (len > 0)%nat ->
   mmlist sz len p r |-- valid_pointer p.
Proof.
destruct len; unfold mmlist; fold mmlist; intros; normalize.
omega.  auto with valid_pointer.
Qed.

Hint Resolve mmlist_ne_valid_pointer : valid_pointer.

(* TODO lemmas for add/remove at head of mmlist 
   Could do a version in terms of malloc token but is that useful?
   Instead of add/remove entailments Andrew suggested a single result
   that's an equality (whence two-way entailment by pred_extensionality).
*)

Lemma mmlist_unroll_nonempty:
  forall sz len p, p <> nullval -> 
  ( mmlist sz len p nullval
  =   EX q:val,
      data_at Tsh tuint (Vptrofs (Ptrofs.repr sz)) (offset_val (- WORD) p) *
      data_at Tsh (tptr tvoid) q p *
      memory_block Tsh (sz - WORD) (offset_val WORD p) *
      mmlist sz (len - 1) q nullval
  ).
Admitted.


(* module invariant:
Each element of array points to a null-terminated list of right size blocks.

This version folds over index list, which makes it easy to express the 
block size per bin; it may facilitate per-index update.
*)
Definition mm_inv (arr: val): mpred := 
  EX bins: list val, EX lens: list nat,
  !! (Zlength bins = BINS /\ Zlength lens = BINS)  &&
  data_at Tsh (tarray (tptr tvoid) BINS) bins arr * 
  fold_right (fun (i: nat) => fun (mp: mpred) => 
      (mmlist (bin2sizeZ (Z.of_nat i)) (nth i lens O) (nth i bins nullval) nullval) * mp )
     emp 
     (seq 0 (Z.to_nat BINS)).

(* copy of malloc_spec' from floyd library, with mm_inv added *)
Definition malloc_spec' := 
   DECLARE _malloc
   WITH n:Z, bin:val
   PRE [ 1%positive OF tuint ]
       PROP (0 <= n <= Ptrofs.max_unsigned)
       LOCAL (temp 1%positive (Vptrofs (Ptrofs.repr n)); gvar _bin bin)
       SEP ( mm_inv bin )
   POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mm_inv bin;
             if eq_dec p nullval then emp
             else (malloc_token Tsh n p * memory_block Tsh n p)).

Definition free_spec' := (* copy from floyd lib, with mm_inv added *)
   DECLARE _free
   WITH p:_, n:_, bin:_
   PRE [ 1%positive OF tptr tvoid ]
       PROP ()
       LOCAL (temp 1%positive p; gvar _bin bin)
       SEP (malloc_token Tsh n p; memory_block Tsh n p; mm_inv bin)
   POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mm_inv bin).

Definition malloc_small_spec :=
   DECLARE _malloc_small
   WITH n:Z, bin:val
   PRE [ 1%positive OF tuint ]
       PROP (0 <= n <= bin2sizeZ(BINS-1))
       LOCAL (temp 1%positive (Vptrofs (Ptrofs.repr n)); gvar _bin bin)
       SEP ( mm_inv bin )
   POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mm_inv bin; 
            if eq_dec p nullval then emp
            else (malloc_token Tsh n p * memory_block Tsh n p)).

Definition free_small_spec :=
   DECLARE _free_small
   WITH p:_, n:_, bin:_
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tint ]
       PROP (0 <= n <= bin2sizeZ(BINS-1))
       LOCAL (temp 1%positive p; temp 2%positive (Vptrofs (Ptrofs.repr n)); gvar _bin bin)
       SEP (malloc_token Tsh n p; memory_block Tsh n p; mm_inv bin)
   POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mm_inv bin).


(* The postcondition describes the list returned.  It ignores the 
wasted space at the beginning and end of the big block from sbrk. *)
Definition fill_bin_spec :=
 DECLARE _fill_bin
  WITH b: _
  PRE [ _b OF tint ]
     PROP(0 <= b < BINS) LOCAL (temp _b (Vint (Int.repr b))) SEP ()
  POST [ (tptr tvoid) ] EX p:_, EX len:Z,
     PROP( len > 0 ) 
     LOCAL(temp ret_temp p)
     SEP ( mmlist (bin2sizeZ b) (Z.to_nat len) p nullval ).


Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ]  main_post prog nil u.

Definition Gprog : funspecs := 
 ltac:(with_library prog [ 
   sbrk_spec; bin2size_spec; size2bin_spec; fill_bin_spec;
   malloc_small_spec; free_small_spec; malloc_spec'; free_spec';
   main_spec]).


Lemma body_bin2size: semax_body Vprog Gprog f_bin2size bin2size_spec.
Proof. start_function. 
unfold BINS in H.
forward. entailer!. repeat split; try rep_omega. 
Qed.

(* Opaque BINS.*)

Lemma body_size2bin: semax_body Vprog Gprog f_size2bin size2bin_spec.
Proof. start_function. 
  forward_call (BINS-1).  unfold BINS;   omega.
  assert (H0:= bin2sizeBINS_eq).
  forward_if(PROP() LOCAL() SEP (FF)). (* FF because join point unreachable *)
  - (* then *) 
  forward. entailer!. f_equal. f_equal. unfold size2binZ; simpl. if_tac; normalize.  
  - (* else *)
  forward.  entailer!. f_equal. unfold size2binZ. unfold BINS in *. if_tac.
    +  simpl in H2. rewrite Int.unsigned_repr in H1. omega.  simpl in H0.  rep_omega. 
    + admit. (* TODO divu property *) 
  - (* fi *) entailer.
Admitted.


(* Invariant for loop in fill_bin.
q points to the beginning of a list block (size field), unlike the link field
which points to the link field of the following list block. 
The mmlist predicate also refers to link field addresses.
*)

Definition fill_bin_Inv (p:val) (s:Z) (N:Z) := 
  EX j:_,
  PROP ( N = (BIGBLOCK-s) / (s+WORD) /\ 
         0 <= s <= bin2sizeZ(BINS-1) /\
         0 <= j < N )  
(* j remains strictly smaller than N because 
j is the number of finished blocks, and the last block
gets finished following the loop 
TODO also waste at high end? or can be ignored owing to intuitionistic SL?
*)
  LOCAL( temp _q (offset_val (s+(j*(s+WORD))) p);
         temp _p p; 
         temp _s       (Vint (Int.repr s));
         temp _Nblocks (Vint (Int.repr N));
         temp _j       (Vint (Int.repr j)))  
  SEP (memory_block Tsh s p; (* waste *)
       mmlist s (Z.to_nat j) (offset_val s p) (offset_val (s+(j*(s+WORD))) p); 
       memory_block Tsh (BIGBLOCK-(s+j*(WORD+s))) (offset_val (s+(j*(s+WORD))) p)). (* big block *)


(* fold an mmlist with tail pointing to next object. *)
Lemma fill_bin_mmlist:
  forall s j r q,
  mmlist s (Z.to_nat j) r q * 
  field_at Tsh (tarray tuint 1) [] [(Vint (Int.repr s))] q * 
  memory_block Tsh (s-WORD) (offset_val (WORD+WORD) q) *
  field_at Tsh (tptr tvoid) [] (offset_val (s+WORD) q) (offset_val WORD q)  
  =
  mmlist s (Z.to_nat (j+1)) r (offset_val (s+WORD) q ).
Proof.
(* TODO The LHS uses (tarray tuint 1) for the size field because 
that's how the store instruction is written. But mmlist is currently 
defined using simply tuint; change mmlist before proving this?
*)
Admitted.

(* fold an mmlist with tail pointing to null
TODO ugh! quick hack for now; clean up after verifying malloc&free 
Also: I've ordered the conjuncts to match where used; it would be 
nicer to order same as in def of mmlist. 
*)
Lemma fill_bin_mmlist_null:
  forall s j r q,
  mmlist s (Z.to_nat j) r q * 
  field_at Tsh (tarray tuint 1) [] [(Vint (Int.repr s))] q * 
  field_at Tsh (tptr tvoid) [] nullval (offset_val WORD q) *
  memory_block Tsh (s-WORD) (offset_val (WORD+WORD) q) 
  =
  mmlist s (Z.to_nat (j+1)) r nullval.
Proof.
(* TODO The LHS uses (tarray tuint 1) for the size field because 
that's how the store instruction is written. But mmlist is currently 
defined using simply tuint; change mmlist before proving this?
*)
Admitted.



Lemma memory_block_split_block:
  forall s m q, 0 <= s /\ s+WORD <= m -> 
   memory_block Tsh m q = 
   data_at_ Tsh (tarray tuint 1) q * (*size*)
   data_at_ Tsh (tptr tvoid) (offset_val WORD q) * (*nxt*)   
   memory_block Tsh (s - WORD) (offset_val (WORD+WORD) q) * (*rest of block*)
   memory_block Tsh (m-(s+WORD)) (offset_val (s+WORD) q). (*rest of big*)
Proof.
intros s m q [Hs Hm]. 
(* TODO first rewrite big memory block into memory blocks including
   memory_block Tsh WORD q * (*size*)
   memory_block Tsh WORD (offset_val WORD q) * (*nxt*)   
then use lemma memory_block_data_at_ 
 *) 
Admitted. 

Lemma weak_valid_pointer_end:
forall p,
valid_pointer (offset_val (-1) p) |-- weak_valid_pointer p.
Admitted.

Lemma sepcon_weak_valid_pointer1: 
 forall (P Q : mpred) (p : val),
   P |-- weak_valid_pointer p -> P * Q |-- weak_valid_pointer p.
Admitted.

Lemma sepcon_weak_valid_pointer2:
  forall (P Q : mpred) (p : val),
    P |-- weak_valid_pointer p -> Q * P |-- weak_valid_pointer p.
Admitted.

Hint Resolve weak_valid_pointer_end: valid_pointer. 
Hint Resolve sepcon_weak_valid_pointer1: valid_pointer. 
Hint Resolve sepcon_weak_valid_pointer2: valid_pointer. 

Lemma memory_block_weak_valid_pointer:
forall n p sh,
 sepalg.nonidentity sh ->
 memory_block sh n p
  |-- weak_valid_pointer p.
Admitted.

Lemma memory_block_weak_valid_pointer2:
forall (sh : share) (n : Z) (p : val) (i : Z),
       0 <= i <= n ->
       sepalg.nonidentity sh ->
       memory_block sh n p |-- weak_valid_pointer (offset_val i p).
Admitted.

Hint Resolve memory_block_weak_valid_pointer: valid_pointer. 

(* maybe: *)
Hint Resolve memory_block_weak_valid_pointer2: valid_pointer.


Lemma body_fill_bin: semax_body Vprog Gprog f_fill_bin fill_bin_spec.
Proof. 
assert (H0:= bin2sizeBINS_eq).
start_function. 
forward_call (b).  (* s = bin2size(b) *)
set (s:=bin2sizeZ b).
assert (0 <= s <= bin2sizeZ(BINS-1)).
{ unfold s. admit. (* monotonicities of arith *) }
clearbody s.
forward_call (BIGBLOCK).  (* *p = sbrk(BIGBLOCK) *)  
{ apply BIGBLOCK_size. }
Intros p.    
forward. (* Nblocks = (BIGBLOCK-s) / (s+WORD) *)
{ (* nonzero divisor *) entailer!. rewrite Int.eq_false. simpl; auto. 
  unfold Int.zero. intro. apply repr_inj_unsigned in H3;  auto; rep_omega. }
deadvars!.  clear H.  
assert_PROP (isptr p) by entailer!. destruct p; try contradiction.
rename b0 into pblk. rename i into poff. (* p as blk+ofs *)
unfold BINS in *; simpl in *.
forward. (* q = p+s *)
rewrite ptrofs_of_intu_unfold.
rewrite ptrofs_mul_repr.
normalize.
forward. (* j = 0 *) 
forward_while (fill_bin_Inv (Vptr pblk poff) s ((BIGBLOCK-s) / (s+WORD)) ).

* (* pre implies inv *)
  Exists 0. 
  (*   Exists ((BIGBLOCK - s) / (s + WORD)). *)
  entailer!.
  - repeat split; try omega.
    + assert (Hbig: BIGBLOCK - s > 0). 
      { unfold BIGBLOCK. simpl. rewrite H0 in H1. omega. }
      admit. (* TODO arith *)
    + admit. (* arith fact, and WORD = sizeof tuint *)
    + rep_omega.
    + apply Ptrofs.eq_true.
  - replace BIGBLOCK with (s+(BIGBLOCK-s)) at 1 by omega.
     rewrite <- (Ptrofs.repr_unsigned poff). 
     rewrite  memory_block_split; try omega. 
     + entailer!. 
     + admit. (* by BIGBLOCK_enough *) 
     + admit. (* Ptrofs and arith *)

* (* pre implies guard defined *)
  entailer!. (* TODO entailer! used to suffice here, and it's just Int  *)
  admit.

* (* body preserves inv *)
  freeze [0] Fwaste. clear H.
  rewrite (memory_block_split_block s (BIGBLOCK - (s + j * (WORD + s))) 
             (offset_val (s + j * (s + WORD)) (Vptr pblk poff))).
  Intros. (* flattens the SEP clause *)
  do 3 rewrite offset_offset_val. (* TODO knee-jerk simplification, undone later *)

  forward. (*** q[0] = s; ***)
  freeze [1; 2; 4; 5] fr1.  
  assert_PROP ( 
  (Vptr pblk
      (Ptrofs.add (Ptrofs.add poff (Ptrofs.repr (s + j * (s + WORD))))
        (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr 1))))) 
    = field_address (tptr tvoid) [] 
        (offset_val (s + j * (s + WORD) + WORD) (Vptr pblk poff))).
  { entailer!. unfold field_address.  simpl. normalize. admit. } 

  forward. (*** *(q+WORD) = q+(s+WORD); ***)
  forward. (*** q += s+WORD; ***)
  forward. (*** j++; ***) 
    admit. (* typecheck j+1 *)
  (* reestablish inv *)  
  Exists (j+1). entailer!.  normalize. 
  { split. 
   + destruct H2 as [H2a [H2b H2c]]. admit. (* by arith from HRE and H2c *)
   + do 3 f_equal. unfold WORD. admit. (* by arith *) }
  thaw fr1.  thaw Fwaste.
  do 2 cancel.
normalize.
(* folding the list: *)  

assert (Hsing:
(upd_Znth 0 (default_val (nested_field_type (tarray tuint 1) []))
       (Vint (Int.repr s)))
 = [(Vint (Int.repr s))]) by (unfold default_val; normalize).
rewrite Hsing; clear Hsing.

(* cancel the big block *)
assert (Hbsz: 
   (BIGBLOCK - (s + j * (WORD + s)) - (s + WORD))
 = (BIGBLOCK - (s + (j + 1) * (WORD + s)))) by admit.
rewrite Hbsz; clear Hbsz.
assert (Hbpt:
   (offset_val (s + j * (s + WORD) + (s + WORD)) (Vptr pblk poff))
 = (Vptr pblk (Ptrofs.add poff (Ptrofs.repr (s + (j + 1) * (s + WORD)))))) by admit.
rewrite <- Hbpt; clear Hbpt.
cancel.

(* apply folding lemma *)
assert (Hs: (Vptr pblk (Ptrofs.add poff (Ptrofs.repr s)))
  = (offset_val s (Vptr pblk poff))) by normalize.
rewrite Hs; clear Hs.
assert (Hq: 
   (Vptr pblk (Ptrofs.add poff (Ptrofs.repr (s + j * (s + WORD) + (s + 4)))))
 = (offset_val (s+WORD) (offset_val (s + j * (s + WORD)) (Vptr pblk poff)))) by normalize.
rewrite Hq; clear Hq.
assert (Hq4:
   (Vptr pblk (Ptrofs.add poff (Ptrofs.repr (s + j * (s + WORD) + WORD))))
 = (offset_val WORD (offset_val (s + j * (s + WORD)) (Vptr pblk poff)))) by
normalize.
rewrite Hq4; clear Hq4.
assert (Hq:
   (offset_val (s + j * (s + WORD) + (WORD + WORD)) (Vptr pblk poff)) 
 = (offset_val (WORD+WORD) (offset_val (s + j * (s + WORD)) (Vptr pblk poff)))) by normalize.
rewrite Hq; clear Hq.
rewrite fill_bin_mmlist.
entailer!.

(* TODO held over bound on s - arith *)
admit.

  * (* after the loop *) 
(* TODO eventually: here we're setting up the assignments 
to finish the last block; this is like setting up in the loop body.
Then we fold into the list, like end of loop body. 
It would be nice to factor commonalities. *)

rewrite (memory_block_split_block s (BIGBLOCK - (s + j * (WORD + s))) 
           (offset_val (s + j * (s + WORD)) (Vptr pblk poff))).
Intros. (* flattens the SEP clause *) 
rewrite offset_offset_val.
freeze [0;5] Fwaste. (* discard what's not needed for post *)

forward. (*** q[0] = s ***)
assert (Hsing:
(upd_Znth 0 (default_val (nested_field_type (tarray tuint 1) []))
       (Vint (Int.repr s)))
 = [(Vint (Int.repr s))]) by (unfold default_val; normalize).
rewrite Hsing; clear Hsing.

assert_PROP (
  (Vptr pblk
    (Ptrofs.add (Ptrofs.add poff (Ptrofs.repr (s + j * (s + WORD))))
      (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr 1)))) 
  = field_address (tptr tvoid) []
      (offset_val (s + j * (s + WORD) + WORD) (Vptr pblk poff)))) by admit. 

forward. (***   *(q+WORD) = NULL ***)

assert (Hqw: 
  (offset_val (s + j * (s + WORD) + WORD) (Vptr pblk poff))
=  (offset_val WORD (offset_val (s + j * (s + WORD)) (Vptr pblk poff)))) by normalize.
rewrite Hqw; clear Hqw.

change (Vint (Int.repr 0)) with nullval.



(* WORKING HERE
The proof state seems set up to do 
  rewrite fill_bin_mmlist_null.
which should unify with
   r := (offset_val s (Vptr pblk poff))
   q := (offset_val (s + j*(s+WORD)) (Vptr pblk poff))
But I get an error, no matching subterm. 
A similar rewrite is done earlier in the proof, but inside an entailment.  
So I'm trying forward, expecting to get the entailment.
*) 


forward. (***   return p+s+WORD ***) 










assert (Hs: s = bin2sizeZ(b)) by admit. (* how to get this? s was set at outset *) 




(* TODO likely lemmas for malloc_small?
- Adding or removing at the head preserves mmlist (just unfold def, 
increment or decrement the length witness).
- If bin[i] is null then assigning an mmlist preserves mm_inv 
(induct on indices to get to i).
*)
Lemma body_malloc_small:  semax_body Vprog Gprog f_malloc_small malloc_small_spec.
Proof. 
start_function. 
rewrite <- seq_assoc.
(*
forward_call (n).
*)
(* ??? why does this fail?  *)

(* 
freeze [0] MMinv.
thaw MMinv.
*)



Lemma body_free_small:  semax_body Vprog Gprog f_free_small free_small_spec.
Admitted.

(* TODO Complete implementation of malloc and free,
   and an interesting main, before verifying these. *)
Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Admitted.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_size2bin.
semax_func_cons body_bin2size.
semax_func_cons body_fill_bin.
semax_func_cons body_malloc_small.
semax_func_cons body_free_small.
semax_func_cons body_malloc.
semax_func_cons body_free.
semax_func_cons body_main.
Qed.

