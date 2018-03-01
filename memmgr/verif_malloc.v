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
because fill_bin unconditionally initializes the last chunk). 
The proofs should guide us to the requisite constraints.
*)
Definition WORD: Z := 4.  (* sizeof(size_t) is 4 for 32bit Clight *)
Definition ALIGN: Z := 2.
Definition BINS: Z := 8. 
Definition BIGBLOCK: Z := ((Z.pow 2 17) * WORD).

Lemma BIGBLOCK_repr: 
Int.repr BIGBLOCK = Int.mul (Int.shl (Int.repr 2) (Int.repr 16)) (Int.repr WORD).
Admitted.

Lemma BIGBLOCK_size: 0 <= BIGBLOCK <= Int.max_unsigned.
Proof. 
Admitted.

Lemma BINS_eq: BINS=8.  Proof. reflexivity. Qed.
Hint Rewrite BINS_eq : rep_omega.

Lemma BIGBLOCK_eq: BIGBLOCK=524288.  Proof. reflexivity. Qed.
Hint Rewrite BIGBLOCK_eq : rep_omega.


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

(* PENDING revision for irregular blocks - allows for larger than request,
   without constraining hom much larger *)
Definition malloc_tok (sh: share) (n: Z) (p: val) (s: Z): mpred := 
   !! (0 <= n <= s /\ s <= Ptrofs.max_unsigned ) &&
   data_at Tsh tuint (offset_val (- WORD) p) (Vptrofs (Ptrofs.repr s))
 * memory_block Tsh (s - n) (offset_val n p). 
Definition malloc_token' (sh: share) (n: Z) (p: val): mpred := 
   EX s:Z, malloc_tok sh n p s.



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

(* linked list segment, for free blocks of a fixed size.

p points to a linked list of len blocks, terminated at r.

Blocks are viewed as (sz,nxt,remainder) where nxt points to the
next block in the list.  Each block begins with the stored size
value sz.  Each pointer, including p, points to the nxt field, 
not to sz.
The value of sz should be the number of bytes in (nxt,remainder)

A segment predicate is needed to cater for fill_bin which grows 
the list at its tail. For non-empty segment, terminated at r means 
that r is the nxt field of the last block -- which may be null or 
a valid pointer to not-necessarily-initialized memory. 

The definition uses nat, for ease of termination check, at cost 
of Z conversions.  

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

(* PENDING exploring variation for list of irregular blocks. 
May not be needed; may use map from sizes to same-size lists.
*)

Fixpoint mmlist_irr (len: nat) (p: val) (r: val): mpred :=
 match len with
 | O => !! (is_pointer_or_null p /\ ptr_eq p r) && emp 
 | (S n) => EX q:val, 
            EX s:Z, !! is_pointer_or_null q && 
         data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p) *
         data_at Tsh (tptr tvoid) q p *
         memory_block Tsh (s - WORD) (offset_val WORD p) *
         mmlist_irr n q r
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

Lemma mmlist_ne_len:
  forall sz len p q, p<>q ->
    mmlist sz len p q |-- !! ((Z.of_nat len) > 0).
Proof.
Admitted.

(* ?? TODO fix this abomination:
The following is formulated as an equality so it can be used in 
both directions.  It is followed by a second copy, where "len - 1"
is written using Nat.pred to get around Coq's not inferring the type
in scripts, though it does infer the type for len - 1 in the lemma.

One way is to replace len by (Z.to_nat len).

*)
Lemma mmlist_unroll_nonempty:
  forall sz len p, p <> nullval -> (Z.of_nat len) > 0 -> 
  ( mmlist sz len p nullval
  =   EX q:val,
      data_at Tsh tuint (Vptrofs (Ptrofs.repr sz)) (offset_val (- WORD) p) *
      data_at Tsh (tptr tvoid) q p *
      memory_block Tsh (sz - WORD) (offset_val WORD p) *
      mmlist sz (len - 1) q nullval
  ).
Admitted.

(* stupid copy of preceding lemma *)
Lemma mmlist_unroll_nonempty':
  forall sz len p, p <> nullval -> (Z.of_nat len) > 0 -> 
  ( mmlist sz len p nullval
  =   EX q:val,
      data_at Tsh tuint (Vptrofs (Ptrofs.repr sz)) (offset_val (- WORD) p) *
      data_at Tsh (tptr tvoid) q p *
      memory_block Tsh (sz - WORD) (offset_val WORD p) *
      mmlist sz (Nat.pred len) q nullval
  ).
Admitted.

Lemma mmlist_empty: 
  forall sz len, mmlist sz len nullval nullval = emp.
Admitted.


(* lemmas on constructing an mmlist from a big block (used in fill_bin) *)

(* fold an mmlist with tail pointing to initialized next object. *)
Lemma fill_bin_mmlist:
  forall s j r q,
  mmlist s (Z.to_nat j) r (offset_val WORD q) * 
  field_at Tsh (tarray tuint 1) [] [(Vint (Int.repr s))] q * 
  memory_block Tsh (s-WORD) (offset_val (WORD+WORD) q) *
  field_at Tsh (tptr tvoid) [] (offset_val (s+WORD+WORD) q) (offset_val WORD q)  
  =
  mmlist s (Z.to_nat (j+1)) r (offset_val (s+WORD+WORD) q ).
Proof.
(* TODO The LHS uses (tarray tuint 1) for the size field because 
that's how the store instruction is written. But mmlist is currently 
defined using simply tuint; change mmlist before proving this?
The lemmas also probably need antecedents about integer ranges.
*)
Admitted.

(* fold an mmlist with tail pointing to null
TODO ugh! quick hack for now; clean up after verifying malloc&free 
Also: I've ordered the conjuncts to match where used; it would be 
nicer to order same as in def of mmlist. 
*)
Lemma fill_bin_mmlist_null: 
  forall s j r q,
  mmlist s (Z.to_nat j) r (offset_val WORD q) * 
  field_at Tsh (tarray tuint 1) [] [(Vint (Int.repr s))] q * 
  field_at Tsh (tptr tvoid) [] nullval (offset_val WORD q) *
  memory_block Tsh (s-WORD) (offset_val (WORD+WORD) q) 
  = 
  mmlist s (Z.to_nat (j+1)) r nullval.
Proof.
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



(* module invariant:

Each element of array points to a null-terminated list of right size blocks.

This version folds over index list, which makes it easy to express the 
block size per bin; it may facilitate per-index update.

Not making a local-facts lemma, because it's the split form that will 
be used most.

TODO: add TT so TT can be removed from the post of malloc.
*)
Definition mm_inv (arr: val): mpred := 
  EX bins: list val, EX lens: list nat,
  !! (Zlength bins = BINS /\ Zlength lens = BINS)  &&
  data_at Tsh (tarray (tptr tvoid) BINS) bins arr * 
  fold_right (fun (i: Z) => fun (mp: mpred) => 
      (mmlist (bin2sizeZ i) (Znth i lens O) (Znth i bins Vundef) nullval) * mp )
     emp 
     (map Z.of_nat (seq 0 (Z.to_nat BINS))).


Lemma mm_inv_split: (* extract list at index b *)
 forall arr, forall b:Z, 0 <= b < BINS ->
   mm_inv arr  
 = 
  EX bins: list val, EX lens: list nat,
  !! (Zlength bins = BINS /\ Zlength lens = BINS)  &&
    data_at Tsh (tarray (tptr tvoid) BINS) bins arr 
  * fold_right (fun (i: nat) => fun (mp: mpred) => 
     (mmlist (bin2sizeZ (Z.of_nat i)) (nth i lens O) (nth i bins Vundef) nullval) * mp )
     emp 
     (filter (fun (i: nat) =>
       negb (Nat.eqb i (Z.to_nat b))) (seq 0 (Z.to_nat BINS)))
  * (mmlist (bin2sizeZ b) (Znth b lens O) (Znth b bins Vundef) nullval).
Proof.
Admitted.



(* technical result about the fold in mm_inv *)
Lemma mm_inv_fold_except_b:
forall (bins: list val) bins' (lens: list nat) lens' b p n, 
bins' = upd_Znth b bins p ->
lens' = upd_Znth b lens n ->
       (fold_right
          (fun (i : nat) (mp : mpred) =>
           mmlist (bin2sizeZ (Z.of_nat i)) (nth i lens 0%nat)
             (nth i bins Vundef) nullval * mp) emp
          (filter (fun i : nat => negb (i =? Z.to_nat b)%nat)
             (seq 0 (Z.to_nat BINS))))
= 
       (fold_right
          (fun (i : nat) (mp : mpred) =>
           mmlist (bin2sizeZ (Z.of_nat i)) (nth i lens' 0%nat)
             (nth i bins' Vundef) nullval * mp) emp
          (filter (fun i : nat => negb (i =? Z.to_nat b)%nat)
             (seq 0 (Z.to_nat BINS)))).
Proof. 
(* (nth i bins Vundef) and (nth i lens Vundef) only eval'd at i<>b and bins' lens' differ only there *)
Admitted.



(* TODO it would be nice to combine this to_* lemma with the following from_* one. 
Also make the size-unrestricted one work for all cases.
*)
Lemma to_malloc_token_and_block:
forall n p q sz, 0 <= n <= bin2sizeZ(BINS-1) -> sz = bin2sizeZ(size2binZ(n)) -> 
(     data_at Tsh tuint (Vptrofs (Ptrofs.repr sz)) (offset_val (- WORD) p) *
     ( data_at Tsh (tptr tvoid) q p *
     memory_block Tsh (sz - WORD) (offset_val WORD p)  )
|--  malloc_token Tsh n p * memory_block Tsh n p).
Admitted.


Lemma from_malloc_token_and_block: 
forall n p sz,
  0 <= n <= Ptrofs.max_unsigned -> sz = bin2sizeZ(size2binZ(n)) -> 
    (malloc_token Tsh n p * memory_block Tsh n p)
  = ( data_at Tsh tuint (Vptrofs (Ptrofs.repr sz)) (offset_val (- WORD) p) *
      data_at_ Tsh (tptr tvoid) p *
      memory_block Tsh (sz - WORD) (offset_val WORD p) 
).
Admitted.
(* Maybe prove in two steps: 
from (malloc_token Tsh n p * memory_block Tsh n p)
get (data_at Tsh tuint (Vptrofs (Ptrofs.repr sz)) (offset_val (- WORD) p) *
     memory_block Tsh n p) * 
     memory_block Tsh (bin2sizeZ(size2binZ(n)) - n) (offset_val n p). 
whence 
    (data_at Tsh tuint (Vptrofs (Ptrofs.repr sz)) (offset_val (- WORD) p) *
     memory_block Tsh sz p) *
     memory_block Tsh (bin2sizeZ(size2binZ(n)) - n) (offset_val n p). 
and finally, carve off the pointer field at p and catenate the remainder block.
*)



(* copy of malloc_spec' from floyd library, with mm_inv added *)
Definition malloc_spec' := 
   DECLARE _malloc
   WITH n:Z, bin:val
   PRE [ _nbytes OF tuint ]
       PROP (0 <= n <= Ptrofs.max_unsigned)
       LOCAL (temp _nbytes (Vptrofs (Ptrofs.repr n)); gvar _bin bin)
       SEP ( mm_inv bin )
   POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mm_inv bin;
             if eq_dec p nullval then emp
             else (malloc_token Tsh n p * memory_block Tsh n p)).

(* copy from floyd lib, revised to allow NULL as per unix std,
and with mm_inv added.
n is the requested size, not the actual block size *)
Definition free_spec' := 
   DECLARE _free
   WITH p:_, n:_, bin:_
   PRE [ _p OF tptr tvoid ]
       PROP ()
       LOCAL (temp _p p; gvar _bin bin)
       SEP (mm_inv bin; 
            if eq_dec p nullval then emp
            else (malloc_token Tsh n p * memory_block Tsh n p))
   POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mm_inv bin).

(* Using TT as simple way to account for waste space *)

Definition malloc_small_spec :=
   DECLARE _malloc_small
   WITH n:Z, bin:val
   PRE [ _nbytes OF tuint ]
       PROP (0 <= n <= bin2sizeZ(BINS-1))
       LOCAL (temp _nbytes (Vptrofs (Ptrofs.repr n)); gvar _bin bin)
       SEP ( mm_inv bin )
   POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mm_inv bin; 
            if eq_dec p nullval then emp
            else (malloc_token Tsh n p * memory_block Tsh n p * TT)).

(* s is the stored block size and n is the original request amount. *)
Definition free_small_spec :=
   DECLARE _free_small
   WITH p:_, s:_, bin:_, n:_
   PRE [ _p OF tptr tvoid, _s OF tuint ]
       PROP (0 <= n <= bin2sizeZ(BINS-1) /\ s = bin2sizeZ(size2binZ(n)))
       LOCAL (temp _p p; temp _s (Vptrofs (Ptrofs.repr s)); gvar _bin bin)
       SEP (malloc_token Tsh n p; memory_block Tsh n p; mm_inv bin )
   POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mm_inv bin).


(* The postcondition describes the list returned, together with
   TT for the wasted space at the beginning and end of the big block from sbrk. *)
Definition fill_bin_spec :=
 DECLARE _fill_bin
  WITH b: _
  PRE [ _b OF tint ]
     PROP(0 <= b < BINS) LOCAL (temp _b (Vint (Int.repr b))) SEP ()
  POST [ (tptr tvoid) ] EX p:_, EX len:Z,
     PROP( len > 0 ) 
     LOCAL(temp ret_temp p)
     SEP ( mmlist (bin2sizeZ b) (Z.to_nat len) p nullval * TT).


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
Proof. start_function. forward. 
Qed.

(* Opaque BINS.*)

Lemma body_size2bin: semax_body Vprog Gprog f_size2bin size2bin_spec.
Proof. start_function. 
  forward_call (BINS-1).  
  rep_omega. (* prev: unfold BINS;   omega. *)
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
  PROP ( N = (BIGBLOCK-s) / (s+WORD) /\ (* number of blocks that fit in big block *)
         0 <= s <= bin2sizeZ(BINS-1) /\ (* size of each block *)
         0 <= j < N )  
(* j remains strictly smaller than N because j is the number 
of finished blocks and the last block gets finished following the loop. *)
  LOCAL( temp _q (offset_val (s+(j*(s+WORD))) p);
         temp _p p; 
         temp _s       (Vint (Int.repr s));
         temp _Nblocks (Vint (Int.repr N));
         temp _j       (Vint (Int.repr j)))  
(* (offset_val (s+ M + WORD) p) accounts for waste plus M many blocks plus
the offset for size field.  The last block's nxt points one word _inside_ 
the remaining part of the big block. *)
  SEP (memory_block Tsh s p; (* waste *)
       mmlist s (Z.to_nat j) (offset_val (s + WORD) p) 
                             (offset_val (s + (j*(s+WORD)) + WORD) p); 
       memory_block Tsh (BIGBLOCK-(s+j*(WORD+s))) (offset_val (s+(j*(s+WORD))) p)). 



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
forward_call b.  (*** s = bin2size(b) ***)
set (s:=bin2sizeZ b).
assert (0 <= s <= bin2sizeZ(BINS-1)).
{ unfold s. admit. (* monotonicities of arith *) }
(* clearbody s. -- nope, need (s = bin2sizeZ b) for return; or rewrite post now? *)
forward_call BIGBLOCK.  (*** *p = sbrk(BIGBLOCK) ***)  
{ apply BIGBLOCK_size. }
Intros p.    
forward. (*** Nblocks = (BIGBLOCK-s) / (s+WORD) ***)
{ (* nonzero divisor *) entailer!. 
unfold Int.zero in H3. apply repr_inj_unsigned in H3; rep_omega. }
deadvars!.  clear H.  
assert_PROP (isptr p) by entailer!. destruct p; try contradiction.
rename b0 into pblk. rename i into poff. (* p as blk+ofs *)
unfold BINS in *; simpl in H0,H1
|-*. (* should be simpl in * but messes up postcond *)
forward. (*** q = p+s ***)
rewrite ptrofs_of_intu_unfold. rewrite ptrofs_mul_repr. normalize.
forward. (*** j = 0 ***) 

forward_while (fill_bin_Inv (Vptr pblk poff) s ((BIGBLOCK-s) / (s+WORD)) ).

* (* pre implies inv *)
  Exists 0. 
  entailer!.
  - repeat split; try omega.
    + assert (Hbig: BIGBLOCK - s > 0). 
      { unfold BIGBLOCK. simpl. rewrite H0 in H1. omega. }
      admit. (* arith *)
    + admit. (* arith fact, and WORD = sizeof tuint *)
    + apply Ptrofs.eq_true.
  - replace BIGBLOCK with (s+(BIGBLOCK-s)) at 1 by omega.
     rewrite <- (Ptrofs.repr_unsigned poff). 
     rewrite  memory_block_split; try omega. 
     + entailer!. 
     + admit. (* by BIGBLOCK_enough *) 
     + admit. (* Ptrofs and arith *)

* (* pre implies guard defined *)
  entailer!. (* ?? TODO entailer! used to suffice here, and it's just Int  *)
  admit. (* arith *)

* (* body preserves inv *)
  freeze [0] Fwaste. clear H.
  rewrite (memory_block_split_block s (BIGBLOCK - (s + j * (WORD + s))) 
             (offset_val (s + j * (s + WORD)) (Vptr pblk poff))).
- Intros. (* flattens the SEP clause *)
  rewrite offset_offset_val. 
  forward. (*** q[0] = s; ***)
  freeze [1; 2; 4; 5] fr1.
  (* prepare for next assignment, as suggested by hint from forward tactic *)
  assert_PROP ( 
  (Vptr pblk
      (Ptrofs.add (Ptrofs.add poff (Ptrofs.repr (s + j * (s + WORD))))
        (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr 1))))) 
    = field_address (tptr tvoid) [] 
        (offset_val (s + j * (s + WORD) + WORD) (Vptr pblk poff))).
  { entailer!. unfold field_address.  simpl. normalize. 
    admit. (* involves invariant, value of N, constraints on BIGBLOCK etc *) } 
  forward. (*** *(q+WORD) = q+WORD+(s+WORD); ***)
  forward. (*** q += s+WORD; ***)
  forward. (*** j++; ***) 
    admit. (* typecheck j+1 *)
  (* reestablish inv *)  
  Exists (j+1).  entailer!.  normalize. 
  { split. 
   + destruct H2 as [H2a [H2b H2c]]. admit. (* by arith from HRE and H2c *)
   + do 3 f_equal. unfold WORD. admit. (* by arith *) }
  thaw fr1. 
  thaw Fwaste; cancel. (* thaw and cancel the waste *)
  normalize. (* TODO try omitting this, since more rewrites are needed anyway *)

(* cancel the big block, prior to folding the list 
TODO how best do the next few rewrites?  
Normalize combines offset-vals which isn't always what's needed.
Some of the work could be moved to the lemmas.
*)

assert (Hbsz: 
   (BIGBLOCK - (s + j * (WORD + s)) - (s + WORD))
 = (BIGBLOCK - (s + (j + 1) * (WORD + s)))) by admit. (*arith*)
rewrite Hbsz; clear Hbsz.
assert (Hbpt:
   (offset_val (s + j * (s + WORD) + (s + WORD)) (Vptr pblk poff))
 = (Vptr pblk (Ptrofs.add poff (Ptrofs.repr (s + (j + 1) * (s + WORD)))))) by admit. (*arith*)
rewrite <- Hbpt; clear Hbpt.
cancel.

(* fold list; aiming to apply lemma, first rewrite the conjuncts, in order *)

set (q':= (offset_val (s + j * (s + WORD)) (Vptr pblk poff))). (* q' is name for previous value of q *)
set (r:=(offset_val (s + WORD) (Vptr pblk poff))). (* start of list *)

change (offset_val (s + WORD) (Vptr pblk poff)) with r.

assert (Hmmlist: 
  (offset_val (s + j * (s + WORD) + WORD) (Vptr pblk poff)) 
= (offset_val WORD q')) by (unfold q'; normalize).
rewrite Hmmlist; clear Hmmlist.
assert (Hsing:
(upd_Znth 0 (default_val (nested_field_type (tarray tuint 1) []))
       (Vint (Int.repr s)))
 = [(Vint (Int.repr s))]) by (unfold default_val; normalize).
rewrite Hsing; clear Hsing.

assert (Hmemblk: 
  (offset_val (s + j * (s + WORD) + (WORD + WORD)) (Vptr pblk poff))
= (offset_val (WORD+WORD) q' )) by (unfold q'; normalize). 
rewrite Hmemblk; clear Hmemblk.
change 4 with WORD in *. (* ugh *)

assert (HnxtContents:
    (Vptr pblk
       (Ptrofs.add poff
          (Ptrofs.repr (s + j * (s + WORD) + (WORD + (s + WORD))))))
  = (offset_val (s+WORD+WORD) q')) by (unfold q'; normalize; admit).
rewrite HnxtContents; clear HnxtContents.
assert (HnxtAddr:
    (Vptr pblk (Ptrofs.add poff (Ptrofs.repr (s + j * (s + WORD) + WORD))))
  = (offset_val WORD q')) by (unfold q'; normalize).
rewrite HnxtAddr; clear HnxtAddr. 

rewrite fill_bin_mmlist. (* finally, use lemma to rewrite antecedent *)
assert (Hfrom:
  (Vptr pblk (Ptrofs.add poff (Ptrofs.repr (s + WORD)))) = r ) by (unfold r; normalize).
rewrite Hfrom; clear Hfrom.
assert (Hto:
  (Vptr pblk (Ptrofs.add poff (Ptrofs.repr (s + (j + 1) * (s + WORD) + WORD))))
= (offset_val (s+WORD+WORD) (offset_val (s + j*(s+WORD)) (Vptr pblk poff)))) by admit.
rewrite Hto; clear Hto.
entailer.

- admit. (* TODO held over bound on s; just arith *)

  * (* after the loop *) 

(* TODO eventually: here we're setting up the assignments 
to finish the last block; this is like setting up in the loop body.
Then we fold into the list, like at the end of the loop body. 
It would be nice to factor commonalities. *)

rewrite (memory_block_split_block s (BIGBLOCK - (s + j * (WORD + s))) 
           (offset_val (s + j * (s + WORD)) (Vptr pblk poff))).
- 
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
      (offset_val (s + j * (s + WORD) + WORD) (Vptr pblk poff))))  by admit. 

forward. (***   *(q+WORD) = NULL ***)
{ 
normalize.
set (q:= (offset_val (s + j * (s + WORD)) (Vptr pblk poff))). 
set (r:=(offset_val (s + WORD) (Vptr pblk poff))).

gather_SEP 1 2 3 4. (* TODO need this here so the antecedent will be *'d,
                       otherwise fill_bin_mmlist_null rewrite fails *)
apply semax_pre with
  (PROP ( )
     LOCAL (temp _q q; temp _p (Vptr pblk poff); temp _s (Vint (Int.repr s));
     temp _Nblocks (Vint (Int.repr ((BIGBLOCK - s) / (s + WORD))));
     temp _j (Vint (Int.repr j)))
     SEP (FRZL Fwaste; (mmlist s (Z.to_nat (j+1)) r nullval))).
{  cancel. (* ugh, used to find the waste, before gather_SEP added above *)
assert (HmmlistEnd:
  (offset_val (s + j * (s + WORD) + WORD) (Vptr pblk poff))
= (offset_val WORD q)) by (unfold q; normalize).
rewrite HmmlistEnd; clear HmmlistEnd.
change (Vint (Int.repr 0)) with nullval.
assert (Hmblk:
  (offset_val (s + j * (s + WORD) + (WORD + WORD)) (Vptr pblk poff))
= (offset_val (WORD + WORD) q)) by (unfold q; normalize).
rewrite Hmblk; clear Hmblk.
rewrite (fill_bin_mmlist_null s j r q).
entailer!.
}

forward. (***   return p+s+WORD ***) 
Exists r (j + 1).
entailer!.
unfold s.
entailer!.
}

- admit. (* arith *)
Admitted.


Lemma nth_Znth {X}:
forall n (xs:list X) (x:X), 
0 <= n < Zlength xs ->
(nth (Z.to_nat n) xs x) = (Znth n xs x).
Admitted. 

Lemma nth_upd_Znth:
forall n nats x, 
nth (Z.to_nat n) (upd_Znth n nats x) 0%nat = x.
Admitted.

Lemma upd_Znth_same_val:
forall n xs, 0 <= n < Zlength xs ->
   (upd_Znth n xs (Znth n xs Vundef)) = xs.
Admitted.

Lemma upd_Znth_twice {X}:
forall n x y (xs:list X), 0 <= n < Zlength xs ->
   (upd_Znth n (upd_Znth n xs x) y) = (upd_Znth n xs y).
Admitted.


Lemma body_malloc:  semax_body Vprog Gprog f_malloc malloc_spec'.
Proof. 
start_function. 
forward_call (BINS-1).
assert (H0:= bin2sizeBINS_eq). rep_omega. 
forward_if 
(* join assertion is just the postcondition; could avoid having to copy that
here by using returns in the code, or the new forward_if tactic. *)
(      EX r:_,
       PROP ()
       LOCAL (temp _result r)
       SEP ( mm_inv bin;
             if eq_dec r nullval then emp
             else (malloc_token Tsh n r * memory_block Tsh n r * TT))).
- (* case nbytes > bin2size(BINS-1) *)
  forward. (*** result = NULL ***)
  Exists (Vint (Int.repr 0)).
  entailer!.
- (* case nbytes <= bin2size(BINS-1) *)
  forward_call(n,bin).  (*** t'2 = malloc_small(nbytes) ***)
  { (* precond *) 
    rewrite Int.unsigned_repr in H0. rep_omega. admit. (* bin2sizeZ range *) 
  }
  Intros p.
  forward. (*** result = t'2 ***)
  Exists p. 
  entailer!.
- (* after the conditional *)
  Intros p.
  forward. (*** return ***)
  Exists p.
  entailer!.
Admitted.


Lemma body_free:  semax_body Vprog Gprog f_free free_spec'.
Proof. 
start_function. 
(* TODO revisit spec of free_small, which is only called from here
   and assume token+block already opened *)

forward_if (PROP()LOCAL()SEP(mm_inv bin)). (*** if (p != NULL) ***)
- (* typecheck *) admit.
- (* case p!=NULL *)

(* TODO following is similar to from_malloc_token_and_block but 
without size constraint and also it reads sz at type (tptr tvoid) to fit
with the desugared clight code *)
apply semax_pre with (EX sz:_,  
PROP(0 <= sz <= Ptrofs.max_unsigned)
LOCAL(temp _p p; gvar _bin bin)
SEP( data_at Tsh (tptr tvoid) (Vptrofs (Ptrofs.repr sz)) (offset_val (- WORD) p) *
     data_at_ Tsh (tptr tvoid) p *
     memory_block Tsh (sz - WORD) (offset_val WORD p) )).
{ admit. (* TODO simplify by p<>NULL; the rest is 
            similar to from_malloc_token_and_block but needs thought *) }
Intros sz.
assert_PROP( (* note that this is reading as type **void; next assignment casts *)
(force_val
   (sem_add_ptr_int (tptr tvoid) Signed (force_val (sem_cast_pointer p))
      (eval_unop Oneg tint (Vint (Int.repr 1)))) 
  = field_address (tptr tvoid) [] (offset_val (- WORD) p))) by admit.
forward. (*** t'2 = p[-1] ***)
{ admit. (* typecheck *) } 
forward. (*** s = t'2 ***)  (* TODO - why Vint ?*)
{ admit. (* typecheck *) } 
forward_call(BINS - 1). (*** t'1 = bin2size(BINS - 1) ***)
{ admit. (* arith *) }

  (* ugh - restore token+block for malloc_small, undoing preceding semax_pre *)
apply semax_pre with(PROP()
     LOCAL (temp _t'1 (Vptrofs (Ptrofs.repr (bin2sizeZ (BINS - 1))));
     temp _s (Vint (Ptrofs.to_int (Ptrofs.repr sz))); 
     temp _t'2 (Vptrofs (Ptrofs.repr sz)); temp _p p; 
     gvar _bin bin)
   SEP (malloc_token Tsh n p; memory_block Tsh n p; mm_inv bin)).
{ admit. } (* like to_malloc_token_and_block, but need to revisit *) 

forward_if (PROP () LOCAL () SEP (mm_inv bin)). (*** if s <= t'1 ***)
-- (* case s <= bin2sizeZ(BINS-1) *)
forward_call(p,sz,bin,n). (*** free_small(p,s) ***) 
{ (* preconds *) split.
  admit. (* because n <= sz <= bin2size(BINS-1) from guard condition *)
  admit. (* assumption that's part of the spec fix noted above *) 
}
entailer!.
-- (* case s > bin2sizeZ(BINS-1) *)
 forward.
 admit. (* TODO code known to be incorrect; doesn't free non-small blocks *)

- (* case p == NULL *) 
forward.
entailer!.

- (* after if *)
 forward. (*** return ***)
Admitted.


Lemma body_malloc_small:  semax_body Vprog Gprog f_malloc_small malloc_small_spec.
Proof. 
start_function. 
rewrite <- seq_assoc. 
forward_call n. (*** t'1 = size2bin(nbytes) ***)
{ admit. (* TODO n is in range, by type of bin2size though not by bin2sizeZ; need to specify explicitly? *) }
forward. (*** b = t'1 ***)
set (b:=size2binZ n).
assert (Hb: 0 <= b < BINS) by ( apply (claim2 n); assumption). 
rewrite (mm_inv_split bin b). (* expose bins[b] in mm_inv *)
Intros bins lens.
freeze [1] Otherlists.
deadvars!.
(* TODO us Hb to get p<>Vundef here?  or deal with it as needed? *)
forward. (*** *p = bin[b] ***)
(*
- admit. (* TODO typecheck -- nth stuff using Hb *)
(* TODO why is len Z? not changing now since it will affect fill_bin verif;
   but it results in annoying conversion in else branch below.  *)
*)
2: apply Hb.
forward_if(
     EX p:val, EX len:Z,
     PROP(p <> nullval)
     LOCAL (temp _p p; temp _b (Vint (Int.repr b)); gvar _bin bin)
     SEP (FRZL Otherlists; TT; 
          data_at Tsh (tarray (tptr tvoid) BINS) (upd_Znth b bins p) bin;
          mmlist (bin2sizeZ b) 
                 (nth (Z.to_nat b) (upd_Znth b lens (Z.to_nat len)) 0%nat) p nullval)).
  + admit. (* TODO nontriv typecheck; nth stuff, local facts, ptr lemmas *)
  + (* then branch (TODO: could wait to clear empty list later)  *)
    assert (Hpnull: (Znth b bins Vundef) = nullval) by admit. (* TODO rewrite guard condition *) 
    rewrite Hpnull; clear Hpnull. rewrite mmlist_empty.
    forward_call b. (*** *p = fill_bin(b) ***) (* nice that forward_call handled sequence with temp *)
    Intro r_with_l; destruct r_with_l as [root len]; simpl.
    Intros. (* flatten SEP clause *) 
    forward. (*** bin[b] = p ***)
    Exists root. Exists len.
    rewrite nth_upd_Znth.
    entailer. cancel. unfold force_val. entailer.
    assert (Hlenpos: Z.to_nat len <> 0%nat) by admit. (* TODO H3 len > 0 *)
    admit. (* TODO root <> nullval by H5 and Hlenpos *)
  + (* else branch *)
    forward. (*** skip ***)
    Exists (Znth b bins Vundef).  
    Exists (Z.of_nat (nth (Z.to_nat b) lens 0%nat)). (* annoying conversion *)
    rewrite Nat2Z.id.  rewrite nth_upd_Znth.  
    rewrite upd_Znth_same_val by (rewrite H0; assumption).
    entailer!.
    admit. (* H9 contradicts H2; non-null branch, p loaded from bins[b] *)
    rewrite <- nth_Znth by (rewrite H1; assumption).
    entailer!.
  + (* after if: unroll and pop mmlist *)
    Intros p len.
    set (s:=bin2sizeZ b).  
    rewrite nth_upd_Znth. 

assert_PROP (len > 0). { admit. (* TODO how use mmlist_ne_len? *) }

    rewrite (mmlist_unroll_nonempty s (Z.to_nat len) p).
    3: (rewrite Z2Nat.id; admit ). (* TODO by H3 *) 
    2: assumption.
    Intros q.
    assert_PROP( force_val (sem_cast_pointer p) = field_address (tptr tvoid) [] p) by admit.
    forward. (*** q = *p ***)
    forward. (*** bin[b]=q ***)

   (* prepare token+block to return (might be nicer to do invar first) *)
   thaw Otherlists.  gather_SEP 3 4 5.
   replace_SEP 0 (malloc_token Tsh n p * memory_block Tsh n p).
   go_lower.  change (-4) with (-WORD). (* ugh *)
   apply (to_malloc_token_and_block n p q s). 
   assumption. unfold s; unfold b; reflexivity. 
   (* refold invariant *)
   rewrite upd_Znth_twice by (rewrite H0; apply Hb).
   assert (Hfield_data:
     field_at Tsh (tarray (tptr tvoid) BINS) []
        (upd_Znth b bins (force_val (sem_cast (tptr tvoid) (tptr tvoid) q))) bin
   = data_at Tsh (tarray (tptr tvoid) BINS) 
       (upd_Znth b bins (force_val (sem_cast (tptr tvoid) (tptr tvoid) q))) bin) by admit. (* TODO not sure; data_at is defined from field_at *)
   rewrite Hfield_data; clear Hfield_data.
   gather_SEP 1 3 4.
   replace_SEP 0 (mm_inv bin).
   ++ admit. (* TODO mm_inv_split but EX *)
   ++ forward. (*** return p ***)
      Exists p.
      entailer!.
      if_tac. contradiction. entailer!.
Admitted.


Lemma body_free_small:  semax_body Vprog Gprog f_free_small free_small_spec.
Proof. 
start_function. 
forward_call s. (*** b = size2bin(s) ***)
{ (* function precond *) admit. (* from H: s range *) }
set (b:=(size2binZ n)). 
destruct H as [Hn Hs].
assert (Hb: b = size2binZ s) by (subst; rewrite claim3; auto).
rewrite <- Hb.
assert (Hb': 0 <= b < BINS). 
{ change b with (size2binZ n). apply claim2. assumption. }
(* now expose bins[b] in mm_inv *)
rewrite (mm_inv_split bin b); try apply Hb'.
Intros bins lens.
forward. (***  void *q = bin[b] ***) 
gather_SEP 0 1.
rewrite (from_malloc_token_and_block n p s); try assumption.
Intros.
assert_PROP( (force_val (sem_cast_pointer p) = field_address (tptr tvoid) [] p) ) by admit. 
forward. (***  *((void ** )p) = q ***)
assert( Hguess: (* TODO - may need to strengthen mm_inv concerning what's in bins *)
    (force_val (sem_cast (tptr tvoid) (tptr tvoid) (Znth b bins Vundef)))
  = (Znth b bins Vundef)) by admit. rewrite Hguess; clear Hguess.
change (field_at Tsh (tptr tvoid) [] (Znth b bins Vundef) p)
  with (data_at Tsh (tptr tvoid) (Znth b bins Vundef) p).
gather_SEP 0 1 2 5.
set (q:=(Znth b bins Vundef)).
apply semax_pre with 
    (PROP ( )
     LOCAL (temp _q q; temp _b (Vint (Int.repr b)); 
     temp _p p; temp _s (Vptrofs (Ptrofs.repr s)); 
     gvar _bin bin)
     SEP ((EX q': val, 
          data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p) *
          data_at Tsh (tptr tvoid) q' p *
          memory_block Tsh (s - WORD) (offset_val WORD p) *
          mmlist (bin2sizeZ b) (Znth b lens 0%nat) q' nullval) ;
     data_at Tsh (tarray (tptr tvoid) BINS) bins bin;
     fold_right
       (fun (i : nat) (mp : mpred) =>
        mmlist (bin2sizeZ (Z.of_nat i)) (nth i lens 0%nat) 
          (nth i bins Vundef) nullval * mp) emp
       (filter (fun i : nat => negb (i =? Z.to_nat b)%nat)
          (seq 0 (Z.to_nat BINS))))).
{ Exists q. 
entailer!. }
assert (Hbs: bin2sizeZ b = s) by auto. rewrite Hbs; clear Hbs.
change (Znth b lens 0%nat)
  with (Nat.pred (Nat.succ (Znth b lens 0%nat))).
rewrite <- (mmlist_unroll_nonempty' s (Nat.succ (Znth b lens 0%nat)) p).
2: admit. (* p <> null from data_at *)

forward. (***  bin[b] = p ***)

set (bins':=(upd_Znth b bins p)).
set (lens':=(upd_Znth b lens (Nat.succ (Znth b lens 0%nat)))).
assert(Hguess: (force_val (sem_cast (tptr tvoid) (tptr tvoid) p)) = p) by admit.
rewrite Hguess; clear Hguess.
change (field_at Tsh (tarray (tptr tvoid) BINS) [] (upd_Znth b bins p) bin)
  with (data_at Tsh (tarray (tptr tvoid) BINS) (upd_Znth b bins p) bin).
gather_SEP 1 2 0.
apply semax_pre with 
    (PROP ( )
     LOCAL (temp _q q; temp _b (Vint (Int.repr b)); 
     temp _p p; temp _s (Vptrofs (Ptrofs.repr s)); 
     gvar _bin bin)
     SEP (
  EX bins1: list val, EX lens1: list nat,
  !! (Zlength bins1 = BINS /\ Zlength lens1 = BINS)  &&
    data_at Tsh (tarray (tptr tvoid) BINS) bins1 bin 
  * fold_right (fun (i: nat) => fun (mp: mpred) => 
     (mmlist 
       (bin2sizeZ (Z.of_nat i)) (nth i lens1 O) (nth i bins1 Vundef) nullval) * mp )
     emp 
     (filter (fun (i: nat) =>
       negb (Nat.eqb i (Z.to_nat b))) (seq 0 (Z.to_nat BINS)))
  * (mmlist (bin2sizeZ b) (Znth b lens1 O) (Znth b bins1 Vundef) nullval)
)).
{ Exists bins'. Exists lens'.
  assert_PROP(Zlength bins' = BINS /\ Zlength lens' = BINS) by admit. (* update/len *)
(*  normalize. *)
(*  change (upd_Znth b bins p) with bins'.  *)
(*  change (upd_Znth b lens (Nat.succ (Znth b lens 0%nat))) with lens'. *)
(*  assert (Hbs: bin2sizeZ b = s) by auto. rewrite Hbs; clear Hbs. *)
  assert (Hbp: (Znth b bins' Vundef) = p) 
    by (unfold bins'; rewrite upd_Znth_same; auto; rewrite H; assumption). 
    rewrite Hbp; clear Hbp. 
  assert (Hlen: (Nat.succ (Znth b lens 0%nat)) = (Znth b lens' 0%nat)) 
    by (unfold lens'; rewrite upd_Znth_same; try reflexivity; omega).
    rewrite Hlen; clear Hlen. 
  rewrite (mm_inv_fold_except_b bins bins' lens lens' b p (Nat.succ (Znth b lens 0%nat)))
    by (try unfold bins'; unfold lens'; reflexivity).
  entailer!.
}
rewrite <- (mm_inv_split bin b); try apply Hb'.
forward. (*** return ***)
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

