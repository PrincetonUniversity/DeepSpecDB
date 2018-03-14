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

Definition WA: Z := (WORD*ALIGN) - WORD. (* WASTE *)

(* The following hints empower rep_omega and lessen the need for 
   me to explicitly unfold the constant definitions. *)

Lemma BINS_eq: BINS=8.  Proof. reflexivity. Qed.
Hint Rewrite BINS_eq : rep_omega.
Global Opaque BINS. (* make rewrites only happen in rep_omega *)

Lemma BIGBLOCK_eq: BIGBLOCK=524288.  Proof. reflexivity. Qed.
Hint Rewrite BIGBLOCK_eq : rep_omega.
Global Opaque BIGBLOCK.

Lemma WORD_eq: WORD=4.  Proof. reflexivity. Qed.
Hint Rewrite WORD_eq : rep_omega.
Global Opaque WORD.

Lemma ALIGN_eq: ALIGN=2.  Proof. reflexivity. Qed.
Hint Rewrite ALIGN_eq : rep_omega.
Global Opaque ALIGN.

Lemma WA_eq: WA=4.  Proof. reflexivity. Qed.
Hint Rewrite WA_eq : rep_omega.
Global Opaque WA.


Lemma BIGBLOCK_repr: 
Int.repr BIGBLOCK = Int.mul (Int.shl (Int.repr 2) (Int.repr 16)) (Int.repr WORD).
Proof. admit. 
Admitted.

(* Note that following is Int.max_unsigned, not Ptrofs.max_unsigned;
   increasing BIGBLOCK could require the code to use long instead of int. *)
Lemma BIGBLOCK_size: 0 <= BIGBLOCK <= Int.max_unsigned.
Proof. rep_omega. Qed.


Definition bin2sizeZ := fun b: Z => (Z.mul ((Z.mul (b+1) ALIGN)-1) WORD).

Definition size2binZ : Z -> Z := fun s => 
   if zlt (bin2sizeZ(BINS-1)) s then -1 
   else (s+(Z.mul WORD (ALIGN-1))-1) / (Z.mul WORD ALIGN).


(* This is a required constraint on BIGBLOCK: it fits at least one
   block of max size, together with the alignment prefix for that size. *)
Lemma BIGBLOCK_enough: WA + bin2sizeZ(BINS-1) + WORD <= BIGBLOCK.
Proof.  unfold bin2sizeZ. rep_omega. Qed.

Lemma BIGBLOCK_enough': 
  forall s, 0 <= s <= bin2sizeZ(BINS-1) -> (BIGBLOCK - WA) / (s + WORD) >= 1.
Proof. admit. 
Admitted. 


Lemma bin2size_range: 
  forall b, 0 <= b <BINS -> 
    0 <= bin2sizeZ b <= bin2sizeZ(BINS-1) /\
    bin2sizeZ b <= Ptrofs.max_unsigned.
Proof.
intros. unfold bin2sizeZ in *. split; simpl in *; try rep_omega.
Qed.


(*Lemma bin2size_rangeA: 
  forall b, 0 <= b <BINS -> 
    0 <= bin2sizeZ b <= bin2sizeZ(BINS-1).
Proof.
intros. apply bin2size_range. assumption. 
Qed.
*)

Lemma bin2size_rangeB: 
  forall b, 0 <= b <BINS -> 
    0 <= bin2sizeZ b <= Ptrofs.max_unsigned.
Proof.
intros. unfold bin2sizeZ in *. split; simpl in *; try rep_omega.
Qed.

Lemma  bin2sizeBINS_eq: bin2sizeZ(BINS-1) = 60.
Proof. reflexivity. Qed.
Hint Rewrite bin2sizeBINS_eq: rep_omega.

(* Some sanity checks; may not be needed for code verification. *)

Lemma claim1: forall s,
0 <= s <= bin2sizeZ(BINS-1) -> s <= bin2sizeZ(size2binZ s).
Proof. intros. unfold bin2sizeZ in *. unfold size2binZ in *. simpl in *.
assert (H1: bin2sizeZ (BINS-1) = 60) by normalize. rewrite H1. 
if_tac. rep_omega. 
admit.
Admitted.


Lemma claim2: forall s, 
0 <= s <= bin2sizeZ(BINS-1) -> 0 <= size2binZ s < BINS.
Proof. admit. 
Admitted.

Lemma claim3: forall s, 0 <= s <= bin2sizeZ(BINS-1) 
    -> size2binZ(bin2sizeZ(size2binZ(s))) = size2binZ(s).
Proof. admit.
Admitted.

Lemma claim4: forall b,
0 <= b < BINS -> Z.rem (bin2sizeZ b + WORD) (Z.mul WORD ALIGN) = 0.
Proof.
intros.  admit.
Admitted.

Lemma claim5: forall b, 
0 <= b < BINS -> size2binZ(bin2sizeZ(b)) = b.
Proof.
  intros. unfold size2binZ.
  assert (H1: (bin2sizeZ (BINS - 1) >= (bin2sizeZ b))) 
    by ( unfold bin2sizeZ; rep_omega).
  destruct (zlt (bin2sizeZ (BINS - 1)) (bin2sizeZ b)) as [H2|H2]. contradiction.
  unfold bin2sizeZ. 
  assert (H3: 
     (((b + 1) * ALIGN - 1) * WORD + WORD * (ALIGN - 1) - 1) / (WORD * ALIGN)
     = (b*ALIGN*WORD + 2*ALIGN*WORD - 2*WORD -1)/(WORD*ALIGN)).
  f_equal. f_equal.
  (* TODO algebra incl. integer quotient *) admit. admit.
Admitted.


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
   without constraining how much larger *)
Definition malloc_tok (sh: share) (n: Z) (p: val) (s: Z): mpred := 
   !! (0 <= n <= s /\ s <= Ptrofs.max_unsigned ) &&
   data_at Tsh tuint (offset_val (- WORD) p) (Vptrofs (Ptrofs.repr s))
 * memory_block Tsh (s - n) (offset_val n p). 
Definition malloc_token' (sh: share) (n: Z) (p: val): mpred := 
   EX s:Z, malloc_tok sh n p s.


Definition malloc_tok1 (sh: share) (n: Z) (p: val) (s: Z): mpred := 
   !! (0 <= n <= s /\ s <= Ptrofs.max_unsigned ) &&
   data_at Tsh tuint (offset_val (- WORD) p) (Vptrofs (Ptrofs.repr s))
 * memory_block Tsh (s - n) (offset_val n p). 



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
- (* 0 *) admit. (* intros. unfold mmlist. entailer!. split; reflexivity. *)
- (* N>0 *) intros. entailer!.
admit.
Admitted.

Hint Resolve mmlist_local_facts : saturate_local.

Lemma mmlist_local_facts_Zlen:
  forall sz len p r,
   mmlist sz (Z.to_nat len) p r |--
   !! (0 <= sz <= Ptrofs.max_unsigned /\ 
       is_pointer_or_null p /\ is_pointer_or_null r /\ (p=r <-> len=0)).
Admitted.
Hint Resolve mmlist_local_facts_Zlen : saturate_local.

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
both directions.  It's written using Nat.pred instead of len-1 because
Coq couldn't infer the type for len-1 in scripts that rely on this lemma.
(One workaround would involve replacing len by (Z.to_nat len).)

Note that by type of len, and mmlist_local_facts, 
p <> nullval and (mmlist sz len p nullval) imply (Z.of_nat len) > 0,
so that antecedent is only needed for the RHS-to-LHS direction.
*)
Lemma mmlist_unroll_nonempty:
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
(*  field_at Tsh (tarray tuint 1) [] [(Vint (Int.repr s))] q * *)
  data_at Tsh (tarray tuint 1) [(Vint (Int.repr s))] q * 
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
      (mmlist (bin2sizeZ i) (Znth i lens) (Znth i bins) nullval) * mp )
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
  * (mmlist (bin2sizeZ b) (Znth b lens) (Znth b bins) nullval).
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
(* TODO 
(nth i bins Vundef) and (nth i lens Vundef) only eval'd at i<>b and bins' lens' differ only there *)
Admitted.



(* TODO it would be nice to combine this to_* lemma with the following from_* one. *)
Lemma to_malloc_token_and_block:
forall n p q sz, 0 <= n <= bin2sizeZ(BINS-1) -> sz = bin2sizeZ(size2binZ(n)) -> 
(     data_at Tsh tuint (Vptrofs (Ptrofs.repr sz)) (offset_val (- WORD) p) *
     ( data_at Tsh (tptr tvoid) q p *
     memory_block Tsh (sz - WORD) (offset_val WORD p)  )
|--  malloc_token Tsh n p * memory_block Tsh n p).
Admitted.


Lemma from_malloc_token_and_block: 
(* version that caters for irregular sized blocks *)
forall n p,
  0 <= n <= Ptrofs.max_unsigned -> 
    (malloc_token Tsh n p * memory_block Tsh n p)
  = (EX s:Z,
      !! (n <= s <= Ptrofs.max_unsigned) && 
      data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p) *
      data_at_ Tsh (tptr tvoid) p *
      memory_block Tsh (s - WORD) (offset_val WORD p) ).
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


(* copy of malloc_spec' from floyd library, with mm_inv added
TODO upper bound of n should allow for header, within size that
can be obtained by mmap.
*)
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
             else (malloc_token Tsh n p * memory_block Tsh n p * TT)).

(* copy from floyd lib, revised to allow NULL as per posix std,
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
       SEP ( data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p); 
            data_at_ Tsh (tptr tvoid) p;
            memory_block Tsh (s - WORD) (offset_val WORD p);
            mm_inv bin)
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


Lemma body_size2bin: semax_body Vprog Gprog f_size2bin size2bin_spec.
Proof. start_function. 
  forward_call (BINS-1).  
  rep_omega. 
  assert (H0:= bin2sizeBINS_eq). 
  forward_if(PROP() LOCAL() SEP (FF)). (* FF because join point unreachable *)
  - (* then *) 
  forward. entailer!. f_equal. f_equal. unfold size2binZ; simpl. if_tac; normalize.  
  - (* else *)
  forward.  entailer!. f_equal. unfold size2binZ. if_tac.
    + rep_omega.
    + unfold Int.divu. do 2 rewrite Int.unsigned_repr by rep_omega. 
      f_equal. normalize.  f_equal. rep_omega.
  - (* fi *) entailer.
Qed.


(* Invariant for loop in fill_bin.
p, N, s are fixed
s + WORD is size of a (small) block (including header)
p is start of the big block
N is the number of blocks that fit following the waste prefix of size s
q points to the beginning of a list block (size field), unlike the link field
which points to the link field of the following list block. 
(Recall that the mmlist predicate also refers to link field addresses.)
*)


Definition fill_bin_Inv (p:val) (s:Z) (N:Z) := 
  EX j:_,
  PROP ( N = (BIGBLOCK-WA) / (s+WORD) /\ 
         0 <= s <= bin2sizeZ(BINS-1) /\ 
         0 <= j < N )  
(* j remains strictly smaller than N because j is the number 
of finished blocks and the last block gets finished following the loop. *)
  LOCAL( temp _q (offset_val (WA+(j*(s+WORD))) p);
         temp _p p; 
         temp _s       (Vint (Int.repr s));
         temp _Nblocks (Vint (Int.repr N));
         temp _j       (Vint (Int.repr j)))  
(* (offset_val (s+ M + WORD) p) accounts for waste plus M many blocks plus
the offset for size field.  The last block's nxt points one word _inside_ 
the remaining part of the big block. *)
  SEP (memory_block Tsh WA p; (* initial waste *)
       mmlist s (Z.to_nat j) (offset_val (WA + WORD) p) 
                             (offset_val (WA + (j*(s+WORD)) + WORD) p); 
       memory_block Tsh (BIGBLOCK-(WA+j*(WORD+s))) (offset_val (WA+(j*(s+WORD))) p)). 


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
assert (H0:= bin2sizeBINS_eq). (* TODO still needed or are the rewrites enough? if not, should I add the other similar hypotheses? *)
start_function. 
forward_call b.  (*** s = bin2size(b) ***)
set (s:=bin2sizeZ b).
assert (0 <= s <= bin2sizeZ(BINS-1)).
{ apply bin2size_range; try assumption. }
(* clearbody s. -- nope, need (s = bin2sizeZ b) for return; or rewrite post now? *)
forward_call BIGBLOCK.  (*** *p = sbrk(BIGBLOCK) ***)  
{ apply BIGBLOCK_size. }
Intros p.    
forward. (*** Nblocks = (BIGBLOCK-WASTE) / (s+WORD) ***)
{ (* nonzero divisor *) entailer!. apply repr_inj_unsigned in H3; rep_omega. }
deadvars!.  clear H.  
assert_PROP (isptr p) by entailer!. destruct p; try contradiction.
rename b0 into pblk. rename i into poff. (* p as blk+ofs *)
simpl in H0,H1|-*.  (* should be simpl in * but that would mess up postcond *)
forward. (*** q = p + WASTE ***)
rewrite ptrofs_of_intu_unfold. rewrite ptrofs_mul_repr. normalize.
forward. (*** j = 0 ***) 

forward_while (fill_bin_Inv (Vptr pblk poff) s ((BIGBLOCK-WA) / (s+WORD)) ).

* (* pre implies inv *)
  Exists 0. 
  entailer!.  
(* Note: doing the following next causes stack overflow:
2: apply TT_sepcon.
*)
(* apply andp_right. apply prop_right. *)
  - repeat split; try omega.
    + assert (Hbig: (BIGBLOCK - WA)/(s + WORD) >= 1) by 
         (apply (BIGBLOCK_enough' s); assumption).  omega.
    + f_equal. unfold Int.divu. rewrite Int.unsigned_repr by rep_omega. do 2 f_equal. 
    + apply Ptrofs.eq_true.

  - replace BIGBLOCK with (WA+(BIGBLOCK-WA)) at 1 by omega.
     rewrite <- (Ptrofs.repr_unsigned poff). 
     rewrite  memory_block_split; try omega. 
     + entailer!. 
     + rep_omega.
     + rep_omega.
     + assert (HB: WA+(BIGBLOCK-WA) = BIGBLOCK) by omega; rewrite HB; clear HB. (* WA? *)
       unfold size_compatible' in H2. rep_omega.

* (* pre implies guard defined *)
  entailer!. (* ?? TODO entailer! used to suffice here, and it's just Int  *)
  admit. (* arith and BIGBLOCK_enough *)

* (* body preserves inv *)
  freeze [0] Fwaste. clear H.
  rewrite (memory_block_split_block s (BIGBLOCK - (WA + j * (WORD + s))) 
             (offset_val (WA + j * (s + WORD)) (Vptr pblk poff))).
- Intros. (* flattens the SEP clause *)
  rewrite offset_offset_val. 
  forward. (*** q[0] = s; ***)
  freeze [1; 2; 4; 5] fr1. 
  (* prepare for next assignment, as suggested by hint from forward tactic *)
  assert_PROP ( 
  (Vptr pblk
      (Ptrofs.add (Ptrofs.add poff (Ptrofs.repr (WA + j * (s + WORD))))
        (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr 1))))) 
    = field_address (tptr tvoid) [] 
        (offset_val (WA + j * (s + WORD) + WORD) (Vptr pblk poff))).
  { entailer!. unfold field_address.  simpl. normalize. 
    if_tac. reflexivity. contradiction. }
  forward. (*** *(q+WORD) = q+WORD+(s+WORD); ***)
  forward. (*** q += s+WORD; ***)
  forward. (*** j++; ***) 
  { (* typecheck j+1 *)
    entailer!.
    assert (HB: (BIGBLOCK-WA)/(s+WORD) <= Int.max_signed) by admit. (* TODO *)
    destruct H2 as [H2a [H2b [H2low H2up]]].  
    assert (Hx: Int.min_signed <= j+1) by rep_omega.
    split. rewrite Int.signed_repr. rewrite Int.signed_repr. assumption.
    rep_omega. rep_omega. rewrite Int.signed_repr. rewrite Int.signed_repr.
    assert (Hxx: j + 1 <= (BIGBLOCK-WA)/(s+WORD)) by omega.
    apply (Z.le_trans (j+1) ((BIGBLOCK-WA)/(s+WORD))); assumption.
    rep_omega. rep_omega. } 
  (* reestablish inv *)  
  Exists (j+1).  
  entailer!.  (* TODO ! was culprit for unprovable? *)
  normalize. 
  { split. 
   + destruct H2 as [H2a [H2b H2c]].
     assert (HRE' : j <> ((BIGBLOCK - WA) / (s + WORD) - 1)) by (apply repr_neq_e; assumption). 
     clear - HRE' H2c. omega. 
       (* rep_omega not quite working here; it may with VST update *)
   + do 3 f_equal.
     assert (Hdist: ((j+1)*(s+WORD))%Z = j*(s+WORD) + (s+WORD))
       by (rewrite Z.mul_add_distr_r; omega). rep_omega.
  }
  thaw fr1. 
  thaw Fwaste; cancel. (* thaw and cancel the waste *)
  normalize. 

(* cancel the big block, prior to folding the list 
TODO how best do the next few rewrites?  
Normalize combines offset-vals which isn't always what's needed.
Some of the work could be moved to the lemmas. *)

  assert (Hdist: ((j+1)*(s+WORD))%Z = j*(s+WORD) + (s+WORD))
       by (rewrite Z.mul_add_distr_r; omega). 
  assert (Hassoc: BIGBLOCK - (WA + j * (WORD + s)) - (s + WORD) 
                = BIGBLOCK - (WA + j * (WORD + s) + (s + WORD))) by omega.
  assert (Hcomm: WORD+s = s+WORD) by omega.
  assert (Hbsz: (BIGBLOCK - (WA + j * (WORD + s)) - (s + WORD))
              = (BIGBLOCK - (WA + (j + 1) * (WORD + s)))) 
     by ( rewrite Hassoc; rewrite Hcomm; rewrite Hdist; rep_omega). 
  clear Hassoc. clear Hcomm.
  rewrite Hbsz; clear Hbsz.
  assert (Hbpt:
     (offset_val (WA + j * (s + WORD) + (s + WORD)) (Vptr pblk poff))
   = (Vptr pblk (Ptrofs.add poff (Ptrofs.repr (WA + (j + 1) * (s + WORD)))))).
  { simpl. do 3 f_equal. rewrite Hdist. rep_omega. }
  rewrite <- Hbpt; clear Hbpt.
  cancel.

  (* fold list; aiming to apply lemma fill_bin_mmlist, first rewrite the conjuncts, in order *)

  set (q':= (offset_val (WA + j * (s + WORD)) (Vptr pblk poff))). (* q' is previous value of q *)
  set (r:=(offset_val (WA + WORD) (Vptr pblk poff))). (* r is start of list *)
  change (offset_val (WA + WORD) (Vptr pblk poff)) with r.
  assert (Hmmlist: 
    (offset_val (WA + j * (s + WORD) + WORD) (Vptr pblk poff)) 
   = (offset_val WORD q')) by (unfold q'; normalize).
  rewrite Hmmlist; clear Hmmlist.
  assert (Hsing:
    (upd_Znth 0 (default_val (tarray tuint 1) ) (Vint (Int.repr s)))
   = [(Vint (Int.repr s))]) by (unfold default_val; normalize).
   rewrite Hsing; clear Hsing.
  assert (Hmemblk: 
     (offset_val (WA + j * (s + WORD) + (WORD + WORD)) (Vptr pblk poff))
   = (offset_val (WORD+WORD) q' )) by (unfold q'; normalize). 
  rewrite Hmemblk; clear Hmemblk.
  change 4 with WORD in *. (* ugh *)
  assert (HnxtContents:
    (Vptr pblk
       (Ptrofs.add poff
          (Ptrofs.repr (WA + j * (s + WORD) + (WORD + (s + WORD))))))
    = (offset_val (WORD+WORD) q')). 
  { simpl. f_equal. rewrite Ptrofs.add_assoc. f_equal. normalize.

(* WORKING HERE clearly false but proved before changed waste; entailer!? *)


(* 


    assert (Harith: WORD+(s+WORD) = s+WORD+WORD) by rep_omega.
    rewrite Harith; clear Harith. reflexivity. }
  rewrite HnxtContents; clear HnxtContents.
  assert (HnxtAddr:
      (Vptr pblk (Ptrofs.add poff (Ptrofs.repr (WA + j * (s + WORD) + WORD))))
    = (offset_val WORD q')) by (unfold q'; normalize). 
  rewrite HnxtAddr; clear HnxtAddr. 

  rewrite fill_bin_mmlist. (* finally, use lemma to rewrite antecedent *)
  assert (Hfrom:
    (Vptr pblk (Ptrofs.add poff (Ptrofs.repr (s + WORD)))) = r ) by (unfold r; normalize).
  rewrite Hfrom; clear Hfrom.
  assert (Hto: (* TODO very similar to HnxtAddr *)
    (Vptr pblk (Ptrofs.add poff (Ptrofs.repr (WA + (j + 1) * (s + WORD) + WORD))))
  = (offset_val (s+WORD+WORD) (offset_val (WA + j*(s+WORD)) (Vptr pblk poff)))).
  { simpl. f_equal. rewrite Ptrofs.add_assoc. f_equal. normalize.
    rewrite Hdist. f_equal. rep_omega. }
  rewrite Hto; clear Hto.
  subst q'. (* TODO this wasn't needed with previous versions of entailer *)
  entailer.

- split; try omega.  destruct H2 as [H2a [H2b H2c]].
  admit. (* by H2c and BIGBLOCK_enough *) 

  * (* after the loop *) 

(* TODO eventually: here we're setting up the assignments 
to finish the last block; this is like setting up in the loop body.
Then we fold into the list, like at the end of the loop body. 
It would be nice to factor commonalities. *)

rewrite (memory_block_split_block s (BIGBLOCK - (WA + j * (WORD + s))) 
           (offset_val (WA + j * (s + WORD)) (Vptr pblk poff))).
- 
Intros. (* flattens the SEP clause *) 
rewrite offset_offset_val.
freeze [0;5] Fwaste. (* discard what's not needed for post *)

forward. (*** q[0] = s ***)
assert (Hsing:
(upd_Znth 0 (default_val (tarray tuint 1) ) (Vint (Int.repr s)))
 = [(Vint (Int.repr s))]) by (unfold default_val; normalize).
rewrite Hsing; clear Hsing.
assert_PROP (
  (Vptr pblk
    (Ptrofs.add (Ptrofs.add poff (Ptrofs.repr (WA + j * (s + WORD))))
      (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr 1)))) 
  = field_address (tptr tvoid) []
      (offset_val (WA + j * (s + WORD) + WORD) (Vptr pblk poff)))).
{ entailer!. normalize. 
  unfold field_address. if_tac. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal. normalize. contradiction. }
forward. (***   *(q+WORD) = NULL ***)
normalize.
set (q:= (offset_val (WA + j * (s + WORD)) (Vptr pblk poff))). 
set (r:=(offset_val (WA + WORD) (Vptr pblk poff))).   (* WA? *)

gather_SEP 1 2 3 4. (* prepare for fill_bin_mmlist_null rewrite *)
apply semax_pre with
  (PROP ( )
     LOCAL (temp _q q; temp _p (Vptr pblk poff); temp _s (Vint (Int.repr s));
     temp _Nblocks (Vint (Int.repr ((BIGBLOCK - WA) / (s + WORD))));
     temp _j (Vint (Int.repr j)))
     SEP (FRZL Fwaste; (mmlist s (Z.to_nat (j+1)) r nullval))).
{  cancel. (* ugh, used to find the waste, before gather_SEP added above *)
  assert (HmmlistEnd:
    (offset_val (WA + j * (s + WORD) + WORD) (Vptr pblk poff))
  = (offset_val WORD q)) by (unfold q; normalize).
  rewrite HmmlistEnd; clear HmmlistEnd.
  change (Vint (Int.repr 0)) with nullval.
  assert (Hmblk:
    (offset_val (WA + j * (s + WORD) + (WORD + WORD)) (Vptr pblk poff))
  = (offset_val (WORD + WORD) q)) by (unfold q; normalize).
  rewrite Hmblk; clear Hmblk.
  rewrite (fill_bin_mmlist_null s j r q).
  entailer!.
}
forward. (***   return p+WASTE+WORD ***) 
Exists r (j + 1).
entailer!.
unfold s.
entailer!.

- split; try omega. admit. (* arith same as earlier *)

*)
Admitted.



(* drop in favor of unfold Znth? 
Lemma nth_Znth {X}:
forall n (xs:list X) (x:X), 0 <= n < Zlength xs ->
(nth (Z.to_nat n) xs 0) = (Znth n xs).
Admitted. 
*)

Lemma nth_upd_Znth:
forall n nats x, 
nth (Z.to_nat n) (upd_Znth n nats x) 0%nat = x.
Admitted.

Lemma upd_Znth_same_val:
  forall n xs, 0 <= n < Zlength xs ->
   (upd_Znth n xs (Znth n xs)) = xs.
Admitted.

Lemma upd_Znth_twice {X}:
forall n x y (xs:list X), 0 <= n < Zlength xs ->
   (upd_Znth n (upd_Znth n xs x) y) = (upd_Znth n xs y).
Admitted.


Lemma body_malloc:  semax_body Vprog Gprog f_malloc malloc_spec'.
Proof. 
start_function. 
forward_call (BINS-1).
{ assert (H0:= bin2sizeBINS_eq). rep_omega. }
forward_if.
- (* case nbytes > bin2size(BINS-1) *)
  forward. (*** result = NULL ***)
  Exists (Vint (Int.repr 0)).
  entailer!.
- (* case nbytes <= bin2size(BINS-1) *)
  forward_call(n,bin).  (*** t'2 = malloc_small(nbytes) ***)
  { (* precond *) rep_omega. }
(*    rewrite Int.unsigned_repr in H0. rep_omega.  
    apply bin2size_rangeB.  rep_omega. } *) 
  Intros p.
  forward. (*** result = t'2 ***)
  Exists p. 
  entailer!.
Qed.


Lemma body_free:  semax_body Vprog Gprog f_free free_spec'.
Proof. 
start_function. 
forward_if (PROP()LOCAL()SEP(mm_inv bin)). (*** if (p != NULL) ***)
- (* typecheck *) if_tac; entailer!.
- (* case p!=NULL *)
apply semax_pre with 
    (PROP ( )
     LOCAL (temp _p p; gvar _bin bin)
     SEP (mm_inv bin;  malloc_token Tsh n p * memory_block Tsh n p)).
{ if_tac; entailer!. }
assert_PROP ( 0 <= n <= Ptrofs.max_unsigned ) by entailer!.
rewrite (from_malloc_token_and_block n p H0).
Intros s.
assert_PROP( 
(force_val
   (sem_add_ptr_int tuint Signed (force_val (sem_cast_pointer p))
      (eval_unop Oneg tint (Vint (Int.repr 1)))) 
  = field_address tuint [] (offset_val (- WORD) p))).
{ entailer!. simpl. unfold field_address. if_tac. normalize. contradiction. }
forward. (*** t'2 = p[-1] ***)
forward. (*** s = t'2 ***) 
forward_call(BINS - 1). (*** t'1 = bin2size(BINS - 1) ***)
{ rep_omega. } 
forward_if (PROP () LOCAL () SEP (mm_inv bin)). (*** if s <= t'1 ***)
-- (* case s <= bin2sizeZ(BINS-1) *)
forward_call(p,s,bin,n). (*** free_small(p,s) ***) 
{ (* preconds *) split.
  split. omega.
  admit. (* TODO easy but may need to strengthen malloc_token for small case *)
  admit. (* TODO easy but may need to strengthen malloc_token for small case *)
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
{ assert (Hn: bin2sizeZ(BINS-1) <= Ptrofs.max_unsigned)
    by (apply bin2size_rangeB; rep_omega). rep_omega.  }
forward. (*** b = t'1 ***)
set (b:=size2binZ n).
assert (Hb: 0 <= b < BINS) by ( apply (claim2 n); assumption). 
rewrite (mm_inv_split bin b) by apply Hb. (* expose bins[b] in mm_inv *)
Intros bins lens.
freeze [1] Otherlists.
deadvars!.
forward. (*** p = bin[b] ***)
(* TODO why is len Z? not changing now since it will affect fill_bin verif;
   but it results in annoying conversion in else branch below.  *)
forward_if(
     EX p:val, EX len:Z,
     PROP(p <> nullval)
     LOCAL (temp _p p; temp _b (Vint (Int.repr b)); gvar _bin bin)
     SEP (FRZL Otherlists; TT; 
          data_at Tsh (tarray (tptr tvoid) BINS) (upd_Znth b bins p) bin;
          mmlist (bin2sizeZ b) 
                 (nth (Z.to_nat b) (upd_Znth b lens (Z.to_nat len)) 0%nat) p nullval)).
  + admit. (* TODO nontriv typecheck; nth stuff, local facts, ptr lemmas *)
  + (* then branch p==NULL (TODO: could wait to clear empty list later)  *)
    assert (Hpnull: (Znth b bins) = nullval) by admit. (* TODO rewrite guard condition *) 
    rewrite Hpnull; clear Hpnull. rewrite mmlist_empty.
    forward_call b. (*** p = fill_bin(b) ***) 
    (* nice that forward_call handled sequence with temp; why not elsewhere so? *)
    Intro r_with_l; destruct r_with_l as [root len]; simpl.
    Intros. (* flatten SEP clause *) 
    forward. (*** bin[b] = p ***)
    Exists root. Exists len.
    rewrite nth_upd_Znth.
    entailer. cancel. unfold force_val. entailer.
    assert (Hlenpos: Z.to_nat len <> 0%nat) by admit. (* TODO H3 len > 0 *)
    entailer!. 
    rewrite (proj1 H5) in Hlenpos. apply Hlenpos. reflexivity. reflexivity.
  + (* else branch p!=NULL *)
    forward. (*** skip ***)
    Exists (Znth b bins).  
    Exists (Z.of_nat (nth (Z.to_nat b) lens 0%nat)). (* annoying conversion *)
    rewrite Nat2Z.id.  rewrite nth_upd_Znth.   
(* TODO revised Znth in VST broke the following *)
    rewrite upd_Znth_same_val by (rewrite H0; assumption). 
    entailer!.
(*    admit.*) (* H9 contradicts H2; non-null branch, p loaded from bins[b] *)
    rewrite <- nth_Znth by (rewrite H1; assumption).
    entailer!.
  + (* after if: unroll and pop mmlist *)
    Intros p len.
    set (s:=bin2sizeZ b).  
    rewrite nth_upd_Znth. 
    assert_PROP (len > 0). {
         entailer!.  admit. (* TODO how use mmlist_ne_len? *) }
    rewrite (mmlist_unroll_nonempty s (Z.to_nat len) p).
    3: (rewrite Z2Nat.id; rep_omega). 
    2: assumption.
    Intros q.
    assert_PROP( force_val (sem_cast_pointer p) = field_address (tptr tvoid) [] p).
entailer!.
(* TODO make little tactic for this idiom, also used above: *)
unfold field_address. if_tac. normalize. contradiction.

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
    gather_SEP 3 1 4.
    set (lens':=(upd_Znth b lens (Nat.pred (Z.to_nat len)))).
    set (bins':=(upd_Znth b bins (force_val (sem_cast_pointer q)))).
    assert (Hlens: Nat.pred (Z.to_nat len) = (Znth b lens' 0%nat)) by admit.
    rewrite Hlens; clear Hlens.
    assert (Hbins: q = (Znth b bins' Vundef)). 
    { unfold bins'. rewrite upd_Znth_same. unfold force_val. 
      admit. (* TODO lost info about q? *) rewrite H0; apply Hb. }
    rewrite Hbins at 2; clear Hbins.
    change s with (bin2sizeZ b).
    apply semax_pre with
    (PROP ( )
     LOCAL (temp _q q; temp _p p; temp _b (Vint (Int.repr b)); gvar _bin bin)
     SEP(
        (EX bins1: list val, EX lens1: list nat, 
         !! (Zlength bins1 = BINS /\ Zlength lens1 = BINS)  &&
          data_at Tsh (tarray (tptr tvoid) BINS) bins1 bin *
          (fold_right
             (fun (i : nat) (mp : mpred) =>
              mmlist (bin2sizeZ (Z.of_nat i)) (nth i lens1 0%nat)
                (nth i bins1 Vundef) nullval * mp) emp
             (filter (fun i : nat => negb (i =? Z.to_nat b)%nat)
                (seq 0 (Z.to_nat BINS)))) *
           mmlist (bin2sizeZ b)(Znth b lens1 0%nat)(Znth b bins1 Vundef) nullval
        );
        malloc_token Tsh n p * memory_block Tsh n p; TT )).
    { Exists bins'. Exists lens'.
      assert_PROP(Zlength bins' = BINS /\ Zlength lens' = BINS).
      { unfold bins'.  unfold lens'.  
        rewrite upd_Znth_Zlength. rewrite upd_Znth_Zlength. entailer!. omega. omega. }
      admit.
    }
    rewrite <- (mm_inv_split bin b); try apply Hb.
    forward. (*** return p ***)
    Exists p.
    entailer!.
    if_tac. contradiction. entailer!.
Admitted.


Lemma body_free_small:  semax_body Vprog Gprog f_free_small free_small_spec.
Proof. 
start_function. 
destruct H as [Hn Hs].
forward_call s. (*** b = size2bin(s) ***)
{ subst. apply bin2size_rangeB. apply claim2; assumption. }
set (b:=(size2binZ n)). 
assert (Hb: b = size2binZ s) by (subst; rewrite claim3; auto).
rewrite <- Hb.
assert (Hb': 0 <= b < BINS). 
{ change b with (size2binZ n). apply claim2. assumption. }
(* now expose bins[b] in mm_inv *)
rewrite (mm_inv_split bin b); try apply Hb'.
Intros bins lens.
forward. (***  void *q = bin[b] ***) 
assert_PROP( (force_val (sem_cast_pointer p) = field_address (tptr tvoid) [] p) ) by admit. 
forward. (***  *((void ** )p) = q ***)
gather_SEP 0 1 2 5.
set (q:=(Znth b bins Vundef)).
assert_PROP (p <> nullval) by entailer!.
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
{ Exists q. entailer!. entailer. } 
assert (Hbs: bin2sizeZ b = s) by auto. rewrite Hbs; clear Hbs.
change (Znth b lens 0%nat)
  with (Nat.pred (Nat.succ (Znth b lens 0%nat))).
rewrite <- (mmlist_unroll_nonempty s (Nat.succ (Znth b lens 0%nat)) p).
3: admit. (* TODO successor of a nat is pos *)
2: assumption. 
forward. (***  bin[b] = p ***)
set (bins':=(upd_Znth b bins p)).
set (lens':=(upd_Znth b lens (Nat.succ (Znth b lens 0%nat)))).
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
  assert_PROP(Zlength bins' = BINS /\ Zlength lens' = BINS).
  { unfold bins'.  unfold lens'.  
    rewrite (upd_Znth_Zlength b bins p).
    match goal with |- context [upd_Znth b lens ?X] => set (foo:=X) end.
    rewrite (upd_Znth_Zlength b lens foo). 
    entailer!. (* TODO faster proof of this propositional entailment *)
    omega. omega.
  }
  assert (Hbs: bin2sizeZ b = s) by auto. rewrite Hbs; clear Hbs. 
  assert (Hbp: (Znth b bins' Vundef) = p) 
    by (unfold bins'; rewrite upd_Znth_same; auto; rewrite H; assumption). 
    rewrite Hbp; clear Hbp. 
  assert (Hlen: (Nat.succ (Znth b lens 0%nat)) = (Znth b lens' 0%nat)) 
    by (unfold lens'; rewrite upd_Znth_same; try reflexivity; omega).
    rewrite Hlen; clear Hlen. 
  rewrite (mm_inv_fold_except_b bins bins' lens lens' b p (Nat.succ (Znth b lens 0%nat)))
    by (try unfold bins'; unfold lens'; reflexivity).
entailer!.
change (upd_Znth (size2binZ n) bins p) with bins'.
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

