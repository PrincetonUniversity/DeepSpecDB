Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.

Ltac start_function_hint ::= idtac. (* no hint reminder *)


(* First draft specs.  Not specifying that chunks are aligned (but they are). 

ALERT: overriding the definition of malloc_token, malloc_spec', and free_spec' in floyd.library 
Current version is out of sync with floyd: malloc_token uses number of bytes
rather than a type expression.
*)

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

Definition WA: Z := (WORD*ALIGN) - WORD. (* WASTE at start of big block *)

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

(* Note that following is Int.max_unsigned, not Ptrofs.max_unsigned;
   increasing BIGBLOCK could require the code to use long instead of int. *)
Lemma BIGBLOCK_size: 0 <= BIGBLOCK <= Int.max_unsigned.
Proof. rep_omega. Qed.

Definition bin2sizeZ := fun b: Z => (Z.mul ((Z.mul (b+1) ALIGN)-1) WORD).

Definition size2binZ : Z -> Z := fun s => 
   if zlt (bin2sizeZ(BINS-1)) s then -1 
   else (s+(Z.mul WORD (ALIGN-1))-1) / (Z.mul WORD ALIGN).

Lemma bin2size_range: 
  forall b, 0 <= b <BINS -> 
    0 <= bin2sizeZ b <= bin2sizeZ(BINS-1) /\
    bin2sizeZ b <= Ptrofs.max_unsigned.
Proof.
intros. unfold bin2sizeZ in *. split; simpl in *; try rep_omega.
Qed.

Lemma bin2size_rangeB: 
  forall b, 0 <= b <BINS -> 
    0 <= bin2sizeZ b <= Ptrofs.max_unsigned.
Proof.
intros. unfold bin2sizeZ in *. split; simpl in *; try rep_omega.
Qed.

Lemma  bin2sizeBINS_eq: bin2sizeZ(BINS-1) = 60.
Proof. reflexivity. Qed.
Hint Rewrite bin2sizeBINS_eq: rep_omega.

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

(* check on alignment, as sanity check on specs *)
Lemma claim4: forall b,
0 <= b < BINS -> Z.rem (bin2sizeZ b + WORD) (Z.mul WORD ALIGN) = 0.
Proof.
intros.  admit.
Admitted.

Lemma Z_DivFact:
  forall a b c, 0 <= b < c -> (a*c + b)/c = a.
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
     = (b*ALIGN*WORD + 2*ALIGN*WORD - 2*WORD -1)/(WORD*ALIGN))
    by (f_equal; f_equal; rep_omega).  rewrite H3.
  assert (H4:
     (b * ALIGN * WORD + 2 * ALIGN * WORD - 2 * WORD - 1)  
   = (b * (WORD * ALIGN) + (ALIGN*WORD-1))) by rep_omega.   rewrite H4.
  apply Z_DivFact.
  rep_omega.
Qed.


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


(* Specifications for posix mmap and munmap as used by this memory manager. *)

Definition MAP_FAILED: Z := -1. (* typed as void* in include/sys/mman.h *)

Definition mmap_spec := 
   DECLARE _mmap
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
            temp 4%positive (Vint (Int.repr 4098)); (* MAP_PRIVATE|MAP_ANONYMOUS *)
            temp 5%positive (Vint (Int.repr (-1)));
            temp 6%positive (Vlong (Int64.repr 0)))
     SEP ()
   POST [ tptr tvoid ] EX p:_, 
     PROP ( if eq_dec p (Vptrofs (Ptrofs.repr MAP_FAILED))  
            then True else (* aligned enough *) 
              (exists zp, p = (Vptrofs (Ptrofs.repr zp)) /\ (zp mod 4 = 0)) )
     LOCAL (temp ret_temp p)
     SEP ( if eq_dec p (Vptrofs (Ptrofs.repr MAP_FAILED))  
           then emp else memory_block Tsh n p).


(* NOTE: the postcondition should be if ret==0 then the memory was freed. *)
Definition munmap_spec := 
   DECLARE _munmap
   WITH p:val, n:Z
   PRE [ 1%positive (*_addr*) OF (tptr tvoid), 
         2%positive (*_len*) OF tuint ]
     PROP (0 <= n <= Ptrofs.max_unsigned)
     LOCAL (temp 1%positive nullval; 
            temp 2%positive (Vptrofs (Ptrofs.repr n)) )
     SEP ( memory_block Tsh n p )
   POST [ tint ] EX res: Z,
     PROP ()
     LOCAL (temp ret_temp (Vint (Int.repr res)))
     SEP ( emp ).

(* malloc token: accounts for both the size field and alignment padding.
n is the number of bytes requested.
Unfolding the definition reveals the stored size value s, which 
is not the request n but rather the size of the block (not 
counting the size field itself).

The constraint s + WA + WORD <= Ptrofs.max_unsigned caters for 
padding and is used e.g. in proof of body_free.

About waste: for small blocks, there is only waste at the beginning of each
big block used by fill_bin, and mm_inv accounts for it.
For large blocks, each has its own waste, accounted for by malloc_token'.

Note that offset_val is in bytes, not like C pointer arith. 
*)

Definition malloc_tok (sh: share) (n: Z) (s: Z) (p: val): mpred := 
   !! (0 <= n <= s /\ s + WA + WORD <= Ptrofs.max_unsigned /\
       (s <= bin2sizeZ(BINS-1) -> s = bin2sizeZ(size2binZ(n))) ) &&
   data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p)
 * memory_block Tsh (s - n) (offset_val n p)
 * (if zle s (bin2sizeZ(BINS-1)) 
    then emp
    else memory_block Tsh WA (offset_val (-(WA+WORD)) p)).

Definition malloc_token' (sh: share) (n: Z) (p: val): mpred := 
   EX s:Z, malloc_tok sh n s p.

Lemma malloc_token_valid_pointer':
  forall sh n p, malloc_token' sh n p |-- valid_pointer p.
Admitted.

Lemma malloc_token_valid_pointer_size':
  forall sh n p, malloc_token' sh n p |-- valid_pointer (offset_val (- WORD) p).
Admitted.

Lemma malloc_token_precise':
  forall sh n p, predicates_sl.precise (malloc_token' sh n p).
Admitted.

Lemma malloc_token_local_facts':
  forall sh n p, malloc_token' sh n p 
  |-- !!( malloc_compatible n p /\ 0 <= n <= Ptrofs.max_unsigned - WORD ).
Admitted.

Hint Resolve malloc_token_valid_pointer' : valid_pointer.
Hint Resolve malloc_token_valid_pointer_size' : valid_pointer.
Hint Resolve malloc_token_precise' : valid_pointer.
Hint Resolve malloc_token_local_facts' : saturate_local.


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
  forall sz, mmlist sz 0 nullval nullval = emp.
Admitted.


(* lemmas on constructing an mmlist from a big block (used in fill_bin) *)

(* fold an mmlist with tail pointing to initialized next object. *)
Lemma fill_bin_mmlist:
  forall s j r q,
  mmlist s (Z.to_nat j) r (offset_val WORD q) * 
  field_at Tsh (tarray tuint 1) [] [(Vint (Int.repr s))] q * 
  memory_block Tsh (s-WORD) (offset_val (WORD+WORD) q) *
  field_at Tsh (tptr tvoid) [] (offset_val (WORD+s+WORD) q) (offset_val WORD q)  
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
   memory_block Tsh (m-(s+WORD)) (offset_val (s+WORD) q). (*rest of large*)
Proof.
intros s m q [Hs Hm]. 
(* TODO first rewrite big memory block into memory blocks including
   memory_block Tsh WORD q * (*size*)
   memory_block Tsh WORD (offset_val WORD q) * (*nxt*)   
then use lemma memory_block_data_at_ 
 *) 
Admitted. 

Lemma free_large_memory_block: 
  (* TODO overly specific, for malloc_large. 
     And may need tighter bound on s. Also: don't need to 
     separate nxt from data since nxt not used (?). *)
  forall s p, 0 <= s <= Ptrofs.max_unsigned -> 
  memory_block Tsh (s + WA + WORD) (offset_val (- (WA + WORD)) p) 
  = 
  data_at_ Tsh tuint (offset_val (- WORD) p) *        (* size *)
  data_at_ Tsh (tptr tvoid) p *                       (* nxt *)
  memory_block Tsh (s - WORD) (offset_val WORD p) *   (* data *)
  memory_block Tsh WA (offset_val (- (WA + WORD)) p). (* waste *)
Proof.
Admitted.


Lemma malloc_large_memory_block: 
  forall n p, 0 <= n <= Ptrofs.max_unsigned -> 
  memory_block Tsh (n + WA + WORD) p
  = 
  memory_block Tsh WA p *                      (* waste *)
  data_at_ Tsh tuint (offset_val WA p) *       (* size *)
  memory_block Tsh n (offset_val (WA+WORD) p). (* data *)
Proof.
Admitted.



(* module invariant:
There is an array,
its elements point to null-terminated lists of right size blocks, 
and there is some wasted memory.
*) 

Definition mmlist' (it: nat * val * Z) :=
  mmlist (bin2sizeZ (snd it)) (fst (fst it)) (snd (fst it)) nullval. 

Definition zip3 (bs:list nat) (cs:list val) (ds:list Z) := (combine (combine bs cs) ds).

Lemma sublist_zip3:
forall i j bs cs ds, 
  0 <= i <= j -> j <= Zlength bs ->
  Zlength bs = Zlength cs -> Zlength cs = Zlength ds ->
(sublist i j (zip3 bs cs ds)) = 
(zip3 (sublist i j bs) (sublist i j cs) (sublist i j ds)).
Proof.
admit. (* TODO *)
Admitted.

Definition mm_inv (gv: globals): mpred := 
  EX bins: list val, EX lens: list nat, EX idxs: list Z,
    !! (Zlength bins = BINS /\ Zlength lens = BINS /\
        idxs = map Z.of_nat (seq 0 (Z.to_nat BINS))) &&
  data_at Tsh (tarray (tptr tvoid) BINS) bins (gv _bin) * 
  iter_sepcon (zip3 lens bins idxs) mmlist' * 
  TT. (* waste, which arises due to alignment in bins *)

Lemma mm_inv_splitX: (* new version for sepcon *)
 forall gv:globals, forall b:Z, 0 <= b < BINS ->
   mm_inv gv
 = 
  EX bins: list val, EX lens: list nat, EX idxs: list Z,
    !! (Zlength bins = BINS /\ Zlength lens = BINS /\ Zlength idxs = BINS 
        /\ idxs = map Z.of_nat (seq 0 (Z.to_nat BINS))) &&
  data_at Tsh (tarray (tptr tvoid) BINS) bins (gv _bin) * 
  iter_sepcon (sublist 0 b (zip3 lens bins idxs)) mmlist' * 
  mmlist (bin2sizeZ b) (Znth b lens) (Znth b bins) nullval * 
  iter_sepcon (sublist (b+1) BINS (zip3 lens bins idxs)) mmlist' *  
  TT. 
Proof.
Admitted.

Lemma mm_inv_splitX': (* new version for sepcon *)
 forall b:Z, forall bins lens idxs,
     0 <= b < BINS -> Zlength bins = BINS -> Zlength lens = BINS -> 
     idxs = map Z.of_nat (seq 0 (Z.to_nat BINS)) ->
 iter_sepcon (sublist 0 b (zip3 lens bins idxs)) mmlist' * 
 iter_sepcon (sublist (b+1) BINS (zip3 lens bins idxs)) mmlist' * 
 mmlist (bin2sizeZ b) (Znth b lens) (Znth b bins) nullval
  =
 iter_sepcon (zip3 lens bins idxs) mmlist'. 
Proof.  
Admitted.


(* TODO maybe drop q in favor of data_at_ *)
Lemma to_malloc_token_and_block:
forall n p q s, 0 <= n <= bin2sizeZ(BINS-1) -> s = bin2sizeZ(size2binZ(n)) -> 
(     data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p) *
     ( data_at Tsh (tptr tvoid) q p *
     memory_block Tsh (s - WORD) (offset_val WORD p)  )
|--  malloc_token' Tsh n p * memory_block Tsh n p).
Admitted.


Lemma from_malloc_token_and_block: 
(* version that caters for irregular sized blocks *)
forall n p,
  0 <= n <= Ptrofs.max_unsigned - WORD -> 
    (malloc_token' Tsh n p * memory_block Tsh n p)
  = (EX s:Z,
      !! ( n <= s /\ s + WA + WORD <= Ptrofs.max_unsigned /\ 
           (s <= bin2sizeZ(BINS-1) -> s = bin2sizeZ(size2binZ(n)))) && 
      data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p) * (* size *)
      data_at_ Tsh (tptr tvoid) p *                                         (* nxt *)
      memory_block Tsh (s - WORD) (offset_val WORD p) *                     (* data *)
      (if zle s (bin2sizeZ(BINS-1)) then emp                                (* waste *)
       else memory_block Tsh WA (offset_val (-(WA+WORD)) p))).
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


(* copy of malloc_spec' from floyd/library, with mm_inv added
and size bound revised to refer to Ptrofs and to account for
the header of size WORD.  
*)
Definition malloc_spec' := 
   DECLARE _malloc
   WITH n:Z, bin:val, gv:globals
   PRE [ _nbytes OF tuint ]
       PROP (0 <= n <= Ptrofs.max_unsigned - (WA+WORD))
       LOCAL (temp _nbytes (Vptrofs (Ptrofs.repr n)); gvars gv)
       SEP ( mm_inv gv )
   POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mm_inv gv;
             if eq_dec p nullval then emp
             else (malloc_token' Tsh n p * memory_block Tsh n p)).

(* copy from floyd lib, revised to allow NULL as per posix std,
and with mm_inv added.
n is the requested size, not the actual block size *)
Definition free_spec' := 
   DECLARE _free
   WITH p:_, n:_, gv:globals
   PRE [ _p OF tptr tvoid ]
       PROP ()
       LOCAL (temp _p p; gvars gv)
       SEP (mm_inv gv; 
            if eq_dec p nullval then emp
            else (malloc_token' Tsh n p * memory_block Tsh n p))
   POST [ Tvoid ]
       PROP ()
       LOCAL ( )
       SEP (mm_inv gv).

Definition malloc_small_spec :=
   DECLARE _malloc_small
   WITH n:Z, gv:globals
   PRE [ _nbytes OF tuint ]
       PROP (0 <= n <= bin2sizeZ(BINS-1))
       LOCAL (temp _nbytes (Vptrofs (Ptrofs.repr n)); gvars gv)
       SEP ( mm_inv gv )
   POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mm_inv gv; 
            if eq_dec p nullval then emp
            else (malloc_token' Tsh n p * memory_block Tsh n p)).

(* Note that this is a static function so there's no need to hide
globals in its spec; but that seems to be needed, given the definition 
of mm_inv.*)
Definition malloc_large_spec :=
   DECLARE _malloc_large
   WITH n:Z, gv:globals
   PRE [ _nbytes OF tuint ]
       PROP (bin2sizeZ(BINS-1) < n <= Ptrofs.max_unsigned - (WA+WORD))
       LOCAL (temp _nbytes (Vptrofs (Ptrofs.repr n)); gvars gv)
       SEP ( mm_inv gv )
   POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mm_inv gv; 
            if eq_dec p nullval then emp
            else (malloc_token' Tsh n p * memory_block Tsh n p)).


(* s is the stored block size and n is the original request amount. *)
Definition free_small_spec :=
   DECLARE _free_small
   WITH p:_, s:_, n:_, gv:globals
   PRE [ _p OF tptr tvoid, _s OF tuint ]
       PROP (0 <= n <= bin2sizeZ(BINS-1) /\ s = bin2sizeZ(size2binZ(n)))
       LOCAL (temp _p p; temp _s (Vptrofs (Ptrofs.repr s)); gvars gv)
       SEP ( data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p); 
            data_at_ Tsh (tptr tvoid) p;
            memory_block Tsh (s - WORD) (offset_val WORD p);
            mm_inv gv)
   POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mm_inv gv).

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

(* 
Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ]  main_post prog nil u.
*)

Definition Gprog : funspecs := 
 ltac:(with_library prog [ 
   mmap_spec; munmap_spec; bin2size_spec; size2bin_spec; fill_bin_spec;
   malloc_small_spec; malloc_large_spec; free_small_spec; malloc_spec'; 
   free_spec']).


Lemma body_bin2size: semax_body Vprog Gprog f_bin2size bin2size_spec.
Proof. start_function. forward. 
Qed.


Lemma body_size2bin: semax_body Vprog Gprog f_size2bin size2bin_spec.
Proof. start_function. 
  forward_call (BINS-1). rep_omega. 
  forward_if.
  - (* then *) 
  forward. entailer!. f_equal. f_equal. unfold size2binZ; simpl. if_tac; normalize.  
  - (* else *)
  forward.  entailer!. f_equal. unfold size2binZ. if_tac.
    + rep_omega.
    + unfold Int.divu. do 2 rewrite Int.unsigned_repr by rep_omega. 
      f_equal. normalize.  f_equal. rep_omega.
Qed.


(* Invariant for loop in fill_bin.
p, N, s are fixed
s + WORD is size of a (small) block (including header)
p is start of the big block
N is the number of blocks that fit following the waste prefix of size s
q points to the beginning of a list block (size field), unlike the link field
which points to the link field of the following list block. 
(Recall that the mmlist predicate also refers to link field addresses.)

It may be that  s + WORD <= BIGBLOCK - WA - j*(s+WORD)  is a consequence 
of the other invariants, but maintaining it is an easier way to prove it 
where needed.
*)

Definition fill_bin_Inv (p:val) (s:Z) (N:Z) := 
  EX j:_,
  PROP ( N = (BIGBLOCK-WA) / (s+WORD) /\ 
         0 <= s <= bin2sizeZ(BINS-1) /\ 
         0 <= j < N /\ 
         s + WORD <= BIGBLOCK - WA - j*(s+WORD)
)  
(* j remains strictly smaller than N because j is the number 
of finished blocks and the last block gets finished following the loop. *)
  LOCAL( temp _q (offset_val (WA+(j*(s+WORD))) p);
         temp _p p; 
         temp _s       (Vint (Int.repr s));
         temp _Nblocks (Vint (Int.repr N));
         temp _j       (Vint (Int.repr j)))  
(* (offset_val (WA + M + WORD) p) accounts for waste plus M many blocks plus
the offset for size field.  The last block's nxt points one word _inside_ 
the remaining part of the big block. *)
  SEP (memory_block Tsh WA p; (* initial waste *)
       mmlist s (Z.to_nat j) (offset_val (WA + WORD) p) 
                             (offset_val (WA + (j*(s+WORD)) + WORD) p); 
       memory_block Tsh (BIGBLOCK-(WA+j*(s+WORD))) (offset_val (WA+(j*(s+WORD))) p)). 


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

(* TODO if I'm using the following only in one dir., make them autorewrites *)
Lemma nth_upd_Znth:
forall n xs x, 
nth (Z.to_nat n) (upd_Znth n xs x) 0%nat = x.
Admitted.

Lemma upd_Znth_same_val {A}:
  forall n (xs: list A) (d: Inhabitant A), 0 <= n < Zlength xs ->
   (upd_Znth n xs (Znth n xs)) = xs.
Admitted.

Lemma upd_Znth_twice {X}:
forall n x y (xs:list X), 0 <= n < Zlength xs ->
   (upd_Znth n (upd_Znth n xs x) y) = (upd_Znth n xs y).
Admitted.

Lemma succ_pos:  
  forall n:nat, 
  Z.of_nat (Nat.succ n) > 0.
Proof.
Admitted.


Lemma body_fill_bin: semax_body Vprog Gprog f_fill_bin fill_bin_spec.
Proof. 
start_function. 

forward_call b.  (*** s = bin2size(b) ***)
set (s:=bin2sizeZ b).
assert (0 <= s <= bin2sizeZ(BINS-1)).
{ apply bin2size_range; try assumption. }

forward_call BIGBLOCK.  (*** *p = mmap(BIGBLOCK) ***)  
{ apply BIGBLOCK_size. }
Intros p. 
forward_if. (*** if p == -1 ***)
- (* typecheck guard *) entailer!. 
  (* TODO typecheck_error *) admit. 
- (* case p == -1 *)
  forward. (*** return NULL ***)
(* Andrew, why is H2 a typed_true instead of something nicer? 
   Similarly in connection with MAP_FAILED in the following. *)
  if_tac. (* split cases in mmap post *)
  -- Exists nullval. Exists 1. entailer!.
  -- (* contradictory case *)
    elimtype False. clear H1. simpl in H2. unfold MAP_FAILED in H3.
    destruct p; try contradiction; simpl in *; try subst i; inversion H2.

- (* case p <> -1 *) 
  if_tac. (* split cases in mmap post *)
  { (* contradictory case *) 
    elimtype False. clear H1. 
    destruct p; try contradiction; simpl in *; try inversion H3;
    try subst i; inversion H2. }
  forward. (*** Nblocks = (BIGBLOCK-WASTE) / (s+WORD) ***)
  { (* nonzero divisor *) entailer!. apply repr_inj_unsigned in H5; rep_omega. }
  deadvars!. (*  clear H.  *)
  assert_PROP (isptr p) by entailer!. destruct p; try contradiction.
  rename b0 into pblk. rename i into poff. (* p as blk+ofs *)
  simpl in H0,H1|-*.  (* should be simpl in * but that would mess up postcond *)
  forward. (*** q = p + WASTE ***)
  rewrite ptrofs_of_intu_unfold. rewrite ptrofs_mul_repr. normalize.
  forward. (*** j = 0 ***) 
  forward_while (*** while (j != Nblocks - 1) ***) 
    (fill_bin_Inv (Vptr pblk poff) s ((BIGBLOCK-WA) / (s+WORD)) ).
* (* pre implies inv *)
  Exists 0. 
  entailer!.  
* (* pre implies guard defined *)
  entailer!. 
* (* body preserves inv *)
  freeze [0] Fwaste. clear H.
  rewrite (memory_block_split_block s (BIGBLOCK - (WA + j * (s + WORD))) 
             (offset_val (WA + j * (s + WORD)) (Vptr pblk poff))).
  -- Intros. (* flattens the SEP clause *) rewrite offset_offset_val. 
  forward. (*** q[0] = s; ***)
  freeze [1; 2; 4; 5] fr1. 
  (* prepare for next assignment, as suggested by hint from forward tactic *)
  assert_PROP ( 
  (Vptr pblk
      (Ptrofs.add (Ptrofs.add poff (Ptrofs.repr (WA + j * (s + WORD))))
        (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr 1))))) 
    = field_address (tptr tvoid) [] 
        (offset_val (WA + j * (s + WORD) + WORD) (Vptr pblk poff))).
  + entailer!.  
  + forward. (*** *(q+WORD) = q+WORD+(s+WORD); ***)
    forward. (*** q += s+WORD; ***)
    forward. (*** j++; ***) 
  (* reestablish inv *)  
  Exists (j+1).  
  entailer!.  
  -- destruct H5 as [H5a [H5b [H5c H5d]]]. split; rep_omega. 
* (* after the loop *) 
(* TODO eventually: here we're setting up the assignments 
to finish the last block; this is like setting up in the loop body.
Then we fold into the list, like at the end of the loop body. 
It would be nice to factor commonalities. *)
  rewrite (memory_block_split_block s (BIGBLOCK - (WA + j * (s + WORD))) 
           (offset_val (WA + j * (s + WORD)) (Vptr pblk poff))).
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
  { entailer!. } 
  forward. (***   *(q+WORD) = NULL ***)
  normalize.
  set (q:= (offset_val (WA + j * (s + WORD)) (Vptr pblk poff))). 
  set (r:=(offset_val (WA + WORD) (Vptr pblk poff))).   
  gather_SEP 1 2 3 4. (* prepare for fill_bin_mmlist_null rewrite *)
  apply semax_pre with
   (PROP ( )
     LOCAL (temp _q q; temp _p (Vptr pblk poff); temp _s (Vint (Int.repr s));
     temp _Nblocks (Vint (Int.repr ((BIGBLOCK - WA) / (s + WORD))));
     temp _j (Vint (Int.repr j)))
     SEP (FRZL Fwaste; (mmlist s (Z.to_nat (j+1)) r nullval))).
  { cancel. (* ugnnnnnnnnnh, used to find the waste, before gather_SEP added above *)
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
  split; try omega. 
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
assert (Hb: 0 <= b < BINS) by (apply (claim2 n); assumption). 
rewrite (mm_inv_splitX gv b) by apply Hb. (* expose bins[b] in mm_inv *)
Intros bins lens idxs.
freeze [1; 3] Otherlists.
deadvars!.
forward. (*** p = bin[b] ***)
forward_if((*Jpost*) (*** if p==NULL ***)
    EX p:val, EX len:Z,
     PROP(p <> nullval)
     LOCAL(temp _p p; temp _b (Vint (Int.repr b)); gvar _bin (gv _bin); gvars gv)
     SEP(FRZL Otherlists; TT; 
         data_at Tsh (tarray (tptr tvoid) BINS) (upd_Znth b bins p) (gv _bin);
         mmlist (bin2sizeZ b) (Z.to_nat len) p nullval)). 

  + (* typecheck guard *)
  destruct (Znth b lens). 
  (*Set Printing Implicit. -- to see the need for following step. *)
  change Inhabitant_val with Vundef in H12.
  rewrite (proj2 H12 (eq_refl _)).
  auto 20 with valid_pointer. 
  assert (S n0 > 0)%nat by omega.
  auto 15 with valid_pointer.
  (* TODO add hints for mmlist *)
  + (* case p==NULL *) 
    change Inhabitant_val with Vundef in *.
    rewrite H4. 
    assert_PROP(Znth b lens = 0%nat) as Hlen0
        by (entailer!; apply H10; reflexivity).
    rewrite Hlen0.
    rewrite mmlist_empty.
    forward_call b. (*** p = fill_bin(b) ***) 
    Intro r_with_l; destruct r_with_l as [root len]; simpl.
    forward_if( (*** if p==NULL ***)
     (*Jpost*)EX p:val, EX len:Z,
     PROP(p <> nullval)
     LOCAL (temp _p p; temp _b (Vint (Int.repr b)); gvar _bin (gv _bin); gvars gv)
     SEP (FRZL Otherlists; TT; 
          data_at Tsh (tarray (tptr tvoid) BINS) (upd_Znth b bins p) (gv _bin);
          mmlist (bin2sizeZ b) 
                 (nth (Z.to_nat b) (upd_Znth b lens (Z.to_nat len)) 0%nat) p nullval)).
    {  admit. (* TODO typecheck *) } 
    ++ (* case p==NULL after fill_bin() *) 
      forward.
      Exists nullval.  entailer!. clear H6.
      thaw Otherlists.
      set (idxs:= (map Z.of_nat (seq 0 (Z.to_nat BINS)))).
      assert (Hemp: data_at Tsh (tarray (tptr tvoid) BINS) bins (gv _bin) =
                    data_at Tsh (tarray (tptr tvoid) BINS) bins (gv _bin) * emp) 
        by normalize.
      rewrite Hemp; clear Hemp.
      rewrite <- (mmlist_empty (bin2sizeZ b)) at 2.
      rewrite <- Hlen0 at 1.
      unfold mm_inv. Exists bins. Exists lens. Exists idxs.
      entailer!. 
      rewrite <- H4 at 1.
      rewrite (mm_inv_splitX' b); auto.
    ++ (* case p<>NULL *)
      if_tac. contradiction.
      gather_SEP 0 1.  (* gather_SEP 1 2. rewrite TT_sepcon_TT. *) 
      Intros.
      forward. (*** bin[b] = p ***)
      Exists root. Exists len.  
      rewrite nth_upd_Znth.
      entailer. cancel. 
++ admit. (* TODO what's this? same as preceding but with quantif
   rewrite (nth_upd_Znth b lens (Z.to_nat len0)). *)   
  + (* else branch p!=NULL *)
    forward. (*** skip ***)
    Exists (Znth b bins).  
    Exists (Z.of_nat (nth (Z.to_nat b) lens 0%nat)). (* annoying conversion *)
    rewrite Nat2Z.id.  
    rewrite upd_Znth_same_val by (rewrite H0; assumption). 
    entailer!.
    rewrite <- nth_Znth by (rewrite H1; assumption).  
    entailer.
  + (* after if: unroll and pop mmlist *)
    Intros p len.
    set (s:=bin2sizeZ b).  
    assert_PROP (len > 0). {
         entailer!.
         admit. (* TODO how use mmlist_ne_len? *) }
    rewrite (mmlist_unroll_nonempty s (Z.to_nat len) p); 
       try (rewrite Z2Nat.id; rep_omega); try assumption.
    Intros q.
    assert_PROP(force_val (sem_cast_pointer p) = field_address (tptr tvoid) [] p).
    { entailer!.
      (* TODO make little tactic for this idiom, also used above: *)
      unfold field_address. if_tac. normalize. contradiction. }
    forward. (*** q = *p ***)
    forward. (*** bin[b]=q ***)
    (* prepare token+block to return *)
    deadvars!.
    thaw Otherlists.  gather_SEP 4 5 6.
    replace_SEP 0 (malloc_token' Tsh n p * memory_block Tsh n p).
    go_lower.  change (-4) with (-WORD). (* ugh *)
    apply (to_malloc_token_and_block n p q s). 
    assumption. unfold s; unfold b; reflexivity. 
    (* refold invariant *)
    rewrite upd_Znth_twice by (rewrite H0; apply Hb).
    gather_SEP 4 1 5.
    set (lens':=(upd_Znth b lens (Nat.pred (Z.to_nat len)))).
    set (bins':=(upd_Znth b bins (force_val (sem_cast_pointer q)))).
    assert (Hlens: Nat.pred (Z.to_nat len) = (Znth b lens')).
    { unfold lens'. rewrite upd_Znth_same. reflexivity. rewrite H1. assumption. }
    rewrite Hlens; clear Hlens.
    change s with (bin2sizeZ b).
    forward. (*** return p ***)
    Exists p. entailer!. if_tac. contradiction. cancel.
    unfold mm_inv. Exists bins'. Exists lens'. 
    set (idxs:= (map Z.of_nat (seq 0 (Z.to_nat BINS)))).
    Exists idxs. cancel.
    entailer!.
    subst lens'; rewrite upd_Znth_Zlength; rewrite H1; auto.
(* TODO tactics and autorewrite for following; also in body_free_small *)

    assert (Hbins': sublist 0 b bins' = sublist 0 b bins)
      by (unfold bins'; rewrite sublist_upd_Znth_l; try reflexivity; try rep_omega).
    assert (Hlens': sublist 0 b lens' = sublist 0 b lens)
      by (unfold lens'; rewrite sublist_upd_Znth_l; try reflexivity; try rep_omega).
    assert (Hbins'': sublist (b+1) BINS bins' = sublist (b+1) BINS bins)
      by (unfold bins'; rewrite sublist_upd_Znth_r; try reflexivity; try rep_omega).
    assert (Hlens'': sublist (b+1) BINS lens' = sublist (b+1) BINS lens)
      by (unfold lens'; rewrite sublist_upd_Znth_r; try reflexivity; try rep_omega).
    assert (Hsub:  sublist 0 b (zip3 lens bins idxs)  
                 = sublist 0 b (zip3 lens' bins' idxs)).
    { repeat rewrite sublist_zip3; try rep_omega.
      rewrite Hbins'. rewrite Hlens'.  reflexivity.
      - unfold lens'; rewrite upd_Znth_Zlength; repeat rep_omega.
      - (* TODO lengths -  Set Printing Implicit. *) admit.
      - (* TODO lengths -  Set Printing Implicit. *) admit.
      - unfold idxs.  rewrite Zlength_map. (*seq_length Zlength_length*) admit.
    } 
    assert (Hsub': 
              sublist (b + 1) BINS (zip3 lens bins idxs) = 
              sublist (b + 1) BINS (zip3 lens' bins' idxs)) by admit. (* see preceding *)
    rewrite Hsub. rewrite Hsub'.
    (* Here's a place where it would be nice if sep_apply could do rewriting *)
    rewrite pull_right.
    assert (Hq: q = (Znth b bins')). (* TODO clean this mess *)
    { unfold bins'. rewrite upd_Znth_same.  
      destruct q; auto 10  with valid_pointer.
      auto 10  with valid_pointer; destruct PNq. destruct PNq. destruct PNq.
      rewrite H0; assumption. }
    rewrite Hq.
    rewrite mm_inv_splitX'; try entailer!; auto.
    subst lens'; rewrite upd_Znth_Zlength; rewrite H1; auto.
Admitted.

Lemma body_malloc_large: semax_body Vprog Gprog f_malloc_large malloc_large_spec.
Proof.
start_function. 
(* TODO freeze mm_inv *)
forward_call (n+WA+WORD). (*** t'1 = mmap(NULL, nbytes+WASTE+WORD, ...) ***)
{ rep_omega. }
Intros p.
forward_if. (*** if (p==MAP_FAILED) ***)
- (* typecheck guard *) 
entailer!.
 admit. (* TODO another typecheck_error *)
- (* case p == MAP_FAILED *) 
  forward. (*** return NULL  ***)
  Exists (Vint (Int.repr 0)).
  if_tac. (* cases in post of mmap *)
  + if_tac; entailer!. 
  + (* impossible case *)
    elimtype False. destruct p; try contradiction; simpl in *.
    subst i; simpl in *. inversion H1. inversion H1. 
- (* case p <> MAP_FAILED *) 
  if_tac. (* cases in post of mmap *)
  + (* impossible case *)
    elimtype False. destruct p; try contradiction; simpl in *; try inversion H2.
    subst i; simpl in *; inversion H1.
  + assert_PROP (
    (force_val
     (sem_add_ptr_int tuint Signed
        (force_val
           (sem_cast_pointer
              (force_val
                 (sem_add_ptr_int tschar Unsigned p
                    (Vint
                       (Int.sub
                          (Int.mul (Ptrofs.to_int (Ptrofs.repr 4)) (Int.repr 2))
                          (Ptrofs.to_int (Ptrofs.repr 4))))))))
         (Vint (Int.repr 0))) = field_address tuint [] (offset_val WA p)) ).
     { entailer!. change (4 * 2 - 4) with WA.  

destruct H0 as [zp [Hzp Hp_align]].
destruct p; try contradiction. simpl. normalize.
rewrite field_address_offset. simpl. normalize. repeat split; auto.
(* size *) 
red. red in H3.
rewrite <- (Ptrofs.repr_unsigned i).
normalize. rewrite Ptrofs.unsigned_repr; simpl sizeof; rep_omega. 
(* alignment *)
(* TODO use Hp_align *) admit.

SearchHead (align_compatible _ _).

}

    rewrite malloc_large_memory_block; try rep_omega. 
    Intros. (* flatten sep *)
    forward. (*** (p+WASTE)[0] = nbytes;  ***)
    { (* typecheck *) entailer!. destruct p; try contradiction; simpl; auto. }

    forward. (*** return (p+WASTE+WORD);  ***)
    Exists (offset_val (WA+WORD) p).
    entailer!.  destruct p; try contradiction; simpl; auto. normalize.
    if_tac. entailer!. 
    elimtype False. destruct p; try contradiction; simpl in *. inversion H1.
    entailer!.
    unfold malloc_token'.
    Exists n.
    unfold malloc_tok.
    if_tac. rep_omega. entailer!. cancel.
    assert (Hz: n - n = 0) by omega. rewrite Hz.
    rewrite memory_block_zero.
    entailer!.
Admitted.



Lemma body_free_small:  semax_body Vprog Gprog f_free_small free_small_spec.
Proof. 
start_function. 
(*destruct H as [Hn Hs].*)
destruct H as [[Hn Hn'] Hs].
forward_call s. (*** b = size2bin(s) ***)
{ subst; apply bin2size_rangeB; apply claim2; auto.  }
set (b:=(size2binZ n)). 
assert (Hb: b = size2binZ s) by (subst; rewrite claim3; auto).
rewrite <- Hb.
assert (Hb': 0 <= b < BINS) 
  by (change b with (size2binZ n); apply claim2; split; assumption).
(* now expose bins[b] in mm_inv *)
rewrite (mm_inv_splitX gv b Hb').
Intros bins lens idxs.
forward. (***  void *q = bin[b] ***) 
assert_PROP( (force_val (sem_cast_pointer p) = field_address (tptr tvoid) [] p) ). 
entailer!.
unfold field_address; normalize; if_tac; auto; contradiction.
forward. (***  *((void ** )p) = q ***)
gather_SEP 0 1 2 5.
set (q:=(Znth b bins)).
assert_PROP (p <> nullval) by entailer!.
apply semax_pre with 
    (PROP ( )
     LOCAL (temp _q q; temp _b (Vint (Int.repr b)); 
     temp _p p; temp _s (Vptrofs (Ptrofs.repr s)); 
     gvar _bin (gv _bin); gvars gv)
     SEP ((EX q': val, 
          data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p) *
          data_at Tsh (tptr tvoid) q' p *
          memory_block Tsh (s - WORD) (offset_val WORD p) *
          mmlist (bin2sizeZ b) (Znth b lens) q' nullval) ;
     data_at Tsh (tarray (tptr tvoid) BINS) bins (gv _bin);
     iter_sepcon (sublist 0 b (zip3 lens bins idxs)) mmlist';
     iter_sepcon (sublist (b + 1) BINS (zip3 lens bins idxs)) mmlist';
     TT)).
{ Exists q. entailer!.  entailer. } 
assert (Hbs: bin2sizeZ b = s) by auto. rewrite Hbs; clear Hbs.
change (Znth b lens)
  with (Nat.pred (Nat.succ (Znth b lens))).
rewrite <- (mmlist_unroll_nonempty s (Nat.succ (Znth b lens)) p).
3: apply succ_pos.
2: assumption. 
forward. (***  bin[b] = p ***)
set (bins':=(upd_Znth b bins p)).
set (lens':=(upd_Znth b lens (Nat.succ (Znth b lens)))).
gather_SEP 1 2 3 0. 
apply semax_pre with 
    (PROP ( )
     LOCAL (temp _q q; temp _b (Vint (Int.repr b)); 
     temp _p p; temp _s (Vptrofs (Ptrofs.repr s)); 
     gvar _bin (gv _bin); gvars gv)
     SEP (
  EX bins1: list val, EX lens1: list nat, EX idxs1: list Z,
  !! (Zlength bins1 = BINS /\ Zlength lens1 = BINS /\ Zlength idxs1 = BINS
      /\ idxs1 = map Z.of_nat (seq 0 (Z.to_nat BINS))) &&
    data_at Tsh (tarray (tptr tvoid) BINS) bins1 (gv _bin) * 
    iter_sepcon (sublist 0 b (zip3 lens1 bins1 idxs1)) mmlist' *
    mmlist (bin2sizeZ b) (Znth b lens1) (Znth b bins1) nullval *
    iter_sepcon (sublist (b + 1) BINS (zip3 lens1 bins1 idxs1)) mmlist' *
    TT )).
{ Exists bins'. Exists lens'. Exists idxs.
  assert_PROP(Zlength bins' = BINS /\ Zlength lens' = BINS).
  { unfold bins'.  unfold lens'.  
    rewrite (upd_Znth_Zlength b bins p); try omega.
    match goal with |- context [upd_Znth b lens ?X] => set (foo:=X) end.
    rewrite (upd_Znth_Zlength b lens foo); try omega. 
    entailer!. 
  }
  assert (Hbs: bin2sizeZ b = s) by auto. rewrite Hbs; clear Hbs. 
  assert (Hbp: (Znth b bins') = p) 
    by (unfold bins'; rewrite upd_Znth_same; auto; rewrite H; assumption). 
    rewrite Hbp; clear Hbp. 
  assert (Hlen: (Nat.succ (Znth b lens)) = (Znth b lens')) 
    by (unfold lens'; rewrite upd_Znth_same; try reflexivity; omega).
    rewrite Hlen; clear Hlen. 
  entailer!.
  change (upd_Znth (size2binZ n) bins p) with bins'.
  entailer!.
  (* remains to show bins' and lens' are same as originals aside from n *)
  set (idxs:=(map Z.of_nat (seq 0 (Z.to_nat BINS)))) in *.
  repeat rewrite sublist_zip3; try rep_omega.
  assert (Hlens_l: (sublist 0 (size2binZ n) lens') 
                 = (sublist 0 (size2binZ n) lens)) by
   (unfold lens'; rewrite sublist_upd_Znth_l; try reflexivity; try rep_omega).
  assert (Hlens_r: (sublist (size2binZ n + 1) BINS lens') 
                 = (sublist (size2binZ n + 1) BINS lens)) by 
   (unfold lens'; rewrite sublist_upd_Znth_r; try reflexivity; try rep_omega).
  assert (Hbins_l: (sublist 0 (size2binZ n) bins')
                 = (sublist 0 (size2binZ n) bins)) by 
   (unfold bins'; rewrite sublist_upd_Znth_l; try reflexivity; try rep_omega).
  assert (Hbins_r: (sublist (size2binZ n + 1) BINS bins')
                 = (sublist (size2binZ n + 1) BINS bins)) by 
   (unfold bins'; rewrite sublist_upd_Znth_r; try reflexivity; try rep_omega).
  rewrite Hbins_l. rewrite Hbins_r. rewrite Hlens_l. rewrite Hlens_r.
  entailer!.
}
rewrite <- (mm_inv_splitX gv b Hb'). 
forward. (*** return ***) 
Qed.






Lemma body_malloc:  semax_body Vprog Gprog f_malloc malloc_spec'.
Proof. 
start_function. 
forward_call (BINS-1). (*** t'3 = bin2size(BINS-1) ***)
rep_omega. 
forward_if. (*** if nbytes > t'3 ***)
- (* case nbytes > bin2size(BINS-1) *)
  forward_call (n,gv).  (*** t'1 = malloc_large(nbytes) ***)
  { (* precond *) rep_omega.  }
  Intros p.
  forward. (*** return t'1 ***) 
  if_tac.
  + (* case p = null *) Exists nullval. entailer!.
  + Exists p. if_tac. contradiction. 
    entailer!.  
- (* case nbytes <= bin2size(BINS-1) *)
  forward_call(n,gv).  (*** t'2 = malloc_small(nbytes) ***)
  { (* precond *) rep_omega. }
  Intros p.
  forward. (*** result = t'2 ***)
  Exists p. 
  entailer!.
Qed.


Lemma body_free:  semax_body Vprog Gprog f_free free_spec'.
Proof. 
start_function. 
forward_if (PROP()LOCAL()SEP(mm_inv gv)). (*** if (p != NULL) ***)
- (* typecheck *) if_tac; entailer!.
- (* case p!=NULL *)
apply semax_pre with 
    (PROP ( )
     LOCAL (temp _p p; gvars gv)
     SEP (mm_inv gv;  malloc_token' Tsh n p * memory_block Tsh n p)).
{ if_tac; entailer!. }
assert_PROP ( 0 <= n <= Ptrofs.max_unsigned - WORD ) by entailer!.
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
{ (* precond *) rep_omega. } 
forward_if (PROP () LOCAL () SEP (mm_inv gv)). (*** if s <= t'1 ***)
 -- (* case s <= bin2sizeZ(BINS-1) *)
    forward_call(p,s,n,gv). (*** free_small(p,s) ***) 
    { (* preconds *) split. split;  omega. omega. } 
    entailer!. if_tac. entailer. omega.
 -- (* case s > bin2sizeZ(BINS-1) *)
    if_tac. omega.
    (*** munmap( p-(WASTE+WORD), s+WASTE+WORD ) ***)
    forward_call( (offset_val (-(WA+WORD)) p), (s+WA+WORD) ).
    + (* TODO pointer arith? *) admit.
    + entailer!. rewrite free_large_memory_block. entailer!. rep_omega.
    + rep_omega.
    + entailer!.
- (* case p == NULL *) 
forward.
entailer!.
- (* after if *)
forward. (*** return ***)
Admitted.



(* TODO Complete implementation of malloc and free,
   and an interesting main, before verifying these. 
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
semax_func_cons body_malloc_large.
semax_func_cons body_free_small.
semax_func_cons body_malloc.
semax_func_cons body_free.
semax_func_cons body_main.
Qed.

*)
