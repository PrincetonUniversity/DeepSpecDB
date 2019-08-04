Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import Lia. (* for lia tactic (nonlinear integer arithmetic) *) 

Require Import malloc_lemmas. (* background *)
Require Import malloc_shares.  

Ltac start_function_hint ::= idtac. (* no hint reminder *)

Require Import malloc. (* the program *)
(* Note about clightgen:
Compiling malloc.c triggers a warning from a header file:
/usr/include/sys/cdefs.h:81:2: warning: "Unsupported compiler detected"
This is ok.
*)

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Local Open Scope Z.
Local Open Scope logic.  

(*+ assumed specs *)

(* Specifications for posix mmap0 and munmap as used by this memory manager.
   Using wrapper mmap0 (in malloc.v) which returns 0 on failure, because 
   mmap returns -1, and pointer comparisons with non-zero literals violate 
   the C standard.   Aside from that, mmap0's spec is the same as mmap's.

   The posix spec says the pointer will be aligned on page boundary.  Our
   spec uses malloc_compatible which says it's on the machine's natural 
   alignment. 
*)

Definition mmap_align: Z := 4. 

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
            temp 4%positive (Vint (Int.repr 4098)); (* MAP_PRIVATE|MAP_ANONYMOUS *)
            temp 5%positive (Vint (Int.repr (-1)));
            temp 6%positive (Vlong (Int64.repr 0)))
     SEP ()
   POST [ tptr tvoid ] EX p:_, 
     PROP ( if eq_dec p nullval
            then True else malloc_compatible n p )
     LOCAL (temp ret_temp p)
     SEP ( if eq_dec p nullval
           then emp else memory_block Tsh n p).

(* NOTE: the postcondition should be if ret==0 then the memory was freed. *)
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
 
(*
(* TODO working on sharable token - based on Andrew's email of 11 Oct *)
(*Require Import VST.veric.shares. *)
Require Import VST.msl.sepalg.
Require Import VST.msl.shares. (* uses tree_shares *)

Definition Lsh := VST.msl.shares.Share.Lsh. 
Definition split := VST.msl.shares.Share.split.
Definition lub := VST.msl.shares.Share.lub.
Definition bot := VST.msl.shares.Share.bot.
Definition top := VST.msl.shares.Share.top.
*)

Definition comp := VST.msl.shares.Share.comp.

Definition maltok (sh: share) (s: Z) (p: val) := 
   data_at Tsh tuint (Vint (Int.repr s)) (offset_val (-WORD) p) * (* size *)
   memory_block (comp Ews) s p.                           (* chunk *)

(*
Lemma maltok_valid_pointer':
  forall sh s p, s>0 -> leftmost_eps sh ->
            memory_block (maybe_sliver_leftmost sh) s p |-- valid_pointer p.
Proof.
  intros.
  apply memory_block_valid_ptr; try assumption.
  unfold maybe_sliver_leftmost.
  destruct (leftmost_epsilon sh).
  apply nonidentity_comp_Ews.
  exfalso; unfold leftmost_eps in *; auto.
Qed.
*)

(* TODO allow n=0 *)
Lemma maltok_valid_pointer:
  forall sh n p, n>0 -> (* leftmost_eps sh -> *)
            maltok sh n p |-- valid_pointer p.
Proof.
  intros. unfold maltok.
  entailer!.
  sep_apply (memory_block_valid_pointer (comp Ews) n p 0).
  omega.
  apply nonidentity_comp_Ews.
  entailer.
Qed.


(*
Lemma cleave_data_at:
  forall sh t v p, data_at (fst (cleave sh)) t v p * data_at (snd (cleave sh)) t v p 
              = data_at sh t v p.
Proof.
  intros. pose (cleave_join sh). apply data_at_share_join; auto.
Qed.

Lemma shave_data_at:
  forall sh t v p, data_at (fst (shave sh)) t v p * data_at (snd (shave sh)) t v p 
              = data_at sh t v p.
Proof.
  intros. pose (shave_join sh). apply data_at_share_join; auto.
Qed.


Definition maltok' (sh: share) (s: Z) (p: val) : mpred := 
   EX sh':share, !! tokChunk sh sh' &&
   data_at (augment sh) tuint (Vint (Int.repr s)) (offset_val (-WORD) p) * (* size *)
   memory_block sh' s p.                           (* chunk *)

Lemma maltok'_valid_pointer:
  forall sh n p, n > 0 -> sh <> bot -> 
    maltok' sh n p |-- valid_pointer p.
Proof.
intros.
unfold maltok'.
entailer.
assert (sh' <> bot) by (intro; subst; pose proof  (tokChunk_bot sh H1); auto).
assert (nonidentity sh') by (intro; apply identity_share_bot in H3; auto).
entailer!.
Qed.

Lemma shave_maltok':
  forall sh sh1 sh2 n p, (sh1,sh2) = shave sh -> sh <> bot ->
    maltok' sh n p |-- maltok' sh1 n p * maltok' sh2 n p.
Proof.
intros.
unfold maltok'.
entailer.
assert (sh' <> bot) by (intro; subst; pose proof (tokChunk_bot sh H1); auto).
pose proof (tokChunk_shave _ _ _ _ H1 H).
destruct H3 as [sh1' H3].
destruct H3 as [sh2' H3].
destruct H3 as [Hjoin [Hsh1' Hsh2']].
Exists sh2'.
Exists sh1'.
entailer!.
rewrite <- (memory_block_share_join _ _ _ _ _ Hjoin).
entailer!.

destruct (leftmost_epsilon sh).
admit. (* shave_leftmost lemmas and def augment *)
admit. (* shave_leftmost lemmas and def augment *)
all: fail.
Admitted.


Lemma to_maltok'_block: 
forall n p, 
  data_at Tsh tuint (Vptrofs (Ptrofs.repr n)) (offset_val (- WORD) p) *
  memory_block Tsh n p 
  = maltok' Ews n p * memory_block Ews n p.
Proof.
intros.
apply pred_ext.
- (* |-- *)
unfold maltok'.
Exists (comp Ews).
pose proof tokChunk_Ews.
entailer!.
assert (join (comp Ews) Ews Tsh) by (apply join_comm; apply join_comp_Tsh).
rewrite <- (memory_block_share_join (comp Ews) Ews Tsh); auto.
rewrite augment_Ews.
entailer!.
- (* --| *)
unfold maltok'.
rewrite augment_Ews.
entailer!.
assert (sh' = comp Ews)  
  by (pose proof tokChunk_Ews; apply tokChunk_functional with Ews; assumption).
subst.
assert (join (comp Ews) Ews Tsh) by (apply join_comm; apply join_comp_Tsh).
rewrite <- (memory_block_share_join (comp Ews) Ews Tsh); auto.
Qed.

*)

(*+ malloc token *)

(* Accounts for the size field, alignment padding, 
   and a share of the allocated block so that malloc_token sh n p |- valid_pointer p
   where p is the address returned by malloc.

Shadows malloc_token in floyd/library.  

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
*)

Definition malloc_tok (sh: share) (n: Z) (s: Z) (p: val): mpred := 
   !! (0 <= n <= s /\ s + WA + WORD <= Ptrofs.max_unsigned /\ 
       (s <= bin2sizeZ(BINS-1) -> s = bin2sizeZ(size2binZ n)) /\
       (s > bin2sizeZ(BINS-1) -> s = n) /\
       malloc_compatible s p ) &&
    data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p) (* stored size *)
  * memory_block (comp Ews) s p                               (* retainer *)
(* TODO retainer size n shared with user's block; (s-n) shared with following *)
  * memory_block Ews (s - n) (offset_val n p)                 (* waste at end of small *)
  * (if zle s (bin2sizeZ(BINS-1))  
    then emp
    else memory_block Tsh WA (offset_val (-(WA+WORD)) p)).  (* waste at start of large *)

Definition malloc_token (sh: share) (t: type) (p: val): mpred := 
   EX s:Z, malloc_tok sh (sizeof t) s p.

Definition malloc_token' (sh: share) (n: Z) (p: val): mpred := 
   EX s:Z, malloc_tok sh n s p.


Lemma malloc_token_valid_pointer_size:
  forall sh t p, 
(*sepalg.nonidentity sh -> *)
malloc_token sh t p |-- valid_pointer (offset_val (- WORD) p).
Proof.
  intros; unfold malloc_token, malloc_tok; entailer!.
  sep_apply (data_at_valid_ptr Tsh tuint (Vint (Int.repr s)) (offset_val(-WORD) p)).
  apply top_share_nonidentity.
  entailer!.
Qed.

Lemma malloc_token_local_facts:
  forall sh t p, malloc_token sh t p 
  |-- !!( malloc_compatible (sizeof t) p /\ 
          0 <= (sizeof t) <= Ptrofs.max_unsigned - (WA+WORD)).
Proof.
  intros; unfold malloc_token; Intro s; unfold malloc_tok; entailer!.
  apply (malloc_compatible_prefix (sizeof t) s p); try omega; try assumption.
Qed.

Lemma malloc_token_valid_pointer:
  forall sh t p, malloc_token sh t p |-- valid_pointer p.
Proof.
  intros.  unfold malloc_token.
  entailer!.
  unfold malloc_tok.
  assert_PROP (s > 0). { 
    entailer!. bdestruct(bin2sizeZ (BINS-1) <? s). rep_omega.
    apply Znot_lt_ge in H9. apply Z.ge_le in H9. apply H1 in H9.
    pose proof (bin2size_range (size2binZ (sizeof t))). subst.
    pose proof (size2bin_range (sizeof t)). rep_omega.
  }
  sep_apply (memory_block_valid_pointer (comp Ews) s p 0); try omega.
  apply nonidentity_comp_Ews.
  entailer.
Qed.

Hint Resolve malloc_token_valid_pointer_size : valid_pointer.
Hint Resolve malloc_token_valid_pointer : valid_pointer.
Hint Resolve malloc_token_local_facts : saturate_local.

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


Lemma mmlist_local_facts:
  forall sz len p r,
   mmlist sz len p r |--
   !! (0 <= sz <= Ptrofs.max_unsigned /\ 
        is_pointer_or_null p /\ is_pointer_or_null r /\ (p = r <-> len=O)). 
Proof.
  intros; generalize dependent p; induction len.
  - (* len 0 *)
    destruct p; try contradiction; simpl; entailer!;
    try (split; intro; reflexivity).
  - (* len > 0 *) 
    intros p; unfold mmlist; fold mmlist.
    Intro q. specialize (IHlen q); entailer. 
    sep_apply IHlen; entailer.
    assert (p = r <-> S len = 0%nat) by
        (split; intro; try contradiction; try omega).
    entailer.
Qed.
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
    mmlist sz (Z.to_nat len) p q |-- !! (len > 0).
Proof. 
  intros. destruct len.
  simpl; normalize. entailer!; omega. simpl. entailer!.
Qed.

(* The following is formulated as an equality so it can be used in 
both directions.  It's written using Nat.pred instead of len-1 because
Coq couldn't infer the type for len-1 in scripts that rely on this lemma.
(One workaround would involve replacing len by (Z.to_nat len).)

Note that by type of len, and mmlist_local_facts, 
p <> nullval and (mmlist sz len p nullval) imply (Z.of_nat len) > 0,
so that antecedent is only needed for the RHS-to-LHS direction.
*)

Lemma mmlist_unroll_nonempty:
  forall sz len p r, (Z.of_nat len) > 0 ->
      mmlist sz len p r
  =   EX q:val,
      !!(malloc_compatible sz p /\ p <> r) && 
      data_at Tsh tuint (Vptrofs (Ptrofs.repr sz)) (offset_val (- WORD) p) *
      data_at Tsh (tptr tvoid) q p *
      memory_block Tsh (sz - WORD) (offset_val WORD p) *
      mmlist sz (Nat.pred len) q r.
Proof.
  intros. apply pred_ext.
  - (* LHS |-- RHS *)
    destruct len. elimtype False; simpl in *; omega.
    simpl. Intros q; Exists q. entailer.
  - (* RHS |-- LHS *)
    Intros q. destruct len. elimtype False; simpl in *; omega.
    simpl. Exists q. entailer!.
Qed.


Lemma mmlist_empty: 
  forall sz, 0 < sz <= bin2sizeZ(BINS - 1) ->
             mmlist sz 0 nullval nullval = emp.
Proof.
  intros. apply pred_ext; simpl; entailer!.
Qed.

(* lemmas on constructing an mmlist from a big block (used in fill_bin) *)

Lemma malloc_compatible_offset_isptr:
  forall n m q, malloc_compatible n (offset_val m q) -> isptr q.
Proof. intros. destruct q; auto. unfold isptr; auto. 
Qed.

Ltac mcoi_tac := 
  eapply malloc_compatible_offset_isptr;  
  match goal with | H: malloc_compatible _ _ |- _ => apply H end.


Lemma mmlist_fold_last: 
(* Adding tail chunk. 
Formulated in the manner of lseg_app' in vst/progs/verif_append2.v.
The preserved chunk is just an idiom for list segments, because we have
seg p q * q|->r * r|-> s entails seg p r * r|-> s
but not 
seg p q * q|->r entails seg p r 

This lemma is for folding at the end, in the non-null case, so the
length of the preserved chunk can be assumed to be at least s+WORD. *)
  forall s n r q m,  malloc_compatible s (offset_val WORD q) -> 
                WORD < m -> m - WORD <= Ptrofs.max_unsigned -> 
                s <= bin2sizeZ(BINS-1) ->
  mmlist s n r (offset_val WORD q) * 
  data_at Tsh (tarray tuint 1) [(Vint (Int.repr s))] q * 
  data_at Tsh (tptr tvoid) (offset_val (s+WORD+WORD) q) (offset_val WORD q) *
  memory_block Tsh (s - WORD) (offset_val (WORD + WORD) q) *
  memory_block Tsh m (offset_val (s + WORD) q) (* preserved *)
  |-- mmlist s (n+1) r (offset_val (s + WORD + WORD) q ) *
      memory_block Tsh m (offset_val (s + WORD) q). (* preserved *)
Proof.
(* By induction.  For the ind step, unroll at the start of the lists,
in both antecedent and consequent, in order to apply the ind hyp. *)
intros. generalize dependent r. induction n. 
- intros. unfold mmlist; fold mmlist. rewrite Nat.add_1_r. 
  assert_PROP( r = (offset_val WORD q)) by entailer!; subst. 
  rewrite mmlist_unroll_nonempty; change (Nat.pred 1) with 0%nat; 
    try (change 0 with (Z.of_nat 0); rewrite <- Nat2Z.inj_gt; omega).
  Exists (offset_val (s + WORD + WORD) q).
  unfold mmlist; fold mmlist.
  replace ((offset_val (- WORD) (offset_val WORD q))) with q
    by (normalize; rewrite isptr_offset_val_zero; auto; try mcoi_tac).

  assert_PROP(offset_val WORD q <> offset_val (s + WORD + WORD) q).
  { (* use memory_block_conflict to prove this disequality *)
    (* similar to Andrew's proof steps in induction case below *)
    apply not_prop_right; intro; subst.
    simpl; normalize.
    replace m with (WORD + (m-WORD)) by omega.
    rewrite memory_block_split_offset; normalize; try rep_omega.
    match goal with | |- context[data_at ?sh (tptr tvoid) ?Vs ?op] => 
                  sep_apply (data_at_memory_block sh (tptr tvoid) Vs op) end.
    match goal with | HA: offset_val _ _ = offset_val _ _ |- _ => rewrite <- HA end.
    normalize.
    match goal with | |- context[ 
                      memory_block ?sh1 ?sz1 (offset_val WORD q) * (_ * (_ * (_ *
                      memory_block ?sh2 ?sz2 (offset_val WORD q) )))] => 
        sep_apply (memory_block_conflict sh1 sz1 sz2 (offset_val WORD q)) end.
    apply top_share_nonunit; try rep_omega.
    split.
    change (sizeof(tptr tvoid)) with WORD; rep_omega.
    change (sizeof(tptr tvoid)) with WORD; rep_omega.
    simpl; rep_omega.
    entailer!.  
  }
  erewrite data_at_singleton_array_eq; try reflexivity.  entailer!. cancel.
- intros. rewrite Nat.add_1_r.
  rewrite (mmlist_unroll_nonempty s (S(S n)));  
    try auto; try (change 0 with (Z.of_nat 0); rewrite <- Nat2Z.inj_gt; omega).
  rewrite (mmlist_unroll_nonempty s (S n));
    try auto; try (change 0 with (Z.of_nat 0); rewrite <- Nat2Z.inj_gt; omega).
  Intro p; Exists p.
  assert_PROP (r <> (offset_val (s+WORD+WORD) q)).
  { (* use memory_block_conflict to prove this disequality *)
    replace m with (WORD+(m-WORD)) by omega.
    destruct q; auto; try entailer.
    replace (offset_val (s + WORD) (Vptr b i))
      with (Vptr b (Ptrofs.add (Ptrofs.repr (s+WORD)) i))
      by (simpl; f_equal; rewrite Ptrofs.add_commut; reflexivity).
    rewrite memory_block_split_repr; try rep_omega. 
    2: { split; try rep_omega.
         unfold size_compatible' in *; simpl in *;
         rewrite Ptrofs.add_commut; rep_omega.
    }
    replace (Ptrofs.add (Ptrofs.add (Ptrofs.repr (s + WORD)) i) (Ptrofs.repr WORD)) 
      with (Ptrofs.add i (Ptrofs.repr (s + WORD + WORD))) 
      by ( rewrite <- Ptrofs.add_commut; rewrite Ptrofs.add_assoc; 
           rewrite (Ptrofs.add_commut i); rewrite <- Ptrofs.add_assoc; normalize).
    replace (offset_val (s + WORD + WORD) (Vptr b i))
      with (Vptr b (Ptrofs.add i (Ptrofs.repr (s + WORD + WORD))))
        by (simpl; reflexivity).
    clear IHn H2 H4 H5 H6 H7 H8 H9 H10 H12 H13 H14 H15 H16 H17.
    assert (m - WORD > 0) by omega.
    (* Andrew's heroic proof of the disequality: *)
    apply not_prop_right; intro; subst.
    simpl. normalize.
    replace (s + WORD + WORD + - WORD) with (s + WORD) by omega.
    rewrite <- !(Ptrofs.add_commut i).  (* rewrite at least once *)
    sep_apply (data_at_memory_block Tsh tuint (Vint (Int.repr s)) (Vptr b (Ptrofs.add i (Ptrofs.repr (s + WORD)))) ).
    change (sizeof tuint) with WORD.
    sep_apply (memory_block_conflict Tsh WORD WORD (Vptr b (Ptrofs.add i (Ptrofs.repr (s + WORD))))); try rep_omega.
    apply top_share_nonunit; try rep_omega.
    entailer!.
  } 
  entailer.  (* avoid cancelling trailing block needed by IHn *)
  change (Nat.pred (S n)) with n; change (Nat.pred (S(S n))) with (S n).
  replace (S n) with (n+1)%nat by omega.
  specialize (IHn p).
  sep_apply IHn; entailer!.
Qed.



Lemma mmlist_fold_last_null: 
  forall s n r q,  malloc_compatible s (offset_val WORD q) -> 
  mmlist s n r (offset_val WORD q) * 
  data_at Tsh (tarray tuint 1) [(Vint (Int.repr s))] q * 
  data_at Tsh (tptr tvoid) nullval (offset_val WORD q) *
  memory_block Tsh (s - WORD) (offset_val (WORD + WORD) q) 
  |-- mmlist s (n+1) r nullval.
Proof.  (* By induction, similar to mmlist_fold_last. *)
intros. generalize dependent r. induction n. 
- intros. unfold mmlist; fold mmlist. rewrite Nat.add_1_r. 
  assert_PROP( r = (offset_val WORD q)) by entailer!; subst. 
  rewrite mmlist_unroll_nonempty; change (Nat.pred 1) with 0%nat; 
    try (change 0 with (Z.of_nat 0); rewrite <- Nat2Z.inj_gt; omega).
  Exists nullval.
  unfold mmlist; fold mmlist.
  replace ((offset_val (- WORD) (offset_val WORD q))) with q
    by (normalize; rewrite isptr_offset_val_zero; auto; try mcoi_tac).
  entailer!.  
  erewrite data_at_singleton_array_eq; try reflexivity.  entailer!.
- intros. rewrite Nat.add_1_r.
  rewrite (mmlist_unroll_nonempty s (S(S n)) r nullval); 
    try auto; try (change 0 with (Z.of_nat 0); rewrite <- Nat2Z.inj_gt; omega).
  rewrite Nat.pred_succ.
  rewrite (mmlist_unroll_nonempty s (S n) r (offset_val WORD q)); 
    try auto; try (change 0 with (Z.of_nat 0); rewrite <- Nat2Z.inj_gt; omega).
  Intro p; Exists p.
  entailer!. 
  change (Nat.pred (S n)) with n. 
  specialize (IHn p).
  replace (S n) with (n+1)%nat by omega.
  sep_apply IHn; entailer!.
Qed.


(*+ module invariant mem_mgr *)

(* There is an array, its elements point to null-terminated lists 
of right size chunks, and there is some wasted memory.
*) 

Definition mem_mgr (gv: globals): mpred := 
  EX bins: list val, EX lens: list nat, EX idxs: list Z,
    !! (Zlength bins = BINS /\ Zlength lens = BINS /\
        idxs = map Z.of_nat (seq 0 (Z.to_nat BINS))) &&
  data_at Tsh (tarray (tptr tvoid) BINS) bins (gv _bin) * 
  iter_sepcon mmlist' (zip3 lens bins idxs) * 
  TT. (* waste, which arises due to alignment in bins *)

(*  This is meant to describe the extern global variables of malloc.c,
    as they would appear as processed by CompCert and Floyd. *)
Definition initialized_globals (gv: globals) := 
   !! (headptr (gv _bin)) &&
   data_at Tsh (tarray (tptr tvoid) BINS) (repeat nullval (Z.to_nat BINS)) (gv _bin).

Lemma create_mem_mgr: 
  forall (gv: globals), initialized_globals gv |-- mem_mgr gv.
Proof.
  intros gv.
  unfold initialized_globals; entailer!.
  unfold mem_mgr.
  Exists (repeat nullval (Z.to_nat BINS));
  Exists (repeat 0%nat (Z.to_nat BINS));
  Exists (Zseq BINS); entailer!.
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



Lemma mem_mgr_split':
 forall b:Z, forall bins lens idxs,
     0 <= b < BINS -> Zlength bins = BINS -> Zlength lens = BINS -> 
     idxs = map Z.of_nat (seq 0 (Z.to_nat BINS)) ->
 iter_sepcon mmlist' (sublist 0 b (zip3 lens bins idxs)) * 
 iter_sepcon mmlist' (sublist (b+1) BINS (zip3 lens bins idxs)) *
 mmlist (bin2sizeZ b) (Znth b lens) (Znth b bins) nullval 
  =
 iter_sepcon mmlist' (zip3 lens bins idxs). 
Proof. 
  intros.
  replace (mmlist (bin2sizeZ b) (Znth b lens) (Znth b bins) nullval)
     with (mmlist' ((Znth b lens), (Znth b bins), b)) by (unfold mmlist'; auto).
  assert (Hassoc: 
      iter_sepcon mmlist' (sublist 0 b (zip3 lens bins idxs)) *
      iter_sepcon mmlist' (sublist (b + 1) BINS (zip3 lens bins idxs)) *
      mmlist' (Znth b lens, Znth b bins, b) 
    = 
      iter_sepcon mmlist' (sublist 0 b (zip3 lens bins idxs)) *
      mmlist' (Znth b lens, Znth b bins, b) * 
      iter_sepcon mmlist' (sublist (b + 1) BINS (zip3 lens bins idxs)) )
    by ( apply pred_ext; entailer!).
  rewrite Hassoc; clear Hassoc.
  assert (Hidxs: Zlength idxs = BINS) 
    by  (subst; rewrite Zlength_map; rewrite Zlength_correct; 
         rewrite seq_length; try rep_omega).
  replace (Znth b lens, Znth b bins, b) with (Znth b (zip3 lens bins idxs)).
  replace BINS with (Zlength (zip3 lens bins idxs)).
  erewrite <- (iter_sepcon_split3 b _ mmlist'); auto.
  split.
  - omega.
  - rewrite Zlength_zip3; try rep_omega. 
  - rewrite Zlength_zip3; try rep_omega. 
  - rewrite Znth_zip3 by rep_omega. replace b with (Znth b idxs) at 6; auto.
    subst. rewrite Znth_map. unfold Znth. if_tac. omega.
    rewrite seq_nth. simpl. rep_omega. rep_omega.
    rewrite Zlength_correct. rewrite seq_length. rep_omega.
Qed.


Lemma mem_mgr_split: 
 forall gv:globals, forall b:Z, 0 <= b < BINS ->
   mem_mgr gv
 = 
  EX bins: list val, EX lens: list nat, EX idxs: list Z,
    !! (Zlength bins = BINS /\ Zlength lens = BINS /\ Zlength idxs = BINS 
        /\ idxs = map Z.of_nat (seq 0 (Z.to_nat BINS))) &&
  data_at Tsh (tarray (tptr tvoid) BINS) bins (gv _bin) * 
  iter_sepcon mmlist' (sublist 0 b (zip3 lens bins idxs)) * 
  mmlist (bin2sizeZ b) (Znth b lens) (Znth b bins) nullval * 
  iter_sepcon mmlist' (sublist (b+1) BINS (zip3 lens bins idxs)) *  
  TT. 
Proof. 
  intros. apply pred_ext.
  - (* LHS -> RHS *)
    unfold mem_mgr.
    Intros bins lens idxs. Exists bins lens idxs. entailer!.
    rewrite <- (mem_mgr_split' b); try assumption. 
    entailer!. reflexivity.
  - (* RHS -> LHS *)
    Intros bins lens idxs. 
    unfold mem_mgr. Exists bins lens idxs. 
    entailer!.
    set (idxs:=(map Z.of_nat (seq 0 (Z.to_nat BINS)))).
    replace (
        iter_sepcon mmlist' (sublist 0 b (zip3 lens bins idxs)) *
        mmlist (bin2sizeZ b) (Znth b lens) (Znth b bins) nullval *
        iter_sepcon mmlist' (sublist (b + 1) BINS (zip3 lens bins idxs)) )
      with (
          iter_sepcon mmlist' (sublist 0 b (zip3 lens bins idxs)) *
          iter_sepcon mmlist' (sublist (b + 1) BINS (zip3 lens bins idxs)) *
          mmlist (bin2sizeZ b) (Znth b lens) (Znth b bins) nullval )
      by (apply pred_ext; entailer!).  
    rewrite (mem_mgr_split' b); try assumption.
    cancel.  auto.
Qed.


(*+ splitting/joining memory blocks +*)

(* These results involve memory predicates that depend on compspecs *)

(* notes towards possibly subsuming lemmas:
- malloc_large uses malloc_large_chunk to split off size and waste parts.
- malloc_small uses to_malloc_token_and_block to change a bin chunk into token plus user chunk.
- free uses from_malloc_token_and_block to access the size; that also exposes nxt,
  which is helpful for free_small
- free free_large_chunk to reassemble block to give to munmap; this includes
  the nxt field (could simplify by not exposing that in the first place).  
- fill_bin uses memory_block_split_block to split off size, next, and remainder for a chunk, from a big block.
*)

Lemma memory_block_split_block:
(* Note: an equality but only used in this direction. *) 
  forall s m q, WORD <= s -> s+WORD <= m -> malloc_compatible (m - WORD) (offset_val WORD q) ->
   align_compatible (tarray tuint 1) q ->
   memory_block Tsh m q |-- 
   data_at_ Tsh (tarray tuint 1) q * (*size*)
   data_at_ Tsh (tptr tvoid) (offset_val WORD q) * (*nxt*)   
   memory_block Tsh (s - WORD) (offset_val (WORD+WORD) q) * (*rest of chunk*)
   memory_block Tsh (m-(s+WORD)) (offset_val (s+WORD) q). (*rest of large*)
Proof.
  intros s m q Hs Hm Hmcq Hacq.
  (* split antecedent memory block into right sized pieces *)
  replace m with (WORD + (m - WORD)) at 1 by omega. 
  rewrite (memory_block_split_offset _ q WORD (m - WORD)) by rep_omega.
  replace (m - WORD) with (WORD + (m - (WORD+WORD))) by omega.
  rewrite (memory_block_split_offset 
             _ (offset_val WORD q) WORD (m - (WORD+WORD))) by rep_omega.
  replace (offset_val WORD (offset_val WORD q)) with (offset_val (WORD+WORD) q) by normalize.
  replace (m - (WORD+WORD)) with ((s - WORD) + (m - (s+WORD))) by rep_omega.
  rewrite (memory_block_split_offset 
             _ (offset_val (WORD+WORD) q) (s - WORD) (m - (s+WORD))) by rep_omega.
  (* rewrite into data_at_ *)
  normalize.
  change WORD with (sizeof (tarray tuint 1)) at 1.
  change WORD with (sizeof (tptr tvoid)) at 1.
  replace (WORD + WORD + (s - WORD)) with (s + WORD) by omega.
  entailer!. 
  rewrite memory_block_data_at_.
  rewrite memory_block_data_at_.
  cancel.
  - (* field_compatible (offset_val WORD q) *)
    hnf. repeat split; auto.
    destruct q; try auto.
    eapply align_compatible_rec_by_value; try reflexivity. simpl in *.
    destruct Hmcq as [Halign Hbound].
    assert (H48: (4|natural_alignment)).
    { unfold natural_alignment; replace 8 with (2*4)%Z by omega. 
      apply Z.divide_factor_r; auto. }
    eapply Z.divide_trans. apply H48. auto.
  - (* field_compatible q *)
    hnf. repeat split; auto.
Qed.


Lemma free_large_chunk: 
  forall s p, WORD <= s <= Ptrofs.max_unsigned -> 
  data_at Tsh tuint (Vint (Int.repr s)) (offset_val (- WORD) p) * 
  data_at_ Tsh (tptr tvoid) p *                                    
  memory_block Tsh (s - WORD) (offset_val WORD p) *
  memory_block Tsh WA (offset_val (- (WA + WORD)) p)
  |-- memory_block Tsh (s + WA + WORD) (offset_val (- (WA + WORD)) p) .
Proof.
  intros.
  assert_PROP(field_compatible (tptr tvoid) [] p ) by entailer.
  assert_PROP(field_compatible tuint [] (offset_val (- WORD) p)) by entailer.
  assert(Hsiz: sizeof (tptr tvoid) = WORD) by auto.
  rewrite <- memory_block_data_at_; auto.
  match goal with | |- context[data_at ?sh ?t ?Vs ?op] => 
                    sep_apply (data_at_data_at_ sh t Vs op) end.
  rewrite <- memory_block_data_at_; auto.
  change (sizeof tuint) with WORD.
  rewrite Hsiz; clear Hsiz.
  do 2 rewrite <- sepcon_assoc.
  replace (
      memory_block Tsh WORD (offset_val (- WORD) p) * memory_block Tsh WORD p *
      memory_block Tsh (s - WORD) (offset_val WORD p) *
      memory_block Tsh WA (offset_val (- (WA + WORD)) p) 
    )with(
         memory_block Tsh WORD p *
         memory_block Tsh (s - WORD) (offset_val WORD p) *
         memory_block Tsh WORD (offset_val (- WORD) p) *
         memory_block Tsh WA (offset_val (- (WA + WORD)) p) 
       ) by (apply pred_ext; entailer!);
    rewrite <- memory_block_split_offset; try rep_omega.
  replace (WORD+(s-WORD)) with s by omega;
    replace p with (offset_val WORD (offset_val (- WORD) p)) at 1 by normalize;
    replace(
        memory_block Tsh s (offset_val WORD (offset_val (- WORD) p)) *
        memory_block Tsh WORD (offset_val (- WORD) p) 
      )with(
           memory_block Tsh WORD (offset_val (- WORD) p) *
           memory_block Tsh s (offset_val WORD (offset_val (- WORD) p))
         ) by (apply pred_ext; entailer!);
    rewrite <- (memory_block_split_offset _ (offset_val (- WORD) p)); try rep_omega.
  replace (offset_val (-WORD) p) 
    with (offset_val WA (offset_val (-(WA+WORD)) p)) by normalize;
    replace (
        memory_block Tsh (WORD + s) (offset_val WA (offset_val (- (WA + WORD)) p)) *
        memory_block Tsh WA (offset_val (- (WA + WORD)) p)
      )with( 
           memory_block Tsh WA (offset_val (- (WA + WORD)) p) *
           memory_block Tsh (WORD + s) (offset_val WA (offset_val (- (WA + WORD)) p)) 
         ) by (apply pred_ext; entailer!);
    rewrite <- memory_block_split_offset; try rep_omega.
  replace (WA+(WORD+s)) with (s+WA+WORD) by omega;
    entailer!.
Qed.


(* following only used L to R but this form enables simple rewrite *)
Lemma malloc_large_chunk: 
  forall n p, 0 <= n -> n + WA + WORD <= Ptrofs.max_unsigned -> 
         malloc_compatible (n + WA + WORD) p -> 
  memory_block Tsh (n + WA + WORD) p
  = 
  memory_block Tsh WA p *                      (* waste *)
  data_at_ Tsh tuint (offset_val WA p) *       (* size *)
  memory_block Tsh n (offset_val (WA+WORD) p). (* data *)
Proof. 
  intros n p H H0 H1. destruct p; try normalize.
  apply pred_ext.
  - (* L to R where (p is Vptr b i) *)
    rewrite data_at__memory_block.
    normalize.
    entailer!.
    -- (* field_compatible *)
      hnf. 
      assert (H4: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr WA))
               = Ptrofs.unsigned i + WA ). 
      { replace i with (Ptrofs.repr(Ptrofs.unsigned i)) at 1
          by (rewrite Ptrofs.repr_unsigned; reflexivity).
        rewrite ptrofs_add_repr.
        rewrite Ptrofs.unsigned_repr; try reflexivity.
        split.
        assert (0 <= Ptrofs.unsigned i) by apply Ptrofs.unsigned_range.
        rep_omega. unfold size_compatible' in *. rep_omega.
      }
      repeat split; auto.
      --- (* size *)
        simpl; simpl in H1.
        replace ( Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr WA)) )
          with ( Ptrofs.unsigned i + WA ). 
        replace (Ptrofs.unsigned i + (n + WA + WORD))
          with (n + Ptrofs.unsigned i + WA + 4)
          in H1 by rep_omega.
        assert (0 + Ptrofs.unsigned i + WA + 4 <= n + Ptrofs.unsigned i + WA + 4)
          by (do 3 apply Z.add_le_mono_r; auto).
        rep_omega. 
      --- (* align *)
        simpl.
        eapply align_compatible_rec_by_value; try reflexivity. simpl in *.
        rewrite H4.
        apply Z.divide_add_r.
        destruct H1 as [Hal ?]. 
        assert (H48: (4|natural_alignment)).
        { unfold natural_alignment; replace 8 with (2*4)%Z by omega. 
          apply Z.divide_factor_r; auto. }
        eapply Z.divide_trans. apply H48. auto.
        rewrite WA_eq. 
        apply Z.divide_refl.
    -- 
      replace (sizeof tuint) with WORD by normalize. 
      change (sizeof tuint) with WORD.
      replace (n + WORD + WORD) with (WORD + (n + WORD)) by omega.
      erewrite (memory_block_split_offset _ _ WORD (n+WORD)); try rep_omega.
      replace (n+WORD) with (WORD+n) by omega.
      change (sizeof tuint) with WORD.
      erewrite memory_block_split_offset; try rep_omega. 
      entailer!; rep_omega.
      
  - (* R to L *)
    rewrite data_at__memory_block; normalize.
    erewrite <- memory_block_split_offset; try rep_omega.
    replace (sizeof tuint) with WORD by normalize.
    erewrite <- memory_block_split_offset; try rep_omega.
    replace (WORD+WORD+n) with (n+WORD+WORD) by omega.
    cancel; rep_omega.
    change (sizeof tuint) with WORD; rep_omega.
Qed.

(* Note: In the antecedent in the following entailment, the conjunct
   data_at Tsh (tptr tvoid) _ p
   ensures that p is aligned for its type, but noted in comment in the 
   proof, that alignment is modulo 4 rather than natural_alignment (8). 
*)
Lemma to_malloc_token_and_block:
forall n p q s t, n = sizeof t -> 0 <= n <= bin2sizeZ(BINS-1) -> s = bin2sizeZ(size2binZ(n)) -> 
     malloc_compatible s p -> 
  (  data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p) *
     ( data_at Tsh (tptr tvoid) q p *   
     memory_block Tsh (s - WORD) (offset_val WORD p) )
|--  malloc_token Ews t p * memory_block Ews n p).
Proof.
  intros n p q s t Ht Hn Hs Hmc.
  unfold malloc_token.
  Exists s.
  unfold malloc_tok.
  if_tac.
  - (* small chunk *)
    entailer!. 
    split.
    -- pose proof (claim1 (sizeof t) (proj2 Hn)). rep_omega.
    -- match goal with | HA: field_compatible _ _ _ |- _ => 
                         unfold field_compatible in H2;
                           destruct H2 as [? [? [? [? ?]]]] end.
       destruct p; auto; try (apply claim1; rep_omega).
    -- set (s:=(bin2sizeZ(size2binZ(sizeof t)))).
       sep_apply (data_at_memory_block Tsh (tptr tvoid) q p).
       simpl.
       rewrite <- memory_block_split_offset; try rep_omega.
       --- 
       replace (WORD+(s-WORD)) with s by omega.
       rewrite sepcon_assoc.
       replace (
           memory_block Ews (s - sizeof t) (offset_val (sizeof t) p) *
           memory_block Ews (sizeof t) p)
         with (memory_block Ews s p).
       + rewrite (memory_block_share_join (comp Ews) Ews Tsh). cancel.
         unfold comp; rewrite comp_Ews.
         apply sepalg.join_comm.
         apply join_Ews.
       + rewrite sepcon_comm.
         rewrite <- memory_block_split_offset; try rep_omega.
         replace (sizeof t + (s - sizeof t)) with s by omega. reflexivity.
         destruct Hn; auto.
         set (n:=sizeof t) in *. subst s.
         assert (n <= bin2sizeZ (size2binZ n)) by (apply claim1; rep_omega).
         rep_omega.
       --- 
       set (n:=sizeof t) in *. subst s.
       pose proof (size2bin_range n Hn) as Hn'.
       pose proof (bin2size_range (size2binZ (sizeof t)) Hn').
       rep_omega.
  - (* large chunk - contradicts antecedents *)
    exfalso.
    assert (size2binZ n < BINS) by (apply size2bin_range; omega).
    assert (size2binZ n <= BINS - 1 ) by omega.
    rewrite Hs in H.
    assert (bin2sizeZ (size2binZ n) <= bin2sizeZ (BINS-1)) by
        (apply bin2size_range; apply size2bin_range; rep_omega).
    rep_omega.
Qed.

(* TODO tactic for repeated parts of following and prev proofs *)

Lemma from_malloc_token'_and_block:  
forall n p, 0 <= n <= Ptrofs.max_unsigned - WORD ->  
    (malloc_token' Ews n p * memory_block Ews n p)
  |--  (EX s:Z,
      !! ( n <= s /\ s + WA + WORD <= Ptrofs.max_unsigned /\ 
           malloc_compatible s p /\ 
           (s <= bin2sizeZ(BINS-1) -> s = bin2sizeZ(size2binZ(n))) /\ 
           (s > bin2sizeZ(BINS-1) -> s = n)) && 
      data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p) * (* size *)
      data_at_ Tsh (tptr tvoid) p *                                         (* nxt *)
      memory_block Tsh (s - WORD) (offset_val WORD p) *                     (* data *)
      (if zle s (bin2sizeZ(BINS-1)) then emp                                (* waste *)
       else memory_block Tsh WA (offset_val (-(WA+WORD)) p))).
(* Note that part labelled data can itself be factored into the user-visible
part of size n - WORD and, for small chunks, waste of size s - n *)
Proof.
  intros.
  unfold malloc_token'.
  Intros s; Exists s.
  unfold malloc_tok.
  entailer!.
  pose proof (zle WORD n) as Hnw.
  destruct Hnw as [H_ok | Hn_tiny].
  - (* WORD <= n so we can get the pointer from the n block *)
    replace n with (WORD + (n - WORD)) at 3 by omega.
    rewrite memory_block_split_offset; try rep_omega.
    change WORD with (sizeof (tptr tvoid)) at 1.
(* PENDING until verif_malloc and verif_malloc_small 
    rewrite memory_block_data_at_.
    + replace (offset_val n p) with (offset_val (n-WORD) (offset_val WORD p)).
      2: (normalize; replace (WORD+(n-WORD)) with n by omega; reflexivity).
      replace ( (* rearrangement *)
          memory_block Ews (s - n) (offset_val (n - WORD) (offset_val WORD p)) *
          (data_at_ Ews (tptr tvoid) p * memory_block Ews (n - WORD) (offset_val WORD p))
        )with(
             memory_block Ews (n - WORD) (offset_val WORD p) *
             memory_block Ews (s - n) (offset_val (n - WORD) (offset_val WORD p)) *
             data_at_ Ews (tptr tvoid) p 
           ) by (apply pred_ext; entailer!).
      rewrite <- memory_block_split_offset; try rep_omega.
      replace (n-WORD+(s-n)) with (s-WORD) by omega.
      entailer!.
    + (* field_compatible *)
      hnf.  repeat split; auto.
      -- (* size_compatible *)
        destruct p; try auto.
        unfold size_compatible.
        match goal with | HA: malloc_compatible _ _ |- _ => 
                          unfold malloc_compatible in HA; destruct HA end.
        change (sizeof (tptr tvoid)) with WORD; rep_omega.
      -- (* align_compatible *)
        destruct p; try auto.
        unfold align_compatible.
        eapply align_compatible_rec_by_value; try reflexivity.
        simpl.
        match goal with | HA: malloc_compatible _ _ |- _ => 
                          unfold malloc_compatible in HA; destruct HA end.
        assert (H48: (4|natural_alignment)).
        { unfold natural_alignment; replace 8 with (2*4)%Z by omega. 
          apply Z.divide_factor_r; auto. }
        eapply Z.divide_trans. apply H48. auto.
  - (* WORD > n so part of the pointer is in the token block *)
    replace 
      (memory_block Ews (s - n) (offset_val n p) * memory_block Ews n p)
      with 
        (memory_block Ews n p * memory_block Ews (s - n) (offset_val n p))
      by (apply pred_ext; entailer!).
    rewrite <- memory_block_split_offset; try rep_omega.
    replace (n+(s-n)) with s by omega.
    replace s with (WORD + (s-WORD)) at 1 by omega.
    rewrite memory_block_split_offset; try rep_omega.
    cancel.
    change WORD with (sizeof (tptr tvoid)).
    rewrite memory_block_data_at_.
    +  entailer!.
    + (* field_compatible *)
      hnf. repeat split; auto.
      -- (* size_compatible *)
        destruct p; try auto.
        unfold size_compatible.
        match goal with | HA: malloc_compatible _ _ |- _ => 
                          unfold malloc_compatible in HA; destruct HA end.
        change (sizeof (tptr tvoid)) with WORD.
        assert (WORD <= s); try rep_omega.
        {  destruct H0. 
           pose proof (zle s (bin2sizeZ (BINS-1))) as Hsmall.
           destruct Hsmall as [Hsmall | Hsbig]; try rep_omega.
           (* case s <= bin2sizeZ(BINS-1) *)
           match goal with | HA: s<=bin2sizeZ(BINS-1) -> _ |- _ => apply HA in Hsmall end. 
           pose proof (bin2size_range (size2binZ n)) as Hrng.
           subst.  pose proof (size2bin_range n).
           assert (Hn: 0 <= n <= bin2sizeZ (BINS - 1)) by rep_omega. 
           match goal with | HA: 0<=n<=bin2sizeZ(BINS-1) -> _ |- _ => apply HA in Hn end. 
           apply Hrng in Hn. rep_omega.
        }
      -- (* align_compatible *)
        destruct p; try auto.
        unfold align_compatible.
        eapply align_compatible_rec_by_value; try reflexivity.
        simpl.
        match goal with | HA: malloc_compatible _ _ |- _ => 
                          unfold malloc_compatible in HA; destruct HA end.
        assert (H48: (4|natural_alignment)).
        { unfold natural_alignment; replace 8 with (2*4)%Z by omega. 
          apply Z.divide_factor_r; auto. }
        eapply Z.divide_trans. apply H48. auto.
    + assert (WORD <= s); try rep_omega.
      {  destruct H0. 
         pose proof (zle s (bin2sizeZ (BINS-1))) as Hsmall.
         destruct Hsmall as [Hsmall | Hsbig]; try rep_omega.
         (* case s <= bin2sizeZ(BINS-1) *)
         match goal with | HA: s<=bin2sizeZ(BINS-1) -> _ |- _ => apply HA in Hsmall end. 
         pose proof (bin2size_range (size2binZ n)) as Hrng.
         subst.  pose proof (size2bin_range n).
         assert (Hn: 0 <= n <= bin2sizeZ (BINS - 1)) by rep_omega. 
         match goal with | HA: 0<=n<=bin2sizeZ(BINS-1) -> _ |- _ => apply HA in Hn end. 
         apply Hrng in Hn. rep_omega.
      }
Qed.
*)
admit.
Admitted.

Lemma from_malloc_token_and_block:  
forall t n p,
  n = sizeof t -> 0 <= n <= Ptrofs.max_unsigned - WORD -> 
    (malloc_token Ews t p * data_at_ Ews t p)
  |--  (EX s:Z,
      !! ( n <= s /\ s + WA + WORD <= Ptrofs.max_unsigned /\ 
           malloc_compatible s p /\ 
           (s <= bin2sizeZ(BINS-1) -> s = bin2sizeZ(size2binZ(n))) /\ 
           (s > bin2sizeZ(BINS-1) -> s = n)) && 
      data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p) * (* size *)
      data_at_ Tsh (tptr tvoid) p *                                         (* nxt *)
      memory_block Tsh (s - WORD) (offset_val WORD p) *                     (* data *)
      (if zle s (bin2sizeZ(BINS-1)) then emp                                (* waste *)
       else memory_block Tsh WA (offset_val (-(WA+WORD)) p))).
Proof.
  intros. rewrite data_at__memory_block. normalize.
  unfold malloc_token. rewrite <- H.
  replace   (EX s : Z, malloc_tok Ews n s p) 
    with (malloc_token' Ews n p) by normalize.
  sep_apply (from_malloc_token'_and_block n p H0).
  Intro s. Exists s. entailer!.
Qed.


(*+ code specs *)

(* Similar to current specs in floyd/library, with mem_mgr added and size bound 
revised to account for the header of size WORD and its associated alignment.
Also free allows null, as per Posix standard.
*)

(* public interface *)

Definition malloc_spec {cs: compspecs } := 
   DECLARE _malloc
   WITH t:type, gv:globals
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

Definition free_spec {cs:compspecs} := 
   DECLARE _free
   WITH t:_, p:_, gv:globals
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

(* other functions *)

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
   WITH t:type, gv:globals
   PRE [ _nbytes OF tuint ]
       PROP (0 <= sizeof t <= bin2sizeZ(BINS-1) /\
             complete_legal_cosu_type t = true /\
             natural_aligned natural_alignment t = true)
       LOCAL (temp _nbytes (Vptrofs (Ptrofs.repr (sizeof t))); gvars gv)
       SEP ( mem_mgr gv )
   POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mem_mgr gv; 
            if eq_dec p nullval then emp
            else (malloc_token Ews t p * data_at_ Ews t p)).

(* Note that this is a static function so there's no need to hide
globals in its spec; but that seems to be needed, given the definition 
of mem_mgr.*)
Definition malloc_large_spec :=
   DECLARE _malloc_large
   WITH t:type, gv:globals
   PRE [ _nbytes OF tuint ]
       PROP (bin2sizeZ(BINS-1) < sizeof t <= Ptrofs.max_unsigned - (WA+WORD) /\
             complete_legal_cosu_type t = true /\
             natural_aligned natural_alignment t = true)
       LOCAL (temp _nbytes (Vptrofs (Ptrofs.repr (sizeof t))); gvars gv)
       SEP ( mem_mgr gv )
   POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mem_mgr gv; 
            if eq_dec p nullval then emp
            else (malloc_token Ews t p * data_at_ Ews t p)).

(* s is the stored chunk size and n is the original request amount. *)
Definition free_small_spec :=
   DECLARE _free_small
   WITH p:_, s:_, n:_, gv:globals
   PRE [ _p OF tptr tvoid, _s OF tuint ]
       PROP (0 <= n <= bin2sizeZ(BINS-1) /\ s = bin2sizeZ(size2binZ(n)) /\ 
             malloc_compatible s p)
       LOCAL (temp _p p; temp _s (Vptrofs (Ptrofs.repr s)); gvars gv)
       SEP ( data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p); 
            data_at_ Tsh (tptr tvoid) p;
            memory_block Tsh (s - WORD) (offset_val WORD p);
            mem_mgr gv)
   POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr gv).




Definition Gprog : funspecs := 
 ltac:(with_library prog [ 
   mmap0_spec; munmap_spec; bin2size_spec; size2bin_spec; fill_bin_spec;
   malloc_small_spec; malloc_large_spec; free_small_spec; malloc_spec; 
   free_spec]).





