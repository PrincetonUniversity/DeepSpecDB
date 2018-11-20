(*+ specs and background for memmgr *)

(* The code verifications are in separate files, e.g., 
   verif_malloc_free.v proves the two main function bodies.
   Although some lemmas are only used to verify a single function,
   they're collected here to facilitate possible reorganization later. *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.

Require Import Lia. (* for lia tactic (nonlinear integer arithmetic) *) 

Ltac start_function_hint ::= idtac. (* no hint reminder *)

(*+ miscellany *)

(* from VFA *)
Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof. intros x y. apply iff_reflect. symmetry. apply Z.eqb_eq. Qed.
Hint Resolve ReflOmegaCore.ZOmega.IP.blt_reflect 
  ReflOmegaCore.ZOmega.IP.beq_reflect beq_reflect : bdestruct.
Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop); assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

(* A bit of infrastructure for brute force proof of claim3. 
   TODO consider using Zseq in place of seq in mem_mgr. 
*)
Definition Zseq n := 
  if n <? 0 then [] else map Z.of_nat (seq 0 (Z.to_nat n)).

Lemma in_Zseq: forall len n : Z, len >= 0 -> ( In n (Zseq len) <-> (0 <= n < len) ). 
Proof.
  intros. unfold Zseq.  bdestruct (len <? 0); try omega. clear H0.
  rewrite in_map_iff. split.
  - intros. destruct H0. destruct H0. 
    rewrite in_seq in H1.
    rewrite <- H0. split. rep_omega. destruct H1. simpl in H2.
    apply inj_lt in H2. rewrite Z2Nat.id in H2 by omega. auto.
  - intro. exists (Z.to_nat n).
    split; try rep_omega.
    rewrite in_seq.
    assert (0 <= Z.to_nat n)%nat by (destruct H0; omega). 
    simpl. split; try omega. rep_omega.
Qed.

Lemma forall_Forall_range: 
     forall (P : Z -> Prop) (n : Z), 0 <= n ->
       ( (forall x, 0 <= x < n -> P x) <-> Forall P (Zseq n) ).
Proof.
  intros.
  assert (Hi:  
          (forall x : Z, 0 <= x < n -> P x) <->  (forall x : Z, In x (Zseq n) -> P x)).
  { split. - intros; apply H0; rewrite <- in_Zseq; try omega; auto.
    - intros; apply H0; rewrite in_Zseq; try omega. }
  rewrite Hi. rewrite Forall_forall. reflexivity.
Qed.

(* NOTE: background for upd_Znth_same_val, belongs in a library *)
Lemma list_extensional {A}{d: Inhabitant A}: 
  forall (xs ys: list A),
  Zlength xs = Zlength ys ->
  (forall i, 0 <= i < Zlength xs -> Znth i xs = Znth i ys) -> xs = ys.
Proof.
  intros xs.
  induction xs. 
  - intros [|w ws] H Hi. reflexivity.
    rewrite Zlength_nil in H. rewrite Zlength_cons in H. 
    assert (0 <= Zlength ws) by apply Zlength_nonneg. omega.
  - intros [|w ws] H Hi. 
    rewrite Zlength_nil in H; rewrite Zlength_cons in H. 
    assert (H0: 0 <= Zlength xs) by apply Zlength_nonneg; omega.
    specialize (IHxs ws). 
    assert (H1: Zlength xs = Zlength ws) by 
        ( do 2 rewrite Zlength_cons in H; apply Z.succ_inj in H; auto).
    assert (H2: 0<=0<Zlength (a::xs)) by 
        (split; try omega; rewrite Zlength_cons; rep_omega).
    assert (H3: Znth 0 (a :: xs) = Znth 0 (w :: ws)) by (apply Hi; auto).
    apply IHxs in H1.
    + subst. apply Hi in H2. do 2 rewrite Znth_0_cons in H2. subst. reflexivity.
    + apply Hi in H2. do 2 rewrite Znth_0_cons in H2.  subst. 
      intros. specialize (Hi (i+1)).   do 2 rewrite Znth_pos_cons in Hi; try omega.
      replace (i+1-1) with i in Hi by omega.
      apply Hi. split; try omega. rewrite Zlength_cons; rep_omega.
Qed.

Lemma upd_Znth_same_val {A} {d: Inhabitant A}:
  forall n (xs: list A), 0 <= n < Zlength xs ->
   (upd_Znth n xs (Znth n xs)) = xs.
Proof.
  intros.  symmetry.  eapply list_extensional.
  rewrite upd_Znth_Zlength; auto.
  intros.  bdestruct (Z.eqb n i).
  - subst. rewrite upd_Znth_same; auto. 
  - rewrite upd_Znth_diff; auto.
Qed.

Lemma upd_Znth_twice {A} {d: Inhabitant A}:
forall n x y (xs:list A),
   0 <= n < Zlength xs ->
   (upd_Znth n (upd_Znth n xs x) y) = (upd_Znth n xs y).
Proof.
  intros n x y xs H. symmetry.
  eapply list_extensional.
  repeat (rewrite upd_Znth_Zlength; auto).
  intros. bdestruct (n =? i).
  - subst. repeat rewrite upd_Znth_same; auto. 
    rewrite upd_Znth_Zlength in *; auto.
  - assert (0 <= i < Zlength xs) by (rewrite upd_Znth_Zlength in H0; auto). 
    repeat rewrite upd_Znth_diff; auto;
    rewrite upd_Znth_Zlength in *; auto.
Qed. 


(* NOTE: maybe some of the next lemmas belong in floyd *)
Lemma malloc_compatible_prefix:
  forall n s p, 0 <= n <= s -> 
  malloc_compatible s p -> malloc_compatible n p.
Proof.
  intros n s p H H0; unfold malloc_compatible in *; destruct p; try auto.
  destruct H0. split; try assumption; rep_omega.
Qed.

Lemma malloc_compatible_offset:
  forall n m p, 0 <= n -> 0 <= m ->
  malloc_compatible (n+m) p -> (natural_alignment | m) -> 
  malloc_compatible n (offset_val m p).
Proof.
  intros n m p Hn Hm Hp Ha. unfold malloc_compatible in *.
  destruct p; try auto. destruct Hp as [Hi Hinm]. simpl.  split.
- replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr m)))
     with (m + (Ptrofs.unsigned i)).
  apply Z.divide_add_r; auto.
  rewrite Ptrofs.add_unsigned;
  rewrite Ptrofs.unsigned_repr; rewrite Ptrofs.unsigned_repr;
     try omega; try split; try rep_omega. 
- replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr m)))
     with (m + (Ptrofs.unsigned i)); try rep_omega. 
  rewrite Ptrofs.add_unsigned;
  rewrite Ptrofs.unsigned_repr; rewrite Ptrofs.unsigned_repr;
     try omega; try split; try rep_omega. 
Qed. 

(* variations on VST's memory_block_split *)

Lemma memory_block_split_repr:
  forall (sh : share) (b : block) (ofs : ptrofs) (n m : Z), 0 <= n -> 0 <= m ->
       n + m <= n + m + (Ptrofs.unsigned ofs) < Ptrofs.modulus -> 
       memory_block sh (n + m) (Vptr b ofs) =
       memory_block sh n (Vptr b ofs) *
       memory_block sh m (Vptr b (Ptrofs.add ofs (Ptrofs.repr n))).
Proof.
  intros sh b ofs n m Hn Hm Hnm.
  assert (Hofs: ofs = (Ptrofs.repr (Ptrofs.unsigned ofs)))
    by (rewrite Ptrofs.repr_unsigned; auto). 
  rewrite Hofs.
  normalize.
  erewrite memory_block_split; try assumption.
  reflexivity.
Qed.

Lemma memory_block_split_offset:
  forall (sh : share) (p : val) (n m : Z), 0 <= n -> 0 <= m ->
       memory_block sh (n + m) p =
       memory_block sh n p *
       memory_block sh m (offset_val n p).
Proof.
  intros sh p n m Hn Hm.
  apply pred_ext. (* to enable use of entailer - at cost of duplicate proof *)
  - (* LHS |-- RHS *)
    destruct p; try entailer!.
    rewrite <- offset_val_unsigned_repr.
    simpl.
    rewrite memory_block_split_repr; try assumption. 
    + entailer!. 
      rewrite Ptrofs.unsigned_repr. cancel.
      unfold size_compatible' in *; rep_omega. 
    + unfold size_compatible' in *; rep_omega.
  - (* RHS |-- LHS 
       TODO almost same proof, followed by clumsy finish *)
    destruct p; try entailer!. 
    rewrite <- offset_val_unsigned_repr.
    simpl.  rewrite memory_block_split_repr; try assumption. 
    entailer!. rewrite Ptrofs.unsigned_repr. cancel.
    unfold size_compatible' in *. rep_omega. 
    unfold size_compatible' in *.
    split. rep_omega. 
    simpl in *.
    rewrite Ptrofs.modulus_eq32; try unfold Archi.ptr64; auto.
    replace (n+m+Ptrofs.unsigned i) with ((n + Ptrofs.unsigned i)+m) by omega.
    assert (Hni: 
              n + Ptrofs.unsigned i = (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr n)))).
    { rewrite Ptrofs.add_unsigned. rewrite Ptrofs.unsigned_repr; try rep_omega.
      rewrite Ptrofs.unsigned_repr; try rep_omega. 
      split; try rep_omega. rewrite Ptrofs.unsigned_repr; rep_omega. 
    }
    rewrite Hni; rep_omega.
Qed.


(*+ the program *)

Require Import malloc.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Local Open Scope Z.
Local Open Scope logic.  

Definition WORD: Z := 4.  (* sizeof(size_t) is 4 for 32bit Clight *)
Definition ALIGN: Z := 2.
Definition BINS: Z := 8. 
Definition BIGBLOCK: Z := ((Z.pow 2 17) * WORD).
Definition WA: Z := (WORD*ALIGN) - WORD. (* WASTE at start of block *)

(* Note re CompCert 3: I'm currently using tuint for what in the code
is size_t.  That works for 32bit mode.  To generalize the proof
to 64bit as well, it may work to replace tuint by t_size_t defined like 
t_size_t := if Archi.ptr64 then tulong else tuint
*)

(* Note about clightgen:
Compiling malloc.c triggers a warning from a header file:
/usr/include/sys/cdefs.h:81:2: warning: "Unsupported compiler detected"
This is ok.
*)

Lemma WORD_ALIGN_aligned:
  (natural_alignment | WORD * ALIGN)%Z.
Proof. unfold natural_alignment, WORD, ALIGN; simpl. apply Z.divide_refl. Qed.


(* The following hints empower rep_omega and lessen the need for 
   manually unfolding the constant definitions. *)

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

(*+ bin/size conversions and their properties *)

Definition bin2sizeZ := fun b: Z => (((b+1)*ALIGN - 1) * WORD)%Z. 

Definition size2binZ : Z -> Z := fun s => 
   if (bin2sizeZ(BINS-1)) <? s 
   then -1 
   else (s+(WORD * (ALIGN-1))-1) / (WORD * ALIGN).

Lemma bin2size_range: 
  forall b, 0 <= b < BINS -> 
    WORD <= bin2sizeZ b <= bin2sizeZ(BINS-1). 
Proof. intros. unfold bin2sizeZ in *. split; simpl in *; try rep_omega. Qed.

Lemma  bin2sizeBINS_eq: bin2sizeZ(BINS-1) = 60.
Proof. reflexivity. Qed.
Hint Rewrite bin2sizeBINS_eq: rep_omega.

Lemma bin2size_align:
  forall b, 0 <= b < BINS -> (natural_alignment | bin2sizeZ b + WORD).
Proof. (* by counting in unary *)
  apply forall_Forall_range; try rep_omega; rewrite BINS_eq; rewrite WORD_eq.
  unfold natural_alignment.
  cbn.
  repeat constructor.
  Ltac tac1 n := 
    unfold bin2sizeZ; rewrite ALIGN_eq; rewrite WORD_eq; simpl;
    match goal with | |- (8|?e) => 
        set (E:=e); replace E with (8 * n)%Z by omega; apply Z.divide_factor_l
    end. 
  (* TODO express generically, for 1 up to BINS *)
  tac1 1. tac1 2. tac1 3. tac1 4. tac1 5. tac1 6. tac1 7. tac1 8.
Qed.


Lemma size2bin_range: 
  forall s, 0 <= s <= bin2sizeZ(BINS-1) -> 0 <= size2binZ s < BINS.
Proof. 
  intros. unfold size2binZ. 
  bdestruct (bin2sizeZ (BINS - 1) <? s); try omega.
  rewrite bin2sizeBINS_eq in *.
  rewrite WORD_eq. rewrite ALIGN_eq. rewrite BINS_eq. simpl. 
  replace (s + 4 - 1) with (s + 3) by omega.
  split.
  - apply Z.div_pos; rep_omega.
  - apply Z.div_lt_upper_bound; rep_omega.
Qed.

Fact small_chunks_nonempty: bin2sizeZ(size2binZ(0)) > 0.
Proof. reflexivity. Qed.

Lemma claim1: forall s, 
  s <= bin2sizeZ(BINS-1) -> s <= bin2sizeZ(size2binZ s).
Proof. 
  intros s H. 
  unfold bin2sizeZ, size2binZ in *. 
  assert (H1: bin2sizeZ (BINS-1) = 60) by normalize; rewrite H1. 
  bdestruct (60 <? s); try rep_omega.
  rewrite WORD_eq in *; rewrite ALIGN_eq in *; rewrite BINS_eq in *.
  simpl in *; clear H0 H1. 
  replace ((((s + 4 - 1) / 8 + 1) * 2 - 1) * 4)%Z
     with ((s + 4 - 1) / 8 * 8 + 4)%Z by omega.
  replace (s + 4 - 1)%Z with (s + 3) by omega.
  assert (Zmod_eq': forall a b, b > 0 -> (a / b * b)%Z = a - a mod b) 
     by (intros; rewrite Zmod_eq; omega);
  rewrite Zmod_eq' by omega; clear Zmod_eq'.
  replace (s + 3 - (s + 3) mod 8 + 4)%Z  with (s + 7 - (s + 3) mod 8)%Z by omega.
  assert ( 0 <= (s+3) mod 8 < 8 ) by (apply Z_mod_lt; omega); omega.
Qed.

Lemma claim2: forall s, 
  0 <= s <= bin2sizeZ(BINS-1) -> 0 <= size2binZ s < BINS.
Proof. 
  intros; unfold bin2sizeZ in *; unfold size2binZ.
  rewrite WORD_eq in *;  rewrite ALIGN_eq in *; 
  rewrite bin2sizeBINS_eq; rewrite BINS_eq in *.
  change (((8 - 1 + 1) * 2 - 1) * 4)%Z with 60 in *.
  bdestruct (60 <? s); try rep_omega.
  simpl; split.
  apply Z.div_pos; replace (s+4-1) with (s+3) by omega.
  apply Z.add_nonneg_nonneg; try omega. omega.
  replace (s+4-1) with (s+3) by omega.
  apply Z.div_lt_upper_bound. omega. simpl.
  change 64 with (61 + 3). apply Zplus_lt_compat_r. omega.
Qed.

Lemma claim3: forall s, 0 <= s <= bin2sizeZ(BINS-1) 
    -> size2binZ(bin2sizeZ(size2binZ(s))) = size2binZ(s).
Proof. 
  intros. 
  pose proof ((size2bin_range s) H). 
  pose proof ((bin2size_range (size2binZ(s))) H0).
  unfold size2binZ.
  bdestruct (bin2sizeZ (BINS - 1) <? s).
  bdestruct (bin2sizeZ (BINS - 1) <? bin2sizeZ (-1)); try omega.
  bdestruct (bin2sizeZ (BINS - 1) <?
             bin2sizeZ ((s + WORD * (ALIGN - 1) - 1) / (WORD * ALIGN))).
  - rewrite WORD_eq in *;  rewrite ALIGN_eq in *;  simpl.
    replace (s + 4 - 1) with (s + 3) by omega.
    exfalso; clear H2.
    replace  ((s + 4 * (2 - 1) - 1) / (4 * 2)) with (size2binZ s) in H3; try omega. 
    unfold size2binZ; bdestruct (bin2sizeZ (BINS - 1) <? s); try omega.
    rewrite WORD_eq in *; rewrite ALIGN_eq in *; omega.
  - unfold bin2sizeZ; rewrite WORD_eq in *;  rewrite ALIGN_eq in *; simpl.
    (* gave up fumbling with algebra; 
       finish by evaluation, of enumerating the values of s in a list *)
    assert (Htest: forall s,  0 <= s < bin2sizeZ(BINS-1) + 1 -> 
      ((((s + 4 - 1) / 8 + 1) * 2 - 1) * 4 + 4 - 1) / 8  = (s + 4 - 1) / 8).
    { set (Q:=fun t => 
                ((((t + 4 - 1) / 8 + 1) * 2 - 1) * 4 + 4 - 1) / 8  = (t + 4 - 1) / 8).
      assert (Hs: 0 <= s < bin2sizeZ(BINS - 1) + 1) by omega.
      assert (Hb: 0 <= bin2sizeZ(BINS - 1) + 1) by omega.
      pose proof (forall_Forall_range Q ((bin2sizeZ (BINS - 1))+1) Hb). 
      clear H1 H2 H3 Hb; unfold Q in H4; rewrite H4.
      rewrite bin2sizeBINS_eq. simpl. cbn.
      repeat constructor.
    }
    apply (Htest s); omega.
Qed.

(* BIGBLOCK needs to be big enough for at least one chunk of the 
largest size, because fill_bin unconditionally initializes the last chunk. *)
Lemma BIGBLOCK_enough: (* and not too big *)
  forall s, 0 <= s <= bin2sizeZ(BINS-1) ->  
            0 < (BIGBLOCK - WA) / (s + WORD) < Int.max_signed.
Proof.
  intros; rewrite bin2sizeBINS_eq in *; split. 
  apply Z.div_str_pos; rep_omega.
  rewrite Z_div_lt; rep_omega.
Qed.

Lemma BIGBLOCK_enough_j: 
  forall s j, 0 <= s -> j < (BIGBLOCK-WA) / (s+WORD) ->
              (s+WORD) <= (BIGBLOCK-WA) - (j * (s+WORD)).
Proof.
  assert (Hlem: forall sw j bw, 0 < sw -> 0 < bw -> j < bw / sw -> sw <= bw - j*sw).
  { intros. assert (j+1 <= bw/sw) by omega.
    assert (bw/sw*sw <= bw) by (rewrite Z.mul_comm; apply Z.mul_div_le; rep_omega).
    assert ((j+1)*sw <= bw/sw*sw) by (apply Zmult_le_compat_r; rep_omega).
    assert ((j+1)*sw <= bw) by rep_omega.
    replace ((j+1)*sw)%Z with (sw + j*sw)%Z in *.
    rep_omega. replace (j+1) with (Z.succ j) by omega; rewrite Z.mul_succ_l; omega.
  }
  intros; apply Hlem; try rep_omega.
Qed.


(*+ function specs and data structures  *)


(* Specifications for posix mmap0 and munmap as used by this memory manager.
   Using wrapper mmap0 which returns 0 on failure, because mmap returns -1,
   and pointer comparisons with non-zero literals violate the C standard.
   Aside from that, mmap0's spec is the same as mmap's.

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



(*+ malloc token *)

(* Accounts for both the size field and alignment padding. 

Similar to current definition in floyd/library.v but using Tsh

n: sizeof t where t is the type requested
p: the address returned by malloc 
  
Unfolding the definition reveals the stored size value s, which 
is not the request n but rather the size of the chunk (not 
counting the size field itself).

The constraint s + WA + WORD <= Ptrofs.max_unsigned caters for 
padding and is used e.g. in proof of body_free.
(The conjunct (malloc_compatible s p) implies (s < Ptrofs.modulus) but 
that's not enough.)

About waste: for small chunks, there is waste at the beginning of each big 
block used by fill_bin, and the module invariant mem_mgr accounts for it. 
In addition, there is waste of size s - n at the end of each small chunk 
(as n gets rounded up to the nearest size2binZ), and each large chunk has 
waste at the start, for alignment; these are accounted for by malloc_token.

About the share: The idea is that one might want to be able to split tokens,
though there doesn't seem to be a compelling case for that.  To do so, the API
in floyd/library.v would need to include a splitting lemma, and given that 
malloc_token (here and in envisioned alternate implementations) involves memory
blocks with differing permissions, a splitting lemma is nonobvious.  For now,
we keep parameter sh but do not provide a splitting lemma. 

PENDING: n > 0 currently required, to ensure valid_pointer p.
An alternate way to achieve that would be for the token to have partial share
of the user data, and to exploit that bin2sizeZ(size2binZ(0)) > 0.
*)

Definition malloc_tok (sh: share) (n: Z) (s: Z) (p: val): mpred := 
   !! (0 < n <= s /\ s + WA + WORD <= Ptrofs.max_unsigned /\ 
       (s <= bin2sizeZ(BINS-1) -> s = bin2sizeZ(size2binZ n)) /\
       (s > bin2sizeZ(BINS-1) -> s = n) /\
       malloc_compatible s p ) &&
    data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p) (* stored size *)
  * memory_block Tsh (s - n) (offset_val n p)                 (* waste at end of small *)
  * (if zle s (bin2sizeZ(BINS-1))  
    then emp
    else memory_block Tsh WA (offset_val (-(WA+WORD)) p)).  (* waste at start of large *)

Definition malloc_token (sh: share) (t: type) (p: val): mpred := 
   EX s:Z, malloc_tok sh (sizeof t) s p.

Definition malloc_token' (sh: share) (n: Z) (p: val): mpred := 
   EX s:Z, malloc_tok sh n s p.


(* PENDING
Lemma malloc_token_valid_pointer:
  forall sh n p, malloc_token sh n p |-- valid_pointer p.
*)

Lemma malloc_token_valid_pointer_size:
  forall sh t p, malloc_token sh t p |-- valid_pointer (offset_val (- WORD) p).
Proof.
  intros; unfold malloc_token, malloc_tok; entailer!.
  sep_apply (data_at_valid_ptr Tsh tuint (Vint (Int.repr s)) (offset_val(-WORD) p)).
  normalize. simpl; omega. entailer!.
Qed.

Lemma malloc_token_local_facts:
  forall sh t p, malloc_token sh t p 
  |-- !!( malloc_compatible (sizeof t) p /\ 
          0 <= (sizeof t) <= Ptrofs.max_unsigned - (WA+WORD)).
Proof.
  intros; unfold malloc_token; Intro s; unfold malloc_tok; entailer!.
  apply (malloc_compatible_prefix (sizeof t) s p); try omega; try assumption.
Qed.

Hint Resolve malloc_token_valid_pointer_size : valid_pointer.
Hint Resolve malloc_token_local_facts : saturate_local.

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
    split; try rep_omega.
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

Definition zip3 (bs:list nat) (cs:list val) (ds:list Z) := (combine (combine bs cs) ds).

Lemma Zlength_zip3:
   forall bs cs ds,
   Zlength bs = Zlength cs -> Zlength cs = Zlength ds ->
   Zlength (zip3 bs cs ds) = Zlength bs.
Proof.
  intros bs cs ds Hbc Hcd.  unfold zip3.  do 2 rewrite Zlength_correct in *.
  do 2 rewrite combine_length.  
  do 2 rewrite Nat2Z.inj_min. rewrite Hbc. rewrite <- Hcd.  
  rewrite Z.min_r; try reflexivity.  rewrite Z.min_r; try reflexivity.
Qed.

Lemma Znth_zip3:
   forall bs cs ds n,
   Zlength bs = Zlength cs -> Zlength cs = Zlength ds ->
   0 <= n < Zlength bs ->
   Znth n (zip3 bs cs ds) = (Znth n bs, Znth n cs, Znth n ds).
Proof.
  intros bs cs ds n Hbc Hcd Hn. 
  pose proof (Zlength_zip3 bs cs ds Hbc Hcd) as Hz.
  unfold zip3. rewrite <- nth_Znth.
- rewrite combine_nth. rewrite combine_nth.
  rewrite nth_Znth; try omega. rewrite nth_Znth; try omega.
  rewrite nth_Znth; try omega; reflexivity.
  repeat rewrite Zlength_correct in *; omega. rewrite combine_length. 
  assert (H3: length bs = length cs) by (repeat rewrite Zlength_correct in *; omega).
  assert (H4: length cs = length ds) by (repeat rewrite Zlength_correct in *; omega).
  rewrite H3; rewrite H4; rewrite Nat.min_id; reflexivity.
- unfold zip3 in Hz; omega.
Qed.


Lemma sublist_zip3:
forall i j bs cs ds, 
  0 <= i <= j -> j <= Zlength bs ->
  Zlength bs = Zlength cs -> Zlength cs = Zlength ds ->
(sublist i j (zip3 bs cs ds)) = 
(zip3 (sublist i j bs) (sublist i j cs) (sublist i j ds)).
Proof. 
  intros.  destruct H as [Hi Hij]. 
  apply list_extensional.
  - repeat (try rewrite Zlength_sublist; try rewrite Zlength_zip3; try omega).
  - intros.  destruct H as [Hi0lo Hi0hi].
  assert (Hi0: i0 < j - i) by
    (rewrite Zlength_sublist in Hi0hi; auto; rewrite Zlength_zip3; try omega).
  repeat (try rewrite Znth_sublist; try rewrite Znth_zip3; try rewrite Zlength_sublist; 
          try omega); auto.
Qed.


Definition mem_mgr (gv: globals): mpred := 
  EX bins: list val, EX lens: list nat, EX idxs: list Z,
    !! (Zlength bins = BINS /\ Zlength lens = BINS /\
        idxs = map Z.of_nat (seq 0 (Z.to_nat BINS))) &&
  data_at Tsh (tarray (tptr tvoid) BINS) bins (gv _bin) * 
  iter_sepcon mmlist' (zip3 lens bins idxs) * 
  TT. (* waste, which arises due to alignment in bins *)


(* Two lemmas from hashtable exercise *)
Lemma iter_sepcon_1:
  forall {A}{d: Inhabitant A} (a: A) (f: A -> mpred), iter_sepcon f [a] = f a.
Proof. intros. unfold iter_sepcon. normalize. 
Qed.

Lemma iter_sepcon_split3: 
  forall {A}{d: Inhabitant A} (i: Z) (al: list A) (f: A -> mpred),
   0 <= i < Zlength al   -> 
  iter_sepcon f al = 
  iter_sepcon f (sublist 0 i al) * f (Znth i al) * iter_sepcon f (sublist (i+1) (Zlength al) al).
Proof. 
  intros. rewrite <- (sublist_same 0 (Zlength al) al) at 1 by auto.
  rewrite (sublist_split 0 i (Zlength al)) by rep_omega.
  rewrite (sublist_split i (i+1) (Zlength al)) by rep_omega.
  rewrite sublist_len_1 by rep_omega.
  rewrite iter_sepcon_app. rewrite iter_sepcon_app. rewrite iter_sepcon_1.
  rewrite sepcon_assoc. reflexivity.
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
      assert (H3: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr WA))
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
        rewrite H3.
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
forall n p q s, 0 < n <= bin2sizeZ(BINS-1) -> s = bin2sizeZ(size2binZ(n)) -> 
     malloc_compatible s p -> 
  (  data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p) *
     ( data_at Tsh (tptr tvoid) q p *   
     memory_block Tsh (s - WORD) (offset_val WORD p) )
|--  malloc_token' Tsh n p * memory_block Tsh n p).
Proof.
  intros n p q s Hn Hs Hmc.
  unfold malloc_token'.
  Exists s.
  unfold malloc_tok.
  if_tac.
  - (* small chunk *)
    entailer!. split.
    -- pose proof (claim1 n (proj2 Hn)). rep_omega.
    -- match goal with | HA: field_compatible _ _ _ |- _ => 
                         unfold field_compatible in H2;
                           destruct H2 as [? [? [? [? ?]]]] end.
       destruct p; auto; try (apply claim1; rep_omega).
    -- set (s:=(bin2sizeZ(size2binZ(n)))).
       sep_apply (data_at_memory_block Tsh (tptr tvoid) q p).
       simpl.
       rewrite <- memory_block_split_offset; try rep_omega.
       rewrite sepcon_comm by omega.
       rewrite <- memory_block_split_offset; try rep_omega.
       replace (WORD+(s-WORD)) with s by omega.
       replace (n+(s-n)) with s by omega.
       entailer!.
       subst s.
       assert (n <= bin2sizeZ (size2binZ n)) by (apply claim1; rep_omega).
       rep_omega.
       assert (Hn' : 0 <= n <= bin2sizeZ (BINS - 1)) by rep_omega.
       pose proof (size2bin_range n Hn') as Hn''.
       pose proof (bin2size_range (size2binZ n) Hn'').
       subst s; rep_omega.
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
    (malloc_token' Tsh n p * memory_block Tsh n p)
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
    rewrite memory_block_data_at_.
    + replace (offset_val n p) with (offset_val (n-WORD) (offset_val WORD p)).
      2: (normalize; replace (WORD+(n-WORD)) with n by omega; reflexivity).
      replace ( (* rearrangement *)
          memory_block Tsh (s - n) (offset_val (n - WORD) (offset_val WORD p)) *
          (data_at_ Tsh (tptr tvoid) p * memory_block Tsh (n - WORD) (offset_val WORD p))
        )with(
             memory_block Tsh (n - WORD) (offset_val WORD p) *
             memory_block Tsh (s - n) (offset_val (n - WORD) (offset_val WORD p)) *
             data_at_ Tsh (tptr tvoid) p 
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
      (memory_block Tsh (s - n) (offset_val n p) * memory_block Tsh n p)
      with 
        (memory_block Tsh n p * memory_block Tsh (s - n) (offset_val n p))
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


Lemma from_malloc_token_and_block:  
forall t n p,
  n = sizeof t -> 0 <= n <= Ptrofs.max_unsigned - WORD -> 
    (malloc_token Tsh t p * data_at_ Tsh t p)
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
  replace   (EX s : Z, malloc_tok Tsh n s p) 
    with (malloc_token' Tsh n p) by normalize.
  sep_apply (from_malloc_token'_and_block n p H0).
  Intro s. Exists s. entailer!.
Qed.



(*+ code specs *)


(* Similar to current specs in floyd/library, with mem_mgr added and size bound 
revised to account for the header of size WORD and its associated alignment.
Also free allows null, as per Posix standard.

Still pending: less than Tsh share, which in turn will allow size 0. 
*)
Definition malloc_spec {cs: compspecs } := 
   DECLARE _malloc
   WITH t:type, gv:globals
   PRE [ _nbytes OF size_t ]
       PROP (0 < sizeof t <= Ptrofs.max_unsigned - (WA+WORD);
             complete_legal_cosu_type t = true;
             natural_aligned natural_alignment t = true)
       LOCAL (temp _nbytes (Vptrofs (Ptrofs.repr (sizeof t))); gvars gv)
       SEP ( mem_mgr gv )
   POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mem_mgr gv;
             if eq_dec p nullval then emp
             else (malloc_token Tsh t p * data_at_ Tsh t p)).

Definition free_spec {cs:compspecs} := 
   DECLARE _free
   WITH p:_, t:_, gv:globals
   PRE [ _p OF tptr tvoid ]
       PROP ()
       LOCAL (temp _p p; gvars gv)
       SEP (mem_mgr gv; 
            if eq_dec p nullval then emp
            else (malloc_token Tsh t p * data_at_ Tsh t p))
   POST [ Tvoid ]
       PROP ()
       LOCAL ( )
       SEP (mem_mgr gv).

Definition malloc_small_spec :=
   DECLARE _malloc_small
   WITH t:type, gv:globals
   PRE [ _nbytes OF tuint ]
       PROP (0 < sizeof t <= bin2sizeZ(BINS-1) /\
             complete_legal_cosu_type t = true /\
             natural_aligned natural_alignment t = true)
       LOCAL (temp _nbytes (Vptrofs (Ptrofs.repr (sizeof t))); gvars gv)
       SEP ( mem_mgr gv )
   POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mem_mgr gv; 
            if eq_dec p nullval then emp
            else (malloc_token Tsh t p * data_at_ Tsh t p)).

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
            else (malloc_token Tsh t p * data_at_ Tsh t p)).


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


Definition Gprog : funspecs := 
 ltac:(with_library prog [ 
   mmap0_spec; munmap_spec; bin2size_spec; size2bin_spec; fill_bin_spec;
   malloc_small_spec; malloc_large_spec; free_small_spec; malloc_spec; 
   free_spec]).

(*+ code correctness *)


Lemma malloc_compat_WORD_q:
(* key consequence of the invariant: remainder during fill_bin is aligned *)
forall N j p s q,
  malloc_compatible BIGBLOCK p ->
  N = (BIGBLOCK-WA) / (s+WORD) -> 
  0 <= j < N ->
  0 <= s <= bin2sizeZ(BINS-1) ->  
  q = (offset_val (WA+(j*(s+WORD))) p) -> 
  (natural_alignment | (s + WORD)) -> 
  malloc_compatible (BIGBLOCK - (WA + j * (s + WORD)) - WORD) (offset_val WORD q).
Proof.
  intros N j p s q H HN Hj Hs Hq Ha.
  replace (offset_val (WA + (j*(s+WORD))) p) with
          (offset_val WA (offset_val (j*(s+WORD)) p)) in Hq.
  2: (rewrite offset_offset_val; 
      replace (j * (s + WORD) + WA) with (WA + j * (s + WORD)) by omega; reflexivity).
  subst q. do 2 rewrite offset_offset_val.
  apply malloc_compatible_offset.
  - pose proof (BIGBLOCK_enough_j s j) as He.
    destruct Hj as [Hj0 Hj1]; destruct Hs as [Hs0 Hs1]; subst N.
    apply He in Hs0 as H0; auto.
    replace (BIGBLOCK - (WA + j * (s + WORD)) - WORD)
      with (BIGBLOCK - WA - j * (s + WORD) - WORD) by omega.
    apply Zle_minus_le_0.
    rep_omega.
  - apply Z.add_nonneg_nonneg; try rep_omega.
    apply Z.mul_nonneg_nonneg; try rep_omega.
  - replace (BIGBLOCK - (WA + j * (s + WORD)))%Z
      with (BIGBLOCK - WA - j * (s + WORD))%Z by omega.
    replace (BIGBLOCK - WA - j * (s + WORD) - WORD + (j * (s + WORD) + (WA + WORD)))%Z
    with BIGBLOCK by omega; auto.
  - assert ((natural_alignment | WA+WORD)) 
      by (pose proof WORD_ALIGN_aligned; change (WA+WORD) with (WORD*ALIGN)%Z; auto).
    apply Z.divide_add_r; try auto. 
    apply Z.divide_mul_r; try auto. 
Qed.



Lemma weak_valid_pointer_end:
forall p,
valid_pointer (offset_val (-1) p) |-- weak_valid_pointer p.
Proof.
intros.
unfold valid_pointer, weak_valid_pointer.
change predicates_hered.orp with orp. (* delete me *)
apply orp_right2.
destruct p; try solve [simpl; auto].
simpl.
change predicates_hered.FF with FF. apply FF_left.
unfold offset_val.
hnf.
Transparent Nveric.
red.
Opaque Nveric.
red.
hnf; intros.
simpl in *.
replace (Ptrofs.unsigned i + -1)
with (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr (-1))) + 0); auto.
clear H.
rewrite Z.add_0_r.
Abort.  (* Not true *)

Lemma sepcon_weak_valid_pointer1: 
 forall (P Q : mpred) (p : val),
   P |-- weak_valid_pointer p -> P * Q |-- weak_valid_pointer p.
Proof.
  intros.
  eapply derives_trans; [ | apply (extend_weak_valid_pointer p Q)].
  apply sepcon_derives; auto.
Qed.

Lemma sepcon_weak_valid_pointer2:
  forall (P Q : mpred) (p : val),
    P |-- weak_valid_pointer p -> Q * P |-- weak_valid_pointer p.
Proof.
  intros. rewrite sepcon_comm.
  apply sepcon_weak_valid_pointer1; auto.
Qed.

(* Hint Resolve weak_valid_pointer_end: valid_pointer.  *)
Hint Resolve sepcon_weak_valid_pointer1: valid_pointer. 
Hint Resolve sepcon_weak_valid_pointer2: valid_pointer. 

Lemma memory_block_weak_valid_pointer:
forall n p sh,
 sepalg.nonidentity sh ->
 n > 0 ->
 memory_block sh n p
  |-- weak_valid_pointer p.
Proof.
  intros.
  rewrite memory_block_isptr. normalize.
  eapply derives_trans.
  apply memory_block_valid_pointer with (i:=0).
  omega.
  auto.
  normalize. apply valid_pointer_weak.
Qed.

Lemma memory_block_weak_valid_pointer2:
forall (sh : share) (n : Z) (p : val) (i : Z),
       n > 0 ->
       0 <= i <= n ->
       sepalg.nonidentity sh ->
       memory_block sh n p |-- weak_valid_pointer (offset_val i p).
Proof.
  intros.
  apply SeparationLogic.memory_block_weak_valid_pointer; auto.
  omega.
Qed.

Hint Resolve memory_block_weak_valid_pointer: valid_pointer. 

(* maybe: *)
Hint Resolve memory_block_weak_valid_pointer2: valid_pointer.

Lemma max_unsigned_32: Ptrofs.max_unsigned = Int.max_unsigned.
Proof.
  unfold Ptrofs.max_unsigned, Int.max_unsigned.
  unfold Ptrofs.modulus, Int.modulus.
  unfold Ptrofs.wordsize, Int.wordsize.
  unfold Wordsize_Ptrofs.wordsize, Wordsize_32.wordsize.
  unfold Archi.ptr64.
  reflexivity.
Qed.


Lemma Zdiv_prod:
  forall a b c, (a*b|c) -> (a|c).
Proof.
  intros. unfold Z.divide in *. destruct H as [z Hz]. exists (z*b)%Z. lia.
Qed.


Lemma ptrofs_add_for_alignment:
   forall poff n, 0 <= n -> Ptrofs.unsigned poff + n <= Ptrofs.max_unsigned ->
     Ptrofs.unsigned (Ptrofs.add poff (Ptrofs.repr n))
     = Ptrofs.unsigned poff + n. 
Proof.
  intros.
  replace poff with (Ptrofs.repr(Ptrofs.unsigned poff)) at 1
    by (rewrite Ptrofs.repr_unsigned; reflexivity).
  rewrite ptrofs_add_repr.
  rewrite Ptrofs.unsigned_repr; try reflexivity.
  split.
  assert (0 <= Ptrofs.unsigned poff) by apply Ptrofs.unsigned_range.
  rep_omega.
  assumption.
Qed.







