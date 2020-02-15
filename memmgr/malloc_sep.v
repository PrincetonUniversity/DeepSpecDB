Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import Lia. (* for lia tactic (nonlinear integer arithmetic) *) 
Require Import malloc_lemmas. (* background *)
Require Import malloc_shares. (* for comp_Ews *)
Require Import spec_malloc.

(*Require Import malloc_shares.  *)

(* this file has results that depend on the code and are used in its verification *)

Ltac start_function_hint ::= idtac. (* no hint reminder *)

Require Import malloc. (* the program *)

Instance CompSpecs : compspecs. make_compspecs prog. Defined. 
Definition Vprog : varspecs. mk_varspecs prog. Defined. 

Local Open Scope Z.
Local Open Scope logic.  

(* TODO just like Forall_list_repeat but for repeat *)
Lemma Forall_repeat:
  forall {T} (P:T->Prop) (n:nat) (a:T), P a -> Forall P (repeat a n).
Proof.  
 intros.
 induction n; simpl; auto.
Qed.

Ltac simple_if_tac' H := 
  match goal with |- context [if ?A then _ else _] => 
    lazymatch type of A with
    | bool => destruct A eqn: H
    | sumbool _ _ => fail "Use if_tac instead of simple_if_tac, since your expression "A" has type sumbool"
    | ?t => fail "Use simple_if_tac only for bool; your expression"A" has type" t
  end end.
Ltac simple_if_tac'' := let H := fresh in simple_if_tac' H.


(*+ mmlist *)

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

Lemma mmlist_ne_nonnull:
  forall sz len p, (len > 0)%nat ->
    mmlist sz len p nullval |-- !! (p <> nullval).
Proof.
  intros. destruct len. inversion H. unfold mmlist; fold mmlist. entailer.
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


Lemma mmlist_fold_last: 
(* Adding tail chunk. 
Formulated in the manner of lseg_app' in vst/progs/verif_append2.v.
The preserved chunk is just an idiom for list segments, because we have
seg p q * q|->r * r|-> s entails seg p r * r|-> s
but not 
seg p q * q|->r entails seg p r (owing to potential cycle) 

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


(* no longer used; and can be derived using mmlist_app_null
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
*)

Lemma mmlist_app_null: 
  forall s p r m n, mmlist s n p r * mmlist s m r nullval |-- mmlist s (m+n) p nullval.
Proof.
  intros. revert p. induction n.
  - intros. simpl. replace (m+0)%nat with m%nat by lia. entailer!.
  - intros. rewrite mmlist_unroll_nonempty; try lia.
    change (Nat.pred(S n)) with n.
    Intros q. sep_apply (IHn q).
    eapply derives_trans.
    2: { rewrite mmlist_unroll_nonempty. apply derives_refl. lia. }
    Exists q.
    replace (Nat.pred (m + S n)) with (m+n)%nat by lia.
    entailer!.
Qed.

(*+ mem_mgr *) 

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


Lemma mem_mgr_split_R: 
 forall gv:globals, forall b:Z, forall rvec: resvec, 0 <= b < BINS ->
   mem_mgr_R gv rvec
 = 
  EX bins: list val, EX idxs: list Z, EX lens: list nat,
    !! (Zlength bins = BINS /\ Zlength lens = BINS /\ Zlength idxs = BINS 
        /\ lens = map Z.to_nat rvec
        /\ idxs = map Z.of_nat (seq 0 (Z.to_nat BINS))
        /\ no_neg rvec ) &&
  data_at Ews (tarray (tptr tvoid) BINS) bins (gv _bin) * 
  iter_sepcon mmlist' (sublist 0 b (zip3 lens bins idxs)) * 
  mmlist (bin2sizeZ b) (Znth b lens) (Znth b bins) nullval * 
  iter_sepcon mmlist' (sublist (b+1) BINS (zip3 lens bins idxs)) *  
  TT. 
Proof. 
  intros. apply pred_ext.
  - (* LHS -> RHS *)
    unfold mem_mgr. unfold mem_mgr_R.
    Intros bins idxs lens. Exists bins idxs lens. entailer!.
    rewrite <- (mem_mgr_split' b); try assumption. 
    entailer!. reflexivity.
  - (* RHS -> LHS *)
    Intros bins idxs lens. 
    unfold mem_mgr; unfold mem_mgr_R. Exists bins idxs lens. 
    entailer!.
    set (idxs:=(map Z.of_nat (seq 0 (Z.to_nat BINS)))).

    set (lens:=(map Z.to_nat rvec)).

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

Lemma memory_block_Ews_join:
forall (n : Z) (p : val),
  memory_block (comp Ews) n p * memory_block Ews n p = memory_block Tsh n p.
Proof.
  intros.
  rewrite (memory_block_share_join (comp Ews) Ews Tsh). reflexivity.
  apply sepalg.join_comm. 
  replace comp with Share.comp by normalize.
  rewrite comp_Ews.  
  apply join_Ews.
Qed.


(* The following results involve memory predicates that depend on compspecs *)

(* notes towards possibly subsuming lemmas:
- malloc_large uses malloc_large_chunk to split off size and waste parts.
- malloc_small uses to_malloc_token_and_block to change a bin chunk into token plus user chunk.
- free uses from_malloc_token_and_block to access the size, for both large
  and small chunks; the lemma also exposes nxt which is helpful for free_small
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



Lemma to_malloc_token'_and_block:
forall n p q s, 0 <= n <= bin2sizeZ(BINS-1) -> s = bin2sizeZ(size2binZ(n)) -> 
     malloc_compatible s p -> 
  ( data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p) *
     ( data_at Tsh (tptr tvoid) q p *   
     memory_block Tsh (s - WORD) (offset_val WORD p) )
|--  malloc_token' Ews n p * memory_block Ews n p).
Proof.
  intros n p q s Hn Hs Hmc.
  unfold malloc_token'.
  Exists s.
  unfold malloc_tok.
  if_tac.
  - (* small chunk *)
    entailer!. 
    split.
    -- pose proof (claim1 n (proj2 Hn)). rep_omega.
    -- match goal with | HA: field_compatible _ _ _ |- _ => 
                         unfold field_compatible in H2;
                           destruct H2 as [? [? [? [? ?]]]] end.
       destruct p; auto; try (apply claim1; rep_omega).
    -- set (s:=(bin2sizeZ(size2binZ n))).
       sep_apply (data_at_memory_block Tsh (tptr tvoid) q p).
       simpl.
       rewrite <- memory_block_split_offset; try rep_omega.
       --- 
       replace (WORD+(s-WORD)) with s by omega.
       rewrite sepcon_assoc.
       replace (
           memory_block Ews (s - n) (offset_val n p) *
           memory_block Ews n p)
         with (memory_block Ews s p).
       + rewrite memory_block_Ews_join. cancel.
       + rewrite sepcon_comm.
         rewrite <- memory_block_split_offset; try rep_omega.
         replace (n + (s - n)) with s by omega. reflexivity.
         destruct Hn; auto.
         subst s.
         assert (n <= bin2sizeZ (size2binZ n)) by (apply claim1; rep_omega).
         rep_omega.
       --- 
       subst s.
       pose proof (size2bin_range n Hn) as Hn'.
       pose proof (bin2size_range (size2binZ n) Hn').
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
  assert (WORD <= s). { 
    destruct H0 as [Hn Hns]. 
    pose proof (zle s (bin2sizeZ (BINS-1))) as Hsmall.
    destruct Hsmall as [Hsmall | Hsbig]; try rep_omega.
    match goal with | HA: s<=bin2sizeZ(BINS-1) -> _ |- _ => apply HA in Hsmall end. 
    pose proof (bin2size_range (size2binZ n)); subst.
    pose proof (size2bin_range n); rep_omega.
  }
  replace 
  (  memory_block (comp Ews) s p * memory_block Ews (s - n) (offset_val n p) *
     memory_block Ews n p ) 
    with ( memory_block (comp Ews) s p * (memory_block Ews n p * 
                                          memory_block Ews (s - n) (offset_val n p)))
    by (apply pred_ext; entailer!).
  rewrite <- memory_block_split_offset; try rep_omega.
  replace (n+(s-n)) with s by rep_omega.
  rewrite memory_block_Ews_join.
  replace s with (WORD + (s-WORD)) at 1 by omega.
  rewrite memory_block_split_offset; try rep_omega.
  change WORD with (sizeof (tptr tvoid)) at 1.
  rewrite memory_block_data_at_.
  cancel.
  (* field_compatible *)
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
Qed.



