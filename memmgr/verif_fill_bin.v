Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import Lia.
Require Import malloc_lemmas.
Require Import malloc.
Require Import spec_malloc.
Require Import linking. (* just for mk_body *)

Definition Gprog : funspecs := external_specs ++ private_specs.

(* Invariant for loop in fill_bin.
p, s, N are fixed
s + WORD is size of a (small) chunk (including header)
         and we will have s = bin2sizeZ(b) for 0<=b<BINS
p is start of the big block
N is the number of chunks that fit following the waste prefix of size WA
q points to the beginning of a list chunk (size field), unlike the link field
which points to the link field of the following chunk.
*)
Definition fill_bin_inv (p:val) (s:Z) (N:Z) := 
  EX j:_,
  PROP ( N = (BIGBLOCK-WA) / (s+WORD) /\ 0 <= j < N /\
         align_compatible (tarray tuint 1) (offset_val (WA+(j*(s+WORD))) p) (* q *)
)  
(* j remains strictly smaller than N because j is the number 
of finished chunks and the last chunk gets finished following the loop. *)
  LOCAL( temp _q (offset_val (WA+(j*(s+WORD))) p);
         temp _p p; 
         temp _s       (Vint (Int.repr s));
         temp _Nblocks (Vint (Int.repr N));
         temp _j       (Vint (Int.repr j)))  
(* (offset_val (WA + ... + WORD) p) accounts for waste plus M many chunks plus
the offset for size field.  The last chunk's nxt points one word _inside_ 
the remaining part of the big block. *)
  SEP (memory_block Tsh WA p; (* initial waste *)
       mmlist s (Z.to_nat j) (offset_val (WA + WORD) p) 
                             (offset_val (WA + (j*(s+WORD)) + WORD) p); 
       memory_block Tsh (BIGBLOCK-(WA+j*(s+WORD))) (offset_val (WA+(j*(s+WORD))) p)). 


Lemma fill_bin_inv_remainder':
(* The invariant says there's a memory_block at q of size (BIGBLOCK-(WA+j*(s+WORD))),
and later we state that q+WORD is malloc_compatible for ((N-j)*(s+WORD) - WORD).  *)
  forall N s j,
  N = (BIGBLOCK-WA) / (s+WORD) -> 0 <= s -> 0 <= j < N -> 
  BIGBLOCK-(WA+j*(s+WORD)) = (N-j)*(s+WORD) + (BIGBLOCK-WA) mod (s+WORD). 
Proof.
  intros.
  assert ((BIGBLOCK - WA) 
          = (s+WORD) * ((BIGBLOCK - WA)/(s+WORD)) + (BIGBLOCK - WA) mod (s+WORD)) 
    by (apply Z_div_mod_eq; rep_omega).
  rewrite Z.sub_add_distr.
  replace ((BIGBLOCK-WA) mod (s+WORD))%Z
    with ((BIGBLOCK-WA) mod (s+WORD) + j*(s+WORD) - j*(s+WORD))%Z by omega.
  assert (Hsub_cancel_r: forall p n m, n = m -> n-p = m-p)    (* klunky *) 
    by (intros; eapply Z.sub_cancel_r; assumption).
  replace 
    ((N - j) * (s + WORD) + ((BIGBLOCK - WA) mod (s + WORD) + j * (s + WORD) - j * (s + WORD)))
    with (((N - j) * (s + WORD) + ((BIGBLOCK - WA) mod (s + WORD) + j * (s + WORD)) - j * (s + WORD))) by omega.
  apply Hsub_cancel_r.
  replace ((N - j) * (s + WORD) + ((BIGBLOCK - WA) mod (s + WORD) + j * (s + WORD)))
    with ( (N - j)*(s + WORD) + j*(s + WORD) + (BIGBLOCK - WA) mod (s + WORD) ) by omega.
  replace ( (N - j)*(s + WORD) + j*(s + WORD) )%Z 
    with ( N * (s + WORD) )%Z by lia.
  replace (N*(s+WORD))%Z with ((s+WORD)*N)%Z by lia; subst N; auto.
Qed.

Lemma fill_bin_inv_remainder:
(* consequence of fill_bin_inv and the loop guard (j<N-1) *)
  forall N s j, N = (BIGBLOCK-WA) / (s+WORD) -> WORD <= s -> 0 <= j < N-1 -> 
  WORD < BIGBLOCK - (WA + j * (s + WORD)) - (s + WORD).
Proof.
  intros N s j H H0 H1.
  erewrite fill_bin_inv_remainder'; try apply H; try rep_omega.
  assert (N - j >= 2) by omega.
  assert (0 <= (BIGBLOCK - WA) mod (s + WORD)) by (apply Z_mod_lt; rep_omega).
  assert ( (N-j)*(s+WORD) > (s+WORD) ).
  { replace (s+WORD) with (1 * (s+WORD))%Z at 2 by omega; 
     apply Zmult_gt_compat_r; rep_omega.
  }
  assert( (N - j) * (s + WORD) - (s + WORD)
          <= (N - j) * (s + WORD) + (BIGBLOCK - WA) mod (s + WORD) - (s + WORD) ) as H5 by rep_omega.
  eapply Z.lt_le_trans; try apply H5.
  assert ((N - j) * (s + WORD) >= (s+WORD)+(s+WORD)) by nia.
  assert ((N - j) * (s + WORD) - (s+WORD) >= (s+WORD)) by omega.
  apply (Z.lt_le_trans _ (s+WORD) _); try rep_omega.
Qed.


Lemma body_fill_bin: semax_body Vprog Gprog f_fill_bin fill_bin_spec.
Proof. 
start_function. 
forward_call b.  (*! s = bin2size(b) !*)
set (s:=bin2sizeZ b).
assert (WORD <= s <= bin2sizeZ(BINS-1)) by (pose proof (bin2size_range b); rep_omega).
forward_call BIGBLOCK.  (*! *p = mmap0(BIGBLOCK ...) !*)  
{ rep_omega. }
Intros p.
if_tac in H1. (* split cases on mmap post *)
- (* case p = nullval *)
  forward_if. (*! if p == NULL !*)
  (* case p <> nullval *)
  forward. (*! return NULL !*)
  Exists nullval. Exists 1. 
  entailer!.  if_tac; try contradiction. entailer!. contradiction.
- (* case p <> nullval *)
  assert_PROP (isptr p) by entailer!.
  destruct p; try contradiction. 
  rename b0 into pblk; rename i into poff. (* p as blk+ofs *)
  assert_PROP (Ptrofs.unsigned poff + BIGBLOCK < Ptrofs.modulus) by entailer!.
  forward_if; try contradiction.
  match goal with | HA: ?a = ?a |- _  => clear HA end.
  forward. (*! Nblocks = (BIGBLOCK-WASTE) / (s+WORD) !*)
  { (* nonzero divisor *) entailer!.
    match goal with 
    | HA: Int.repr _ = _  |- _  
      => apply repr_inj_unsigned in HA; rep_omega end. }
  deadvars!. 
  forward. (*! q = p + WASTE !*)
  forward. (*! j = 0 !*) 
  forward_while (*! while (j != Nblocks - 1) !*) 
    (fill_bin_inv (Vptr pblk poff) s ((BIGBLOCK-WA) / (s+WORD)) ).
* (* pre implies inv *)
  Exists 0. 
  entailer!.
  ** repeat (try split; try rep_omega).
     *** apply BIGBLOCK_enough; rep_omega. 
     *** (* TODO alignment of q -- once all proved, make a tactic for this mess *)
       eapply align_compatible_rec_Tarray; try reflexivity.
       intros. assert (Hi: i=0) by omega; subst i; simpl; clear H6.
       match goal with | |- context[(Ptrofs.unsigned ?e + 0)] =>
         replace (Ptrofs.unsigned e + 0) with (Ptrofs.unsigned e) by omega end.
       eapply align_compatible_rec_by_value; try reflexivity.
       unfold align_chunk.
       assert (Hpoff: (8 | Ptrofs.unsigned poff)) 
         by (unfold malloc_compatible in H1; destruct H1 as [Halign Hsize]; auto).
       rewrite Mem.addressing_int64_split; auto.
       apply Z.divide_add_r; auto.
       replace 8 with (4*2)%Z in Hpoff by omega.
       apply (Zdiv_prod _ 2 _); auto.  apply Z.divide_reflexive.
     *** unfold Int.divu; normalize. 
  ** replace BIGBLOCK with (WA + (BIGBLOCK - WA)) at 1 by rep_omega.
     rewrite memory_block_split_repr; try rep_omega. 
     simpl. entailer!.
* (* pre implies guard defined *)
  entailer!.
  pose proof BIGBLOCK_enough as HB. 
  assert (H0x: 0 <= s <= bin2sizeZ(BINS-1)) by rep_omega.
  specialize (HB s H0x); clear H0x.
  change (Int.signed (Int.repr 1)) with 1.
  rewrite Int.signed_repr; rep_omega.
* (* body preserves inv *)
  match goal with | HA: _ /\ _ /\ _ |- _ => destruct HA as [? [? Hmc]] end.
  match goal with | HA: ?a = ?a |- _  => clear HA end.
  freeze [0] Fwaste. 
  match goal with | HA: _ |- 
        context[memory_block _ ?mm ?qq] =>set (m:=mm); set (q:=qq) end.
  replace_in_pre
   (memory_block Tsh m q)
   (data_at_ Tsh (tarray tuint 1) q *
    data_at_ Tsh (tptr tvoid) (offset_val WORD q) *
    memory_block Tsh (s - WORD) (offset_val (WORD + WORD) q) *
    memory_block Tsh (m - (s + WORD)) (offset_val (s + WORD) q)).
  { set (N:=(BIGBLOCK-WA)/(s+WORD)).
    sep_apply (memory_block_split_block s m q); 
       try rep_omega; try entailer!; normalize; subst m.
    ** replace (BIGBLOCK - (WA + j * (s + WORD)))
         with (BIGBLOCK - WA - j * (s + WORD)) by omega.
       apply BIGBLOCK_enough_j; rep_omega.
    ** apply (malloc_compat_WORD_q N j (Vptr pblk poff)); auto; try rep_omega.
       subst s; apply bin2size_align; auto.
  }
  Intros. (* flattens the SEP clause *) 
  forward. (*! q[0] = s; !*) 
  freeze [1; 2; 4; 5] fr1.  
  forward. (*! *(q+WORD) = q+WORD+(s+WORD); !*)
  forward. (*! q += s+WORD; !*)
  forward. (*! j++; !*) 
  { (* typecheck *) 
    entailer!.
    pose proof BIGBLOCK_enough. 
    assert (H0x: 0 <= s <= bin2sizeZ(BINS-1)) by rep_omega.
    match goal with | HA: forall _ : _, _ |- _ =>
                specialize (HA s H0x) as Hrng; clear H0x end. 
    assert (Hx: Int.min_signed <= j+1) by rep_omega.
    split. rewrite Int.signed_repr. rewrite Int.signed_repr. assumption.
    rep_omega. rep_omega. rewrite Int.signed_repr. rewrite Int.signed_repr.
    assert (Hxx: j + 1 <= (BIGBLOCK-WA)/(s+WORD)) by omega.
    apply (Z.le_trans (j+1) ((BIGBLOCK-WA)/(s+WORD))).
    assumption. rep_omega. rep_omega. rep_omega. 
  } 
  (* reestablish inv *)  
  Exists (j+1).  
  assert (Hdist: ((j+1)*(s+WORD))%Z = j*(s+WORD) + (s+WORD))
    by (rewrite Z.mul_add_distr_r; omega). 
  entailer!. 
  ** (* pure *)
     assert (HRE' : j <> ((BIGBLOCK - WA) / (s + WORD) - 1)) 
       by (apply repr_neq_e; assumption). 
     assert (HRE2: j+1 < (BIGBLOCK-WA)/(s+WORD)) by rep_omega.  
     split. 
     *** (* alignment of updated q -- TODO, tactic, also for its initial alignment above *)
       split; try rep_omega.
       eapply align_compatible_rec_Tarray; try reflexivity.
       intros. assert (Hi: i=0) by omega; subst i; simpl. 
       match goal with | |- context[(Ptrofs.unsigned ?e + 0)] =>
         replace (Ptrofs.unsigned e + 0) with (Ptrofs.unsigned e) by omega end.
       eapply align_compatible_rec_by_value; try reflexivity.
       unfold align_chunk.
       assert (Hpoff: (8 | Ptrofs.unsigned poff)) 
         by (unfold malloc_compatible in H1; destruct H1 as [Halign Hsize]; auto).
       assert (Hpoff': (4 | Ptrofs.unsigned poff)) by 
           (replace 8 with (4*2)%Z in Hpoff by omega; apply (Zdiv_prod _ 2 _); auto).  
       assert (HWA: (4 | WA)) by (rewrite WA_eq; apply Z.divide_reflexive).
       assert (Hrest: (natural_alignment | (j+1)*(s+WORD)))
         by (apply Z.divide_mul_r; subst s; apply bin2size_align; auto).
       unfold natural_alignment in Hrest.
       assert (Hrest' : (4 | (j + 1) * (s + WORD)))
         by (replace 8 with (4*2)%Z in Hrest by omega; apply (Zdiv_prod _ 2 _); auto).  
       clear Hpoff Hrest H7 H8.
       assert (Hz: (4 | WA + (j + 1) * (s + WORD))) by (apply Z.divide_add_r; auto).
       clear HWA Hpoff' Hrest'.
       rewrite ptrofs_add_for_alignment.
       **** apply Z.divide_add_r; try assumption.
            match goal with | HA: malloc_compatible _ _ |- _ => 
                              simpl in HA; destruct HA as [Hal Hsz] end.
            assert (H48: (4|natural_alignment)).
            { unfold natural_alignment; replace 8 with (2*4)%Z by omega. 
              apply Z.divide_factor_r; auto. }
            eapply Z.divide_trans. apply H48. auto.
       **** assert (j+1>0) by omega; assert (s+WORD>0) by rep_omega.
            assert ((j+1)*(s+WORD) > 0) by (apply Zmult_gt_0_compat; auto).
            rep_omega.
       **** match goal with | HA: malloc_compatible _ _ |- _ => 
                              simpl in HA; destruct HA as [Hal Hsz] end.
            change Ptrofs.max_unsigned with (Ptrofs.modulus - 1).
            (* aiming to use Hsz *)
            assert (WA + (j + 1) * (s + WORD) <= BIGBLOCK).
            { assert (H0s: 0 <= s) by rep_omega.
              pose proof (BIGBLOCK_enough_j s (j+1) H0s HRE2);  rep_omega. 
            }
            rep_omega.
     *** assert (H': 
               BIGBLOCK - WA - ((BIGBLOCK-WA)/(s+WORD)) * (s + WORD) 
               < BIGBLOCK - WA - (j + 1) * (s + WORD))
            by (apply Z.sub_lt_mono_l; apply Z.mul_lt_mono_pos_r; rep_omega).
         unfold offset_val.
         do 3 f_equal; rep_omega.
  ** (* spatial *)
     thaw fr1. thaw Fwaste; cancel. (* thaw and cancel the waste *)
    (* aiming to fold list by lemma mmlist_fold_last, first rewrite conjuncts *)
    set (r:=(offset_val (WA + WORD) (Vptr pblk poff))). (* r is start of list *)
    replace (offset_val (WA + j * (s + WORD) + WORD) (Vptr pblk poff)) 
      with (offset_val WORD q) by (unfold q; normalize).
    replace (upd_Znth 0 (default_val (tarray tuint 1) ) (Vint (Int.repr s)))
      with [(Vint (Int.repr s))] by (unfold default_val; normalize).
    change 4 with WORD in *. (* ugh *)
    assert (HnxtContents: 
    (Vptr pblk
       (Ptrofs.add poff
          (Ptrofs.repr (WA + j * (s + WORD) + (WORD + (s + WORD))))))
    = (offset_val (s + WORD + WORD) q))
      by ( simpl; f_equal; rewrite Ptrofs.add_assoc; f_equal; normalize; f_equal; omega). 
    rewrite HnxtContents; clear HnxtContents.
    replace (Vptr pblk (Ptrofs.add poff (Ptrofs.repr (WA + j*(s+WORD) + WORD))))
      with  (offset_val WORD q) by (unfold q; normalize). 
    replace (offset_val (WA + j * (s + WORD) + (WORD + WORD)) (Vptr pblk poff))
      with  (offset_val (WORD+WORD) q ) by (unfold q; normalize). 
    set (n:=Z.to_nat j).
    replace (Z.to_nat (j+1)) with (n+1)%nat by 
        (unfold n; change 1%nat with (Z.to_nat 1); rewrite Z2Nat.inj_add; auto; omega). 
    set (m':= m - (s+WORD)).
    assert (H0s: 0 <= s) by rep_omega.
    pose proof (BIGBLOCK_enough_j s j H0s (proj2 H6)) as Hsw; clear H0s.
    assert (Hmcq: malloc_compatible s (offset_val WORD  q)).
    { assert (HmcqB:
                malloc_compatible (BIGBLOCK - (WA + j*(s+WORD)) - WORD) (offset_val WORD q)).
      { remember ((BIGBLOCK-WA)/(s+WORD)) as N. 
        apply (malloc_compat_WORD_q N _ (Vptr pblk poff)); try auto.
        rep_omega.
        apply bin2size_align; auto.
      }
      apply (malloc_compatible_prefix s (BIGBLOCK-(WA+j*(s+WORD))-WORD)); try rep_omega; auto.
    }
    assert (Hmpos: WORD < m'). (* space remains, so we can apply mmlist_fold_last *)
    { subst m'; subst m.
      remember ((BIGBLOCK-WA)/(s+WORD)) as N.
      assert (Hsp: 0 <= s) by rep_omega.
      assert (HRE' : j <> ((BIGBLOCK - WA) / (s + WORD) - 1)) 
        by (subst N; apply repr_neq_e; assumption).
      assert (HjN: 0<=j<N-1) by omega; clear HRE HRE'.
      apply (fill_bin_inv_remainder ((BIGBLOCK-WA)/(s+WORD))); rep_omega.
    }
    sep_apply (mmlist_fold_last s n r q m' Hmcq Hmpos); try rep_omega.
    { subst m'. subst m.
      replace (BIGBLOCK - (WA + j * (s + WORD)) - (s + WORD) - WORD)
        with (BIGBLOCK - WA - j * (s + WORD) - s - WORD - WORD) by omega.
      assert (0 <= j*(s+WORD)) by
        (destruct H6; assert (0<=s+WORD) by rep_omega; apply Z.mul_nonneg_nonneg; rep_omega).
      rep_omega.
    }
    entailer!.
    assert (H': 
        (Vptr pblk (Ptrofs.add poff (Ptrofs.repr (WA + (j+1)*(s+WORD) + WORD))))
      = (offset_val (s+WORD+WORD) (offset_val (WA + j*(s+WORD)) (Vptr pblk poff)))).
    { simpl. f_equal. rewrite Ptrofs.add_assoc. f_equal. normalize.
      rewrite Hdist. f_equal. rep_omega. }
    simpl.
    rewrite H'; clear H'.
    unfold r; unfold m'; unfold m.
    assert (H': (offset_val (WA + WORD) (Vptr pblk poff))
             = (Vptr pblk (Ptrofs.add poff (Ptrofs.repr (WA + WORD)))) ) by normalize.
    simpl.
    rewrite <- H'; clear H'.
    unfold q.
    entailer!.    
    assert (H': (BIGBLOCK - (WA + j * (s + WORD)) - (s + WORD))
                   = (BIGBLOCK - (WA + (j + 1) * (s + WORD))) ) by lia.
    rewrite H'; clear H'.
    replace (WA + j * (s + WORD) + (s + WORD)) with (WA + (j + 1) * (s + WORD)) by lia.
    entailer!.

* (* after the loop *) 
(* TODO eventually: here we're setting up the assignments 
to finish the last chunk; this is like setting up in the loop body.
Then we fold into the list, like at the end of the loop body. 
It would be nice to factor commonalities. *)

  set (q:= (offset_val (WA + j * (s + WORD)) (Vptr pblk poff))).
  set (m:= (BIGBLOCK - (WA + j * (s + WORD)))).
  replace_in_pre
   (memory_block Tsh m q)
   (data_at_ Tsh (tarray tuint 1) q *
    data_at_ Tsh (tptr tvoid) (offset_val WORD q) *
    memory_block Tsh (s - WORD) (offset_val (WORD + WORD) q) *
    memory_block Tsh (m - (s + WORD)) (offset_val (s + WORD) q)).
  { 
    sep_apply (memory_block_split_block s m q); try rep_omega.
    ** subst m. replace (BIGBLOCK - (WA + j * (s + WORD)))
              with (BIGBLOCK - WA - j * (s + WORD)) by omega.
       apply BIGBLOCK_enough_j; rep_omega.
    ** subst m. 
       set (N:=(BIGBLOCK-WA)/(s+WORD)).
       apply (malloc_compat_WORD_q N j (Vptr pblk poff)); auto; try rep_omega.
       subst s; apply bin2size_align; auto.
    ** destruct H5 as [H5a [H5j H5align]]; normalize.
    ** entailer!.
  }
  Intros. (* flattens the SEP clause *) 
  freeze [0;5] Fwaste. (* discard what's not needed for post *)
  forward. (*! q[0] = s !*)
  replace (upd_Znth 0 (default_val (tarray tuint 1) ) (Vint (Int.repr s)))
    with [(Vint (Int.repr s))] by (unfold default_val; normalize).
  forward. (*!  *(q+WORD) = NULL !*)
  set (r:=(offset_val (WA + WORD) (Vptr pblk poff))).   
  set (n:=Z.to_nat j).
  replace (offset_val (WA + j * (s + WORD) + WORD) (Vptr pblk poff)) 
    with (offset_val WORD q) by (subst q; normalize).
  assert (Hmc: malloc_compatible s (offset_val WORD q)).
  { (* malloc_compat, for mmlist_fold_last_null *)
    subst q.
    rewrite offset_offset_val.
    replace (WA + j*(s+WORD) + WORD) with (ALIGN*WORD + j*(s+WORD)) by rep_omega.
    apply malloc_compatible_offset; try rep_omega.
    { (* TODO factor out repeated steps in following few *)
      apply Z.add_nonneg_nonneg; try rep_omega.
      assert (0<=s+WORD) by rep_omega; apply Z.mul_nonneg_nonneg; rep_omega.
    }
    { apply (malloc_compatible_prefix _ BIGBLOCK).
      split.
      apply Z.add_nonneg_nonneg; try rep_omega.
      apply Z.add_nonneg_nonneg; try rep_omega.
      assert (0<=s+WORD) by rep_omega; apply Z.mul_nonneg_nonneg; rep_omega.
      destruct H5 as [H5a [[H5jlo H5jhi] H5align]]; normalize.
      assert (Hs0: 0<=s) by rep_omega; pose proof (BIGBLOCK_enough_j s j Hs0 H5jhi).
      rep_omega.      
      assumption.
    } 
    apply Z.divide_add_r.
    apply WORD_ALIGN_aligned.
    apply Z.divide_mul_r.
    apply bin2size_align; auto.
  }
  change (Vint(Int.repr 0)) with nullval.
  sep_apply (mmlist_fold_last_null s n r q Hmc).
  forward. (*! return p+WASTE+WORD !*)
  subst n. 
  Exists r.  Exists (j+1).
  entailer!. 
  if_tac; auto. rep_omega.
  if_tac. 
  *** (* contradiction *)
    match goal with | HA: r = nullval <-> _, HB: r = nullval |- _ 
                      => apply HA in HB; rep_omega end.
  *** entailer!. subst s. 
      replace (Z.to_nat j + 1)%nat with (Z.to_nat (j + 1))%nat.
      entailer!.
      rewrite Z2Nat.inj_add; try rep_omega; reflexivity.
Qed.

Definition module := [mk_body body_fill_bin].
