Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import malloc_lemmas.
Require Import malloc.
Require Import spec_malloc.
Require Import linking.

Definition Gprog : funspecs := private_specs.

Lemma body_free_small:  semax_body Vprog Gprog f_free_small free_small_spec.
Proof. 
start_function. 
destruct H as [[Hn Hn'] [Hs Hmc]].
forward_call s. (*! b = size2bin(s) !*)
{ subst; pose proof (bin2size_range(size2binZ n)); pose proof (claim2 n); rep_omega. }
set (b:=(size2binZ n)). 
assert (Hb: b = size2binZ s) by (subst; rewrite claim3; auto).
rewrite <- Hb.
assert (Hb': 0 <= b < BINS) 
  by (change b with (size2binZ n); apply claim2; split; assumption).
rewrite (mem_mgr_split_R gv b lens Hb'). (* to expose bins[b] in mem_mgr *)
Intros bins idxs.
forward. (*! void *q = bin[b] !*) 
assert_PROP( (force_val (sem_cast_pointer p) = field_address (tptr tvoid) [] p) ). 
{ entailer!. unfold field_address; normalize; if_tac; auto; contradiction. }
forward. (*!  *((void ** )p) = q !*)
gather_SEP 0 1 2 5.
set (q:=(Znth b bins)).
assert_PROP (p <> nullval) by entailer!.
apply semax_pre with 
    (PROP ( )
     LOCAL (temp _q q; temp _b (Vint (Int.repr b)); 
     temp _p p; temp _s (Vptrofs (Ptrofs.repr s)); gvars gv)
     SEP ((EX q': val, 
!!(malloc_compatible s p 
   /\ p <> nullval) && 
          data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p) *
          data_at Tsh (tptr tvoid) q' p *
          memory_block Tsh (s - WORD) (offset_val WORD p) *
          mmlist (bin2sizeZ b) (Znth b lens) q' nullval) ;
     data_at Tsh (tarray (tptr tvoid) BINS) bins (gv _bin);
     iter_sepcon mmlist' (sublist 0 b (zip3 lens bins idxs)) ;
     iter_sepcon mmlist' (sublist (b + 1) BINS (zip3 lens bins idxs)) ;
     TT)).
{ Exists q. entailer!. }
replace (bin2sizeZ b) with s by auto. 
change (Znth b lens)
  with (Nat.pred (Nat.succ (Znth b lens))).

assert_PROP( isptr p ). 
{ entailer!. unfold nullval in *.
  match goal with | HA: p <> _ |- _ => simpl in HA end. (* not Archi.ptr64 *)
  unfold is_pointer_or_null in *. simpl in *.
  destruct p; try contradiction; simpl.  auto. 
}
assert (succ_pos: forall n:nat, Z.of_nat (Nat.succ n) > 0) 
  by (intros; rewrite Nat2Z.inj_succ; rep_omega).
rewrite <- (mmlist_unroll_nonempty s (Nat.succ (Znth b lens)) p nullval);
  try assumption; try apply succ_pos. clear succ_pos.
forward. (*! bin[b] = p !*)
set (bins':=(upd_Znth b bins p)).
(* set (lens':=(upd_Znth b lens (Nat.succ (Znth b lens)))). *)


set (lens':=incr_lens lens b 1).


gather_SEP 1 2 3 0. 
apply ENTAIL_trans with 
    (PROP ( )
     LOCAL (temp _q q; temp _b (Vint (Int.repr b)); 
     temp _p p; temp _s (Vptrofs (Ptrofs.repr s)); gvars gv)
     SEP (
(*  EX bins1: list val, EX lens1: list nat, EX idxs1: list Z,*)
  EX bins1: list val,  EX idxs1: list Z,
(*  !! (Zlength bins1 = BINS /\ Zlength lens' = BINS /\ Zlength idxs1 = BINS *)
  !! (Zlength bins1 = BINS /\ Zlength lens' = BINS /\ Zlength idxs1 = BINS
      /\ idxs1 = map Z.of_nat (seq 0 (Z.to_nat BINS))) &&
    data_at Tsh (tarray (tptr tvoid) BINS) bins1 (gv _bin) * 
    iter_sepcon mmlist' (sublist 0 b (zip3 lens' bins1 idxs1)) *
    mmlist (bin2sizeZ b) (Znth b lens') (Znth b bins1) nullval *
    iter_sepcon mmlist' (sublist (b + 1) BINS (zip3 lens' bins1 idxs1)) *
    TT )).
{ Exists bins'. 

(* Exists lens'. *)

WORKING HERE - incr_lens and decr_lens lemmas may be useful to clients too

Exists idxs.
  assert_PROP(Zlength bins' = BINS /\ Zlength lens' = BINS).
  { unfold bins'.  unfold lens'.  
    rewrite (upd_Znth_Zlength b bins p); try omega.
    match goal with |- context [upd_Znth b lens ?X] => set (foo:=X) end.
    rewrite (upd_Znth_Zlength b lens foo); try omega. 
    entailer!. 
  }
  replace (bin2sizeZ b) with s by auto. 
  replace (bin2sizeZ b) with s by auto. 
  replace (Znth b bins') with p 
    by (unfold bins'; rewrite upd_Znth_same; auto; rewrite H; assumption). 
  replace (Nat.succ (Znth b lens)) with (Znth b lens') 
    by (unfold lens'; rewrite upd_Znth_same; try reflexivity; omega).
  entailer!.
  change (upd_Znth (size2binZ n) bins p) with bins'.  entailer!.
  (* remains to show bins' and lens' are same as originals aside from n *)
  set (idxs:=(map Z.of_nat (seq 0 (Z.to_nat BINS)))) in *.
  repeat rewrite sublist_zip3; try rep_omega.
  replace (sublist 0 (size2binZ n) lens') 
     with (sublist 0 (size2binZ n) lens) by
   (unfold lens'; rewrite sublist_upd_Znth_l; try reflexivity; try rep_omega).
  replace (sublist (size2binZ n + 1) BINS lens') 
     with (sublist (size2binZ n + 1) BINS lens) by 
   (unfold lens'; rewrite sublist_upd_Znth_r; try reflexivity; try rep_omega).
  replace (sublist 0 (size2binZ n) bins')
     with (sublist 0 (size2binZ n) bins) by 
   (unfold bins'; rewrite sublist_upd_Znth_l; try reflexivity; try rep_omega).
  replace (sublist (size2binZ n + 1) BINS bins')
     with (sublist (size2binZ n + 1) BINS bins) by 
   (unfold bins'; rewrite sublist_upd_Znth_r; try reflexivity; try rep_omega).
  entailer!.
}



rewrite <- (mem_mgr_split_R gv b (incr_lens lens (size2binZ n) 1) Hb').
entailer!.
Qed.

Definition module := [mk_body body_free_small].
