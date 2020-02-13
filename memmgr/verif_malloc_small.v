Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import malloc_lemmas.
Require Import malloc.
Require Import spec_malloc.
Require Import linking.

Definition Gprog : funspecs := external_specs ++ private_specs.

Lemma body_malloc_small:  semax_body Vprog Gprog f_malloc_small malloc_small_spec.
Proof. 
start_function. 
rewrite <- seq_assoc.  
forward_call n. (*! t'1 = size2bin(nbytes) !*)
rep_omega.
forward. (*! b = t'1 !*)
set (b:=size2binZ n).
assert (Hprednat: forall m, m > 0 -> Nat.pred(Z.to_nat m) = Z.to_nat(Z.pred m))
  by (intros; rewrite Z2Nat.inj_pred; reflexivity).
assert_PROP(Zlength rvec = BINS) as Hlrvec. { 
  unfold mem_mgr_R; Intros bins idxs lens.
  entailer!. autorewrite with sublist in *. rep_omega.
}
(* Now we split cases on whether success is guaranteed. 
   This which simplifies establishing the different cases in postcondition, 
   but comes at the cost of two symbolic executions. *)
destruct (guaranteed rvec n) eqn: Hguar. 

* (*+ case guaranteed *) 
assert (Hb: 0 <= b < BINS) by (apply (claim2 n); omega).
rewrite (mem_mgr_split_R gv b rvec) by apply Hb.
Intros bins idxs lens.
freeze [1; 3] Otherlists.
deadvars!.
apply is_guaranteed in Hguar.
assert (0 < Znth b lens)%nat. { 
  subst b lens. autorewrite with sublist.
  change 0%nat with (Z.to_nat 0%Z).
  apply Z2Nat.inj_lt; rep_omega. 
}
assert_PROP (Znth b bins <> nullval) as Hnonnull. {
  sep_apply (mmlist_ne_nonnull (bin2sizeZ b) (Znth b lens) (Znth b bins)).
  entailer!.
}
forward. (*! p = bin[b] !*)
forward_if( (*! if p == null *)
     PROP()
     LOCAL(temp _p (Znth b bins); temp _b (Vint (Int.repr b)); gvars gv)
     SEP(FRZL Otherlists; TT; 
         data_at Tsh (tarray (tptr tvoid) BINS) bins (gv _bin);
         mmlist (bin2sizeZ b) (Znth b lens) (Znth b bins) nullval)). 
  + (* branch p==NULL *) contradiction.
  + (* branch p<>NULL *)
    forward. (*! skip *)
    entailer!.
  + (* after if: unroll and pop mmlist *)
    set (p:=Znth b bins) in *. (* TODO clumsy, just to reuse old steps *)
    set (len:=Z.of_nat(Znth b lens)) in *.
    set (s:=bin2sizeZ b).  
    assert_PROP (len > 0).
    { replace (Znth b lens) with (Z.to_nat len);
        try (subst len; rewrite nat_of_Z_eq; reflexivity).
      sep_apply (mmlist_ne_len s len p nullval); auto. entailer!.  }
    assert_PROP (isptr p).
    { entailer!. unfold nullval in *.
      match goal with | HA: p <> _ |- _ => simpl in HA end. (* not Archi.ptr64 *)
      unfold is_pointer_or_null in *. simpl in *.
      destruct p; try contradiction; simpl.
      subst. contradiction. auto. }
    replace (Znth b lens) with (Z.to_nat len); try rep_omega.
    rewrite (mmlist_unroll_nonempty s (Z.to_nat len) p);
      try (subst len; rewrite nat_of_Z_eq; assumption).
    Intros q.
    assert_PROP(force_val (sem_cast_pointer p) = field_address (tptr tvoid) [] p).
    { entailer!. unfold field_address. if_tac. normalize. contradiction. }
    forward. (*! q = *p !*)
    forward. (*! bin[b]=q !*)
    (* prepare token+chunk to return *)
    deadvars!.
    thaw Otherlists.  
    sep_apply (to_malloc_token'_and_block n p q s); try rep_omega.
    (* refold invariant *)
    assert (Hrveclen: Zlength rvec = BINS) by
        (subst lens; rewrite Zlength_map in H1; rep_omega). 
    set (rvec':= add_resvec rvec b (-1)).
    set (lens':= map Z.to_nat rvec').
    set (bins':=(upd_Znth b bins (force_val (sem_cast_pointer q)))).
    assert (Hlens: Nat.pred (Z.to_nat len) = (Znth b lens')).
    { unfold lens'. 
      unfold len.
      rewrite nat_of_Z_eq.
      unfold rvec'.
      rewrite Znth_map; try (rewrite Zlength_add_resvec; rep_omega).
      unfold add_resvec.
      simple_if_tac' Htest.
      -- rewrite upd_Znth_same; try rep_omega.
         replace (Znth b lens) with (Z.to_nat(Znth b rvec))
           by (subst lens; rewrite Znth_map; rep_omega).
         rewrite Hprednat; rep_omega.
      --  bdestruct (Zlength rvec =? BINS); [ | rep_omega].
            bdestruct (0 <=? b); [ | rep_omega].
            bdestruct (b <? BINS); [ |rep_omega]. 
            inv Htest.
    } 
    rewrite Hlens.
    change s with (bin2sizeZ b).
    forward. (*! return p !*) 
    set (lens := map Z.to_nat rvec).
    Exists p. entailer!. 
    unfold mem_mgr_R. 
    Exists bins'. 
    set (idxs:= (map Z.of_nat (seq 0 (Z.to_nat BINS)))).
    Exists idxs. 
    Exists lens'.
    cancel.
    entailer!.
    { split.
      subst lens'. subst rvec'. rewrite Zlength_map. rewrite Zlength_add_resvec. rep_omega. 
      apply add_resvec_no_neg; auto.
      rep_omega.
    }
    (* fold mem_mgr *)
    assert (Zlength lens = BINS) by (unfold lens; rewrite Zlength_map; rep_omega). 
    assert (Zlength lens' = BINS) by (unfold lens'; rewrite Zlength_map; 
                                      unfold rvec'; rewrite Zlength_add_resvec; rep_omega).
    assert (Zlength bins' = BINS) by 
        (replace (Zlength bins') with BINS by auto; reflexivity).
    assert (Zlength idxs = BINS) by auto.
    assert (Hbins': sublist 0 b bins' = sublist 0 b bins) by
      (unfold bins'; rewrite sublist_upd_Znth_l; try reflexivity; try rep_omega).
    assert (Hlens': sublist 0 b lens' = sublist 0 b lens). 
    { unfold lens'; unfold lens; unfold rvec'.
      do 2 rewrite sublist_map; f_equal.
      unfold add_resvec.
      simple_if_tac''; auto.
      rewrite sublist_upd_Znth_l; try rep_omega; auto.  }      
    assert (Hbins'': sublist (b+1) BINS bins' = sublist (b+1) BINS bins) by
      (unfold bins'; rewrite sublist_upd_Znth_r; try reflexivity; try rep_omega).
    assert (Hlens'': sublist (b+1) BINS lens' = sublist (b+1) BINS lens). {
      unfold lens'. unfold lens. unfold rvec'. unfold add_resvec.
      simple_if_tac''; auto. do 2 rewrite sublist_map; try rep_omega.
      rewrite sublist_upd_Znth_r; auto; try rep_omega.
      }
    assert (Hsub:  sublist 0 b (zip3 lens bins idxs)
                 = sublist 0 b (zip3 lens' bins' idxs)).
    { repeat rewrite sublist_zip3; try rep_omega.
      rewrite Hbins'. rewrite Hlens'.  reflexivity.  }
    assert (Hsub':  sublist (b + 1) BINS (zip3 lens bins idxs)  
                  = sublist (b + 1) BINS (zip3 lens' bins' idxs)).
    { repeat rewrite sublist_zip3; try rep_omega.
      rewrite Hbins''. rewrite Hlens''.  reflexivity. }
    rewrite Hsub. rewrite Hsub'.
    rewrite pull_right.
    assert (Hq: q = (Znth b bins')). (* TODO clean this mess *)
    { unfold bins'. rewrite upd_Znth_same.  
      destruct q; auto with valid_pointer.
      match goal with | HA: Zlength bins = _ |- _ => 
                        auto 10  with valid_pointer; rewrite H0; assumption end.  }
    rewrite Hq.
    (* Annoying rewrite, but can't use replace_SEP because that's for 
       preconditions; would have to do use it back at the last forward. *)
    assert (Hassoc:
        iter_sepcon mmlist' (sublist 0 b (zip3 lens' bins' idxs)) *
        mmlist (bin2sizeZ b) (Znth b lens') (Znth b bins') nullval * TT *
        iter_sepcon mmlist' (sublist (b + 1) BINS (zip3 lens' bins' idxs))
      = iter_sepcon mmlist' (sublist 0 b (zip3 lens' bins' idxs)) *
        iter_sepcon mmlist' (sublist (b + 1) BINS (zip3 lens' bins' idxs)) *
        mmlist (bin2sizeZ b) (Znth b lens') (Znth b bins') nullval * TT)
           by (apply pred_ext; entailer!).
    sep_apply Hassoc; clear Hassoc. 
    rewrite mem_mgr_split'; try entailer!; auto.

* (*+ case not guaranteed *) 
assert (Hb: 0 <= b < BINS) by (apply (claim2 n); omega).
rewrite (mem_mgr_split_R gv b rvec) by apply Hb.
Intros bins idxs lens.
freeze [1; 3] Otherlists.
deadvars!.
forward. (*! p = bin[b] !*)
(* TODO may not need post since excluding one branch *)
forward_if( (*! if p == null *)
    EX p:val, EX len:Z,
     PROP(p <> nullval)
     LOCAL(temp _p p; temp _b (Vint (Int.repr b)); gvars gv)
     SEP(FRZL Otherlists; TT; 
         data_at Tsh (tarray (tptr tvoid) BINS) (upd_Znth b bins p) (gv _bin);
         mmlist (bin2sizeZ b) (Z.to_nat len) p nullval)). 

  + (* typecheck guard *)
    set (lens:=map Z.to_nat rvec).
    destruct (Znth b lens) eqn: Hblen. 
    - (* length 0 *)
      match goal with | HA: Znth b bins = nullval <-> _ |- _ => set (Hbn:=HA) end. 
      (*Set Printing Implicit. -- to see the need for following step. *)
      change Inhabitant_val with Vundef in Hbn.
      assert (Znth b bins = nullval) by apply (proj2 Hbn Hblen).
      change (@Znth val Vundef) with (@Znth val Inhabitant_val).
      replace (Znth b bins) with nullval by assumption.
      auto with valid_pointer.
    - (* length non-zero *)
      match goal with | HA: Znth b bins = nullval <-> _ |- _ => destruct HA end.
      assert (Znth b bins <> nullval). {
        assert (S n0 <> 0%nat) by congruence. 
        change lens with (map Z.to_nat rvec) in *.
        rewrite Hblen in *; auto.
      }
      change (Vint Int.zero) with nullval.
      auto with valid_pointer.
      apply denote_tc_test_eq_split; auto with valid_pointer.
      sep_apply (mmlist_ne_valid_pointer (bin2sizeZ b) (S n0) (Znth b bins) nullval).
      omega. change Inhabitant_val with Vundef; entailer!.
  + (* branch p==NULL *) 
    change Inhabitant_val with Vundef in *.
    replace (Znth b bins) with nullval by assumption.
    assert_PROP(Znth b lens = 0%nat) as Hlen0.
   { entailer!.
      match goal with | HA: nullval = nullval <-> _ |- _ => (apply HA; reflexivity) end.  } 
    rewrite Hlen0.
    rewrite mmlist_empty.
    forward_call b. (*! p = fill_bin(b) !*) 
    Intro r_with_l; destruct r_with_l as [root len]; simpl.
    forward_if. (*! if p==NULL !*)
    ++ (* typecheck guard *)
      apply denote_tc_test_eq_split; auto with valid_pointer.
      if_tac. entailer!.
      sep_apply (mmlist_ne_valid_pointer (bin2sizeZ b) (Z.to_nat len) root nullval).
      change (Z.to_nat len > 0)%nat with (0 < Z.to_nat len)%nat.
      change 0%nat with (Z.to_nat 0). apply Z2Nat.inj_lt; rep_omega.
      entailer!.
    ++ (* case p==NULL after fill_bin() *) 
      forward. (*! return null *)
      Exists nullval. entailer!. 
      thaw Otherlists.
      set (idxs:= (map Z.of_nat (seq 0 (Z.to_nat BINS)))).
      replace (data_at Tsh (tarray (tptr tvoid) BINS) bins (gv _bin))
         with (data_at Tsh (tarray (tptr tvoid) BINS) bins (gv _bin) * emp) 
         by normalize.
      rewrite <- (mmlist_empty (bin2sizeZ b)).  (* used to need: at 2. *)
      rewrite <- Hlen0 at 1.
      unfold mem_mgr_R. Exists bins. Exists idxs.  Exists (map Z.to_nat rvec).
      entailer!. 
      match goal with | HA: (Znth b bins = _) |- _ => rewrite <- HA at 1 end.
      rewrite (mem_mgr_split' b); auto.  
      pose proof (bin2size_range b); rep_omega.
    ++ (* case p<>NULL *)
      if_tac. contradiction.
      Intros.
      forward. (*! bin[b] = p !*)
      Exists root. Exists len.
     entailer!. 
    ++ pose proof (bin2size_range b); rep_omega.
  + (* branch p!=NULL *)
    forward. (*! skip !*)
    Exists (Znth b bins).  
    Exists (Z.of_nat (nth (Z.to_nat b) lens 0%nat)).
    rewrite Nat2Z.id.  
    match goal with | HA: Zlength bins = _ |- _ => 
                      rewrite upd_Znth_same_val by (rewrite HA; assumption) end. 
    entailer!.
    rewrite <- nth_Znth; try rep_omega.
    unfold Inhabitant_nat.
    entailer!.
  + (* after if: unroll and pop mmlist *)
    Intros p len.
    set (s:=bin2sizeZ b).  
    assert_PROP (len > 0).
    { sep_apply (mmlist_ne_len s len p nullval); auto. entailer!.  }
    assert_PROP (isptr p).
    { entailer!. clear - H6 PNp. destruct p; auto.
      contradiction H6; simpl in *; subst; auto. }
    rewrite (mmlist_unroll_nonempty s (Z.to_nat len) p)
       by (rewrite Z2Nat.id; rep_omega); try assumption.
    Intros q.
    assert_PROP(force_val (sem_cast_pointer p) = field_address (tptr tvoid) [] p).
    { entailer!. unfold field_address. rewrite if_true by auto. normalize. }
    forward. (*! q = *p !*)
    forward. (*! bin[b]=q !*)
    (* prepare token+chunk to return *)
    deadvars!.
    thaw Otherlists.
    sep_apply (to_malloc_token'_and_block n p q s).
    (* refold invariant *)
    rewrite upd_Znth_twice by (rewrite H0; apply Hb).
    set (lens':=(upd_Znth b lens (Nat.pred (Z.to_nat len)))).
    set (bins':=(upd_Znth b bins (force_val (sem_cast_pointer q)))).
    assert (Hpredlen: Nat.pred (Z.to_nat len) = (Znth b lens')).
    { unfold lens'. rewrite upd_Znth_same. reflexivity. 
      match goal with | HA: Zlength lens = _ |- _ => rewrite HA end. 
      assumption. }
    rewrite Hpredlen. 
    change s with (bin2sizeZ b).
    forward. (*! return p !*)
    Exists p. entailer!. 
    rewrite if_false by auto.
    bdestruct (size2binZ n <? BINS); try rep_omega.
    set (rvec':= add_resvec rvec b (len-1)).
    Exists rvec'.
    assert (Heq_except: eq_except rvec' rvec (size2binZ n))
      by (unfold rvec'; apply add_resvec_eq_except).
    entailer!.
    unfold mem_mgr_R.
    set (lens:= (map Z.to_nat rvec)) in *.
    Exists bins'. 
    set (idxs:= (map Z.of_nat (seq 0 (Z.to_nat BINS)))).
    Exists idxs.   
    Exists lens'.
    assert (Hlbins': Zlength bins' = BINS) 
      by (subst bins'; rewrite upd_Znth_Zlength; rep_omega).
    assert (Hllens': Zlength lens' = BINS) 
      by (subst lens'; rewrite upd_Znth_Zlength; rep_omega). 
    entailer!. 
    { split.
      -- subst lens' rvec'. rewrite Hpredlen, upd_Znth_same by rep_omega.
         unfold add_resvec.
         bdestruct (Zlength rvec =? BINS); [ | rep_omega].
         bdestruct (0 <=? b); [ | rep_omega].
         bdestruct (b <? BINS); [ |rep_omega].
         simpl.
         rewrite <- upd_Znth_map. subst lens. f_equal.
         rewrite Hprednat; auto. f_equal. 
         replace (Znth b rvec) with 0; try rep_omega.
         symmetry.  apply small_not_guaranteed_zero; auto. 
      -- apply add_resvec_no_neg; auto.
         assert (0 <= Znth b rvec).
         { apply Forall_Znth. rep_omega. assumption. }
         rep_omega.
    }
(* TODO following can be more succinct using replace, as in free_small and pre_fill *)
    assert (Hbins': sublist 0 b bins' = sublist 0 b bins) by
      (unfold bins'; rewrite sublist_upd_Znth_l; try reflexivity; try rep_omega).
    assert (Hlens': sublist 0 b lens' = sublist 0 b lens) by 
      (unfold lens'; rewrite sublist_upd_Znth_l; try reflexivity; try rep_omega).
    assert (Hbins'': sublist (b+1) BINS bins' = sublist (b+1) BINS bins) by
      (unfold bins'; rewrite sublist_upd_Znth_r; try reflexivity; try rep_omega).
    assert (Hlens'': sublist (b+1) BINS lens' = sublist (b+1) BINS lens) by
      (unfold lens'; rewrite sublist_upd_Znth_r; try reflexivity; try rep_omega).
    assert (Hsub:  sublist 0 b (zip3 lens bins idxs)
                 = sublist 0 b (zip3 lens' bins' idxs)).
    { repeat rewrite sublist_zip3; try rep_omega.
      - rewrite Hbins'. rewrite Hlens'.  reflexivity.
      - assert (Zlength idxs = BINS) by auto. rep_omega.
      - assert (Zlength idxs = BINS) by auto. rep_omega.
    } 
    assert (Hsub':  sublist (b + 1) BINS (zip3 lens bins idxs)  
                  = sublist (b + 1) BINS (zip3 lens' bins' idxs)).
    { repeat rewrite sublist_zip3; try rep_omega.
      - rewrite Hbins''. rewrite Hlens''.  reflexivity.
      - assert (Zlength idxs = BINS) by auto. rep_omega.
      - assert (Zlength idxs = BINS) by auto. rep_omega.
    }
    rewrite Hsub. rewrite Hsub'.
    rewrite pull_right.
    assert (Hq: q = (Znth b bins')).
    { unfold bins'. rewrite upd_Znth_same.  
      destruct q; auto with valid_pointer. rep_omega.
    }
    rewrite Hq.
    rewrite mem_mgr_split'; try entailer!; auto.
Qed.

Definition module := [mk_body body_malloc_small].
