Require Import bst.bst_conc_lemmas.
Require Import bst.bst_conc_nblocking_spec.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import bst.bst_conc_nblocking.
Require Import VST.atomics.general_locks.
Require Import VST.progs.conclib.
Require Import VST.atomics.SC_atomics.
Require Import VST.msl.iter_sepcon.

Section Proofs.
Notation ghost_snap := (ghost_snap(P := node_ghost)).

Notation empty := (@empty coPset _).
Notation top := (@top coPset _).


Lemma node_data_valid_pointer:
  forall (info: option ghost_info) g  tp lp rp v (range:number *number), node_data info g tp lp rp v range  |-- valid_pointer tp.
Proof.
  intros; unfold node_data; destruct info.
  Intros sh; entailer!. entailer!.
Qed.
Hint Resolve node_data_valid_pointer : valid_pointer.

Lemma node_data_saturate_local:
  forall (info: option ghost_info) g  tp lp rp v (range:number *number), node_data info g tp lp rp v range   |-- !! is_pointer_or_null tp.
Proof.
  intros. unfold node_data; destruct info. Intros sh. entailer!. entailer!.
Qed.
Hint Resolve node_data_saturate_local: saturate_local.

Definition node_data_without_value (info: option ghost_info) g  tp lp rp  (range:number * number)  :=  
(match info with Some data =>  EX sh, !!(readable_share sh /\ Int.min_signed <= data.1.1.1 <= Int.max_signed/\ is_pointer_or_null lp /\ is_pointer_or_null rp /\ is_pointer_or_null data.1.1.2) &&  data_at sh t_struct_tree (Vint (Int.repr data.1.1.1),(data.1.1.2,(lp,rp))) tp * in_tree  data.1.2 ( fst range, Finite_Integer (data.1.1.1)) lp g * in_tree data.2 ( Finite_Integer (data.1.1.1), snd range) rp g | None => !!(tp = nullval /\ lp = nullval /\ rp = nullval) && emp end).



 Definition insert_inv (b: val) (sh: share) (x: Z) (v: val) ( g_root:gname) gv (g:gname)  (inv_names : invG) (P:mpred) (AS:mpred) (ref:val): environ -> mpred :=
( EX np: val, EX g_current:gname,EX n1:number, EX n2:number,
PROP (check_key_exist' x (n1,n2) = true)
LOCAL (temp _ref ref; temp _temp np; temp _t b; temp _x (vint x); temp _value v; gvars gv)
SEP ( |>P; AS && cored;in_tree g_current (n1,n2) np g; mem_mgr gv; malloc_token Ews (tptr Tvoid) ref * data_at Ews (tptr Tvoid) (vint 0) ref; 
   nodebox_rep sh b g_root g 
   ))%assert.
   
Definition lookup_inv (b: val)  (sh: share) (x: Z) ( g_root:gname) gv (g:gname)  (inv_names : invG) (P:mpred) (AS:mpred) Q : environ -> mpred :=
  (EX nb:val, EX tp1: val, EX g_current:gname,
   PROP ( )
   LOCAL (temp _p tp1; temp _ap b; temp _t b; temp _x (vint x); gvars gv)
   SEP ((if eq_dec tp1 nullval
        then Q nullval
        else(EX n1:number, EX n2:number, EX n5:number, EX n6:number,  EX info : option ghost_info, EX lp:val, EX rp:val,!! (check_key_exist' x (n1, n2) = true/\ range_inclusion (n5,n6) (n1,n2)=true) && |> P* ghost_snap (n1, n2, info) g_current * node_data_without_value info g tp1 lp rp (n1, n2)*
      in_tree g_current ( n5, n6) nb g* (AS && cored ))) * mem_mgr gv * nodebox_rep sh b g_root g))%assert.
   
   

Lemma node_data_without_value_R: forall (info: option ghost_info) g  tp lp rp  (range:number *number),  node_data_without_value info g tp  lp rp  range |-- if (eq_dec tp nullval) then !!(info = None /\ lp = nullval /\ rp = nullval) && emp  else 
EX data, EX sh, !!(readable_share sh/\ info = Some data  /\ Int.min_signed <= data.1.1.1 <= Int.max_signed/\ is_pointer_or_null lp /\ is_pointer_or_null rp /\  is_pointer_or_null data.1.1.2) &&   data_at sh t_struct_tree (Vint (Int.repr data.1.1.1),(data.1.1.2,(lp,rp))) tp * in_tree data.1.2( fst range, Finite_Integer data.1.1.1) lp g * in_tree data.2 ( Finite_Integer data.1.1.1, snd range) rp g.
Proof.
intros. unfold node_data_without_value.
destruct info.
- Intros sh.  assert_PROP (tp <> nullval).  { entailer!. } destruct (eq_dec tp nullval). contradiction. Exists g0 sh. entailer!.
- Intros. destruct (eq_dec tp nullval). entailer!. contradiction.
Qed.

Lemma node_data_without_value_valid_pointer:
  forall (info: option ghost_info) g  tp lp rp  (range:number *number), node_data_without_value info g tp lp rp  range  |-- valid_pointer tp.
Proof.
  intros; unfold node_data_without_value; destruct info.
  Intros sh; entailer!. entailer!.
Qed.
Hint Resolve node_data_without_value_valid_pointer : valid_pointer.

Lemma node_data_without_value_saturate_local:
  forall (info: option ghost_info) g  tp lp rp  (range:number *number), node_data_without_value info g tp lp rp  range   |-- !! is_pointer_or_null tp.
Proof.
  intros. unfold node_data_without_value; destruct info. Intros sh. entailer!. entailer!.
Qed.
Hint Resolve node_data_without_value_saturate_local: saturate_local.

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
start_function. 
unfold atomic_shift. Intros P.
 set (AS := ashift _ _ _ _ _ _).
forward.
forward_call ( (tptr Tvoid), gv).
{ simpl. repeat (split; auto); rep_omega. }
Intros ref. 
forward.
 eapply semax_pre; [
    | apply (semax_loop _ (insert_inv b sh x v g_root gv g inv_names P AS ref) (insert_inv b sh x v g_root gv g inv_names P AS ref) )]. 

* (* Precondition *) 
   intros. unfold insert_inv.  Exists b g_root.  unfold nodebox_rep in *.  Intros tp lp. Exists Neg_Infinity Pos_Infinity tp lp. sep_apply (in_tree_split g_root ( Neg_Infinity, Pos_Infinity) b g) . entailer!.

*  (* Loop body *)
   unfold insert_inv. Intros np g_current n1 n2. 
   forward. 
   sep_apply cored_dup.
   sep_apply in_tree_split. 
   Intros.
   (* tp = atomic_load_ptr(temp) *)
   forward_call (np, top, empty, fun tp : val => |> P * EX n n0:number, EX lp:val, EX rp:val, EX info: option ghost_info, !! (check_key_exist' x (n, n0) = true) && ghost_snap (n, n0,info) g_current * node_data_without_value info g tp lp rp  (n,n0) , inv_names).
    { subst Frame;instantiate (1 := [AS && cored; in_tree g_current (n1, n2) np g; mem_mgr gv; malloc_token Ews (tptr Tvoid) ref;  data_at Ews (tptr Tvoid) (vint 0) ref ; nodebox_rep sh b g_root g]).  simpl;cancel.
      iIntros "(( in & [AS1 _]) & P)". 
      iMod ("AS1" with "P") as (BST) "[Tree Tclose]". 
      iDestruct "Tree" as "(% & Tree)".
      unfold tree_rep2 at 1.
      iDestruct "Tree" as (tg) "((% & Tree) & gref)".
      iPoseProof (node_exist_in_tree with "[gref in]") as "%". iFrame. destruct H4 as [r H4]. destruct r as [n n0]. destruct H4.
      iPoseProof ( extract_node_info_from_ghost_tree_rep_2 with "Tree") as "Hadd". apply H4. intros. simpl;auto. apply (sortedness_preserved__in_ghosttree BST tg);auto.
      iDestruct "Hadd" as ( tp o lp rp v0) "(info & Tree)". 
      unfold node_information at 1.
      iDestruct "info" as "(% & ((p & master) & info))". 
       iModIntro; iExists Ews, tp; iFrame "p".
       iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
        iIntros "p".
        iDestruct "Tclose" as "[Tclose _]".
        iPoseProof (make_snap with "[master]") as "master". iFrame.
        iMod ("master") as "[snap master]".  
        iDestruct "in" as (sh2) "in".
       iMod (own_dealloc with "in") as "_".
       unfold node_data, node_data_without_value. 
       destruct o.
        * destruct g0 as [[[k v3] g1 ] g2].  instantiate (2 := x). instantiate (1 := v).  iDestruct "info" as (sh1) "(((((% & v) & malloc ) & tp) & g1) & g2)". simpl in *.
         destruct H7. apply split_readable_share in H7. destruct H7 as (sh3 & sh4 & H7 & H9 & H10). rewrite <- (data_at_share_join sh3 sh4 sh1 _ _ _). iDestruct "tp" as "(tp1 & tp2)".
          rewrite (in_tree_split g1 ( n, Finite_Integer k) lp g). rewrite ( in_tree_split g2 ( Finite_Integer k, n0) rp g ). iDestruct "g1" as "(g11 & g12)". iDestruct "g2" as "(g21 & g22)".
        rewrite -> exp_sepcon2.  iExists n.  rewrite -> exp_sepcon2.  iExists n0.  rewrite -> exp_sepcon2.  iExists lp. rewrite -> exp_sepcon2. iExists rp. rewrite -> exp_sepcon2. iExists (Some (k,v3,g1,g2)). simpl. 
        rewrite (prop_true_andp _ (ghost_snap (n, n0, (Some (k,v3,g1,g2))) g_current) ). rewrite <- !sepcon_assoc.   rewrite -> exp_sepcon2. iExists sh3. rewrite (prop_true_andp ( readable_share sh3 ∧ (Int.min_signed ≤ k ∧ k ≤ Int.max_signed)∧ is_pointer_or_null lp ∧ is_pointer_or_null rp /\  is_pointer_or_null v3  ) _ ).
        iFrame .
       iApply "Tclose". 
       iFrame.
       iSplit. iPureIntro;auto.
       unfold tree_rep2.
       iExists tg.
       iFrame;iSplit;auto.
       iApply "Tree".
       unfold node_information, node_data. rewrite -> exp_sepcon2.  iExists sh4.
       iFrame. iSplit. iPureIntro;auto. auto. auto. 
       unfold range_inclusion, check_key_exist' in *.  apply andb_prop in H1. apply andb_prop in H5. destruct H1, H5. apply andb_true_intro. split. apply less_than_equal_less_than_transitivity with (b := n1). apply H5. apply H1. assert (less_than (Finite_Integer x) n0 = true). { apply less_than_less_than_equal_transitivity with (b := n2). apply H11. apply H12. } apply H13. auto.
      *  rewrite -> exp_sepcon2.  iExists n.  rewrite -> exp_sepcon2.  iExists n0.  rewrite -> exp_sepcon2.  iExists lp. rewrite -> exp_sepcon2. iExists rp. rewrite -> exp_sepcon2. iExists None.   rewrite (prop_true_andp _ (ghost_snap (n, n0, None) g_current) ). iDestruct "info" as "(% & info)".  rewrite (prop_true_andp _ emp). iFrame. 
          iApply "Tclose". 
          iFrame.
         iSplit. iPureIntro;auto.
         unfold tree_rep2.
         iExists tg.
         iFrame;iSplit;auto.
         iApply "Tree".
         unfold node_information, node_data. iFrame. iPureIntro. split. apply H7. auto. destruct H7. destruct H8.  destruct H9. split;auto. 
         unfold range_inclusion, check_key_exist' in *.  apply andb_prop in H1. apply andb_prop in H5. destruct H1, H5. apply andb_true_intro. split. apply less_than_equal_less_than_transitivity with (b := n1). apply H5. apply H1. assert (less_than (Finite_Integer x) n0 = true). { apply less_than_less_than_equal_transitivity with (b := n2). apply H7. apply H8. } apply H9.
  } 
 Intro tp.
 Intros n n0 lp rp info. 
 forward_if.
 - (* then clause *)
  intros. 
  forward_call (t_struct_tree, gv).
  Intros p.
  forward. (*p->key = x;*)
 forward_call(v).
 Intro v1.
 forward.
 forward_call(vint 0).
 Intro lp1.
 forward.
 forward_call( vint 0).
 Intro rp1.
 forward.
 sep_apply node_data_without_value_R. subst. simpl. Intros.
 pose proof split_Ews as share.
 destruct share as [ sh1 share]. destruct share as [ sh2 share]. destruct share. destruct H7.
 rewrite <- ( data_at_share_join sh1 sh2 Ews _ _ _ H8).
 focus_SEP 9.
 sep_apply cored_dup.
 (* atomic_CAS_ptr(temp, ref, p) *)
 forward_call (np, Ews, ref, (vint 0), p, top, empty,
        fun vp : val =>   (if eq_dec vp (vint 0) then  Q else ( |> P *  in_tree g_current (n1, n2) np g * bst_conc_nblocking_spec.atomic_ptr_at Ews (vint 0) rp1 * bst_conc_nblocking_spec.atomic_ptr_at Ews (vint 0) lp1 * bst_conc_nblocking_spec.atomic_ptr_at Ews v v1 * malloc_token Ews t_struct_tree p * data_at sh1 t_struct_tree (vint x, (v1, (lp1, rp1))) p )), inv_names).
        {  subst Frame; instantiate (1 := [ mem_mgr gv; AS && cored; malloc_token Ews (tptr Tvoid) ref; data_at sh2 t_struct_tree (vint x, (v1, (lp1, rp1))) p; nodebox_rep sh b g_root g]). unfold fold_right_sepcon. cancel.
         iIntros "(((((((([AS1 _] & rp1) & lp1) & v1 ) & token ) & p ) &P) &snap) & in)".
         iMod ("AS1" with "P") as (BST) "[Tree Tclose]". 
         iDestruct "Tree" as "(% & Tree)".
         unfold tree_rep2 at 1.
         iDestruct "Tree" as (tg) "((% & Tree) & gref)".
         iPoseProof (node_exist_in_tree with "[gref in]") as "%". iFrame. destruct H11 as [r H11]. destruct r as [n3 n4]. destruct H11.
         iPoseProof ( extract_node_info_from_ghost_tree_rep_2 with "Tree") as "Hadd". eauto. intros. simpl;auto. apply (sortedness_preserved__in_ghosttree BST tg );auto.
        iDestruct "Hadd" as ( tp o1 l r v0) "(info & Tree)".
        unfold node_information at 1.
       iDestruct "info" as "(% & ((ap & master) & info))". 
       iModIntro; iExists Ews, tp; iFrame "ap".
       iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
       destruct (eq_dec tp (vint 0)).
       { 
        iIntros "np".
       iDestruct "Tclose" as "[_ Tclose ]".
       iMod (ghost_node_alloc with "[$]") as (gl) "lg". apply find_ghost_set_finite.
       iDestruct "lg" as "((((% & lg) & ref) & in) & inl)".
       instantiate(1 :=  lp1). instantiate(1 := (n3, Finite_Integer x)). instantiate (1 := None). 
       iMod (ghost_node_alloc with "[ref in]") as (gr) "rg". instantiate (1 := (map_upd (find_ghost_set tg g_root (Neg_Infinity, Pos_Infinity) b) gl (n3, Finite_Integer x, lp1))). apply finite_upd. apply find_ghost_set_finite. iFrame.
       iDestruct "rg" as "((((% & rg) & ref) & in) & inr)".
        iDestruct "in" as (sh5) "in".
       iMod (own_dealloc with "in") as "_".
       instantiate(1 := rp1).  instantiate(1 := (Finite_Integer x, n4)). instantiate (1 := None).
       iFrame. 
        iPoseProof ( bi.and_elim_l with "Tree") as "Tree".  iPoseProof ( bi.and_elim_r with "Tree") as "Tree".
       instantiate (1 := v).  instantiate (1 := x). 
       iSpecialize ("Tree" $! gl gr p).
        iPoseProof (node_data_R with "info") as "info". 
       subst tp. iSimpl in "info". iDestruct "info" as "[% _]".  
       destruct H16. subst o1.       
       iMod (snap_master_update1(ORD := range_order) _ _ _ (n3,n4,Some (x, v1, gl, gr))  with "[$snap $master]") as "[snap master]".
       { simpl. split. rewrite andb_true_intro. auto. split;apply less_than_equal_itself. auto. }
       iMod (own_dealloc with "snap") as "_".
       iApply ("Tclose"  $! tt). simpl.
       iSplitL. iSplit. iPureIntro. apply insert_sorted. auto.      
       unfold tree_rep2. iExists  (insert_ghost x v v1 tg gl lp1 gr rp1).
       iFrame.
       unfold node_information,node_data.
       assert (check_key_exist' x (n3, n4) = true). { unfold range_inclusion, check_key_exist' in *. apply andb_prop in H12. apply andb_prop in H1. destruct H1, H12. 
       rewrite andb_true_intro. auto.  split;auto.  apply less_than_equal_less_than_transitivity with  (b := n1). apply H12. apply H1.
       apply less_than_less_than_equal_transitivity with  (b := n2). apply H16. apply H18. }     
       iSpecialize ("Tree" with "[rp1 lp1 v1 p token np lg inl rg inr master ]") . instantiate(1:= rp1).  instantiate(1:= lp1).   instantiate(1:= v1). 
       rewrite prop_true_andp. rewrite -> exp_sepcon2.  repeat rewrite exp_sepcon1.  iExists sh1. iFrame. iPureIntro. split;auto. destruct H17. repeat split;auto. destruct H. auto. destruct H;auto. 
       destruct H17. destruct H18.  repeat split;auto.
        iDestruct "Tree" as "(% & Tree)".
        rewrite prop_true_andp.  assert (H19 := H18). apply (key_not_exist_in_tree _ _ _ x) in H18.
       rewrite (update_ghost_tree_with_insert x v v1 tg gl gr g_root _ lp1 rp1 b n3 n4 None). iFrame. auto. apply H14. apply H15. apply H18.
        apply (sortedness_preserved__in_ghosttree BST _ H10 H9). intros. simpl;auto. simpl;auto.  intros. simpl;auto.  apply (sortedness_preserved__in_ghosttree BST _ H10 H9). auto. apply insert_preserved_in_ghost_tree. auto. auto.
       
       } 
       iIntros "np".
       iMod (snap_master_update1(ORD := range_order) _ _ _ (n3, n4, o1) with "[$snap $master]") as "[snap master]".
       {  split. apply range_iteself. simpl. destruct o1;auto. } 
        iMod (own_dealloc with "snap") as "_".
        iDestruct "Tclose" as "[Tclose _]".  iFrame.

        iApply "Tclose".  rewrite prop_true_andp.
       unfold tree_rep2.
       iExists tg.
       iFrame;iSplit;auto.
       iApply "Tree".
       unfold node_information.
       iFrame. auto.
     }       
     Intro result.     
     focus_SEP 1.  
     forward_if. 
     (* if (!result) *)
      --  if_tac; [discriminate|]. Intros. 
           forward_call (v1). Exists v. entailer!.
           forward_call (lp1). Exists (vint 0). entailer!.
           forward_call (rp1). Exists (vint 0). entailer!. 
           focus_SEP 8. focus_SEP 4.
           assert_PROP (p <> nullval). { entailer!. } 
           forward_call(t_struct_tree, p, gv ).
           {  if_tac.
             - contradiction.
             - erewrite data_at_share_join. entailer!. auto.
           }
           forward.
           Exists np g_current n1 n2.
           entailer!.
   --   if_tac; [|contradiction]. Intros.
          assert_PROP (ref <> nullval). { entailer!. } 
          forward_call((tptr Tvoid), ref, gv).
          { if_tac.
            - contradiction.
            - entailer!. 
          }
    forward. unfold nodebox_rep. Intros tp lp. rewrite <- !sepcon_assoc. Exists tp (p :: lp). simpl. rewrite <- !sepcon_assoc. Exists sh2. entailer!. admit. (* extra AS && cored, need to fix*)
 -  (* else clause *)
    Intros.  
    sep_apply node_data_without_value_R. 
    if_tac; [contradiction|]. Intros data sh1.
    forward.
    destruct data as [[[ k vp] g1] g2]. simpl. simpl in H7.
    forward_if; [ | forward_if ].
    --  (* Inner if, then clause: x<y *)   
         gather_SEP ( in_tree g2 (Finite_Integer k, n0) rp g) (ghost_snap (n, n0, info) g_current) (in_tree g_current (n1, n2) np g).
         viewshift_SEP 0 (emp). 
         { go_lower. unfold in_tree, ghost_snap, ghost_part. Intros sh4 sh5.  iIntros "[[H1 H2] H3]".
           iMod (own_dealloc with "H1"); iMod (own_dealloc with "H2"); iMod (own_dealloc with "H3"); eauto.
         }
         forward. unfold nodebox_rep. Intros tp0 lp0.
         Exists lp g1 n (Finite_Integer k). Exists tp0 (tp :: lp0). simpl iter_sepcon. Exists sh1. 
          entailer!.
         { unfold check_key_exist' in *. apply andb_true_intro. split. apply andb_prop in H2. destruct H2. auto. simpl.  rewrite Z.ltb_lt. omega. } 
    -- (* Inner if, second branch:  y<x *)
         gather_SEP ( in_tree g1 (n, Finite_Integer k) lp g) (ghost_snap (n, n0, info) g_current) (in_tree g_current (n1, n2) np g).
         viewshift_SEP 0 (emp). 
         { go_lower. unfold in_tree, ghost_snap, ghost_part. Intros sh4 sh5.  iIntros "[[H1 H2] H3]".
           iMod (own_dealloc with "H1"); iMod (own_dealloc with "H2"); iMod (own_dealloc with "H3"); eauto.
         }
         forward. unfold nodebox_rep. Intros tp0 lp0.
         Exists rp g2  (Finite_Integer k) n0. Exists tp0 (tp :: lp0). simpl iter_sepcon. Exists sh1. entailer!.
         { unfold check_key_exist' in *. apply andb_true_intro. split.  simpl.  rewrite Z.ltb_lt. omega.  apply andb_prop in H2. destruct H2. auto. } 
         
    --  (* x = y *)
         forward. 
         focus_SEP 5. 
         forward_call ( vp, v, top, empty, Q , inv_names).
         {  subst Frame. instantiate (1 := [ mem_mgr gv; malloc_token Ews (tptr Tvoid) ref; data_at Ews (tptr Tvoid) (vint 0) ref; data_at sh1 t_struct_tree (vint k, (vp, (lp, rp))) tp; nodebox_rep sh b g_root g]).  unfold fold_right_sepcon. cancel.
         iIntros "((((([AS1 _] & in1) & in2 ) & P ) & snap) & in)".
          iMod ("AS1" with "P") as (BST) "[Tree Tclose]". 
         iDestruct "Tree" as "(% & Tree)".
         unfold tree_rep2 at 1.
         iDestruct "Tree" as (tg) "((% & Tree) & gref)".
         iPoseProof (node_exist_in_tree with "[gref in]") as "%". iFrame. destruct H13 as [r H13]. destruct r as [n3 n4]. destruct H13.
         iPoseProof ( extract_node_info_from_ghost_tree_rep_2 with "Tree") as "Hadd". eauto. intros. simpl;auto. apply (sortedness_preserved__in_ghosttree BST tg );auto.
        iDestruct "Hadd" as (tp0 o lp0 rp0 v0) "(info & Tree)". instantiate (1 := v). instantiate (1 := x).
        unfold node_information at 1.
       iDestruct "info" as "(% & ((ap & master) & info))". 
       iCombine "snap master" as "master"; rewrite -> snap_master_join1. 
       iDestruct "master" as "[ % master]".
       destruct H16.  rewrite H6 in H17. simpl in H17.  rewrite <- H17. unfold node_data.
       iDestruct "info" as (sh4) "(((((% & vp) & token ) & tp ) & in11 ) & in21)".
       unfold in_tree, ghost_part at 1. unfold in_tree, ghost_part at 1. unfold in_tree, ghost_part at 1.
       iDestruct "in1" as (sh8) "in1". iMod (own_dealloc with "in1") as "_".
        iDestruct "in2" as (sh9) "in2". iMod (own_dealloc with "in2") as "_".
       iDestruct "in" as (sh10) "in". iMod (own_dealloc with "in") as "_".
       iModIntro. iExists Ews. rewrite (bst.bst_conc_nblocking_spec.atomic_ptr_at__ Ews v0 _). iFrame "vp".
       iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
        iIntros "np".
       iDestruct "Tclose" as "[_ Tclose ]".
        iApply ("Tclose"  $! tt). simpl.
       iSplitL. iSplit. iPureIntro. apply insert_sorted. auto.
       unfold tree_rep2. iExists  (insert_ghost x v vp tg g1 lp0 g2 rp0).
       assert ( x = k). { omega. }
       assert (check_key_exist' x (n3, n4) = true). { unfold range_inclusion, check_key_exist' in *. apply andb_prop in H14. apply andb_prop in H1. destruct H1, H14. 
       rewrite andb_true_intro. auto.  split;auto.  apply less_than_equal_less_than_transitivity with  (b := n1). apply H14. apply H1.
       apply less_than_less_than_equal_transitivity with  (b := n2). apply H20. apply H21. }     
       iSpecialize ("Tree" with "[np ap tp token  in11  in21 master ]") . instantiate (1 := g2). instantiate (1:=g1). instantiate (1 := vp). 
       rewrite prop_true_andp. unfold node_information,node_data. rewrite -> exp_sepcon2.  repeat rewrite exp_sepcon1.  iExists sh4. simpl.  destruct H19.  iFrame.  iPureIntro. split;auto.
       destruct H19. split;auto.
       iDestruct "Tree" as "(% & Tree)".
       rewrite (update_ghost_tree_with_insert2 x v vp tg g1 g2 g_root (Neg_Infinity, Pos_Infinity) lp0 rp0 b). iFrame. iPureIntro. split;auto. 
       apply insert_preserved_in_ghost_tree;auto. split;auto. apply (sortedness_preserved__in_ghosttree BST tg H12 H11). auto.
   }
   assert_PROP (ref <> nullval). { entailer!. } 
   forward_call((tptr Tvoid), ref, gv).
      { if_tac.
            - contradiction.
            - entailer!. 
      }
  forward. unfold nodebox_rep. Intros tp0 lp0. rewrite <- !sepcon_assoc. Exists tp0 (tp :: lp0). simpl. rewrite <- !sepcon_assoc. Exists sh1. entailer!.
* (* After the loop *)
   forward. normalize. 
    
Admitted.


Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
start_function.
unfold atomic_shift. Intros P.
set (AS := ashift _ _ _ _ _ _).
unfold nodebox_rep. Intros tp lp.
forward. (* atom_ptr *ap = t *)
sep_apply cored_dup.
sep_apply in_tree_split. 
focus_SEP 2.
(* struct tree *p = atomic_load_ptr(ap) *)
forward_call (b, top, empty, fun tp : val => if eq_dec tp nullval then  Q nullval else |> P * EX n n0:number, EX lp:val, EX rp:val, EX info: option ghost_info, !!(range_inclusion (Neg_Infinity, Pos_Infinity) (n, n0) = true) && ghost_snap (n, n0,info) g_root * node_data_without_value info g tp lp rp  (n,n0) , inv_names).
    { subst Frame;instantiate (1 := [AS && cored;in_tree g_root (Neg_Infinity, Pos_Infinity) b g; mem_mgr gv;iter_sepcon (λ p : val, EX sh1 : share, data_at_ sh1 t_struct_tree p) lp;bst_conc_nblocking_spec.atomic_ptr_at sh tp b]).  simpl;cancel.
      iIntros "((in & [AS1 _]) & P )". 
      iMod ("AS1" with "P") as (BST) "[Tree Tclose]". 
      iDestruct "Tree" as "(% & Tree)".
      unfold tree_rep2 at 1.
      iDestruct "Tree" as (tg) "((% & Tree) & gref)".
      iPoseProof (node_exist_in_tree with "[gref in]") as "%". iFrame. destruct H2 as [r H2]. destruct r as [n n0]. destruct H2.
      iPoseProof ( extract_left_node_info_from_ghost_tree_rep with "Tree") as "Hadd". apply H2. intros. simpl;auto.
      iDestruct "Hadd" as ( tp1 o lp1 rp1 v0) "(info & Tree)". 
      unfold node_information at 1.
      iDestruct "info" as "( % &  ((p & master) & info))". 
       iModIntro; iExists Ews, tp1. iFrame "p".
       iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
        iIntros "p".
        iPoseProof (make_snap with "[master]") as "master". iFrame.
        iMod ("master") as "[snap master]".  
        iDestruct "in" as (sh2) "in".
       iMod (own_dealloc with "in") as "_". rewrite node_data_R.
       destruct (eq_dec tp1 nullval).
       * iMod (own_dealloc with "snap") as "_".
         iDestruct "Tclose" as "[_ Tclose]".  iSpecialize ("Tclose" $! nullval). iApply "Tclose". iDestruct "info" as "(% & _)".
         rewrite prop_true_andp.
         unfold tree_rep2.
          rewrite -> exp_sepcon1.  
         iExists tg.
         iFrame;iSplit;auto.
         iApply "Tree".
         unfold node_information, node_data. destruct H5. rewrite H5. iFrame. iPureIntro. split;auto.
         split;auto. symmetry. apply lookup_not_in. rewrite <- H1 in H0. destruct H5;destruct H6;destruct H7.  rewrite H5 in H4.  rewrite H8 in H4. eapply range_info_in_tree_not_In in H4.  rewrite <- H1. apply H4. auto. 
         assert ( n= Neg_Infinity /\ n0 = Pos_Infinity).
       { unfold range_inclusion in H3. apply andb_prop in H3. destruct H3. destruct n;destruct n0;simpl in H3,H9. discriminate. discriminate. discriminate. discriminate. discriminate. auto. discriminate. discriminate. discriminate. }
        destruct H9; subst n n0;simpl;auto. intros. simpl;auto.
        *        
        iDestruct "Tclose" as "[Tclose _]". unfold node_data_without_value.
       iDestruct "info" as (g0 sh1) "info".  destruct g0 as [[[k v3] g1 ] g2].  iDestruct "info" as "(((((% & v) & malloc ) & tp) & g1) & g2)". simpl in *.
         destruct H5. apply split_readable_share in H5. destruct H5 as (sh3 & sh4 & H7 & H9 & H10). rewrite <- (data_at_share_join sh3 sh4 sh1 _ _ _). iDestruct "tp" as "(tp1 & tp2)".
          rewrite (in_tree_split g1 ( n, Finite_Integer k) lp1 g). rewrite ( in_tree_split g2 ( Finite_Integer k, n0) rp1 g ). iDestruct "g1" as "(g11 & g12)". iDestruct "g2" as "(g21 & g22)".
        rewrite -> exp_sepcon2.  iExists n.  rewrite -> exp_sepcon2.  iExists n0.  rewrite -> exp_sepcon2.  iExists lp1. rewrite -> exp_sepcon2. iExists rp1. rewrite -> exp_sepcon2. iExists (Some (k,v3,g1,g2)). simpl. 
        rewrite <- !sepcon_assoc.   rewrite -> exp_sepcon2. iExists sh3. rewrite (prop_true_andp _ (ghost_snap (n, n0, Some (k, v3, g1, g2)) g_root)). 
        rewrite (prop_true_andp ( readable_share sh3 ∧ (Int.min_signed ≤ k ∧ k ≤ Int.max_signed)∧ is_pointer_or_null lp1 ∧ is_pointer_or_null rp1 /\  is_pointer_or_null v3  ) _ ). destruct H6. rewrite H5.
        iFrame .
       iApply "Tclose". 
       iFrame.
       iSplit. iPureIntro;auto.
       unfold tree_rep2.
       iExists tg.
       iFrame;iSplit;auto.
       iApply "Tree".
       unfold node_information, node_data. rewrite -> exp_sepcon2.  iExists sh4.
       iFrame. iSplit. iPureIntro;auto. auto. destruct H6; split; auto. auto. auto.
      
  }
  Intros tp1.
  forward_while (lookup_inv b sh x g_root gv g inv_names P AS Q). 
 * (* Precondition *) 
    unfold lookup_inv. Exists b tp1 g_root. unfold nodebox_rep.  destruct (eq_dec tp1 nullval).  Exists tp lp. entailer!. admit.  (* extra AS && cored, need to fix*)
    Intros n0 n1 lp0 rp info. Exists n0 n1 Neg_Infinity Pos_Infinity info lp0 rp. Exists tp lp. sep_apply in_tree_split. 
    assert ( n0= Neg_Infinity /\ n1 = Pos_Infinity).
       { unfold range_inclusion in H0. apply andb_prop in H0. destruct H0. destruct n0;destruct n1;simpl in H0,H1. discriminate. discriminate. discriminate. discriminate. discriminate. auto. discriminate. discriminate. discriminate. }
   destruct H1. subst n0. subst n1.  entailer!.
 * (* type checking *) 
    destruct (eq_dec tp0 nullval);Intros. entailer!. Intros n1 n2 n5 n6 info lp0 rp. entailer!.
 
 * (*Loop Body *)
  Intros.  if_tac. contradiction HRE.
  Intros n1 n2 n5 n6 info lp1 rp .
  sep_apply node_data_without_value_R. destruct (eq_dec tp0 nullval). contradiction HRE. Intros data sh1.
  destruct data as [[[k vp] g1 ] g2]. simpl. 
  forward. simpl in H5.  
  forward_if; [ | forward_if ].
   **  (* first if, then clause: x<y *)   
    forward.
    sep_apply (in_tree_split g1 (n1, Finite_Integer k) lp1 g).
    sep_apply cored_dup.
    forward_call (lp1, top, empty, fun tp : val => if eq_dec tp nullval then  Q nullval else |> P * EX n n0:number, EX lp:val, EX rp:val, EX info: option ghost_info, !!(range_inclusion (n1, Finite_Integer k) (n,n0) = true) && ghost_snap (n, n0,info) g1 * node_data_without_value info g tp lp rp  (n,n0) , inv_names).
    { subst Frame;instantiate (1 := [ AS && cored ; in_tree g1 (n1, Finite_Integer k) lp1 g; mem_mgr gv; data_at sh1 t_struct_tree (vint k, (vp, (lp1, rp))) tp0; nodebox_rep sh b g_root g]).  simpl;cancel.
      iIntros "((((( [AS1 _] & in1) & in2) & P ) & snap) & in)". 
      iMod ("AS1" with "P") as (BST) "[Tree Tclose]". 
      iDestruct "Tree" as "(% & Tree)".
      unfold tree_rep2 at 1.
      iDestruct "Tree" as (tg) "((% & Tree) & gref)".
      iPoseProof (node_exist_in_tree with "[gref in1]") as "%". iFrame. destruct H10 as [r H10]. destruct r as [n3 n4]. destruct H10.
      iPoseProof ( extract_left_node_info_from_ghost_tree_rep with "Tree") as "Hadd". apply H10. intros. simpl;auto.
      iDestruct "Hadd" as ( tp2 o lp2 rp2 v) "(info & Tree)". 
      unfold node_information at 1.
      iDestruct "info" as "(% &((p & master) & info))". 
       iModIntro; iExists Ews, tp2. iFrame "p".
       iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
        iIntros "p".
        iPoseProof (make_snap with "[master]") as "master". iFrame.
        iMod ("master") as "[snap1 master]". 
        iDestruct "in" as (sh7) "in".
       iMod (own_dealloc with "in") as "_".
       iDestruct "in1" as (sh8) "in1".
       iMod (own_dealloc with "in1") as "_". 
        iDestruct "in2" as (sh2) "in2".
       iMod (own_dealloc with "in2") as "_".
        iMod (own_dealloc with "snap") as "_".
       rewrite  node_data_R. unfold node_data_without_value. 
       assert ( check_key_exist' x (n3,n4) = true).
       { unfold check_key_exist', range_inclusion in *. apply andb_true_intro. apply andb_prop in H1. apply andb_prop in H11. destruct H1, H11. split.
          apply less_than_equal_less_than_transitivity with (b := n1);auto. apply less_than_less_than_equal_transitivity with  (b := Finite_Integer k);auto. simpl. apply Zaux.Zlt_bool_true ;auto.
        }  
       destruct (eq_dec tp2 nullval).
       * iMod (own_dealloc with "snap1") as "_". iDestruct "Tclose" as "[_ Tclose]".
         iSpecialize ("Tclose" $! nullval). iApply "Tclose". iDestruct "info" as "(% & _)".
         rewrite prop_true_andp.
         unfold tree_rep2.
          rewrite -> exp_sepcon1.  
         iExists tg.
         iFrame;iSplit;auto.
         iApply "Tree".
         unfold node_information, node_data. destruct H14. rewrite H14. iFrame. iPureIntro. split;auto.
         split;auto. symmetry. apply lookup_not_in. destruct H14. rewrite  H14 in H12. destruct H15. destruct H16.  rewrite H17 in H12.  eapply range_info_in_tree_not_In in H12.  rewrite <- H9. apply H12. rewrite <-H9 in H8;auto. auto. intros;auto. 
        * 
          iDestruct "Tclose" as "[Tclose _]".    iDestruct "info" as (g0 sh3) "info".  destruct g0 as [[[k1 v3] g11 ] g12].  iDestruct "info" as "(((((% & v) & malloc ) & tp) & g1) & g2)". simpl in *.
         destruct H14. apply split_readable_share in H14. destruct H14 as (sh4 & sh5 & H18 & H17 & H16). rewrite <- (data_at_share_join sh4 sh5 sh3 _ _ _). iDestruct "tp" as "(tp1 & tp2)".
          rewrite (in_tree_split g11 ( n3, Finite_Integer k1) lp2 g). rewrite ( in_tree_split g12 ( Finite_Integer k1, n4) rp2 g ). iDestruct "g1" as "(g11 & g12)". iDestruct "g2" as "(g21 & g22)".
        rewrite -> exp_sepcon2.  iExists n3.  rewrite -> exp_sepcon2.  iExists n4.  rewrite -> exp_sepcon2.  iExists lp2. rewrite -> exp_sepcon2. iExists rp2. rewrite -> exp_sepcon2. iExists (Some (k1,v3,g11,g12)). simpl. 
        rewrite <- !sepcon_assoc.   rewrite -> exp_sepcon2. iExists sh4.  
         rewrite (prop_true_andp _ (ghost_snap (n3, n4, Some (k1, v3, g11, g12)) g1)). 
        rewrite (prop_true_andp ( readable_share sh4 ∧ (Int.min_signed ≤ k1 ∧ k1 ≤ Int.max_signed)∧ is_pointer_or_null lp2 ∧ is_pointer_or_null rp2 /\  is_pointer_or_null v3  ) _ ).
       destruct H15. rewrite H14.  iFrame .
       iApply "Tclose". 
       iFrame.
       iSplit. iPureIntro;auto.
       unfold tree_rep2.
       iExists tg.
       iFrame;iSplit;auto.
       iApply "Tree".
       unfold node_information, node_data. rewrite -> exp_sepcon2.  iExists sh5.
       iFrame. iSplit. iPureIntro;auto. auto. destruct H15;split; auto. auto. auto.
     }
    Intros tp2.
    if_tac. 
     { gather_SEP ( in_tree g1 (n1, Finite_Integer k) lp1 g).
        viewshift_SEP 0 (emp). 
         { go_lower. unfold in_tree, ghost_snap, ghost_part. Intros sh'.  iIntros "H"; iMod (own_dealloc with "H");eauto. }
        forward. 
        Exists (lp1,tp2,g1). if_tac. unfold nodebox_rep. Intros tp3 lp3.  Exists tp3 (tp0::lp3) . simpl iter_sepcon. Exists sh1. entailer!. admit.  (* extra AS && cored, need to fix*)
      simpl in H9;contradiction H9.
      }
    Intros n3 n4 lp2 rp2 info2. 
    forward.   Exists (lp1,tp2,g1). if_tac. contradiction H8. Exists n3 n4 n1 (Finite_Integer k) info2 lp2 rp2.  unfold nodebox_rep. Intros tp3 lp3. Exists tp3 (tp0::lp3). simpl iter_sepcon. Exists sh1. entailer!.  
    { unfold check_key_exist', range_inclusion in *. apply andb_true_intro. apply andb_prop in H9.  apply andb_prop in H1. destruct H1, H9. split.
      apply less_than_equal_less_than_transitivity with (b := n1);auto. apply less_than_less_than_equal_transitivity with  (b := Finite_Integer k);auto. simpl. apply Zaux.Zlt_bool_true ;auto.
    }  cancel. 
  **   forward. (* second else if, then clause: x<y *)
    sep_apply (in_tree_split g2 ( Finite_Integer k,n2) rp g).
    sep_apply cored_dup.
    forward_call (rp, top, empty, fun tp : val => if eq_dec tp nullval then  Q nullval else |> P * EX n n0:number, EX lp:val, EX rp:val, EX info: option ghost_info, !!(range_inclusion ( Finite_Integer k,n2) (n,n0) = true) && ghost_snap (n, n0,info) g2 * node_data_without_value info g tp lp rp  (n,n0) , inv_names).
    { subst Frame;instantiate (1 := [ AS && cored ; in_tree g2 (Finite_Integer k,n2) rp g; mem_mgr gv; data_at sh1 t_struct_tree (vint k, (vp, (lp1, rp))) tp0; nodebox_rep sh b g_root g]).  simpl;cancel.
      iIntros "((((( [AS1 _] & in1) & in2) & P ) & snap) & in)". 
      iMod ("AS1" with "P") as (BST) "[Tree Tclose]". 
      iDestruct "Tree" as "(% & Tree)".
      unfold tree_rep2 at 1.
      iDestruct "Tree" as (tg) "((% & Tree) & gref)".
      iPoseProof (node_exist_in_tree with "[gref in1]") as "%". iFrame. destruct H11 as [r H11]. destruct r as [n3 n4]. destruct H11.
      iPoseProof ( extract_left_node_info_from_ghost_tree_rep with "Tree") as "Hadd". apply H11. intros. simpl;auto.
      iDestruct "Hadd" as ( tp2 o lp2 rp2 v) "(info & Tree)". 
      unfold node_information at 1.
      iDestruct "info" as "(% &((p & master) & info))". 
       iModIntro; iExists Ews, tp2. iFrame "p".
       iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
        iIntros "p".
        iPoseProof (make_snap with "[master]") as "master". iFrame.
        iMod ("master") as "[snap1 master]". 
        iDestruct "in" as (sh7) "in".
       iMod (own_dealloc with "in") as "_".
       iDestruct "in1" as (sh8) "in1".
       iMod (own_dealloc with "in1") as "_". 
        iDestruct "in2" as (sh2) "in2".
       iMod (own_dealloc with "in2") as "_".
        iMod (own_dealloc with "snap") as "_".
       rewrite  node_data_R. unfold node_data_without_value. 
       assert ( check_key_exist' x (n3,n4) = true).
       { unfold check_key_exist', range_inclusion in *. apply andb_true_intro. apply andb_prop in H1. apply andb_prop in H12. destruct H1, H12. split.
          apply less_than_equal_less_than_transitivity with (b :=  (Finite_Integer k) );auto. simpl. apply Zaux.Zlt_bool_true ;auto. apply less_than_less_than_equal_transitivity with  (b := n2);auto. 
        }  
       destruct (eq_dec tp2 nullval).
       * iMod (own_dealloc with "snap1") as "_". iDestruct "Tclose" as "[_ Tclose]".
         iSpecialize ("Tclose" $! nullval). iApply "Tclose". iDestruct "info" as "(% & _)".
         rewrite prop_true_andp.
         unfold tree_rep2.
          rewrite -> exp_sepcon1.  
         iExists tg.
         iFrame;iSplit;auto.
         iApply "Tree".
         unfold node_information, node_data. destruct H15. rewrite H15. iFrame. iPureIntro. split;auto.
         split;auto. symmetry. apply lookup_not_in. destruct H15. rewrite  H15 in H13. destruct H16. destruct H17. rewrite H18 in H13.  eapply range_info_in_tree_not_In in H13.  rewrite <- H10. apply H13. rewrite <-H10 in H9;auto. auto. intros;auto. 
        * 
          iDestruct "Tclose" as "[Tclose _]".    iDestruct "info" as (g0 sh3) "info".  destruct g0 as [[[k1 v3] g11 ] g12].  iDestruct "info" as "(((((% & v) & malloc ) & tp) & g1) & g2)". simpl in *.
         destruct H15. apply split_readable_share in H15. destruct H15 as (sh4 & sh5 & H18 & H17 & H19). rewrite <- (data_at_share_join sh4 sh5 sh3 _ _ _). iDestruct "tp" as "(tp1 & tp2)".
          rewrite (in_tree_split g11 ( n3, Finite_Integer k1) lp2 g). rewrite ( in_tree_split g12 ( Finite_Integer k1, n4) rp2 g ). iDestruct "g1" as "(g11 & g12)". iDestruct "g2" as "(g21 & g22)".
        rewrite -> exp_sepcon2.  iExists n3.  rewrite -> exp_sepcon2.  iExists n4.  rewrite -> exp_sepcon2.  iExists lp2. rewrite -> exp_sepcon2. iExists rp2. rewrite -> exp_sepcon2. iExists (Some (k1,v3,g11,g12)). simpl. 
        rewrite <- !sepcon_assoc.   rewrite -> exp_sepcon2. iExists sh4.  
         rewrite (prop_true_andp _ (ghost_snap (n3, n4, Some (k1, v3, g11, g12)) g2)). 
        rewrite (prop_true_andp ( readable_share sh4 ∧ (Int.min_signed ≤ k1 ∧ k1 ≤ Int.max_signed)∧ is_pointer_or_null lp2 ∧ is_pointer_or_null rp2 /\  is_pointer_or_null v3  ) _ ).
       destruct H16. rewrite H15.  iFrame .
       iApply "Tclose". 
       iFrame.
       iSplit. iPureIntro;auto.
       unfold tree_rep2.
       iExists tg.
       iFrame;iSplit;auto.
       iApply "Tree".
       unfold node_information, node_data. rewrite -> exp_sepcon2.  iExists sh5.
       iFrame. iSplit. iPureIntro;auto. auto. destruct H16;split; auto. auto. auto.
     }
    Intros tp2.
    if_tac. 
     { gather_SEP ( in_tree g2 ( Finite_Integer k,n2) rp g).
        viewshift_SEP 0 (emp). 
         { go_lower. unfold in_tree, ghost_snap, ghost_part. Intros sh'.  iIntros "H"; iMod (own_dealloc with "H");eauto. }
        forward. 
        Exists (rp,tp2,g2). if_tac. unfold nodebox_rep. Intros tp3 lp3.  Exists tp3 (tp0::lp3) . simpl iter_sepcon. Exists sh1. entailer!. admit.  (* extra AS && cored, need to fix*)
      simpl in H9;contradiction H9.
      }
    Intros n3 n4 lp2 rp2 info2. 
    forward.   Exists (rp,tp2,g2). if_tac. contradiction H9. Exists n3 n4  (Finite_Integer k) n2 info2 lp2 rp2.  unfold nodebox_rep. Intros tp3 lp3. Exists tp3 (tp0::lp3). simpl iter_sepcon. Exists sh1. entailer!.  
    { unfold check_key_exist', range_inclusion in *. apply andb_true_intro. apply andb_prop in H10.  apply andb_prop in H1. destruct H1, H10. split.
      apply less_than_equal_less_than_transitivity with (b := (Finite_Integer k));auto.  simpl. apply Zaux.Zlt_bool_true ;auto. apply less_than_less_than_equal_transitivity with  (b :=n2);auto. 
    }  cancel. 
    
 ** forward. (* else clause  : x = k *)
     focus_SEP 6.
     forward_call (vp, top, empty, fun v:val => Q v, inv_names).
    { subst Frame;instantiate (1 := [data_at sh1 t_struct_tree (vint k, (vp, (lp1, rp))) tp0;mem_mgr gv;nodebox_rep sh b g_root g]).  simpl;cancel.
      iIntros "((((( [AS1 _] & in1) & in2) & P ) & snap) & in)". 
      iMod ("AS1" with "P") as (BST) "[Tree Tclose]". 
      iDestruct "Tree" as "(% & Tree)".
      unfold tree_rep2 at 1.
      iDestruct "Tree" as (tg) "((% & Tree) & gref)".
      iPoseProof (node_exist_in_tree with "[gref in]") as "%". iFrame. destruct H11 as [r H11]. destruct r as [n3 n4]. destruct H11.
      iPoseProof ( extract_left_node_info_from_ghost_tree_rep with "Tree") as "Hadd". apply H11. intros. simpl;auto.
      iDestruct "Hadd" as ( tp2 o lp2 rp2 v) "(info & Tree)". 
      unfold node_information at 1.
      iDestruct "info" as "(% & ((p & master) & info))".
       iCombine "snap master" as "master"; rewrite -> snap_master_join1. 
       iDestruct "master" as "[ % master]".
       destruct H14.  rewrite H4 in H15. simpl in H15.  rewrite <- H15. unfold node_data. 
       iDestruct "info" as (sh4) "(((((% & vp) & token ) & tp ) & in11 ) & in21)".
       unfold in_tree, ghost_part at 1. unfold in_tree, ghost_part at 1. unfold in_tree, ghost_part at 1.
       iDestruct "in1" as (sh8) "in1". iMod (own_dealloc with "in1") as "_".
        iDestruct "in2" as (sh9) "in2". iMod (own_dealloc with "in2") as "_".
       iDestruct "in" as (sh10) "in". iMod (own_dealloc with "in") as "_".
       iModIntro. iExists Ews. iExists v.  iFrame "vp".
       iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
        iIntros "np".
       iDestruct "Tclose" as "[_ Tclose ]".
       iSpecialize ("Tclose" $! v).
       iApply ("Tclose"). rewrite <- H10 in H9. assert (k = x). { omega. } rewrite H17 in H15. rewrite <- H15 in H13.
       apply (sorted_tree_look_up_in x v vp g1 g2 tg _ _ H9) in H13.
       rewrite prop_true_andp. unfold tree_rep2.
       rewrite -> exp_sepcon1. iExists tg.
       iFrame;iSplit;auto.
       iApply "Tree".
       unfold node_information, node_data. rewrite -> exp_sepcon2.  iExists sh4.
       iFrame. iSplit. iPureIntro;auto. auto. split. rewrite <-H10;auto. rewrite <-H10;auto.
     }
     Intros v.
     forward.
     forward.
     Exists v.
     unfold nodebox_rep. Intros tp3 lp3. Exists tp3 (tp0::lp3). simpl iter_sepcon. Exists sh1. entailer!.
* (* After the loop *) 
  if_tac. forward. Exists nullval.  entailer!.  contradiction HRE.  
Admitted.







End Proofs.