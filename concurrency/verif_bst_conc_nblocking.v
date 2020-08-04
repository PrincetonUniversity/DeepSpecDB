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


(* Fixpoint ghost_snap_tree (t: @ ghost_tree val ) (x:Z) (g_root:gname) (g_current:gname) (nb:val) (np:val) range : mpred := 
 match t, range with
 | E_ghost , _ => !! ( eq nb np /\ eq g_root g_current) && ghost_snap (range,  (@None ghost_info) ) g_current
 | (T_ghost a ga lp k v b gb rp ), (l, r) =>  ghost_snap  (range, (@Some ghost_info (x,v,ga,gb))) g_root *
    if (eq_dec nb np) then !! (eq g_root g_current ) && emp else if (x <? k) then ghost_snap_tree a x ga g_current lp np  (l, Finite_Integer x) else if(k >?x) then ghost_snap_tree b x gb g_current rp np (Finite_Integer x, r) else emp
 end. *)
 


   
 Lemma split_non_bot_share sh :
   (sh <> Share.bot) ->
  exists sh1, exists sh2,
     (sh1 <> Share.bot) /\
     (sh2 <> Share.bot) /\
    sepalg.join sh1 sh2 sh.
Proof.
  intros.
  destruct (Share.split sh) as (sh1, sh2) eqn: Hsplit.
  exists sh1, sh2; split; [|split]; auto.
  intro X. contradiction H. apply (Share.split_nontrivial sh1 sh2 sh) . auto. left. auto.
  intro X. contradiction H. apply (Share.split_nontrivial sh1 sh2 sh) . auto. right. auto.
  apply split_join; auto.
Qed.
   
Lemma in_tree_split: forall g_in range p g, in_tree g_in range p g |-- in_tree g_in range p g * in_tree g_in range p g.
Proof.
intros. unfold in_tree. Intro sh. assert_PROP ( sh <> Share.bot).  { unfold ghost_part. sep_apply (own_valid (RA := ref_PCM (map_PCM (A:= gname ) )) g ((Some (sh, ghosts.singleton  (P:= prod_PCM range_ghost (discrete_PCM val)) g_in (range, p)), None) ) compcert_rmaps.RML.R.NoneP). entailer!. inv H. simpl in H0. contradiction. } apply split_non_bot_share in H. destruct H as ( sh1 & sh2 & H1 & H2 & H).
Exists sh1 sh2. rewrite <- (ghost_part_join (P := bst.bst_conc_lemmas.set_PCM (gname * val*number*number)) sh1 sh2 sh (Singleton (gname * val*number*number) a) (Singleton (gname * val*number*number) a)).
cancel. auto. { hnf. apply Extensionality_Ensembles; split; intros ? H3; inv H3.
  - apply Union_introl; apply In_singleton .
  - inv H0; apply In_singleton.
  - inv H0; apply In_singleton.
  } auto. auto. 
 Qed.
 
Notation empty := (@empty coPset _).
Notation top := (@top coPset _).

Definition node_data (info: option ghost_info) g  tp lp rp (range:number * number)  :=  
(match info with Some data =>  EX sh, !!(readable_share sh) &&  data_at sh t_struct_tree (Vint (Int.repr data.1.1.1),(data.1.1.2,(lp,rp))) tp * in_tree g (data.1.2, lp, fst range, Finite_Integer (data.1.1.1)) * in_tree g (data.2, rp, Finite_Integer (data.1.1.1), snd range) | None => !!(tp = nullval) && emp end).
 

Definition node_information (info: option ghost_info) range g g_current tp lp rp np  :=  bst.bst_conc_nblocking_spec.atomic_ptr_at Ews tp np * ghost_master1 (ORD := range_order)  (range, info) g_current * 
node_data info g tp lp rp range.

Lemma node_data_split : forall (info: option ghost_info) g  tp lp rp (range:number *number), node_data info g tp lp rp range |-- node_data info g tp lp rp range * node_data info g tp lp rp range.
Proof.
intros.
unfold node_data; destruct info.
 - Intros sh. apply split_readable_share in H. destruct H as (sh1 & sh2 & H1 & H2 & H3). rewrite <- (data_at_share_join sh1 sh2 sh _ _ _).  
    sep_apply (in_tree_split (g0.1.2, lp, range.1, Finite_Integer (g0.1.1.1)) g). sep_apply ( in_tree_split  (g0.2, rp, Finite_Integer g0.1.1.1, range.2) g ). rewrite <- !sepcon_assoc. Exists sh1 sh2.  entailer!. auto.
- entailer!. 
Qed.


Lemma extract_left_node_info_from_ghost_tree_rep:  forall  tg np b g_root g_current g (r_root: number * number) (range:number*number),
   Ensembles.In (gname * val * number *number) (find_ghost_set tg (g_root,b, fst r_root, snd r_root)) (g_current, np, fst range, snd range) -> ghost_tree_rep tg b g_root g r_root  |--  EX tp:val,  EX o:option ghost_info, EX lp:val, EX rp:val, 
    node_information o range g g_current tp lp rp np  *
   ( node_information o range g g_current tp lp rp np  -* ghost_tree_rep tg b g_root g r_root).
Proof.
 intros.
revert dependent b.
revert dependent g_root.
revert dependent r_root.
induction tg;intros. 
  - inv H. destruct r_root. destruct range.  Exists nullval.  Exists (@None ghost_info) nullval nullval. unfold node_information;simpl. simpl in *. entailer!.  apply wand_refl_cancel_right.
  -  intros. simpl in H. inv H.
     * inv H0;simpl;destruct r_root. 
        ** Intros rtp sh. sep_apply IHtg1.  Intros tp o lp rp. Exists tp o lp rp. entailer!. 
             rewrite -> 5sepcon_assoc.  rewrite <- (emp_wand (bst_conc_nblocking_spec.atomic_ptr_at Ews rtp b * _)) . rewrite wand_sepcon_wand. apply wand_derives.
             rewrite -> sepcon_emp;auto. Exists rtp sh. entailer!.
        ** Intros rtp sh. sep_apply IHtg2.  Intros tp o lp rp. Exists tp o lp rp. entailer!. 
             rewrite -> 5sepcon_assoc.  rewrite <- (emp_wand (bst_conc_nblocking_spec.atomic_ptr_at Ews rtp b * _)) . rewrite wand_sepcon_wand. apply wand_derives.
             rewrite -> sepcon_emp;auto. Exists rtp sh. entailer!.
    * inv H0. destruct r_root. destruct range. simpl in *.  Intros tp sh. Exists  tp (Some ( k, v0, g0, g1)) v v1. unfold node_information. simpl in *. Exists sh. entailer!. rewrite <- wand_sepcon_adjoint. Intro sh1. Exists tp sh1. entailer!.
Qed.


Lemma extract_node_info_from_ghost_tree_rep_2:  forall  tg np b g_root x v g_current g (r_root: number * number) n n0, 
   Ensembles.In (gname * val*number*number) (find_ghost_set tg (g_root,b, fst r_root, snd r_root)) (g_current, np,n,n0) -> (forall k, In_ghost k tg -> check_key_exist' k r_root = true) -> sorted_ghost_tree tg-> ghost_tree_rep tg b g_root g r_root  |--  EX tp:val,  EX o:option ghost_info, EX lp:val, EX rp:val, 
     !!(range_inclusion (n,n0) r_root = true ) && node_information o (n, n0) g g_current tp lp rp np  *
      (( node_information o (n, n0) g g_current tp lp rp np  -* ghost_tree_rep tg b g_root g r_root)
    && (ALL g1 g2:gname,ALL tp1:val, ( !!(o = None /\ tp = nullval  /\ (check_key_exist' x (n,n0) = true) ) && node_information (Some (x,v,g1,g2)) (n, n0) g g_current tp1 lp rp np * node_information None (n, Finite_Integer x) g g1 nullval nullval nullval lp * node_information None (Finite_Integer x, n0) g g2 nullval nullval nullval rp)  -* (!! IsEmptyGhostNode (n,n0,o) tg r_root &&ghost_tree_rep (insert_ghost x v tg g1 lp g2 rp ) b g_root g r_root))
    && (ALL g1 g2:gname, ALL (v0:val), ( !!(o = Some(x,v0,g1,g2) /\ (check_key_exist' x (n,n0) = true)) && node_information (Some (x,v,g1,g2)) (n, n0) g g_current tp lp rp np  ) -* ( !! In_ghost x tg &&ghost_tree_rep (insert_ghost x v tg g1 lp g2 rp ) b g_root g r_root)) ).
Proof.
intros. 
revert dependent r_root. 
revert dependent b.
revert dependent g_root.
induction tg.
 - intros. destruct r_root. inv H. Exists nullval (@None ghost_info) nullval nullval. unfold node_information at 1, node_data at 1. simpl. entailer!.
  { rewrite less_than_equal_itself. rewrite less_than_equal_itself. repeat (split;auto). } repeat apply andp_right.
    * unfold node_information, node_data;simpl. entailer!.  apply wand_refl_cancel_right.
    *  apply allp_right; intro g1. apply allp_right;intro g2. apply allp_right;intro tp1.  rewrite <- wand_sepcon_adjoint. unfold node_information, node_data;simpl. Intro sh.  rewrite <-!sepcon_assoc. Exists tp1 sh. cancel. entailer!. apply InEmptyGhostTree;auto.
    *  apply allp_right; intro g1. apply allp_right;intro g2. apply allp_right;intro v0.  rewrite <- wand_sepcon_adjoint. Intros. 
    
 - intros. inv H.
   * inv H2.
    ** simpl. destruct r_root. Intros tp sh. destruct (x <? k) eqn: E1.
        + simpl. inv H1.  sep_apply IHtg1. 
         {  intros. assert (check_key_exist' k0 (n1, n2) = true). { apply H0. apply InLeft_ghost. apply H1. } unfold check_key_exist' in * . apply andb_prop in H3. destruct H3.
             unfold gt_ghost in H13. apply H13 in H1. rewrite H3;simpl. apply Zaux.Zlt_bool_true. omega. }
             rewrite sepcon_comm. Intros  tp0 o lp rp. Exists tp0 o lp rp. entailer!. 
            { simpl in H1.  apply andb_prop in H1. destruct H1. assert (check_key_exist' k (n1, n2) = true). { apply H0. apply InRoot_ghost. auto. } unfold check_key_exist' in H6.  apply andb_prop in H6. destruct H6. rewrite H1;simpl. apply less_than_to_less_than_equal in H8. apply less_than_equal_transitivity with (b := (Finite_Integer k) ). apply H5. apply H8. }
             rewrite distrib_sepcon_andp.  rewrite distrib_sepcon_andp.  repeat apply andp_derives.
          ++ rewrite <- ( emp_wand (bst_conc_nblocking_spec.atomic_ptr_at Ews tp b * _ * _ * _ * _* _)). rewrite wand_sepcon_wand. apply wand_derives. cancel. Exists tp sh. entailer!.
          ++ apply allp_right; intro g2. apply allp_right;intro g3. apply allp_right;intro tp1. repeat (rewrite allp_sepcon2; eapply allp_left). instantiate(1:= g3).  instantiate(1:= g2).  instantiate(1:= tp1).  rewrite <- ( emp_wand (bst_conc_nblocking_spec.atomic_ptr_at Ews tp b * _ * _ * _ * _* _)).
             rewrite wand_sepcon_wand. apply wand_derives. cancel. simpl. Exists tp sh. entailer!. apply InLeftGhostSubTree. apply H5.
          ++ apply allp_right; intro g2. apply allp_right;intro g3. apply allp_right;intro v5. repeat (rewrite allp_sepcon2; eapply allp_left). instantiate(1:= g3).  instantiate(1:= g2).  instantiate(1:= v5).  rewrite <- ( emp_wand (bst_conc_nblocking_spec.atomic_ptr_at Ews tp b * _ * _ * _ * _* _)).
             rewrite wand_sepcon_wand. apply wand_derives. cancel. simpl. Exists tp sh. entailer!. apply InLeft_ghost. apply H5. 
       +  simpl. inv H1. sep_apply IHtg1.
            { intros. assert (check_key_exist' k0 (n1, n2) = true). { apply H0. apply InLeft_ghost. apply H1. } unfold check_key_exist' in * . apply andb_prop in H3. destruct H3.
             unfold gt_ghost in H13. apply H13 in H1. rewrite H3;simpl. apply Zaux.Zlt_bool_true. omega. }  
         Intros tp0 o lp rp. Exists  tp0 o lp rp. entailer!.
         { simpl in H1.  apply andb_prop in H1. destruct H1. assert (check_key_exist' k (n1, n2) = true). { apply H0. apply InRoot_ghost. auto. } unfold check_key_exist' in H6.  apply andb_prop in H6. destruct H6. rewrite H1;simpl. apply less_than_to_less_than_equal in H8. apply less_than_equal_transitivity with (b := (Finite_Integer k) ). apply H5. apply H8. }
              rewrite -> 5sepcon_assoc, sepcon_comm.  rewrite distrib_sepcon_andp.  rewrite distrib_sepcon_andp.  repeat  apply andp_derives.
         ++  rewrite <- !sepcon_assoc. rewrite <- ( emp_wand (bst_conc_nblocking_spec.atomic_ptr_at Ews tp b * _ * _ * _ * _* _)). rewrite wand_sepcon_wand. apply wand_derives. cancel. Exists tp sh. entailer!.
         ++ apply allp_right; intro g2. apply allp_right;intro g3. apply allp_right;intro tp1. repeat (rewrite allp_sepcon2; eapply allp_left). instantiate(1:= g2).  instantiate(1:= g3).  instantiate(1:= tp1). 
              rewrite <- wand_sepcon_adjoint. assert_PROP (check_key_exist' x (n,n0) = true). { simpl. entailer!. } 
              assert (x < k). { simpl in H1. apply andb_prop in H1. apply andb_prop in H5.  destruct H1,H5. unfold less_than_equal, less_than in *. destruct n0.  apply Z.ltb_lt in H8. apply Zle_bool_imp_le in H6. omega. discriminate. discriminate.  } 
              apply Z.ltb_nlt in E1. omega. 
         ++ apply allp_right; intro g2. apply allp_right;intro g3. apply allp_right;intro v5. repeat (rewrite allp_sepcon2; eapply allp_left). instantiate(1:= g2).  instantiate(1:= g3).  instantiate(1:= v5). 
              rewrite <- wand_sepcon_adjoint. assert_PROP (check_key_exist' x (n,n0) = true). { simpl. entailer!. } 
              assert (x < k). { simpl in H1. apply andb_prop in H5. apply andb_prop in H1.  destruct H1,H5. unfold less_than_equal, less_than in *. destruct n0.  apply Z.ltb_lt in H8. apply Zle_bool_imp_le in H6. omega. discriminate. discriminate.  } 
             apply Z.ltb_nlt in E1. omega. 
  ** simpl. destruct r_root. Intros tp sh. destruct (x <? k) eqn: E1.
       + simpl. inv H1.  unfold lt_ghost in H14. sep_apply IHtg2.
         { intros. assert (check_key_exist' k0 (n1, n2) = true). { apply H0. apply InRight_ghost. apply H1. } unfold check_key_exist' in * . apply andb_prop in H3. destruct H3.
         apply H14 in H1. rewrite H4;simpl. rewrite andb_comm;simpl. apply Zaux.Zlt_bool_true. omega. }       
       Intros tp0 o lp rp. Exists tp0 o lp rp. entailer!. 
         { simpl in H1.  apply andb_prop in H1. destruct H1. assert (check_key_exist' k (n1, n2) = true). { apply H0. apply InRoot_ghost. auto. } unfold check_key_exist' in H6.  apply andb_prop in H6. destruct H6. rewrite H5;simpl. rewrite andb_comm;simpl. apply less_than_to_less_than_equal in H6. apply less_than_equal_transitivity with (b := (Finite_Integer k) ). apply H6. apply H1. }
          rewrite -> 5sepcon_assoc, sepcon_comm.  rewrite distrib_sepcon_andp.  rewrite distrib_sepcon_andp.  repeat  apply andp_derives.
         ++  rewrite <- !sepcon_assoc. rewrite <- ( emp_wand (bst_conc_nblocking_spec.atomic_ptr_at Ews tp b * _ * _ * _ * _* _)). rewrite wand_sepcon_wand. apply wand_derives. cancel. Exists tp sh. entailer!.
         ++ apply allp_right; intro g2. apply allp_right;intro g3. apply allp_right;intro tp1. repeat (rewrite allp_sepcon2; eapply allp_left). instantiate(1:= g2).  instantiate(1:= g3). instantiate(1:= tp1). 
              rewrite <- wand_sepcon_adjoint. assert_PROP (check_key_exist' x (n,n0) = true). { simpl. entailer!. } 
              assert (k < x). { simpl in H1. apply andb_prop in H5. apply andb_prop in H1.  destruct H1,H5. unfold less_than_equal, less_than in *. destruct n.  apply Zle_bool_imp_le in H1. apply Z.ltb_lt in H5. omega. discriminate. discriminate.  } 
             apply Z.ltb_lt in E1. omega. 
         ++ apply allp_right; intro g2. apply allp_right;intro g3. apply allp_right;intro v3. repeat (rewrite allp_sepcon2; eapply allp_left). instantiate(1:= g2).  instantiate(1:= g3). instantiate(1:= v3). 
              rewrite <- wand_sepcon_adjoint. assert_PROP (check_key_exist' x (n,n0) = true). { simpl. entailer!. }  
              assert (k < x). { simpl in H1. apply andb_prop in H5. apply andb_prop in H1.  destruct H1,H5. unfold less_than_equal, less_than in *. destruct n.  apply Zle_bool_imp_le in H1. apply Z.ltb_lt in H5. omega. discriminate. discriminate.  } 
              apply Z.ltb_lt in E1. omega. 
        + destruct (k <? x) eqn:E2. simpl;inv H1.  
          ++ sep_apply IHtg2.
            {  intros. assert (check_key_exist' k0 (n1, n2) = true). { apply H0. apply InRight_ghost. apply H1. } unfold check_key_exist' in * . apply andb_prop in H3. destruct H3.
               unfold lt_ghost in H14. apply H14 in H1. rewrite H4;simpl. rewrite andb_comm;simpl. apply Zaux.Zlt_bool_true. omega. }
            Intros tp0 o lp rp. Exists  tp0 o lp rp. entailer!.
            { simpl in H1.  apply andb_prop in H1. destruct H1. assert (check_key_exist' k (n1, n2) = true). { apply H0. apply InRoot_ghost. auto. } unfold check_key_exist' in H6.  apply andb_prop in H6. destruct H6. rewrite H5;simpl. rewrite andb_comm;simpl.  apply less_than_to_less_than_equal in H6. apply less_than_equal_transitivity with (b := (Finite_Integer k) ). apply H6. apply H1. }
           rewrite -> 5sepcon_assoc, sepcon_comm.  rewrite distrib_sepcon_andp.  rewrite distrib_sepcon_andp.  repeat apply andp_derives.
            +++  rewrite <- !sepcon_assoc.  rewrite <- ( emp_wand (bst_conc_nblocking_spec.atomic_ptr_at Ews tp b * _ * _ * _ * _* _)). rewrite wand_sepcon_wand. apply wand_derives. cancel. Exists tp sh. entailer!.
            +++  apply allp_right; intro g2. apply allp_right;intro g3. apply allp_right;intro tp1. repeat (rewrite allp_sepcon2; eapply allp_left). instantiate(1:= g3).  instantiate(1:= g2).  instantiate(1:= tp1). rewrite <- !sepcon_assoc.   rewrite <- ( emp_wand (bst_conc_nblocking_spec.atomic_ptr_at Ews tp b * _ * _ * _ * _* _)).
             rewrite wand_sepcon_wand. apply wand_derives. cancel. simpl. Exists tp sh. entailer!.  apply InRightGhostSubTree. apply H5. 
            +++ apply allp_right; intro g2. apply allp_right;intro g3. apply allp_right;intro v5. repeat (rewrite allp_sepcon2; eapply allp_left). instantiate(1:= g3).  instantiate(1:= g2).  instantiate(1:= v5). rewrite <- !sepcon_assoc.  rewrite <- ( emp_wand (bst_conc_nblocking_spec.atomic_ptr_at Ews tp b * _ * _ * _ * _* _)).
             rewrite wand_sepcon_wand. apply wand_derives. cancel. simpl. Exists tp sh. entailer!. apply InRight_ghost. apply H5. 
         ++   inv H1.  assert (k = x ). { apply Z.ltb_nlt in E1. apply Z.ltb_nlt in E2. omega. } sep_apply IHtg2. 
            { intros. assert (check_key_exist' k0 (n1, n2) = true). { apply H0. apply InRight_ghost. apply H3. } unfold check_key_exist' in * . apply andb_prop in H4. destruct H4.
              unfold lt_ghost in H14. apply H14 in H3. rewrite H5;simpl. rewrite andb_comm;simpl. apply Zaux.Zlt_bool_true. omega. }
            Intros  tp0 o lp rp. Exists  tp0 o lp rp. entailer!. 
            { simpl in H3.  apply andb_prop in H3. destruct H3. assert (check_key_exist' x (n1, n2) = true). { apply H0. apply InRoot_ghost. auto. } unfold check_key_exist' in H6.  apply andb_prop in H6. destruct H6. rewrite H3;simpl. rewrite andb_comm;simpl. apply less_than_to_less_than_equal in H6. apply less_than_equal_transitivity with (b := (Finite_Integer x) ). apply H6. apply H1. }
             rewrite -> 5sepcon_assoc, sepcon_comm.  rewrite distrib_sepcon_andp.  rewrite distrib_sepcon_andp.  repeat  apply andp_derives.
            +++  rewrite <- !sepcon_assoc.  rewrite <- ( emp_wand (bst_conc_nblocking_spec.atomic_ptr_at Ews tp b * _ * _ * _ * _* _)). rewrite wand_sepcon_wand. apply wand_derives. cancel. Exists tp sh. entailer!.
            +++ apply allp_right; intro g2. apply allp_right;intro g3. apply allp_right;intro tp1. repeat (rewrite allp_sepcon2; eapply allp_left). instantiate(1:= g2).  instantiate(1:= g3).  instantiate(1:= tp1). 
                   rewrite <- wand_sepcon_adjoint. assert_PROP (check_key_exist' x (n,n0) = true). { simpl. entailer!. } 
                   simpl in H2.  apply andb_prop in H3. apply andb_prop in H1.  destruct H3, H1. destruct n. simpl in H1. apply Z.ltb_lt in H1. apply Zle_bool_imp_le in H3. omega. discriminate. simpl in H1. discriminate. 
        
            +++ apply allp_right; intro g2. apply allp_right;intro g3. apply allp_right;intro v3. repeat (rewrite allp_sepcon2; eapply allp_left). instantiate(1:= g2).  instantiate(1:= g3).  instantiate(1:= v3). 
                  rewrite <- wand_sepcon_adjoint. assert_PROP (check_key_exist' x (n, n0) = true). { simpl. entailer!. } 
                 simpl in H3.  apply andb_prop in H3. apply andb_prop in H1.  destruct H3, H1. destruct n. simpl in H1. apply Z.ltb_lt in H1. apply Zle_bool_imp_le in H3. omega. discriminate. simpl in H1. discriminate.     
* inv H2. simpl. destruct r_root. Intros tp sh.  Exists  tp (Some (k, v1, g0, g1)) v0 v2.  unfold node_information at 1, node_data at 1. Exists sh. entailer!. repeat rewrite less_than_equal_itself. simpl;auto. cancel.  repeat  apply andp_right.
   +   rewrite <- wand_sepcon_adjoint. unfold node_information, node_data. simpl.  Intro sh1. Exists  tp sh1. entailer!.
   + apply allp_right; intro g2. apply allp_right;intro g3. apply allp_right;intro tp1. rewrite <- wand_sepcon_adjoint. Intros a.
   + apply allp_right; intro g2. apply allp_right;intro g3. apply allp_right;intro vp. rewrite <- wand_sepcon_adjoint. assert_PROP (Some (k, v1, g0, g1) = Some (x, vp, g2, g3)). { entailer!. } inv H4;subst. simpl.
      destruct (x <? x) eqn: E1. apply Z.ltb_lt in E1. omega. simpl. unfold node_information, node_data. Intro sh1.  entailer!. apply InRoot_ghost. auto. Exists tp sh1. simpl. entailer!.
 Qed.

Lemma node_data_valid_pointer:
  forall (info: option ghost_info) g  tp lp rp (range:number *number), node_data info g tp lp rp range |-- valid_pointer tp.
Proof.
  intros; unfold node_data; destruct info.
  Intros sh; entailer!. entailer!.
Qed.
Hint Resolve node_data_valid_pointer : valid_pointer.

Lemma node_data_saturate_local:
  forall (info: option ghost_info) g  tp lp rp (range:number *number), node_data info g tp lp rp range  |-- !! is_pointer_or_null tp.
Proof.
  intros. unfold node_data; destruct info. Intros sh. entailer!. entailer!.
Qed.
Hint Resolve node_data_saturate_local: saturate_local.

Lemma node_data_R: forall (info: option ghost_info) g  tp lp rp (range:number *number),  node_data info g tp lp rp range |-- if (eq_dec tp nullval) then !!(info = None) && emp  else 
EX data, EX sh, !!(readable_share sh/\ info = Some data) &&  data_at sh t_struct_tree (Vint (Int.repr data.1.1.1),(data.1.1.2,(lp,rp))) tp * in_tree g (data.1.2, lp, fst range, Finite_Integer data.1.1.1) * in_tree g (data.2, rp, Finite_Integer data.1.1.1, snd range).
Proof.
intros. unfold node_data.
destruct info.
- Intros sh.  assert_PROP (tp <> nullval).  { entailer!. } destruct (eq_dec tp nullval). contradiction. Exists g0 sh. entailer!.
- Intros. destruct (eq_dec tp nullval). entailer!. contradiction.
Qed.

Lemma ghost_master1_alloc : forall r:node_info,
  emp |-- (|==> (EX g, ghost_master1 r g))%I.
Proof.
 intros.
 unfold ghost_master1, ghost_master.
 iIntros "e".
  iMod (own_alloc (RA := snap_PCM) (Tsh,r) compcert_rmaps.RML.R.NoneP with "e") as (g) "p".
 simpl;auto.
 iModIntro.
 iExists g.
 iFrame. 
Qed.


 Definition insert_inv (b: val) (sh: share) (x: Z) (v: val) ( g_root:gname) gv (g:gname)  (inv_names : invG) (P:mpred) (AS:mpred) (ref:val): environ -> mpred :=
( EX np: val, EX g_current:gname, EX nodeinfos: list(gname*node_info), EX n1:number, EX n2:number,
PROP (check_key_exist' x (n1,n2) = true)
LOCAL (temp _ref ref; temp _temp np; temp _t b; temp _x (vint x); temp _value v; gvars gv)
SEP ( |>P; AS && cored;in_tree g (g_current,np,n1,n2); mem_mgr gv; malloc_token Ews (tptr Tvoid) ref * data_at Ews (tptr Tvoid) (vint 0) ref; 
   nodebox_rep sh b g_root g ; iter_sepcon (fun info => ghost_snap  (snd info) (fst info)) nodeinfos
   ))%assert.



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
{ intros. unfold insert_inv.  Exists b g_root (@nil (gname *node_info)).  unfold nodebox_rep in *. Intros tp lp. Exists Neg_Infinity Pos_Infinity tp lp. sep_apply (in_tree_split (g_root, b, Neg_Infinity, Pos_Infinity) g) . entailer!. unfold check_key_exist'. simpl. cancel. 
}
* unfold insert_inv. Intros np g_current nodeinfos n1 n2.
   forward. 
   sep_apply cored_dup.
   sep_apply in_tree_split. 
   forward_call (np, top, empty, fun tp : val => |> P * EX lp:val, EX rp:val, EX info: option ghost_info,  ghost_snap (n1,n2,info) g_current * node_data info g tp lp rp (n1,n2), inv_names).
    { subst Frame;instantiate (1 := [AS && cored; in_tree g (g_current, np, n1,n2); mem_mgr gv; malloc_token Ews (tptr Tvoid) ref;  data_at Ews (tptr Tvoid) (vint 0) ref ; nodebox_rep sh b g_root g; iter_sepcon (λ info : own.gname * (number * number * option ghost_info), ghost_snap info.2 info.1)
      nodeinfos]).  simpl;cancel.
     iIntros "(( in & [AS1 _]) & P)". 
      iMod ("AS1" with "P") as (BST) "[Tree Tclose]". 
      iDestruct "Tree" as "(% & Tree)".
      unfold tree_rep2 at 1.
      iDestruct "Tree" as (tg) "((% & Tree) & gref)".
      iPoseProof (node_exist_in_tree with "[gref in]") as "%". iFrame. 
      iPoseProof ( extract_node_info_from_ghost_tree_rep_2 with "Tree") as "Hadd". apply H4. intros. simpl;auto. apply (sortedness_preserved__in_ghosttree BST tg);auto.
      iDestruct "Hadd" as ( tp o lp rp) "(info & Tree)".
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
       iPoseProof (node_data_split with "info") as "(info1 & info2)". 
        rewrite -> exp_sepcon2.  iExists lp. rewrite -> exp_sepcon2. iExists rp. rewrite -> exp_sepcon2. iExists o. simpl. rewrite <- sepcon_assoc.
        iFrame.
       iApply "Tclose". 
       iFrame.
       iSplit. iPureIntro;auto.
       unfold tree_rep2.
       iExists tg.
       iFrame;iSplit;auto.
       iApply "Tree".
       unfold node_information.
       iFrame.

 }
 Intro tp.
 Intros lp rp info. 
 forward_if.
 - intros. 
  forward_call (t_struct_tree, gv).
  { split; simpl; [ rep_omega | auto ]. }
  Intros p.
  forward.
 forward_call(v).
 Intro v1.
 forward.
 forward_call(vint 0).
 Intro lp1.
 forward.
 forward_call( vint 0).
 Intro rp1.
 forward.
 sep_apply node_data_R. subst. simpl. Intros.
 sep_apply cored_dup.
 forward_call (np, Ews, ref, (vint 0), p, top, empty,
        fun vp : val =>  Q *  (if eq_dec vp (vint 0) then  (emp) else ( EX o1: node_info, ghost_snap o1 g_current * bst_conc_nblocking_spec.atomic_ptr_at Ews (vint 0) rp1 * bst_conc_nblocking_spec.atomic_ptr_at Ews (vint 0) lp1 * bst_conc_nblocking_spec.atomic_ptr_at Ews v v1 * malloc_token Ews t_struct_tree p * data_at Ews t_struct_tree (vint x, (v1, (lp1, rp1))) p ))  *
          (iter_sepcon (λ info : own.gname * node_info,
        ghost_snap info.2 info.1) nodeinfos), inv_names).
        {  subst Frame; instantiate (1 := [AS && cored; mem_mgr gv; malloc_token Ews (tptr Tvoid) ref; nodebox_rep sh b g_root g]). unfold fold_right_sepcon. cancel.
            iIntros "((((((((([AS1 _] & rp1) & lp1) & v1 ) & token ) & p ) &P) &snap) & in)&snaps)".
            iMod ("AS1" with "P") as (BST) "[Tree Tclose]". 
           iDestruct "Tree" as "(% & Tree)".
          unfold tree_rep2 at 1.
          iDestruct "Tree" as (tg) "((% & Tree) & gref)".
         iPoseProof (node_exist_in_tree with "[gref in]") as "%". iFrame.
         iPoseProof ( extract_node_info_from_ghost_tree_rep_2 with "Tree") as "Hadd". eauto. intros. simpl;auto. apply (sortedness_preserved__in_ghosttree BST tg );auto.
        iDestruct "Hadd" as ( tp o1 l r) "(info & Tree)".
        unfold node_information at 1.
       iDestruct "info" as "(% & ((ap & master) & info))". 
       iModIntro; iExists Ews, tp; iFrame "ap".
       iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
       destruct (eq_dec tp (vint 0)).
       { (* iIntros "np".
       iDestruct "Tclose" as "[_ Tclose ]".
       iMod (ghost_master1_alloc with "[$]") as (g1) "lg".
        iMod (ghost_master1_alloc with "[$]") as (g2) "rg".
        instantiate(1 := (Finite_Integer x, n0, None)).
        instantiate(1 := (n, Finite_Integer x, None)).
        iFrame.  rewrite  sepcon_emp.
        iApply ("Tclose"  $! tt). simpl.
        iSplitL. iSplit. iPureIntro. apply insert_sorted. auto.
         iPoseProof ( bi.and_elim_l with "Tree") as "Tree".  iPoseProof ( bi.and_elim_r with "Tree") as "Tree".
         instantiate (1 := v).  instantiate (1 := x). 
        iSpecialize ("Tree" $! g1 g2 p).
        unfold tree_rep2. iExists  (insert_ghost x v tg g1 lp1 g2 rp1).
        iFrame.
        iCombine "snap" "master" as "master".
        iPoseProof (snap_master_join1 with "master") as "master". 
        iPoseProof (node_data_R with "info") as "info". 
        subst tp. iSimpl in "info". iDestruct "info" as "[% _]". admit. *)
        admit.
       }
        iIntros "np".
       iMod (snap_master_update1(ORD := range_order) _ _ _ (n, n0, o1) with "[$snap $master]") as "[snap master]".
       {  split. apply range_iteself. simpl. destruct o1;auto. }
        iDestruct "Tclose" as "[Tclose _]".
         iDestruct "in" as (sh2) "in".
       iMod (own_dealloc with "in") as "_". 
        rewrite -> exp_sepcon2.  rewrite exp_sepcon1. iExists (n,n0,o1). iFrame.
        iApply "Tclose". 
       iSplit. iPureIntro;auto.
       unfold tree_rep2.
       iExists tg.
       iFrame;iSplit;auto.
       iApply "Tree".
       unfold node_information.
       iFrame.
     } 
       
       
  
Admitted.


Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
start_function.
Admitted.



End Proofs.