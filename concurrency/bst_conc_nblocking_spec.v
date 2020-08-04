Require Import VST.progs.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import bst.bst_conc_nblocking.
Require Import bst.bst_conc_lemmas.
Require Import VST.atomics.general_locks.
Require Import VST.atomics.SC_atomics.
Require Import Coq.Sets.Ensembles.
Require Import VST.msl.iter_sepcon.

 Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.


Definition atomic_ptr := Tstruct _atom_ptr noattr.
Variable atomic_ptr_at : share -> val -> val -> mpred.
Hypothesis atomic_ptr_at__ : forall sh v p, atomic_ptr_at sh v p |-- atomic_ptr_at sh Vundef p.
Definition t_struct_tree := Tstruct _tree noattr.

Section Specifications.

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:type, gv: globals
   PRE [ _n OF tuint ]
       PROP (0 <= sizeof t <= Int.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       LOCAL (temp _n (Vint (Int.repr (sizeof t))); gvars gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

Fixpoint ghost_tree_rep (t: @ ghost_tree val ) (nb:val) (g_current:gname) (g:gname) range : mpred := 
 match t, range with
 | E_ghost , _ => atomic_ptr_at Ews nullval nb * ghost_master1 (ORD := range_order)  (range,  (@None ghost_info)) g_current 
 | (T_ghost a ga lp x v b gb rp ), (l, r) =>  EX tp, EX sh, !!(readable_share sh) && atomic_ptr_at Ews tp nb * data_at sh t_struct_tree (Vint (Int.repr x),(v,(lp,rp))) tp * ghost_master1 (ORD := range_order)  (range,  (@Some ghost_info (x,v,ga,gb))) g_current * in_tree ga (l, Finite_Integer x) lp g * in_tree gb ( Finite_Integer x, r) rp g *  ghost_tree_rep a  lp ga g (l, Finite_Integer x) * ghost_tree_rep b rp gb g (Finite_Integer x, r)
 end.

Definition tree_rep2 (g:gname) (g_root: gname) (nb:val) (sh:share) (t: @tree val  ) : mpred := EX (tg:ghost_tree), !! (find_pure_tree tg = t) && ghost_tree_rep tg  nb g_root g (Neg_Infinity, Pos_Infinity) 
                                                                                                                                 * bst_conc_lemmas.ghost_ref g (find_ghost_set tg g_root ( Neg_Infinity, Pos_Infinity) nb).

Definition nodebox_rep (sh : share) (nb: val) (g_root: gname) (g:gname)  :=  EX tp:val, EX lp: list val,  atomic_ptr_at sh tp nb * iter_sepcon ( fun p => EX sh1:share, data_at_ sh1 t_struct_tree p ) lp * in_tree g_root (Neg_Infinity, Pos_Infinity) nb g.
 

Program Definition insert_spec :=
  DECLARE _insert
  ATOMIC TYPE (rmaps.ConstType ( val * share * Z * val * globals*gname* gname)) OBJ BST INVS base.empty base.top
  WITH  b, sh, x, v, gv, g, g_root
  PRE [  _tb OF (tptr atomic_ptr), _x OF tint,  _value OF (tptr tvoid) ]
          PROP (readable_share sh;Int.min_signed <= x <= Int.max_signed;  is_pointer_or_null v )
          LOCAL (temp _tb b; temp _x (Vint (Int.repr x)); temp _value v; gvars gv )
          SEP  (mem_mgr gv; nodebox_rep sh b g_root g ) | (!!(sorted_tree BST)&&tree_rep2 g g_root b sh  BST )
  POST[ tvoid  ]
        PROP ()
        LOCAL ()
       SEP (mem_mgr gv; nodebox_rep sh b g_root g) | (!!(sorted_tree (bst_conc_lemmas.insert x v BST))&&tree_rep2 g g_root  b sh (bst_conc_lemmas.insert x v BST) ). 

Program Definition lookup_spec :=
  DECLARE _lookup
  ATOMIC TYPE (rmaps.ConstType ( val * share* Z * globals * gname * gname))
         OBJ BST INVS base.empty base.top
  WITH b, sh, x, gv, g, g_root
  PRE [_tb OF (tptr atomic_ptr), _x OF tint]
    PROP (
          Int.min_signed <= x <= Int.max_signed)
    LOCAL (temp _tb b; temp _x (Vint (Int.repr x)); gvars gv)
    SEP  (mem_mgr gv; nodebox_rep sh b g_root g) |
  (!! sorted_tree BST && tree_rep2 g g_root b sh BST)
  POST [tptr Tvoid]
    EX ret: val,
    PROP ()
    LOCAL (temp ret_temp ret)
    SEP (mem_mgr gv; nodebox_rep sh b g_root g) |
        (!! (sorted_tree BST /\ ret = (bst_conc_lemmas.lookup nullval x BST)) && tree_rep2 g g_root b sh BST).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt nil gv
  POST [ tint ] main_post prog nil gv.
  
  Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release2_spec := DECLARE _release2 release2_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition atomic_load_ptr_spec := DECLARE _atomic_load_ptr (atomic_load_ptr_spec atomic_ptr atomic_ptr_at).
Definition atomic_store_ptr_spec := DECLARE _atomic_store_ptr (atomic_store_ptr_spec atomic_ptr atomic_ptr_at).
Definition atomic_CAS_ptr_spec := DECLARE _atomic_CAS_ptr (atomic_CAS_ptr_spec atomic_ptr atomic_ptr_at).
Definition make_atomic_ptr_spec := DECLARE _make_atomic_ptr ( make_atomic_ptr_spec atomic_ptr atomic_ptr_at).

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release2_spec; makelock_spec;
    freelock2_spec;
    surely_malloc_spec; 
    atomic_load_ptr_spec;
    atomic_store_ptr_spec;
    atomic_CAS_ptr_spec;
    make_atomic_ptr_spec;
    (* treebox_new_spec; *)
    insert_spec;
    lookup_spec;
    spawn_spec;
    main_spec 
  ]).
  
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
Exists sh1 sh2. rewrite <- (ghost_part_join (P:= map_PCM (A:= gname ) ) sh1 sh2 sh  (ghosts.singleton  (P:= prod_PCM range_ghost (discrete_PCM val)) g_in (range, p))  (ghosts.singleton  (P:= prod_PCM range_ghost (discrete_PCM val))  g_in (range, p))).
cancel. auto. { unfold sepalg.join. hnf. intro. hnf. simpl. destruct (ghosts.singleton (P:= prod_PCM range_ghost (discrete_PCM val)) g_in (range, p) k). 
  -  apply psepalg.lower_Some. unfold sepalg.join. hnf. split; hnf. rewrite merge_self;auto. split;auto.
  - apply psepalg.lower_None1. 
  } auto. auto. 
 Qed.
 
Notation empty := (@empty coPset _).
Notation top := (@top coPset _).

Definition node_data (info: option ghost_info) g  tp lp rp (range:number * number)  :=  
(match info with Some data =>  EX sh, !!(readable_share sh) &&  data_at sh t_struct_tree (Vint (Int.repr data.1.1.1),(data.1.1.2,(lp,rp))) tp * in_tree  data.1.2 ( fst range, Finite_Integer (data.1.1.1)) lp g * in_tree data.2 ( Finite_Integer (data.1.1.1), snd range) rp g | None => !!(tp = nullval) && emp end).
 

Definition node_information (info: option ghost_info) range g g_current tp lp rp np  :=  bst.bst_conc_nblocking_spec.atomic_ptr_at Ews tp np * ghost_master1 (ORD := range_order)  (range, info) g_current * 
node_data info g tp lp rp range.

Lemma node_data_split : forall (info: option ghost_info) g  tp lp rp (range:number *number), node_data info g tp lp rp range |-- node_data info g tp lp rp range * node_data info g tp lp rp range.
Proof.
intros.
unfold node_data; destruct info.
 - Intros sh. apply split_readable_share in H. destruct H as (sh1 & sh2 & H1 & H2 & H3). rewrite <- (data_at_share_join sh1 sh2 sh _ _ _).  
    sep_apply (in_tree_split g0.1.2 ( range.1, Finite_Integer (g0.1.1.1)) lp g). sep_apply ( in_tree_split g0.2 ( Finite_Integer g0.1.1.1, range.2) rp g ). rewrite <- !sepcon_assoc. Exists sh1 sh2.  entailer!. auto.
- entailer!. 
Qed.


Lemma extract_left_node_info_from_ghost_tree_rep:  forall  tg np b g_root g_current g (r_root: number * number) (range:number*number),
   (find_ghost_set tg g_root r_root b) g_current = Some (range,np) -> ghost_tree_rep tg b g_root g r_root  |--  EX tp:val,  EX o:option ghost_info, EX lp:val, EX rp:val, 
    node_information o range g g_current tp lp rp np  *
   ( node_information o range g g_current tp lp rp np  -* ghost_tree_rep tg b g_root g r_root).
Proof.
 intros.
revert dependent b.
revert dependent g_root.
revert dependent r_root.
induction tg;intros. 
  -  inv H. destruct r_root. destruct range. unfold ghosts.singleton in H1. Exists nullval.  Exists (@None ghost_info) nullval nullval. unfold node_information;simpl. simpl in *. entailer!.  destruct (eq_dec g_current g_root). inv H1. cancel;apply wand_refl_cancel_right. discriminate.
  -  intros. simpl in H. unfold map_upd in H. destruct (eq_dec g_current g_root). 
     * inv H. destruct range. simpl in *.  Intros tp sh. Exists  tp (Some ( k, v0, g0, g1)) v v1. unfold node_information. simpl in *. Exists sh. entailer!.  rewrite <- wand_sepcon_adjoint. Intro sh1. Exists tp sh1. entailer!.
     * unfold map_add in H. destruct r_root. simpl in *. remember (find_ghost_set tg1 g0 (n0, Finite_Integer k) v g_current) as left_set. destruct left_set.
        ** Intros rtp sh. sep_apply IHtg1. rewrite <- Heqleft_set. apply H.  Intros tp o lp rp. Exists tp o lp rp. entailer!. 
             rewrite -> 5sepcon_assoc.  rewrite <- (emp_wand (bst_conc_nblocking_spec.atomic_ptr_at Ews rtp b * _)) . rewrite wand_sepcon_wand. apply wand_derives.
             rewrite -> sepcon_emp;auto. Exists rtp sh. entailer!.
        ** Intros rtp sh. sep_apply IHtg2.  Intros tp o lp rp. Exists tp o lp rp. entailer!. 
             rewrite -> 5sepcon_assoc.  rewrite <- (emp_wand (bst_conc_nblocking_spec.atomic_ptr_at Ews rtp b * _)) . rewrite wand_sepcon_wand. apply wand_derives.
             rewrite -> sepcon_emp;auto. Exists rtp sh. entailer!.

Qed.


Lemma extract_node_info_from_ghost_tree_rep_2:  forall  tg np b g_root x v g_current g (r_root: number * number) n n0, 
  (find_ghost_set tg g_root r_root b) g_current = Some (n,n0,np)-> (forall k, In_ghost k tg -> check_key_exist' k r_root = true) -> sorted_ghost_tree tg-> ghost_tree_rep tg b g_root g r_root  |--  EX tp:val,  EX o:option ghost_info, EX lp:val, EX rp:val, 
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
 - intros. destruct r_root. simpl in H. unfold ghosts.singleton in H.  destruct (eq_dec g_current g_root). inv H. Exists nullval (@None ghost_info) nullval nullval. unfold node_information at 1, node_data at 1. simpl. entailer!.
  { rewrite less_than_equal_itself. rewrite less_than_equal_itself. repeat (split;auto). } repeat apply andp_right.
    * unfold node_information, node_data;simpl. entailer!.  apply wand_refl_cancel_right.
    *  apply allp_right; intro g1. apply allp_right;intro g2. apply allp_right;intro tp1.  rewrite <- wand_sepcon_adjoint. unfold node_information, node_data;simpl. Intro sh.  rewrite <-!sepcon_assoc. Exists tp1 sh. cancel. entailer!. apply InEmptyGhostTree;auto.
    *  apply allp_right; intro g1. apply allp_right;intro g2. apply allp_right;intro v0.  rewrite <- wand_sepcon_adjoint. Intros. 
    * discriminate.
 - intros.  simpl in H. unfold map_upd in H. destruct (eq_dec g_current g_root) eqn: Eqn.
   * inv H. simpl. Intros tp sh.  Exists  tp (Some (k, v1, g0, g1)) v0 v2.  unfold node_information at 1, node_data at 1. Exists sh. entailer!. repeat rewrite less_than_equal_itself. simpl;auto. cancel.  repeat  apply andp_right.
     +   rewrite <- wand_sepcon_adjoint. unfold node_information, node_data. simpl.  Intro sh1. Exists  tp sh1. entailer!.
     + apply allp_right; intro g2. apply allp_right;intro g3. apply allp_right;intro tp1. rewrite <- wand_sepcon_adjoint. Intros a.
     + apply allp_right; intro g2. apply allp_right;intro g3. apply allp_right;intro vp. rewrite <- wand_sepcon_adjoint. assert_PROP (Some (k, v1, g0, g1) = Some (x, vp, g2, g3)). { entailer!. } inv H4;subst. simpl.
      destruct (x <? x) eqn: E1. apply Z.ltb_lt in E1. omega. simpl. unfold node_information, node_data. Intro sh1.  entailer!. apply InRoot_ghost. auto. Exists tp sh1. simpl. entailer!.
 * unfold map_add in H. rename n1 into eq. destruct r_root as [n1 n2]. simpl in H. remember (find_ghost_set tg1 g0 (n1, Finite_Integer k) v0 g_current) as left_set. destruct left_set.  rename g2 into g_left.
    ** simpl.  Intros tp sh. destruct (x <? k) eqn: E1.
        + simpl. inv H1.  sep_apply IHtg1. rewrite <- Heqleft_set;apply H.
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
       +  simpl. inv H1. sep_apply IHtg1.  rewrite <- Heqleft_set;apply H.
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
  ** simpl. Intros tp sh. destruct (x <? k) eqn: E1.
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
EX data, EX sh, !!(readable_share sh/\ info = Some data) &&  data_at sh t_struct_tree (Vint (Int.repr data.1.1.1),(data.1.1.2,(lp,rp))) tp * in_tree data.1.2( fst range, Finite_Integer data.1.1.1) lp g * in_tree data.2 ( Finite_Integer data.1.1.1, snd range) rp g.
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
  End Specifications.

  