Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import indices.db_client.
Require Import indices.db_cursor.
Require Import indices.ordered_interface.
Require Import indices.btree_instance.
Require Import indices.spec_BtreeIndexASI.
Require Import btrees.btrees_sep.
Require Import btrees.btrees_spec.
Require Import btrees.btrees.
Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import Coq.Init.Datatypes.
Require Import Coq.Strings.String.
Require Import FunInd.

Require Import indices.spec_db_client.

Import OrderedIndex.
Import DB_Cursor.

(* =============== HELPERS =============== *)

Definition attr_lst_node (s: string) (str_ptr: val) (d: Z) (q q0:val)  :=
  malloc_token Ews attr_lst q *
  data_at Ews attr_lst (str_ptr, (Vlong (Int64.repr d), q0)) q * string_rep s str_ptr *
  malloc_token Ews (tarray tschar (Z.of_nat (length s) + 1)) str_ptr.

Fixpoint unzip_attr_lst (lst: list(string *Z)) : list string :=
  match lst with
  | [] => @nil string
  | (s, z) :: t => s :: unzip_attr_lst t
  end.

Lemma cstring_to_string_rep : forall s p,
  cstring Ews (string_to_list_byte s) p = string_rep s p.
Proof.
  intros. unfold cstring. unfold string_rep.
  rewrite length_string_list_byte_eq. auto.
Qed.

Lemma unzip_distr: forall lst1 lst2,
  unzip_attr_lst (lst1 ++ lst2) = unzip_attr_lst lst1 ++ unzip_attr_lst lst2.
Proof.
  intros. induction lst1.
  { simpl. auto. }
  { simpl. destruct a. simpl. rewrite IHlst1. auto. }
Qed.

Lemma calc_indx_in_list: forall lst1 lst2 lst s z0,
  lst1 ++ (s, z0) :: lst2 = lst /\ ~ In s (unzip_attr_lst lst1) ->
  Zlength lst1 = calc_indx lst (id_index lst s).
Proof.
  intros. inversion H. clear H. subst.
  destruct lst1. 
  { simpl. rewrite eqb_refl.
    rewrite Zlength_nil. rewrite Zlength_cons. unfold Z.succ.
    rewrite Z.add_simpl_l. simpl. unfold calc_indx. 
    assert (K: 0 <= Zlength lst2). apply Zlength_nonneg.
    rewrite Zlength_cons. unfold Z.succ. cbn. 
    destruct (Zlength lst2). all: try simpl; auto. contradiction. }
  { destruct p; simpl in H1. apply Classical_Prop.not_or_and in H1.
    inversion H1; clear H1. rewrite Zlength_cons. unfold Z.succ.  
    simpl. apply not_eq_sym in H. apply eqb_neq in H. rewrite H.
    unfold calc_indx. 
    assert (K: id_index (lst1 ++ (s, z0) :: lst2) s = Zlength lst1).
    { induction lst1. simpl. assert (M: s=s) by reflexivity.
      rewrite <- eqb_eq in M. rewrite M. rewrite Zlength_cons. unfold Z.succ.
      rewrite Zlength_nil. rewrite Z.add_simpl_l. easy.
      simpl. destruct a. simpl in H0. apply Classical_Prop.not_or_and in H0.
      inversion H0; clear H0. apply not_eq_sym in H1. apply eqb_neq in H1.
      rewrite H1. apply IHlst1 in H2. rewrite H2. rewrite Zlength_cons.
      unfold Z.succ. apply Z.add_comm. }
      rewrite K. autorewrite with sublist. unfold Z.succ.
      assert (M: 1 + Zlength lst1 <> Zlength lst1 + (Zlength lst2 + 1) + 1).
      { unfold not; intros. clear -H1. rewrite Z.add_comm in H1. 
        rewrite <- OrdersEx.Z_as_OT.add_assoc in H1. 
        apply OrdersEx.Z_as_OT.add_reg_l in H1.
        assert (M: 0 <= Zlength lst2). apply Zlength_nonneg. 
        do 2 apply (@Zplus_le_compat_r _ _ 1) in M. simpl in M.
        rewrite <- H1 in M. contradiction. }
      rewrite <- Z.eqb_neq in M. rewrite M. apply Z.add_comm. }
Qed.

Lemma id_index_not_in_list: forall lst s,
  ~ In s (unzip_attr_lst lst) -> 
  id_index lst s = Zlength lst.
Proof.
  intros. induction lst.
  simpl. auto. destruct a; subst.
  simpl in H. apply Classical_Prop.not_or_and in H. 
  inversion H; clear H. simpl. rewrite Zlength_cons.
  unfold Z.succ. apply IHlst in H1. rewrite H1.
  apply not_eq_sym in H0. apply eqb_neq in H0.
  rewrite H0. apply Z.add_comm.
Qed.

Lemma calc_indx_not_in_list: forall lst s,
  ~ In s (unzip_attr_lst lst) -> 
  (- (1)) = calc_indx lst (id_index lst s).
Proof.
  intros. destruct lst. simpl. auto. 
  simpl. destruct p.
  assert (K: not (eq s s0)). simpl in H. 
  apply Classical_Prop.not_or_and in H. inversion H. 
  apply not_eq_sym. easy. apply eqb_neq in K. rewrite K.
  unfold calc_indx. simpl in H. 
  apply Classical_Prop.not_or_and in H. inversion H. clear H.
  apply id_index_not_in_list in H1.
  rewrite H1. rewrite Zlength_cons. unfold Z.succ.
  assert (M: 1 + Zlength lst = Zlength lst + 1) by (apply Z.add_comm).
  rewrite M. rewrite Z.eqb_refl. auto.
Qed.

Lemma fold_attr_lst_rep: forall str_ptr0 p' z0 q1 lst2 (s: string), 
  (string_rep s str_ptr0 * malloc_token Ews attr_lst p' *
  data_at Ews attr_lst (str_ptr0, (Vlong (Int64.repr z0), q1)) p' *
  malloc_token Ews (tarray tschar (Zlength (string_to_list_byte s) + 1)) str_ptr0 *
  attr_lst_rep lst2 q1)%logic |-- attr_lst_rep ((s, z0) :: lst2) p'.
Proof. 
  intros. unfold attr_lst_rep at 2. Exists q1 str_ptr0. fold attr_lst_rep. 
  rewrite length_string_list_byte_eq. cancel. 
Qed.

Lemma isptr_not_nullval: forall p, isptr p -> p <> nullval.
Proof.
  intros. destruct p; inversion H. unfold nullval. simpl. 
  unfold not. intros. inversion H0.
Qed.

Lemma root_integrity_empty_node: forall x0, 
  root_integrity (empty_node true true true x0).
Proof. 
  intros. unfold empty_node. 
  unfold root_integrity.
  intros. inversion H. subst. unfold node_integrity.
  split. auto. apply llen.
Qed.

(* ================ BODY PROOFS ================ *)

Lemma body_fill_relation:
  semax_body Vprog Gprog f_fill_relation (fill_relation_spec btree_index btree_cursor).
Proof. 
  start_function. Intros. unfold index_attr_rep. Intros attrs_ptr pk_attrs_ptr. forward.
  forward_call(attrs_ptr, attrs). 
  remember (Vptrofs (Ptrofs.repr (Zlength attrs))) as numcols. forward. deadvars!.
  forward. forward.
  unfold attr_lst_rep at 2. destruct pk_attrs.
  inversion H. inversion H0. 
  fold attr_lst_rep. destruct p as (id, domain). 
  Intros next_ptr id_ptr.
  forward_call(attrs, attrs_ptr, (id, domain):: pk_attrs, pk_attrs_ptr, id).
  unfold attr_lst_rep. entailer!. Exists next_ptr. Exists id_ptr. entailer!.
  split. easy. simpl. auto.
  forward. autorewrite with norm. deadvars!. 
  remember (Vlong (Int64.repr (Int.signed (Int.repr (calc_indx attrs (id_index attrs id)))))) as pk_num.
  assert (K: malloc_token Ews index_attr ip *
  data_at Ews index_attr (attrs_ptr, pk_attrs_ptr) ip * 
  attr_lst_rep attrs attrs_ptr * attr_lst_rep ((id, domain) :: pk_attrs) pk_attrs_ptr
   |-- index_attr_rep attrs ((id, domain) :: pk_attrs) ip).
  unfold index_attr_rep. Exists attrs_ptr pk_attrs_ptr. cancel.
  sep_apply K. clear K.
  inversion H; clear H. inversion H1. 
  forward_loop
   (EX i: Z, EX intercur: cursor btree_index, PROP(fill btree_index cur (sublist 0 i x) intercur)
   LOCAL (temp _i (Vlong (Int64.repr i)); temp _pk_num pk_num; temp _numcols numcols; gvars gv; temp _arr data_ptr; 
   temp _cur ws_ptr; temp _numrows (Vlong (Int64.repr numrows)))
   SEP (index_attr_rep attrs ((id, domain) :: pk_attrs) ip; mem_mgr gv; entry_array_rep data data_ptr;
   ord_mtable_rep (gv _btree_mtable); db_cursor_rep btree_index btree_cursor cur ws_ptr))
  (* break clause *)
  break:
  (EX i: Z, EX intercur: cursor btree_index, PROP(fill btree_index cur (sublist 0 i x) intercur)
   LOCAL (temp _i (Vlong (Int64.repr i)); temp _pk_num pk_num; temp _numcols numcols; gvars gv; temp _arr data_ptr; 
   temp _cur ws_ptr; temp _numrows (Vlong (Int64.repr numrows)))
   SEP (index_attr_rep attrs ((id, domain) :: pk_attrs) ip; mem_mgr gv; entry_array_rep data data_ptr;
   ord_mtable_rep (gv _btree_mtable); db_cursor_rep btree_index btree_cursor cur ws_ptr)).
  (* true before loop  - nothing has been inserted *)
  forward. Exists 0 cur. entailer!.
  (* true iteration - i items have been inserted *)
  Intros i intercur.
  forward_if.
  (* if false - continue inserting the next item *)
  { sep_apply entry_array_local_facts. forward.
    remember (force_val
               (sem_binary_operation' Oadd (tptr (Tunion _entry noattr)) tulong data_ptr
                  (eval_binop Omul tulong tulong (Vlong (Int64.repr i)) numcols))) as ptr_to_row.
    forward.
    remember (force_val
               (sem_binary_operation' Oadd (tptr (Tunion _entry noattr)) tulong data_ptr
                  (eval_binop Oadd tulong tulong
                     (eval_binop Omul tulong tulong (Vlong (Int64.repr i)) numcols) pk_num))) as key.
    unfold ord_mtable_rep.
    Intros ci cc c mtn mtf gtk chn pr gr. 
    forward. 
    (* forward_call : WITH cur: oi.(cursor), key:oi.(key), pkey: val, record:oi.(value), gv: globals,
            e_ptr: val, ws_ptr: val *)
    admit.
  }
  (* if true *)
  { forward. Exists numrows. admit. }
  (* after break *)
  Intros i intercur. admit.
Admitted.


Lemma body_malloc_btree_cursor:
  semax_body Vprog Gprog f_malloc_btree_cursor (malloc_btree_cursor_spec btree_index btree_cursor).
Proof. 
  start_function. unfold ord_mtable_rep. simpl.
  Intros ci cc c mtn mtf gtk chn pr gr.
  freeze [1; 5; 6; 7; 8; 9; 10; 11 ] FR1.
  forward. 
  forward_call(u, gv). admit. Intros vret; destruct vret. simpl. 
  Intros. forward. forward. destruct t0 as (r, rp). simpl in H, H0. subst.
  sep_apply relation_rep_local_prop. simpl. Intros. forward_call((r, v), gv, v). 
  simpl. entailer!. 
  simpl. inversion H. simpl in H0. inversion H0. 
  clear H H0. 
  unfold btrees_spec.empty_relation in H1. inversion H1. subst. 
  repeat split; try auto. apply isptr_not_nullval; auto.
  apply root_integrity_empty_node.
  Intros vret.
  forward. forward. Exists vret (r, v) v.
  entailer!. thaw FR1. simpl. unfold ord_mtable_rep.
  Exists ci cc c mtn mtf gtk chn pr gr. entailer!.
Admitted.

Lemma body_index_of_pk_column :
  semax_body Vprog Gprog f_index_of_pk_column index_of_pk_col_spec.
Proof.
  start_function.
  forward. destruct pk.
  { inversion H. contradiction. }
  { unfold attr_lst_rep at 2; fold attr_lst_rep.
    simpl in H. destruct p0. Intros q0 str_ptr.
    forward.
    forward_while
    (EX lst1: list (string * Z), EX lst2: list (string * Z), EX p': val,
     PROP ( lst1 ++ lst2 = lst /\ ~ In s (unzip_attr_lst lst1))
     LOCAL (temp _pk_ID str_ptr; temp _ind (Vint (Int.repr (Zlength lst1)));
     temp _lst p'; temp _pk q)
     SEP (attr_lst_hole_rep lst2 lst p' p; attr_lst_node s str_ptr z q q0;
     attr_lst_rep pk q0)).
     { Exists (@nil (string * Z)) lst p. unfold attr_lst_node.
       entailer!. unfold attr_lst_hole_rep. cancel.
       apply wand_refl_cancel_right. }
     { Intros. entailer!. unfold attr_lst_hole_rep.
       entailer!. }
     { inversion H. simpl in H2. subst.
       unfold attr_lst_hole_rep.
       destruct lst2. Intros. sep_apply attr_lst_local_facts.
       Intros. assert (K: (@nil (string * Z)) = (@nil (string * Z))). auto.
       inversion H2. apply H4 in K. contradiction.
       unfold attr_lst_rep at 1; fold attr_lst_rep. destruct p0.
       Intros q1 str_ptr0. forward.
       forward_call (str_ptr, (string_to_list_byte id), str_ptr0, (string_to_list_byte s)).
       { entailer!. unfold attr_lst_node. entailer!.
         do 2 rewrite cstring_to_string_rep. entailer!. }
       { clear H H1. Intros vret. destruct (Int.eq_dec vret Int.zero).
        { subst. forward_if.
          { forward. entailer!.
            { clear -H H0. apply list_byte_eq in H. subst. 
              erewrite calc_indx_in_list; try apply H0. auto. }
            { inversion H0. rewrite <- H14. unfold attr_lst_rep at 6.
              Exists q0 str_ptr. fold attr_lst_rep. 
              rewrite length_string_list_byte_eq.  
              do 2 rewrite cstring_to_string_rep. entailer!.
              clear. sep_apply fold_attr_lst_rep. 
              apply modus_ponens_wand. }}
           { inversion H1. }}
        { forward_if. forward. forward. entailer!.
          admit.
          forward. Exists ((lst1 ++[(s,z0)]), lst2, q1).
          entailer!. split3. simpl. auto.
          { rewrite <- app_assoc. simpl. easy. }
          { rewrite unzip_distr. simpl. unfold not.
            intros. apply in_app_or in H14. inversion H14.
            easy. apply list_byte_neq in H. 
            inversion H15. rewrite H16 in H. easy. auto. }
          { rewrite Zlength_app. auto. }
          { unfold attr_lst_node.
            do 2 rewrite cstring_to_string_rep. cancel.
            unfold attr_lst_hole_rep. cancel.
            apply wand_frame_intro'. rewrite length_string_list_byte_eq.
            sep_apply fold_attr_lst_rep. 
            cancel. apply modus_ponens_wand. }}}}
      { forward. unfold attr_lst_hole_rep. sep_apply attr_lst_local_facts.
        Intros. assert (K: nullval = nullval) by auto. apply H2 in K. subst. entailer!.
        { simpl in H; inversion H; subst. rewrite app_nil_r in H0. inversion H0; subst.
          apply calc_indx_not_in_list in H5. rewrite H5. auto. }
        { simpl. entailer!. Exists q0. Exists str_ptr. unfold attr_lst_node; cancel.
          rewrite emp_wand. cancel. }}}
Admitted.

Lemma body_attr_list_length:
  semax_body Vprog Gprog f_attr_list_length attr_list_length_spec.
Proof.
  start_function.
  forward.
  forward_while 
  (EX lst1: list (string * Z), EX lst2: list (string * Z), EX p0: val,
  PROP( lst1 ++ lst2 = l) 
  LOCAL(temp _length (Vptrofs (Ptrofs.repr (Zlength lst1))); temp _lst p0)
  SEP(attr_lst_hole_rep lst2 l p0 p)).
  { Exists (@nil (string * Z)) l p.
     entailer!. unfold attr_lst_hole_rep. entailer!.
     apply wand_refl_cancel_right. }
  { Intros. entailer!. unfold attr_lst_hole_rep.
    entailer!. }
  { forward. unfold attr_lst_hole_rep.
    destruct lst2. Intros. sep_apply attr_lst_local_facts.
    Intros. assert (K: (@nil (string * Z)) = (@nil (string * Z))). auto.
    inversion H0. apply H2 in K. contradiction.
    unfold attr_lst_rep at 1; fold attr_lst_rep. destruct p1. Intros q str_ptr.
    forward. Exists ((lst1 ++ [(s, z)]), lst2, q).
    entailer!.
    { split.
      { rewrite app_assoc_reverse. simpl. auto. } 
      { rewrite Zlength_app. cbn. easy. }}
    { unfold attr_lst_hole_rep. 
      entailer!. apply wand_frame_intro'.
      apply wand_sepcon_adjoint. apply wand_frame_intro'. 
      rewrite length_string_list_byte_eq.
      sep_apply fold_attr_lst_rep.
      sep_apply modus_ponens_wand. cancel. }}
     { forward. unfold attr_lst_hole_rep.
       sep_apply attr_lst_local_facts. Intros. 
       assert (K: nullval = nullval). auto. apply H in K. subst.
       entailer!. rewrite <- app_nil_end. auto.
       apply modus_ponens_wand. }
Qed.

Lemma body_btree_create_index: 
  semax_body Vprog Gprog f_btree_create_index btree_create_index_spec.
Proof.
  start_function.
  forward_call (u, gv). 
  Intros vret. forward.
  Exists (fst vret) (snd vret).
  entailer!.
Qed.

Lemma body_btree_put_record: 
  semax_body Vprog Gprog f_btree_put_record btree_put_record_spec.
Proof.
  start_function. Intros.
  forward. forward.
  simpl. Intros tree_ptr cur_ptr. forward.
  { destruct cur. Intros. sep_apply cursor_rep_local_prop.
    entailer!. }
  unfold entry_rep_int. Intros. forward.
  forward_call (cur, cur_ptr, key, pkey, record, gv).
  { simpl. entailer!. }
  Intros vret. Exists vret. entailer!. simpl.
  Exists tree_ptr cur_ptr. entailer!.
  unfold entry_rep_int. cancel.
Qed.

Lemma body_btree_go_to_key: 
  semax_body Vprog Gprog f_btree_go_to_key btree_go_to_key_spec.
Proof.
  start_function.
  Intros. forward. 
  forward. simpl. Intros tree_ptr cur_ptr. forward.
  { destruct cur. Intros. sep_apply cursor_rep_local_prop.
    entailer!. }
  unfold entry_rep_int.
  Intros. forward. 
  forward_call (cur, cur_ptr, key, nullval).
  { destruct cur. unfold cursor_repr; simpl.
    entailer!. }
  Intros. forward. destruct cur.
  forward_call ((b, (btrees.goToKey b0 b key)), cur_ptr).
  { unfold cursor_repr; simpl. entailer!. }
  { simpl in *. split3; try easy.
    apply verif_putrecord.gotokey_complete. easy. }
  forward. entailer!. 
  simpl. Exists tree_ptr cur_ptr. entailer!. 
  unfold entry_rep_int. cancel.
Qed.

Lemma body_btree_create_cursor: 
  semax_body Vprog Gprog f_btree_create_cursor btree_create_cursor_spec.
Proof.
  start_function.
  forward. simpl. Intros.
  forward_call(btree_cursor_t, gv). 
  split3; easy. Intros vret. 
  forward_if (PROP ( )
  LOCAL (temp _cursor vret; temp _tree t_ptr; gvars gv; temp _env t_ptr)
  SEP (mem_mgr gv; malloc_token Ews btree_cursor_t vret * data_at_ Ews btree_cursor_t vret;
  relation_rep r))%assert; try if_tac; try entailer!.
  { forward. entailer!. }
  { forward. entailer!. }
  { admit. }
  { contradiction. }
  Intros. forward.
  forward_call (r, gv, t_ptr). 
  simpl; entailer!.
  Intros vret0. forward. forward.
  Exists vret.
  entailer!. rewrite <- wand_sepcon_adjoint.
  assert (K: t_repr btree_index r (snd r) * 
  (t_repr btree_index r (snd r) -* cursor_repr btree_index (create_cursor btree_index r) vret0) 
  |-- cursor_repr btree_index (create_cursor btree_index r) vret0).
  sep_apply modus_ponens_wand. cancel. 
  sep_apply K. simpl. Exists (snd r) vret0. entailer!.
Admitted. 

Lemma body_btree_get_record: 
  semax_body Vprog Gprog f_btree_get_record btree_get_record_spec.
Proof.
  start_function.
  forward. simpl. Intros tree_ptr cur_ptr. forward.
  destruct cur. Intros. sep_apply cursor_rep_local_prop.
  entailer!.
  forward_call (cur_ptr, cur).
  simpl. entailer!. Intros vret. forward.
  Exists vret.
  simpl. Exists tree_ptr cur_ptr. entailer!.
Qed.

Lemma body_btree_move_to_first: 
  semax_body Vprog Gprog f_btree_move_to_first btree_move_to_first_spec.
Proof.
  start_function.
  forward. simpl. Intros tree_ptr cur_ptr. forward.
  destruct cur. Intros. sep_apply cursor_rep_local_prop.
  entailer!.
  forward_call (gv, cur_ptr, cur).
  simpl. entailer!. forward.
  simpl; entailer!. Exists tree_ptr cur_ptr.
  cancel.
Qed.

Lemma body_btree_move_to_next: 
  semax_body Vprog Gprog f_btree_move_to_next btree_move_to_next_spec.
Proof.
  start_function.
  forward. simpl. Intros tree_ptr cur_ptr. forward.
  destruct cur. Intros. sep_apply cursor_rep_local_prop.
  entailer!.
  forward_call (cur_ptr, cur).
  simpl. entailer!. forward.
  simpl; entailer!.
  Exists tree_ptr cur_ptr. cancel.
Qed.

Lemma body_btree_cursor_has_next: 
  semax_body Vprog Gprog f_btree_cursor_has_next btree_cursor_has_next_spec.
Proof.
  start_function.
  forward. simpl. Intros tree_ptr cur_ptr. forward.
  destruct cur. Intros. sep_apply cursor_rep_local_prop.
  entailer!.
  forward_call (cur, cur_ptr).
  simpl. entailer!. forward.
  simpl; entailer!.
  Exists tree_ptr cur_ptr. cancel.
Qed.

Lemma body_btree_cardinality: 
  semax_body Vprog Gprog f_btree_cardinality btree_cardinality_spec.
Proof.
  start_function.
  forward. simpl. Intros tree_ptr cur_ptr. forward.
  destruct cur. Intros. sep_apply cursor_rep_local_prop.
  entailer!.
  forward_call (cur_ptr, cur).
  simpl. entailer!. forward.
  simpl; entailer!.
  Exists tree_ptr cur_ptr. cancel.
Qed.
