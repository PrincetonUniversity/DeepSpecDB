Require Import VST.floyd.functional_base VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import indices.ordered_interface.
Require Import btrees.btrees.
Require Import btrees.btrees_sep.
Require Import btrees.btrees_spec. 
Require Import indices.btree_wrappers.
Require Import indices.btree_normalized_funspecs.

Import OrderedIndex.


Definition bt_relation := btrees.relation val.
Definition bt_cursor := btrees.cursor val.

Definition btree_index : index :=
  {| key := btrees.key;
     key_val := fun k => (btrees_sep.key_repr k);
     key_type := size_t;

     t := relation val;
     t_type := trelation;

     (* replace numrec with environment? *)
     t_repr := fun m numrec => relation_rep m numrec;

     cursor := (bt_relation * bt_cursor)%type;

     cursor_repr := fun '(m, c) p numrec=> relation_rep m numrec * cursor_rep c m p;
     cursor_type := tcursor;

     (* helpers *)
     valid_cursor := fun '(m, c) => isValid c m;
     norm := fun '(m, c) => (m, normalize c m);
     get_num_rec_levels := get_numrec;

    (* interface *)

     cardinality := fun '(m, c) => get_depth m;

     create_cursor := fun m => (m, (first_cursor (get_root m)));

     (* can we replace these two pointers with an environment ? *)
     create := fun pr pn => (empty_relation pr pn);

     move_to_next := fun '(m, c) => (m, (RL_MoveToNext c m));

     move_to_previous := fun '(m, c) => (m, (RL_MoveToPrevious c m));

     go_to_key := fun '(m, c) k => (m, goToKey c m k);

     move_to_first := fun '(m, c) =>  let (n, p) := m in (m, moveToFirst n empty_cursor O);

     get_record := fun '(m, c) => RL_GetRecord c m;

     (* ptr is the pointer to the new entry (key, record). 
         newx is the new list of pointers for splitnode *)
     put_record := fun '(m, c) key record ptr newx => (*
                                  let (newc,newr) := RL_PutRecord c m key record ptr newx nullval in
                                  (newr, newc); *) (m,c);

     (* needs both C function and wrapper spec *)
     move_to_last := fun '(m, c) =>  let (n, p) := m in (m, moveToLast val n c (Zlength c));

   |}. 

(*Lemma sub_put_record: funspec_sub (put_record_spec btree_index)
    normalized_putRecord_funspec.
Proof. 
  unfold create_spec. 
  apply NDsubsume_subsume.
  { simpl. intros.
  split; extensionality x; reflexivity. }
  { split3; auto. intros [u gv].
    Exists (u, gv) emp.
    rewrite !insert_SEP. 
    apply andp_right. 
    entailer!. 
    entailer!. Exists pr pn. simpl. entailer!. }
Qed.*)

Lemma sub_move_to_last: funspec_sub (move_to_last_spec btree_index) 
    (btree_wrappers.RL_MoveToLast_spec).
Proof. 
  unfold move_to_last_spec. 
  apply NDsubsume_subsume.
  split; extensionality x; reflexivity.
  split3; auto.
  intros [[[[[r cur] p] n] numrec] gv].
  Exists (gv, p, (r, empty_cursor), numrec) emp.
  rewrite !insert_SEP. Intros. 
  apply andp_right. 
  { entailer!. simpl. entailer!. 
    { split.
      { clear -H8. destruct H8. f_equal.
        destruct r. simpl. unfold empty_cursor. simpl. auto. }
      { clear -H9. destruct r.  simpl. unfold empty_cursor in H9. auto. }}
    destruct r; simpl. entailer!. unfold empty_cursor. 
    rewrite Zlength_nil. cancel. }
  entailer!. unfold cursor_repr; simpl; cancel.
Qed.


Lemma sub_create: funspec_sub (create_spec btree_index)
    (snd btrees_spec.RL_NewRelation_spec).
Proof. 
  unfold create_spec. 
  apply NDsubsume_subsume.
  { simpl. intros.
  split; extensionality x; reflexivity. }
  { split3; auto. intros [u gv].
    Exists (u, gv) emp.
    rewrite !insert_SEP. 
    apply andp_right. 
    entailer!. 
    entailer!. Exists pr pn. simpl. entailer!. }
Qed.

Lemma sub_go_to_key: funspec_sub (go_to_key_spec btree_index)
    normalized_goToKey_funspec.
Proof. 
  unfold go_to_key_spec. 
  unfold normalized_goToKey_funspec.
  apply NDsubsume_subsume.
  { simpl. intros.
  split; extensionality x; reflexivity. }
  { split3; auto. intros [[[[c pc] r] key] numrec].
    Exists (r, c, pc, key, numrec) emp. 
    rewrite !insert_SEP. Intros.
    apply andp_right. 
    entailer!. simpl. entailer!.
    entailer!. simpl. cancel. }
Qed.

Lemma sub_get_record: funspec_sub (get_record_spec btree_index)
    normalized_getRecord_funspec.
Proof. 
  unfold get_record_spec. 
  unfold normalized_getRecord_funspec.
  apply NDsubsume_subsume.
  { simpl. intros.
  split; extensionality x; reflexivity. }
  { split3; auto. intros [[[r cur] pc] numrec].
    Exists (pc, (r, cur), numrec) emp. 
    rewrite !insert_SEP. Intros.
    apply andp_right. 
    entailer!. simpl. entailer!. 
    entailer!. simpl. cancel. }
Qed.

Lemma sub_create_cursor: funspec_sub (create_cursor_spec btree_index)
    normalized_newCursor_funspec.
Proof.
  unfold create_cursor_spec. 
  unfold normalized_newCursor_funspec.
  apply NDsubsume_subsume.
  { simpl. intros.
  split; extensionality x; reflexivity. }
  { split3; auto. intros [[r numrec] gv].
    Exists (r, numrec, gv, (getvalr r)) emp. 
    rewrite !insert_SEP. Intros.
    apply andp_right. 
    entailer!. Exists p'. simpl. entailer!.
    entailer!. simpl. cancel. }
Qed.

Lemma sub_move_to_next: funspec_sub (move_to_next_spec btree_index)
    normalized_moveToNext_funspec.
Proof. 
  unfold move_to_next_spec. 
  unfold normalized_moveToNext_funspec.
  apply NDsubsume_subsume.
  { simpl. intros.
  split; extensionality x; reflexivity. }
  split3; auto. 
  intros [[[cur p] r] numrec]. 
  Exists (p, (r, cur), numrec) emp. 
  rewrite !insert_SEP. Intros.
  apply andp_right. 
  entailer!. simpl.
  entailer!. unfold relation_mem._cursor.
  entailer!. unfold cursor_repr. simpl. entailer.
Qed.

Lemma sub_move_to_previous: funspec_sub (move_to_previous_spec btree_index) 
    normalized_moveToPrevious_funspec.
Proof. 
  unfold move_to_previous_spec.
  unfold normalized_moveToPrevious_funspec.
  apply NDsubsume_subsume.
  split; extensionality x; reflexivity.
  split3; auto.
  intros [[[cur p] r] numrec].
  Exists (p, (r, cur), numrec) emp.
  rewrite !insert_SEP. Intros.
  apply andp_right. 
  { entailer!. simpl. entailer!. }
  { entailer!. unfold cursor_repr; simpl; cancel. }
Qed.

Lemma sub_cardinality: funspec_sub (cardinality_spec btree_index)
  (snd btree_wrappers.RL_NumRecords_spec).
Proof.
  unfold move_to_next_spec. 
  apply NDsubsume_subsume.
  split; extensionality x; reflexivity.
  split3; auto.
  intros [[[r cur] p] numrec].
  Exists (p, (r, cur), numrec) emp.
  rewrite !insert_SEP. Intros. 
  apply andp_right. 
  { entailer!. simpl. entailer!. } 
  entailer!. unfold cursor_repr; simpl; cancel.
Qed.

Lemma sub_move_to_first: funspec_sub (move_to_first_spec btree_index) 
    (snd btree_wrappers.RL_MoveToFirst_spec).
Proof. 
  unfold move_to_first_spec. 
  apply NDsubsume_subsume.
  split; extensionality x; reflexivity.
  split3; auto.
  intros [[[[[r cur] p] n] numrec] gv].
  Exists (gv, p, (r, empty_cursor), numrec) emp.
  rewrite !insert_SEP. Intros. 
  apply andp_right. 
  { entailer!. simpl. entailer!. 
    { split.
      { clear -H8. destruct H8. f_equal.
        destruct r. simpl. 
        destruct (isValid (moveToFirst n empty_cursor 0) (n, v)); auto. }
      { clear -H9. destruct r.  simpl.
        destruct (isValid (moveToFirst n empty_cursor 0) (n, v)); auto. }}
    destruct r; simpl. entailer!. }
  entailer!. unfold cursor_repr; simpl; cancel. 
Qed.








