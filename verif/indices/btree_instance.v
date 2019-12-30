Require Import VST.floyd.functional_base VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import indices.ordered_interface.
Require Import indices.definitions.
Require Import btrees.btrees.
Require Import btrees.btrees_sep.
Require Import btrees.btrees_spec. 
Require Import indices.btree_wrappers.

Import OrderedIndex.

Definition bt_relation := btrees.relation val.
Definition bt_cursor := btrees.cursor val.

Definition btree_index : index :=
  {| key := btrees.key;
     key_repr := fun sh k p => data_at sh (tptr tvoid) (btrees_sep.key_repr k) p;

     default_value := nullval;

     t := relation val;

     t_repr := fun sh m p => relation_rep m (get_depth m);

     cursor := (bt_relation * bt_cursor)%type;

     cursor_repr := fun '(m, c) p nr=> relation_rep m nr * cursor_rep c m p;
     cursor_type := tcursor;

     (* helper functions *)
     valid_cursor := fun '(m, c) => if (isValid c m) then true else false;

    (* interface functions *)

     cardinality := fun m => get_depth m;

     move_to_next := fun '(m, c) => (m, (RL_MoveToNext c m));

     move_to_previous := fun '(m, c) => (m, (RL_MoveToPrevious c m));

     move_to_key := fun '(m, c) k => let (n, p) := m in (m, moveToKey val n k c);

     move_to_first := fun '(m, c) =>  let (n, p) := m in (m, moveToFirst n c (length c));

     move_to_last := fun '(m, c) =>  let (n, p) := m in (m, moveToLast val n c (Zlength c));

   |}.

Lemma sub_move_to_next: funspec_sub (move_to_next_spec btree_index) 
    (snd btrees_spec.RL_MoveToNext_spec).
Proof. 
  unfold move_to_next_spec. simpl snd.
  apply NDsubsume_subsume.
  split; extensionality x; reflexivity.
  split3; auto.
  { unfold cursor_type; simpl. (* names? *) admit. }
  { intros [[[cur p] r] numrec].
    Exists (p, (r, cur), numrec) emp.
    rewrite !insert_SEP. Intros.
    apply andp_right. 
    entailer!. simpl. 
    entailer!.
    entailer!. admit.
    unfold cursor_repr. simpl.
    entailer!.
Admitted.


Lemma sub_move_to_first: funspec_sub (move_to_first_spec btree_index) 
    (snd btree_wrappers.RL_MoveToFirst_spec).
Proof. 
  unfold move_to_first_spec. simpl snd. 
  apply NDsubsume_subsume. 
  split; extensionality x; reflexivity.
  split3; auto.
  { unfold cursor_type; simpl. (* names? *) admit. }
  { admit. }
Admitted.


Lemma sub_move_to_last: funspec_sub (move_to_last_spec btree_index) 
    (snd btrees_spec.moveToLast_spec).
Proof.  
  unfold move_to_last_spec. simpl snd.
  apply NDsubsume_subsume. 
  split; extensionality x; reflexivity.
  split3; auto.
  { admit. }
  { admit. }
Admitted.



Lemma sub_move_to_prev: funspec_sub (move_to_previous_spec btree_index) 
    (snd btrees_spec.RL_MoveToPrevious_spec).
Proof. 
  unfold move_to_previous_spec. simpl snd.
  apply NDsubsume_subsume.
  split; extensionality x; reflexivity.
  split3; auto.
  { admit. }
  { admit. }
Admitted.







