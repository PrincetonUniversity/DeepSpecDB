Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.progs.conclib.
Require Import btrees_functional.
Require Import btrees.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition tnode := Tstruct _node noattr.
Definition tentry:= Tstruct _entry noattr.
Definition tbtree := Tstruct _btree noattr.
Definition tcursor_entry := Tstruct _cursor_entry noattr.
Definition tcursor := Tstruct _cursor noattr.

Require Import Program.Basics. Require Import Program.Combinators.

Section Complete.

Definition complete MAX l := l ++ repeat (Vundef, Vundef) (Z.to_nat MAX - length l).

Lemma Znth_complete : forall n l MAX, n < Zlength l -> 
     Znth n (complete MAX l) = Znth n l.
Proof.
  intros; apply app_Znth1; auto.
Qed.

Lemma Zlength_complete : forall l m, Zlength l <= m -> Zlength (complete m l) = m.
Proof.
  intros; unfold complete.
  rewrite Zlength_app, Zlength_repeat; rewrite Zlength_correct in *; rep_omega.
Qed.

End Complete.

Fixpoint node_rep (n: node): mpred :=
malloc_token Ews tnode (node_address n) *
match n with
| leaf entries address =>
  data_at Ews tnode
          (Val.of_bool true,
           (vint (Zlength entries),
            (Vnullptr,
             complete (2*param+1) (map (fun '(k, ptr) => (vint k, proj1_sig ptr)) entries)))) address
| internal ptr0 entries address =>
  data_at Ews tnode
          (Val.of_bool false,
           (vint (Zlength entries),
            (node_address ptr0,
             complete (2*param+1) (map (fun '(k, n) => (vint k, node_address n)) entries)))) address *
  node_rep ptr0 *
  iter_sepcon (node_rep ∘ snd) entries
end.

Lemma node_valid_pointer (n: node):
    node_rep n |-- valid_pointer (node_address n).
Proof.
  destruct n; simpl;
  auto with valid_pointer.
Qed.

Hint Resolve node_valid_pointer: valid_pointer.

Lemma subnode_rep: forall child parent,
    subnode child parent ->
    node_rep parent = node_rep child * (node_rep child -* node_rep parent).
Proof.
  intros * h.
  apply pred_ext.
  + induction h.
    {
      inversion H; simpl.
      * cancel.
        rewrite <- wand_sepcon_adjoint.
        cancel.
      * apply In_Znth in H0.
        destruct H0 as [i [hbounds hznth]]. rewrite Zlength_map in hbounds.
        rewrite (iter_sepcon_Znth _ _ i) by assumption. simpl.
        rewrite Znth_map in hznth by assumption. rewrite hznth.
        cancel. rewrite <- wand_sepcon_adjoint. cancel. 
    }
    apply cancel_emp_wand, derives_refl.
    sep_apply IHh2. sep_apply IHh1.
    cancel. apply wand_frame_ver.
  + apply modus_ponens_wand.
Qed.

Lemma subnode_isptr (n: node):
    node_rep n |-- !! (forall m, subnode m n -> isptr (node_address m)).
Proof.
  eapply derives_trans. apply (allp_right _ (fun m => !! (subnode m n -> isptr (node_address m)))).
  intro m. eapply (derives_trans _ (!! subnode m n --> !! isptr (node_address m))).
  rewrite <- imp_andp_adjoint. Intros. erewrite subnode_rep by eassumption.
  destruct m; simpl; entailer.
  apply prop_imp_prop_left. apply allp_prop_left.
Qed.

Lemma node_rep_local_facts: forall n,
    node_rep n |-- !! (isptr (node_address n) /\
                       forall m, subnode m n -> isptr (node_address m)).
Proof.
  intro n. sep_apply subnode_isptr.
  entailer!. apply H. apply rt_refl.
Qed.

Lemma leaf_rep_local_facts: forall entries address,
    node_rep (leaf entries address) |-- !! (isptr address /\ Zlength entries <= 2 * param + 1).
Proof.
  intros. simpl. unfold_data_at (data_at _ _ _ address).
  rewrite (field_at_data_at _ _ [StructField _entries]). simpl.
  entailer!. rename H7 into h.
  unfold complete in h. rewrite Zlength_app, Zlength_map, Zlength_repeat, map_length in h.
  pose proof (Nat2Z.is_nonneg (Z.to_nat 17 - Datatypes.length entries)).
  rewrite <- h. 
  rewrite <- (Z.add_0_r (Zlength _)).
  apply Zplus_le_compat_l. assumption.
Qed.

Lemma internal_rep_local_facts: forall ptr0 entries address,
    node_rep (internal ptr0 entries address) |-- !! (isptr address /\ Zlength entries <= 2 * param + 1).
Proof.
  intros. simpl. unfold_data_at (data_at _ _ _ address).
  rewrite (field_at_data_at _ _ [StructField _entries]). simpl.
  entailer!. rename H7 into h.
  unfold complete in h. rewrite Zlength_app, Zlength_map, Zlength_repeat, map_length in h.
  pose proof (Nat2Z.is_nonneg (Z.to_nat 17 - Datatypes.length entries)).
  rewrite <- h. 
  rewrite <- (Z.add_0_r (Zlength _)).
  apply Zplus_le_compat_l. assumption.
Qed.

Hint Resolve node_rep_local_facts: saturate_local.

Hint Resolve leaf_rep_local_facts: saturate_local.

Hint Resolve internal_rep_local_facts: saturate_local.

Definition btree_rep {d} (root: node) (h: balanced d root) (p: val): mpred :=
  malloc_token Ews tbtree p
  * data_at Ews tbtree (node_address root, (vint (num_records root), vint d)) p
  * node_rep root.

Lemma btree_rep_local_facts {d} (n: node) (h: balanced d n) (p: val):
    btree_rep n h p |-- !! isptr p.
Proof.
  unfold btree_rep; entailer.
Qed.
  
Hint Resolve btree_rep_local_facts: saturate_local.

Lemma btree_valid_pointer {d} (n: node) (h: balanced d n) (p: val):
    btree_rep n h p |-- valid_pointer p.
Proof.
  unfold btree_rep. auto with valid_pointer.
Qed.

Hint Resolve btree_valid_pointer: valid_pointer.

(* Several cursors can point to the same btree structure. *)
Definition cursor_rep (k: K) (root: node) (p: val): mpred :=
  EX ptree: val,
            let path := find_path k root in
  data_at Ews tcursor (ptree,
                       (vint (Zlength path - 1),
                        complete max_depth (map (fun '(i, n) => (vint i, node_address n)) path))) p.

Definition partial_cursor_rep (k: K) (root: node) (level: Z) (p: val): mpred :=
  EX ptree: val,
  data_at Ews tcursor (ptree,
                       (vint level,
                        complete max_depth (map (fun '(i, n) => (vint i, node_address n)) (find_path k root)))) p.

Lemma cursor_rep_local_facts (k: K) (root: node) (p: val):
    cursor_rep k root p |-- !! (isptr p /\ Zlength (find_path k root) <= max_depth).
Proof.
  unfold cursor_rep. Intro ptree. unfold_data_at (data_at _ _ _ p).
  simpl.
  rewrite (field_at_data_at _ _ [StructField _ancestors]).
  simpl.
  entailer!. unfold complete in H4.
  rewrite Zlength_app, Zlength_map in H4. rep_omega.
Qed.
  
Hint Resolve cursor_rep_local_facts: saturate_local.
