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
| leaf l p =>
  data_at Ews tnode
          (Val.of_bool true,
           (vint (Zlength l),
            (Vnullptr,
             complete (2*param+1) (map (fun '(k, ptr) => (vint k, proj1_sig ptr)) l)))) p
| internal ptr0 l p =>
  data_at Ews tnode
          (Val.of_bool false,
           (vint (Zlength l),
            (node_address ptr0,
             complete (2*param+1) (map (fun '(k, n) => (vint k, node_address n)) l)))) p *
  node_rep ptr0 *
  iter_sepcon (node_rep ∘ snd) l
end.

Lemma node_valid_pointer (n: node):
    node_rep n |-- valid_pointer (node_address n).
Proof.
  destruct n;
  unfold node_rep; fold node_rep;
  auto with valid_pointer.
Qed.

Hint Resolve node_valid_pointer: valid_pointer.

Lemma node_rep_local_facts (n: node):
    node_rep n |-- !! isptr (node_address n).
Proof.
  destruct n; unfold node_rep; fold node_rep;
  entailer.
Qed.
  
Hint Resolve node_rep_local_facts: saturate_local.

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

Fixpoint cursor_entries {root: node} (c: cursor root): list (val * val) :=
match c with
| leaf_cursor l p _ _ i _ _ => [(vint i, p)]
| ptr0_cursor _ _ p c => (vint (-1), p) :: cursor_entries c
| le_child_cursor _ _ p _ _ i _ _ c => (vint i, p) :: cursor_entries c
end.

(* Several cursors can point to the same btree structure. *)
Definition cursor_rep {root: node} (level: Z) (c: cursor root) (p: val): mpred :=
  EX ptree: val,
  data_at Ews tcursor (ptree, (vint level,
                                force_lengthn (Z.to_nat max_depth) (cursor_entries c) (Vundef, Vundef))) p.
