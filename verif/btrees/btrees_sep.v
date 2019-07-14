Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.progs.conclib.
Require Import btrees_functional.
Require Import btrees.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_node := Tstruct _node noattr.
Definition t_entry:= Tstruct _entry noattr.
Definition t_btree := Tstruct _btree noattr.
Definition t_cursor_entry := Tstruct _cursor_entry noattr.
Definition t_cursor := Tstruct _cursor noattr.

Require Import Program.Basics. Require Import Program.Combinators.

Fixpoint node_rep {d} (n: node d): mpred :=
match n with
| leaf l p =>
  EX b: val,
  !! typed_true tuchar b &&
  malloc_token Ews t_node p *
  data_at Ews t_node
          (b,
           (vint (Zlength l),
            (Vnullptr,
             force_lengthn (2*param+1) (map (fun '(k, ptr) => (vint k, proj1_sig ptr)) l) (Vundef, Vundef)))) p

| internal _ ptr0 l p as n =>
  EX b: val,
  !! typed_false tuchar b &&
  malloc_token Ews t_node p *
  data_at Ews t_node
          (b,
           (vint (Zlength l),
            (address ptr0,
             force_lengthn (2*param+1) (map (fun '(k, n) => (vint k, address n)) l) (Vundef, Vundef)))) p *
  node_rep ptr0 *
  iter_sepcon (node_rep ∘ snd) l
end.

Lemma node_rep_local_facts {d} (n: node d):
    node_rep n |-- !! isptr (address n).
Proof.
  destruct n; cbn; entailer.
Qed.
  
Hint Resolve node_rep_local_facts: saturate_local.

Lemma node_valid_pointer {d} (n: node d):
    node_rep n |-- valid_pointer (address n).
Proof.
  destruct n; cbn; entailer.
Qed.

Hint Resolve node_valid_pointer: valid_pointer.

Definition btree_rep {d} (root: node d) (p: val): mpred :=
  malloc_token Ews t_btree p
  * data_at Ews t_btree (address root, (vint (num_records root), vint d)) p
  * node_rep root.

Lemma btree_rep_local_facts {d} (n: node d) (p: val):
    btree_rep n p |-- !! isptr p.
Proof.
  unfold btree_rep; entailer.
Qed.
  
Hint Resolve btree_rep_local_facts: saturate_local.

Lemma btree_valid_pointer {d} (n: node d) (p: val):
    btree_rep n p |-- valid_pointer p.
Proof.
  unfold btree_rep. auto with valid_pointer.
Qed.

Hint Resolve btree_valid_pointer: valid_pointer.

Fixpoint cursor_entries {d} {root: node d} (c: cursor root): list (val * val) :=
match c with
| leaf_cursor l p _ _ i _ _ => [(vint i, p)]
| ptr0_cursor _ _ _ p c => (vint (-1), p) :: cursor_entries c
| le_child_cursor _ _ _ p _ _ i _ _ c => (vint i, p) :: cursor_entries c
end.

(* Several cursors can point to the same btree structure. *)
Definition cursor_rep {d} {root: node d} (c: cursor root) (p: val): mpred :=
  EX ptree: val,
  data_at Ews t_cursor (ptree, (vint d,
                                force_lengthn max_depth (cursor_entries c) (Vundef, Vundef))) p.
