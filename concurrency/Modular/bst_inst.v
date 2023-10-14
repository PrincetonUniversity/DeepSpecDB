Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import bst.puretree.
Require Import bst.bst.
Require Import bst.dataStruct.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* struct node {int key; void *value; struct tree_t *left, *right;} node;*)
Definition t_struct_tree := Tstruct _node noattr.

(* struct tree_t {node *t; lock_t *lock; int min; int max; } tree_t; *)
Definition t_struct_tree_t := Tstruct _tree_t noattr.

(* node_rep_R r.1.1.1 r.1.2 r.2 g, and r is type of node_info *)
#[local]Instance my_specific_tree_rep : NodeRep := {
  node_rep_R := fun tp r g_info g =>
    EX (ga gb : gname), EX (x : Z), EX (v pa pb : val), EX (locka lockb : val),
      !!(g_info = Some (Some (x, v, [pa; pb])) /\ and (Z.le Int.min_signed x) (Z.le x Int.max_signed) /\
       is_pointer_or_null pa /\ is_pointer_or_null locka /\
       is_pointer_or_null pb /\ is_pointer_or_null lockb /\
          (tc_val (tptr Tvoid) v) /\ key_in_range x r = true) &&
       data_at Ews t_struct_tree ((Vint (Int.repr x)), (v, (pa, pb))) tp * 
       malloc_token Ews t_struct_tree tp *
       in_tree g ga pa locka * in_tree g gb pb lockb
}.

Definition extract_node_pn (node: node_info) : list val :=
  match node.2 with
  | Some (Some (_, _, lst)) => lst
  | _ => []
  end.

(* Spec of findnext function *)
(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)
Definition findnext_spec :=
  DECLARE _findNext
  WITH x: Z, p: val, n: val, n_pt : val, tp: val, r : node_info, g: gname, sh: share, gv: globals
  PRE [ tptr tvoid, tptr (tptr tvoid), tint ]
          PROP (writable_share sh(*; is_pointer_or_null pa; is_pointer_or_null pb*) )
          PARAMS (p; n; Vint (Int.repr x)) GLOBALS (gv)
          SEP (node_rep_R r.1.1.1 r.1.2 r.2 g ;
               field_at sh (t_struct_tree_t) [StructField _t] r.1.1.1 p;
               data_at sh (tptr t_struct_tree_t) n_pt n)
  POST [ tint ]
  EX (stt: enum), EX (n' next : val),
         PROP (match stt with
               | F | NF => (n' = p)
               | NN => (n' = next)
               end)
        LOCAL (temp ret_temp (enums stt))
        SEP (match stt with
               | F | NF => data_at sh (tptr t_struct_tree_t) n_pt n
               | NN => !!(n' ∈ extract_node_pn r) && data_at sh (tptr t_struct_tree_t) next n
             end *
               node_rep_R r.1.1.1 r.1.2 r.2 g *
               field_at sh (t_struct_tree_t) [StructField _t] r.1.1.1 p).


Lemma findNext: semax_body Vprog Gprog f_findNext findnext_spec.
Proof.
  start_function.
  (* int y = pn->p->t->key *)
  forward.
  unfold node_rep_R.
  unfold my_specific_tree_rep.
  Intros ga gb x0 v0 pa pb locka lockb.
  repeat forward.
  forward_if. (* if (_x < _y) *)
  - (* pn->n = pn->p->t->left *)
    repeat forward.
    Exists NN pa pa.
    entailer !.
    unfold extract_node_pn.
    rewrite H.
    apply elem_of_list_here.
    Exists ga gb x0 v0 pa pb locka lockb.
    entailer !.
  - forward_if.
    (* pn->n = pn->p->t->right *)
    repeat forward.
    Exists NN pb pb.
    entailer !.
    unfold extract_node_pn.
    rewrite H.
    assert([pa ; pb] = [pa] ++ [pb]); auto.
    rewrite H13.
    rewrite elem_of_app. right.
    apply elem_of_list_here.
    Exists ga gb x0 v0 pa pb locka lockb.
    entailer !.
    forward.
    Exists F p n_pt.
    entailer !.
    Intros.
    Exists ga gb x0 v0 pa pb locka lockb.
    entailer !.
Qed.

Check enums.
Check tint.

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t: type, gv: globals
   PRE [ size_t ]
       PROP (and (Z.le 0 (sizeof t)) (Z.lt (sizeof t) Int.max_unsigned);
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ]
    EX p: _,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

Check enums.

Definition insertOp_spec :=
  DECLARE _insertOp
    WITH b: val, sh: share, x: Z, stt: Z,  v: val, p: val, tp: val, min: Z, max: Z, gv: globals
  PRE [ tptr tvoid, tint, tptr tvoid, tint ]
  PROP (writable_share sh; repable_signed min; repable_signed max; repable_signed x;
        is_pointer_or_null v )
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt))
  GLOBALS (gv)
  SEP (mem_mgr gv;
       (* data_at sh (t_struct_pn) (p, p) b; *)
       field_at Ews t_struct_tree_t (DOT _t) tp p;
       field_at Ews t_struct_tree_t (DOT _min) (Vint (Int.repr min)) p;
       field_at Ews t_struct_tree_t (DOT _max) (Vint (Int.repr max)) p )
  POST[ tvoid ]
  EX (pnt p1' p2' : val) (lock1 lock2 : val),
  PROP (pnt <> nullval)
  LOCAL ()
  SEP (mem_mgr gv;
       (* data_at sh t_struct_pn (p, p) b; *)
       field_at Ews t_struct_tree_t (DOT _t) pnt p;
       malloc_token Ews t_struct_tree pnt;
       malloc_token Ews t_struct_tree_t p1'; malloc_token Ews t_struct_tree_t p2';
       atomic_int_at Ews (vint 0) lock1; atomic_int_at Ews (vint 0) lock2;
       data_at Ews t_struct_tree (vint x, (v, (p1', p2'))) pnt;
       data_at Ews t_struct_tree_t (Vlong (Int64.repr 0), (lock2, (vint x, vint max))) p2';
       data_at Ews t_struct_tree_t (Vlong (Int64.repr 0), (lock1, (vint min, vint x))) p1';
       field_at Ews t_struct_tree_t (DOT _min) (vint min) p;
       field_at Ews t_struct_tree_t (DOT _max) (vint max) p).

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
     surely_malloc_spec; insertOp_spec (* ; traverse_spec; insert_spec; treebox_new_spec*) ]).
(* Proving insertOp satisfies spec *)
Lemma insertOp: semax_body Vprog Gprog f_insertOp insertOp_spec.
Proof.
  start_function.
  forward.
  forward_call (t_struct_tree_t, gv).
  Intros p1.
  forward_call (t_struct_tree_t, gv).
  Intros p2.
  forward.
  assert_PROP (field_compatible t_struct_tree_t [] p1) by entailer!.
  assert_PROP (field_compatible t_struct_tree_t [] p2) by entailer!.
  forward. 
  forward_call (gv).
  Intros lock1.
  forward.
  sep_apply atomic_int_isptr.
  Intros.
  forward_call release_nonatomic (lock1).
  forward_call (gv).
  Intros lock2.
  forward.
  Intros.
  forward_call release_nonatomic (lock2).
  (* make lock invariant *)
  forward_call (t_struct_tree, gv).
  Intros pnt.
  forward. forward. forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward. forward. forward.
  forward. 
  Exists pnt p1 p2 lock1 lock2.
  entailer !.
Qed.

