Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
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
      !!(g_info = Some (Some (x, v)) /\ and (Z.le Int.min_signed x) (Z.le x Int.max_signed) /\
       is_pointer_or_null pa /\ is_pointer_or_null locka /\
       is_pointer_or_null pb /\ is_pointer_or_null lockb /\
          (tc_val (tptr Tvoid) v) /\ key_in_range x r = true) &&
       data_at Ews t_struct_tree ((Vint (Int.repr x)), (v, (pa, pb))) tp * 
       malloc_token Ews t_struct_tree tp *
       in_tree g ga pa locka * in_tree g gb pb lockb
}.


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
        SEP (node_rep_R r.1.1.1 r.1.2 r.2 g *
               field_at sh (t_struct_tree_t) [StructField _t] r.1.1.1 p *
                data_at sh (tptr t_struct_tree_t) next n).


Lemma findNext: semax_body Vprog Gprog f_findNext findnext_spec.
Proof.
  start_function.
  (* int y = pn->p->t->key *)
  forward. 
  unfold node_rep_R.
  simpl.
  Intros ga gb x0 v0 pa pb locka lockb.
  forward.
  forward.
  forward.
  forward_if. (* if (_x < _y) *)
  - (* pn->n = pn->p->t->left *)
    repeat forward.
    Exists NN pa pa.
    entailer !.
    Exists ga gb x0 v0 pa pb locka lockb.
    entailer !.
  - forward_if.
    (* pn->n = pn->p->t->right *)
    repeat forward.
    Exists NN pb pb.
    entailer !.
    simpl.
    Exists ga gb x0 v0 pa pb locka lockb.
    entailer !.
    forward.
    Exists F p n_pt.
    entailer !.
    Exists ga gb x0 v0 pa pb locka lockb.
    entailer !.
Qed.


