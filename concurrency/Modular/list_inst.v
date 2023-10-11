Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.puretree.
Require Import bst.list.
Require Import bst.dataStruct.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* struct node {int key; void *value; struct tree_t *left, *right;} node;*)
Definition t_struct_list := Tstruct _node noattr.

(* struct tree_t {node *t; lock_t *lock; int min; int max; } tree_t; *)
Definition t_struct_list_t := Tstruct _list_t noattr.

(* node_rep_R r.1.1.1 r.1.2 r.2 g, and r is type of node_info *)
#[local]Instance my_specific_tree_rep : NodeRep := {
    node_rep_R :=
      fun tp r g_info g =>
      if eq_dec tp nullval
      then !!(g_info = Some None) && seplog.emp
      else (
    EX (gn : gname), EX (x : Z), EX (v next : val), EX (lockn : val),
      !!(g_info = Some (Some (x, v, [gn])) /\ and (Z.le Int.min_signed x) (Z.le x Int.max_signed) /\
       is_pointer_or_null next /\ is_pointer_or_null lockn /\
          (tc_val (tptr Tvoid) v) /\ key_in_range x r = true) &&
       data_at Ews t_struct_list ((Vint (Int.repr x)), (v, next)) tp *
       malloc_token Ews t_struct_list tp *
       in_tree g gn next lockn)
}.

Definition extract_node_gname (node: node_info) : list gname :=
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
          PROP (writable_share sh)
          PARAMS (p; n; Vint (Int.repr x)) GLOBALS (gv)
          SEP (node_rep_R r.1.1.1 r.1.2 r.2 g ;
               field_at sh (t_struct_list_t) [StructField _t] r.1.1.1 p;
               data_at sh (tptr t_struct_list_t) n_pt n)
  POST [ tint ]
  EX (stt: enum), EX (n' next : val) (g_in : gname),
         PROP (match stt with
               | F | NF => (n' = p)
               | NN => (n' = next)
               end)
        LOCAL (temp ret_temp (enums stt))
        SEP (!!(g_in ∈ extract_node_gname r) &&
               node_rep_R r.1.1.1 r.1.2 r.2 g *
               field_at sh (t_struct_list_t) [StructField _t] r.1.1.1 p *
               data_at sh (tptr t_struct_list_t) next n).


Lemma findNext: semax_body Vprog Gprog f_findNext findnext_spec.
Proof.
  start_function.
  (* int y = pn->p->t->key *)
  forward. 
  unfold node_rep_R.
  destruct (eq_dec r.1.1.1 nullval).
  + rewrite e.
    unfold my_specific_tree_rep.
    rewrite -> if_true; auto.
    forward.
    forward.
    forward.
  Intros gn x0 v0 next lockn.
  forward.
  forward.
  forward.
  forward_if. (* if (_x < _y) *)
  - (* pn->n = pn->p->t->left *)
    forward. (* t1 = pn->p *)
    forward. (* t2 = t1->t *)
    forward. (* t3 = t2->left *)
    forward.
    Exists NN.
    Exists next next gn.
    entailer !.
    unfold extract_node_gname.
    rewrite H.
    apply elem_of_list_here.
    Exists gn x0 v0 next lockn.
    entailer !.
  - forward_if.
    (* pn->n = pn->p->t->right *)
    repeat forward.
    Exists NF p n_pt gn. 
    entailer !.
    unfold extract_node_gname.
    rewrite H.
    apply elem_of_list_here.
    Exists gn x0 v0 next lockn.
    entailer !.
    forward.
    Exists F p n_pt gn.
    entailer !.
    unfold extract_node_gname.
    rewrite H.
    apply elem_of_list_here.
    Exists gn x0 v0 next lockn.
    entailer !.
Qed.


(*
#[export] Instance pointer_lock : Ghost := discrete_PCM (val * val * range).
Definition ghost_info : Type := (key * val)%type.

(* This allows the range to be outdated while the ghost_info may be present or absent. *)
#[export] Instance node_ghost : Ghost := prod_PCM pointer_lock (exclusive_PCM (option ghost_info)).
Notation node_info := (@G node_ghost).

Definition in_tree (g: gname) (g1 : gname) (pn: val) (lock: val):=
      ghost_snap (P := gmap_ghost (K := gname)(A := discrete_PCM (val * val)) )
        ({[g1 := (pn, lock)]}) g.

Lemma in_tree_duplicate g gin pn lock:
  in_tree g gin pn lock |-- in_tree g gin pn lock * in_tree g gin pn lock.
Proof. by rewrite - bi.persistent_sep_dup. Qed.

Class NodeRep : Type := {
  node_rep_R : val -> range -> option (option ghost_info) -> gname -> mpred
  }.


#[export]Instance my_specific_tree_rep : NodeRep := {
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
*)
