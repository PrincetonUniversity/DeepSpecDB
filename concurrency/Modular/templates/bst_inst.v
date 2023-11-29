Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import bst.puretree.
Require Import bst.bst.
Require Import bst.data_struct.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* struct node {int key; void *value; struct tree_t *left, *right;} node;*)
Definition t_struct_tree := Tstruct _node noattr.

(* struct tree_t {node *t; lock_t *lock; int min; int max; } tree_t; *)
(* Definition t_struct_tree_t := Tstruct _tree_t noattr. *)

(* node_rep_R r.1.1.1 r.1.2 r.2 g, and r is type of node_info *)


#[local] Obligation Tactic := idtac.

#[local] Program Instance my_specific_tree_rep : NodeRep := {
  node_rep_R := fun (tp : val) (r : range) (g_info : option (option ghost_info)) g =>
  if eq_dec tp nullval
  then !!(g_info = Some None) && seplog.emp
  else
  (EX (x : Z), EX (v pa pb : val),
      !!(g_info = Some (Some (x, v, [pa; pb])) /\ and (Z.le Int.min_signed x) (Z.le x Int.max_signed) /\
       is_pointer_or_null pa /\ is_pointer_or_null pb /\
          (tc_val (tptr Tvoid) v) /\ key_in_range x r = true) &&
       data_at Ews t_struct_tree ((Vint (Int.repr x)), (v, (pa, pb))) tp * 
       malloc_token Ews t_struct_tree tp)}.

(* ; node_rep_R_valid_pointer }. *)
Next Obligation.
  simpl.
  intros tp r g_info g.
  destruct (EqDec_val tp nullval); [ | Intros x v pa pb]; entailer !.
Defined.
Next Obligation.
  simpl.
  intros tp r g_info g.
  destruct (EqDec_val tp nullval); [ | Intros x v pa pb]; entailer !.
Defined.

Definition extract_node_pn (node: node_info) : list val :=
  match node.2 with
  | Some (Some (_, _, lst)) => lst
  | _ => []
  end.

(* Spec of findnext function *)
(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)
Definition findnext_spec :=
  DECLARE _findNext
  WITH x: Z, p: val, n: val, n_pt : val, r: node_info,
                g: gname, sh: share, gv: globals
  PRE [ tptr t_struct_tree, tptr (tptr tvoid), tint ]
          PROP (writable_share sh(*; is_pointer_or_null pa; is_pointer_or_null pb*) )
          PARAMS (p; n; Vint (Int.repr x)) GLOBALS (gv)
          SEP (node_rep_R r.1.1.1 r.1.2 r.2 g * (!!(p = r.1.1.1 /\ p <> nullval) && seplog.emp) *
               (* field_at sh (t_struct_tree) [StructField _t] r.1.1.1 p; *)
               
               data_at sh (tptr tvoid) n_pt n)
  POST [ tint ]
  EX (stt: enum), EX (n' next : val),
         PROP (match stt with
               | F | NF => (n' = p)
               | NN => (n' = next)
               end)
        LOCAL (temp ret_temp (enums stt))
        SEP (match stt with
               | F | NF => data_at sh (tptr tvoid) n_pt n
               | NN => !!(n' ∈ extract_node_pn r) && data_at sh (tptr tvoid) next n
             end *
               node_rep_R r.1.1.1 r.1.2 r.2 g) .


Lemma findNext: semax_body Vprog Gprog f_findNext findnext_spec.
Proof.
  start_function.
  unfold node_rep_R.
  unfold my_specific_tree_rep.
  Intros.
  subst.
  rewrite -> if_false; eauto.
  Intros x0 v0 pa pb.
  forward.
  forward_if. (* if (_x < _y) *)
  - (* pn->n = pn->p->t->left *)
    forward. forward. forward.
    Exists NN pa pa.
    entailer !.
    unfold extract_node_pn.
    rewrite H.
    apply elem_of_list_here.
    rewrite H.
    simpl.
    rewrite -> if_false; eauto.
    Exists x0 v0 pa pb.
    entailer !.
  - forward_if.
    (* pn->n = pn->p->t->right *)
    repeat forward.
    Exists NN pb pb.
    entailer !.
    unfold extract_node_pn.
    rewrite H.
    assert([pa ; pb] = [pa] ++ [pb]); auto.
    rewrite H12.
    rewrite elem_of_app. right.
    apply elem_of_list_here.
    simpl.
    rewrite -> if_false; eauto.
    Exists x0 v0 pa pb.
    entailer !.
    forward.
    Exists F r.1.1.1  n_pt.
    entailer !.
    simpl.
    rewrite -> if_false; eauto.
    Exists x0 v0 pa pb.
    entailer !.
Qed.

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

Check iter_sepcon (fun p => malloc_token Ews _ p) [_; _].

Definition insertOp_spec :=
  DECLARE _insertOp
    WITH x: Z, stt: Z, v: val, p: val, p1: val, p2: val, r: node_info,
                    g: gname, gv: globals
  PRE [ tptr (tptr t_struct_tree), tint, tptr tvoid, tint, tptr tvoid, tptr tvoid]
  PROP (repable_signed x; is_pointer_or_null v; key_in_range x r.1.2 = true )
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt); p1; p2)
  GLOBALS (gv)
  SEP (mem_mgr gv; node_rep_R nullval r.1.2 r.2 g *
                     (* (!!(p = r.1.1.1 /\ p = nullval)  && seplog.emp); *)
       data_at Ews (tptr t_struct_tree) nullval p)
  POST[ tvoid ]
  EX (pnt : val),
  PROP (pnt <> nullval)
  LOCAL ()
  SEP (mem_mgr gv; node_rep_R pnt r.1.2 (Some (Some (x, v, [p1; p2]))) g;
       data_at Ews (tptr t_struct_tree) pnt p).

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
     surely_malloc_spec; insertOp_spec (* ; traverse_spec; insert_spec; treebox_new_spec*) ]).
(* Proving insertOp satisfies spec *)
Lemma insertOp: semax_body Vprog Gprog f_insertOp insertOp_spec.
Proof.
  start_function.
  forward_call (t_struct_tree, gv).
  Intros new_node.
  forward.
  forward.
  forward.
  forward.
  forward.
  Exists new_node.
  assert_PROP (new_node  <> nullval). entailer !.
  unfold node_rep_R.
  unfold my_specific_tree_rep.

  rewrite if_false; auto.
  Search eq_dec.
  destruct (eq_dec nullval nullval); last first; try easy.
  Intros. 
  entailer !.
  Exists x v p1 p2.
  entailer !. 
Qed.
