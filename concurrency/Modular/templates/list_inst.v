Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.puretree.
Require Import bst.list.
Require Import bst.data_struct.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* struct node {int key; void *value; struct tree_t *left, *right;} node;*)
Definition t_struct_list := Tstruct _node noattr.
(* Define for dynamic list *)
Definition struct_dlist := Tstruct _DList noattr.

#[local] Obligation Tactic := idtac.
(* node_rep_R r.1.1.1 r.1.2 r.2 g, and r is type of node_info *)
#[local] Program Instance my_specific_tree_rep : NodeRep := {
    node_rep_R := fun (tp : val) (r : range) (g_info : option (option ghost_info)) g =>
      if eq_dec tp nullval
      then !!(g_info = Some None) && seplog.emp
      else (EX (x : Z), EX (v next : val),
      !!(g_info = Some (Some (x, v, [next])) /\ and (Z.le Int.min_signed x) (Z.le x Int.max_signed) /\
       is_pointer_or_null next /\ (tc_val (tptr Tvoid) v) /\ key_in_range x r = true) &&
       data_at Ews t_struct_list ((Vint (Int.repr x)), (v, next)) tp *
       malloc_token Ews t_struct_list tp); node_size := 1 }.
Next Obligation.
  simpl.
  intros tp r g_info g.
  destruct (EqDec_val tp nullval); [ | Intros x v next]; entailer !.
Defined.
Next Obligation.
  simpl.
  intros tp r g_info g.
  destruct (EqDec_val tp nullval); [ | Intros x v next]; entailer !.
Defined.

Definition extract_node_pn (node: node_info) : list val :=
  match node.2 with
  | Some (Some (_, _, lst)) => lst
  | _ => []
  end.

(* Spec of findnext function *)
(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)

(* Spec of findnext function *)
(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)
Definition findnext_spec :=
  DECLARE _findNext
  WITH x: Z, p: val, n: val, n_pt : val, r: node_info,
                g: gname, sh: share, gv: globals
  PRE [ tptr t_struct_list, tptr (tptr tvoid), tint ]
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
  Intros x0 v0 next.
  forward.
  forward_if. 
  - forward.
    forward.
    forward.
    Exists NN.
    Exists next next.
    entailer !.
    unfold extract_node_pn.
    rewrite H.
    apply elem_of_list_here.
    unfold node_rep_R.
    simpl.
    rewrite -> if_false; eauto.
    Exists x0 v0 next.
    entailer !.
  - forward_if.
    repeat forward.
    Exists NF r.1.1.1 n_pt.
    entailer !.
    unfold node_rep_R.
    simpl.
    rewrite -> if_false; eauto.
    Exists x0 v0 next.
    entailer !.
    forward.
    Exists F r.1.1.1 n_pt.
    entailer !.
    unfold node_rep_R.
    simpl.
    rewrite -> if_false; eauto.
    Exists x0 v0 next.
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

Definition insertOp_spec :=
  DECLARE _insertOp
    WITH x: Z, stt: Z, v: val, p: val, tp: val, l: val, dl: val, next: list val, r: node_info,
                    g: gname, gv: globals
  PRE [ tptr (tptr t_struct_list), tint, tptr tvoid, tint, tptr (struct_dlist)]
  PROP (repable_signed x; is_pointer_or_null v; key_in_range x r.1.2 = true;
        is_pointer_or_null (Znth 0 next);
        length next = node_size)
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt); l)
  GLOBALS (gv)
  SEP (mem_mgr gv; 
                     field_at Tsh (struct_dlist) [StructField _list] dl l *
                     (* field_at Ews (struct_dlist) [StructField _size] (Vptrofs (Ptrofs.repr 2%Z)) l * *)
                     data_at Ews (tarray (tptr tvoid) (Zlength next)) next dl * 
                     (* (!!(p = r.1.1.1 /\ p = nullval)  && seplog.emp); *)
       data_at Ews (tptr t_struct_list) tp p)
  POST[ tvoid ]
  EX (pnt : val),
  PROP (pnt <> nullval)
  LOCAL ()
  SEP (mem_mgr gv; data_at Ews (tptr t_struct_list) pnt p;
       node_rep_R pnt r.1.2 (Some (Some (x, v, next))) g;
       field_at Tsh struct_dlist (DOT _list) dl l;
       data_at Ews (tarray (tptr tvoid) (Zlength next)) next dl).

Lemma length_equal_1 : forall (x: Z) (v: val) (next : list val),
  length next = 1%nat ->
  Some (Some (x, v, next)) = Some (Some (x, v, [Znth 0 next])).
Proof.
  intros x v next H_length.
  destruct next as [|a [|b tl]] eqn:Heq_next; try discriminate.
  inversion H_length; subst.
  unfold Znth; simpl.
  repeat f_equal.
Qed.

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
     surely_malloc_spec; insertOp_spec (* ; traverse_spec; insert_spec; treebox_new_spec*) ]).
(* Proving insertOp satisfies spec *)
Lemma insertOp: semax_body Vprog Gprog f_insertOp insertOp_spec.
Proof.
  start_function.
  forward_call (t_struct_list, gv).
  Intros new_node.
  forward.
  forward.
  forward.
  forward.
  entailer !.
  simpl in H3.
  rewrite Zlength_correct. lia.
  forward.
  forward.
  Exists new_node.
  assert_PROP (new_node <> nullval). entailer !.
  unfold node_rep_R.
  unfold my_specific_tree_rep.
  rewrite if_false; auto.
  entailer !.
  Exists x v (Znth 0 next).
  entailer !.
  by apply length_equal_1.
Qed.
