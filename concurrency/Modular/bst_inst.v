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

Definition t_struct_tree := Tstruct _node noattr.
Definition t_struct_tree_t := Tstruct _tree_t noattr.

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


Check node_rep_R.
Check range.
(* Spec of findnext function *)
(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)
Definition findnext_spec :=
  DECLARE _findNext
  WITH x: Z, v: val, b: val, p: val, n: val, tp: val, (*,
       pa: val, pb: val, px: Z, pv: val*) r: range, g: gname, g_info : option (option ghost_info), sh: share, gv: globals
  PRE [ tptr tvoid, tptr (tptr tvoid), tint ]
          PROP (writable_share sh(*; is_pointer_or_null pa; is_pointer_or_null pb*) )
          PARAMS (p; n; Vint (Int.repr x)) GLOBALS (gv)
          SEP ((* data_at sh (t_struct_tree_t) (p, n) b *)
            node_rep_R tp r g_info g;
               field_at sh (t_struct_tree_t) [StructField _t] tp p (* ;
               data_at sh t_struct_tree (Vint (Int.repr px), (pv, (pa, pb))) tp *)
               )
  POST [ tint ]
  EX (stt: enum), EX (n' : val), EX (next: val),
         PROP (match stt with
               | NF => (n' = next)
               | F => (n' = p)
               | NN => (n' = p)
               end)
        LOCAL (temp ret_temp (enums stt))
        SEP (match stt with
             | NF =>
               ((* data_at sh (t_struct_tree_t) (p, n') b  * *)
               field_at sh (t_struct_tree_t) [StructField _t] tp p) (* *
               data_at sh t_struct_tree (Vint (Int.repr px), (pv, (pa, pb))) tp*)  
             | F =>
               (field_at sh (t_struct_tree_t) [StructField _t] tp p)
               (*data_at sh (t_struct_tree_t) (p, n) b )  *
               field_at sh (t_struct_tree_t) [StructField _t] tp p *
               data_at sh t_struct_tree (Vint (Int.repr px), (pv, (pa, pb))) tp*)
             | NN => (field_at sh (t_struct_tree_t) [StructField _t] tp p
                     (* data_at sh (t_struct_tree_t) (p, n) b *) )
             end).

Lemma findNext: semax_body Vprog Gprog f_findNext findnext_spec.
Proof.
  start_function.
  (* int y = pn->p->t->key *)
  forward. 
  forward. 
  forward.
  entailer !. admit.
  unfold node_rep_R.
  simpl.
  Intros ga gb x0 v0 pa pb locka lockb.
  forward.
  forward_if. (* if (_x < _y) *)
  - (* pn->n = pn->p->t->left *)
    forward. (* t1 = pn->p *)
    forward. (* t2 = t1->t *)
    forward. (* t3 = t2->left *)
    forward.
    forward.
    Exists true.
    Exists pa.
    entailer !.
  - forward_if.
    (* pn->n = pn->p->t->right *)
    repeat forward.
    Exists true. Exists pb.
    entailer !.
    forward.
    Exists false.
    Exists p.
    entailer !.
Qed.




(* Spec of findnext function *)
Definition findnext_spec :=
  DECLARE _findNext
  WITH x: Z, v: val, b: val, p: val, n: val, tp: val, 
       pa: val, pb: val, px: Z, pv: val, sh: share, gv: globals
  PRE [ tptr tvoid, tptr (tptr tvoid), tint ]
          PROP (writable_share sh; is_pointer_or_null pa; is_pointer_or_null pb)
          PARAMS (b; Vint (Int.repr x); v) GLOBALS (gv)
          SEP (data_at sh (t_struct_tree_t) (p, n) b;
               field_at sh (t_struct_tree_t) [StructField _t] tp p;
               data_at sh t_struct_tree (Vint (Int.repr px), (pv, (pa, pb))) tp)
  POST [ tint ]
  EX (succ: bool), EX (n' : val),
         PROP (match succ with
               | true => ((n' = pa /\ (Z.lt (Int.signed (Int.repr x)) (Int.signed (Int.repr px)))) \/
                         (n' = pb /\ (Z.lt (Int.signed (Int.repr px)) (Int.signed (Int.repr x)))))
               | false => (n' = p /\ Int.signed (Int.repr x) = Int.signed (Int.repr px))
               end)
        LOCAL (temp ret_temp (Vint (if succ then Int.one else Int.zero)))
        SEP (match succ with
             | true =>
               (data_at sh (t_struct_tree) (p, n') b *
               field_at sh (t_struct_tree_t) [StructField _t] tp p *
               data_at sh t_struct_tree (Vint (Int.repr px), (pv, (pa, pb))) tp)
             | false =>
               (data_at sh (t_struct_tree) (p, n) b *
               field_at sh (t_struct_tree_t) [StructField _t] tp p *
               data_at sh t_struct_tree (Vint (Int.repr px), (pv, (pa, pb))) tp)
             end).

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
