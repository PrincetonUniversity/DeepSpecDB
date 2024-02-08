Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import bst.bst_giveup. (* bst_giveup.c *)
Require Import bst.puretree.
Require Import bst.data_struct.
Require Import bst.giveup_lib.
(* Require Import bst.giveup_specs. *)
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition struct_dlist := Tstruct _DList noattr.
Definition t_struct_node := Tstruct _node_t noattr.
Definition t_struct_nodeds := Tstruct _node noattr.

Definition fst_list : list (val * val * val * val) -> list val :=
  fun triples => map (fun '(x, _, _,_) => x) triples.

Definition snd_list : list (val * val * val * val) -> list val :=
  fun triples => map (fun '(_, x, _,_) => x) triples.

Definition thrd_frth_list: list (val * val * val * val) -> list (val * val) :=
  fun triples => map (fun '(_, _, x, y) => (x, y)) triples.


Definition fst_snd_list: list (val * val * val * val) -> list (val * val) :=
  fun triples => map (fun '(x, y, _,_) => (x, y)) triples.

(*getting p that points to min *)

Definition fst_thrd_list: list (val * val * val * val) -> list (val * val) :=
  fun triples => map (fun '(x, _, y,_) => (x, y)) triples.

(*getting p that points to max *)
Definition fst_frth_list: list (val * val * val * val) -> list (val * val) :=
  fun triples => map (fun '(x, _, _, y) => (x, y)) triples.

Section bst_give_up.
  Context {N: NodeRep}.
  Context (Hsize: node_size = 2%nat).
  
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
  PRE [ tptr (tptr t_struct_nodeds), tint, tptr tvoid, tint, tptr (struct_dlist)]
  PROP (repable_signed x; is_pointer_or_null v; key_in_range x r.1.2 = true; length next = node_size)
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt); l)
  GLOBALS (gv)
  SEP (mem_mgr gv; field_at Tsh (struct_dlist) [StructField _list] dl l *
                     (* field_at Ews (struct_dlist) [StructField _size] (Vptrofs (Ptrofs.repr 2%Z)) l * *)
                     data_at Ews (tarray (tptr tvoid) (Zlength next)) next dl * 
                     (* (!!(p = r.1.1.1 /\ p = nullval)  && seplog.emp); *)
       data_at Ews (tptr t_struct_nodeds) tp p)
  POST[ tvoid ]
  EX (pnt : val),
  PROP (pnt <> nullval)
  LOCAL ()
  SEP (mem_mgr gv; data_at Ews (tptr t_struct_nodeds) pnt p;
       node_rep_R pnt r.1.2 (Some (Some (x, v, next))) g;
       field_at Tsh struct_dlist (DOT _list) dl l;
       data_at Ews (tarray (tptr tvoid) (Zlength next)) next dl).

(*

Lemma test (trl : list (val * val * val * val)):
  (iter_sepcon (fun '(pn, lk, fs, ft) =>
                  malloc_token Ews t_struct_node pn *
                  field_at Ews t_struct_node (DOT _t) (Vlong (Int64.repr 0)) pn *
                  atomic_int_at Ews (vint 0) lk *
                  field_at Ews t_struct_node (DOT _lock) lk pn *
                  field_at Ews t_struct_node (DOT _min) fs pn *
                  field_at Ews t_struct_node (DOT _max) ft pn) trl ) |--
iter_sepcon (fun pn => malloc_token Ews t_struct_node pn) (fst_list trl) *
       iter_sepcon (fun pn => field_at Ews t_struct_node (DOT _t) (Vlong (Int64.repr 0)) pn)
         (fst_list trl) *
       iter_sepcon (fun lk => atomic_int_at Ews (vint 0) lk) (snd_list trl) * 
       iter_sepcon (fun fs => field_at Ews t_struct_node (DOT _lock) (snd fs) (fst fs))
         (fst_snd_list trl) *
       iter_sepcon (fun ft => field_at Ews t_struct_node (DOT _min) (snd ft) (fst ft))
         (fst_thrd_list trl) *
       iter_sepcon (fun ff => field_at Ews t_struct_node (DOT _max) (snd ff) (fst ff))
         (fst_frth_list trl).
Proof.
  simpl.
  Search iter_sepcon.
  induction trl. simpl.
  cancel.
  replace (a :: trl) with ([a]++trl); auto.
  rewrite ! iter_sepcon_app.
  sep_apply IHtrl.
  simpl.
  destruct a.
  destruct p. destruct p. simpl. entailer !.
Qed.

 *)

 (* triple (pointer, lock, min, max) *)
Definition post_insert_giveup1 (p pnt : val) (x: Z) v (rg: range)
  min max (trl : list (val * val * val * val)) g :=
       (iter_sepcon (fun '(pn, lk, fs, ft) =>
                  malloc_token Ews t_struct_node pn *
                  field_at Ews t_struct_node (DOT _t) nullval pn *
                  atomic_int_at Ews (vint 0) lk *
                  field_at Ews t_struct_node (DOT _lock) lk pn *
                  field_at Ews t_struct_node (DOT _min) fs pn *
                  field_at Ews t_struct_node (DOT _max) ft pn) trl) *
       node_rep_R pnt rg (Some (Some (x, v, (fst_list trl)))) g *
       field_at Ews t_struct_node (DOT _t) pnt p *
       field_at Ews t_struct_node (DOT _min) (vint min) p * 
       field_at Ews t_struct_node (DOT _max) (vint max) p.

(* For list, just a dummy function for BST *)
Definition post_insert_giveup2 (p pnt : val) (x: Z) v (rg: range)
  min max (trl : list (val * val * val * val)) g :=
       (iter_sepcon (fun '(pn, lk, fs, ft) =>
                  malloc_token Ews t_struct_node pn *
                  field_at Ews t_struct_node (DOT _t) nullval pn *
                  atomic_int_at Ews (vint 0) lk *
                  field_at Ews t_struct_node (DOT _lock) lk pn *
                  field_at Ews t_struct_node (DOT _min) fs pn *
                  field_at Ews t_struct_node (DOT _max) ft pn) trl) *
       node_rep_R pnt rg (Some (Some (x, v, (fst_list trl)))) g *
       field_at Ews t_struct_node (DOT _t) pnt p *
       field_at Ews t_struct_node (DOT _min) (vint min) p * 
       field_at Ews t_struct_node (DOT _max) (vint max) p.



(* For BST, stt <> 2 never happens, just want to have the same spec for all specific ds
   since stt == 2 then tp = nullval (only for BST) *)
Definition insertOp_giveup_spec :=
  DECLARE _insertOp_giveup
    WITH x: Z, stt: Z,  v: val, p: val, tp: val, min: Z, max: Z, r: node_info, g: gname, gv: globals
  PRE [ tptr t_struct_node, tint, tptr tvoid, tint ]
  PROP (repable_signed min; repable_signed max; repable_signed x;
        is_pointer_or_null v; key_in_range x r.1.2 = true; tp = nullval )
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt))
  GLOBALS (gv)
  SEP (mem_mgr gv;
       match (Int.eq (Int.repr stt) (Int.repr 2%Z)) with
        | true => (!!(tp = nullval) && seplog.emp)
        | false => (!!(tp <> nullval) && seplog.emp)
       end;
       field_at Ews t_struct_node (DOT _t) tp p;
       field_at Ews t_struct_node (DOT _min) (vint min) p;
       field_at Ews t_struct_node (DOT _max) (vint max) p;
       node_rep_R tp r.1.2 r.2 g )
  POST[ tvoid ] (* triple (pointer, lock, min, max) *)
  EX (pnt : val) (trl : list (val * val * val * val)),
  PROP (pnt <> nullval)
  LOCAL ()
  SEP (mem_mgr gv;
       match (Int.eq (Int.repr stt) (Int.repr 2%Z)) with
       | true =>  (post_insert_giveup1 p pnt x v r.1.2 min max trl g)
       | false => (post_insert_giveup2 p pnt x v r.1.2 min max trl g)
       end).

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;  
                             insertOp_giveup_spec; insertOp_spec;
                             surely_malloc_spec ]).

Lemma insertOp_bst: semax_body Vprog Gprog f_insertOp_giveup insertOp_giveup_spec.
Proof.
  start_function.
  forward_call (t_struct_node, gv).
  Intros p1.
  forward_call (t_struct_node, gv).
  Intros p2.
  assert_PROP (field_compatible t_struct_node [] p1) by entailer!.
  assert_PROP (field_compatible t_struct_node [] p2) by entailer!.
  forward.
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
  forward.
  forward.
  forward_call (tarray (tptr tvoid) 2, gv). simpl; computable.
  Intros lst.
  forward. forward. forward. forward. forward.
  destruct (Int.eq (Int.repr stt) (Int.repr 2)); last first.
  Intros. easy. (* contradiction *)
  simpl.
  change (upd_Znth 1 (upd_Znth 0 (default_val (tarray (tptr tvoid) 2)) p1) p2) with [p1;p2].
  assert_PROP(field_compatible t_struct_node (DOT _t) p) by entailer !.
  unfold_data_at (data_at _ _ _ v_dlist).
  assert (field_address t_struct_node (DOT _t) p  = p) as I.
  rewrite -> field_compatible_field_address, isptr_offset_val_zero; auto.
  forward_call(x, stt, v, (field_address t_struct_node  [StructField _t] p), tp,
                v_dlist, lst, [p1; p2] , r, g, gv).
  entailer !.
  Intros pnt.
  forward. forward. entailer !. list_solve.
  forward. forward. forward. forward. entailer !. list_solve.
  forward. forward. forward. entailer !. list_solve.
  forward. forward. forward. entailer !. list_solve.
  forward. forward. forward.
  (* free *)
  forward_call (tarray (tptr tvoid) 2, lst, gv).
  {
    assert_PROP (lst <> nullval) by entailer !.
    rewrite if_false; auto. cancel.
  }
  Exists pnt [(p1, lock1, vint min, vint x); (p2, lock2, vint x, vint max)].
  entailer !.
  unfold_data_at (data_at _ _ _ p1).
  unfold_data_at (data_at _ _ _ p2).
  unfold_data_at(data_at_ _ _ v_dlist).
  unfold post_insert_giveup1.
  simpl.
  cancel.
  admit.
Admitted.

End bst_give_up.


