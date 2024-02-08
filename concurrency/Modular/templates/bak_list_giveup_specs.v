Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import bst.list_giveup. (* list_giveup.c *)
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

Definition fst_list : list (val * val * val * val) -> list val := map (fun '(x, _, _,_) => x).
Definition snd_list : list (val * val * val * val) -> list val := map (fun '(_, x, _,_) => x).
Definition thrd_frth_list: list (val * val * val * val) -> list (val * val) :=
  map (fun '(_, _, x, y) => (x, y)).
Definition fst_snd_list: list (val * val * val * val) -> list (val * val) :=
  map (fun '(x, y, _,_) => (x, y)).
(*getting p that points to min *)
Definition fst_thrd_list: list (val * val * val * val) -> list (val * val) :=
  map (fun '(x, _, y,_) => (x, y)).
(*getting p that points to max *)
Definition fst_frth_list: list (val * val * val * val) -> list (val * val) :=
  map (fun '(x, _, _, y) => (x, y)).

Section give_up.
  Context {N: NodeRep}.
  Context (Hsize: node_size = 1%nat).

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t: type, gv: globals
   PRE [ size_t ]
       PROP (and (Z.le 0 (sizeof t)) (Z.lt (sizeof t) Int.max_unsigned);
             complete_legal_cosu_type t = true; natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ]
    EX p: _,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

Definition insertOp_spec :=
  DECLARE _insertOp
    WITH x: Z, stt: Z, v: val, p: val, l: val, dl: val, next: list val, rng: range,
                    g: gname, gv: globals
  PRE [ tptr (tptr t_struct_nodeds), tint, tptr tvoid, tint, tptr (struct_dlist)]
  PROP (repable_signed x; is_pointer_or_null v; key_in_range x rng = true;
        is_pointer_or_null (Znth 0 next);
        length next = node_size)
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt); l)
  GLOBALS (gv)
  SEP (mem_mgr gv; 
                     field_at Tsh (struct_dlist) [StructField _list] dl l *
                     (* field_at Ews (struct_dlist) [StructField _size] (Vptrofs (Ptrofs.repr 2%Z)) l * *)
                     data_at Ews (tarray (tptr tvoid) (Zlength next)) next dl * 
                     (* (!!(p = r.1.1.1 /\ p = nullval)  && seplog.emp); *)
       data_at Ews (tptr t_struct_nodeds) nullval p)
  POST[ tvoid ]
  EX (pnt : val),
  PROP (pnt <> nullval)
  LOCAL ()
  SEP (mem_mgr gv; data_at Ews (tptr t_struct_nodeds) pnt p;
       node_rep_R pnt rng (Some (Some (x, v, next))) g;
       field_at Tsh struct_dlist (DOT _list) dl l;
       data_at Ews (tarray (tptr tvoid) (Zlength next)) next dl).


Definition post_insert_giveup1 (p pnt : val) (x: Z) v (rg: range)
  min max (trl : list (val * val * val * val)) g :=
       iter_sepcon (fun pn => malloc_token Ews t_struct_node pn) (fst_list trl) * 
       iter_sepcon (fun pn => field_at Ews t_struct_node (DOT _t) (Vlong (Int64.repr 0)) pn)
         (fst_list trl) * 
       iter_sepcon (fun lk => atomic_int_at Ews (vint 0) lk) (snd_list trl) * 
       iter_sepcon (fun fs => field_at Ews t_struct_node (DOT _lock) (snd fs) (fst fs))
         (fst_snd_list trl) * 
       iter_sepcon (fun ft => field_at Ews t_struct_node (DOT _min) (snd ft) (fst ft))
         (fst_thrd_list trl) * 
       iter_sepcon (fun ff => field_at Ews t_struct_node (DOT _max) (snd ff) (fst ff))
         (fst_frth_list trl) * 
       node_rep_R pnt rg (Some (Some (x, v, (fst_list trl)))) g *
       field_at Ews t_struct_node (DOT _t) pnt p *
       field_at Ews t_struct_node (DOT _min) (vint min) p * 
       field_at Ews t_struct_node (DOT _max) (vint max) p.

Definition post_insert_giveup2 (p pnt tp: val) (x: Z) v (rg: range)
  min max (trl : list (val * val * val * val)) (r: node_info) g :=
       iter_sepcon (fun pn => malloc_token Ews t_struct_node pn) (fst_list trl) * 
       iter_sepcon (fun pn => field_at Ews t_struct_node (DOT _t) tp pn)
         (fst_list trl) * 
       iter_sepcon (fun lk => atomic_int_at Ews (vint 0) lk) (snd_list trl) * 
       iter_sepcon (fun fs => field_at Ews t_struct_node (DOT _lock) (snd fs) (fst fs))
         (fst_snd_list trl) * 
       iter_sepcon (fun ft => field_at Ews t_struct_node (DOT _min) (snd ft) (fst ft))
         (fst_thrd_list trl) * 
       iter_sepcon (fun ff => field_at Ews t_struct_node (DOT _max) (snd ff) (fst ff))
         (fst_frth_list trl) * 
       node_rep_R tp rg r.2 g * node_rep_R pnt r.1.2 (Some (Some (x, v, (fst_list trl)))) g *
       field_at Ews t_struct_node (DOT _t) pnt p * 
       field_at Ews t_struct_node (DOT _min) (vint min) p * 
       field_at Ews t_struct_node (DOT _max) (vint max) p.

(*
node_rep_R tp r.1.2 r.2 g * field_at Ews t_struct_node (DOT _max) (vint max) p1
  |-- field_at Ews t_struct_node (DOT _max) (vint Int.max_signed) p1

 *)
(*
Check Int.eq (Int.repr 2%Z) Int.zero. 
Definition insertOp_giveup_spec :=
  DECLARE _insertOp_giveup
    WITH x: Z, stt: Z,  v: val, p: val, tp: val, min: Z, max: Z, r: node_info, g: gname, gv: globals
  PRE [ tptr t_struct_node, tint, tptr tvoid, tint ]
  PROP (repable_signed min; repable_signed max; repable_signed x;
        is_pointer_or_null v; is_pointer_or_null v; is_pointer_or_null tp; key_in_range x r.1.2 = true)
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt))
  GLOBALS (gv)
  SEP (mem_mgr gv;
       !!(if (Int.eq (Int.repr stt) (Int.repr 2%Z)) then (tp = nullval) else (tp <> nullval)) && seplog.emp;
       field_at Ews t_struct_node (DOT _t) tp p;
       field_at Ews t_struct_node (DOT _min) (vint min) p;
       field_at Ews t_struct_node (DOT _max) (vint max) p;
       node_rep_R tp r.1.2 r.2 g )
  POST[ tvoid ] (* triple (pointer, lock, min, max) *)
  EX (pnt : val) (trl : list (val * val * val * val)),
  PROP (pnt <> nullval)
  LOCAL ()
  SEP (mem_mgr gv;
       field_at Ews t_struct_node (DOT _t) pnt p;
       (* malloc_token Ews t_struct_nodeds pnt; *)
       iter_sepcon (fun pn => malloc_token Ews t_struct_node pn) (fst_list trl);
       iter_sepcon (fun pn => field_at Ews t_struct_node (DOT _t) (Vlong (Int64.repr 0)) pn)
         (fst_list trl);
       iter_sepcon (fun lk => atomic_int_at Ews (vint 0) lk) (snd_list trl);
       iter_sepcon (fun fs => field_at Ews t_struct_node (DOT _lock) (snd fs) (fst fs))
         (fst_snd_list trl);
       iter_sepcon (fun ft => field_at Ews t_struct_node (DOT _min) (snd ft) (fst ft))
         (fst_thrd_list trl);
       iter_sepcon (fun ff => field_at Ews t_struct_node (DOT _max) (snd ff) (fst ff))
         (fst_frth_list trl);
       node_rep_R pnt r.1.2 (Some (Some (x, v, (fst_list trl)))) g;
       field_at Ews t_struct_node (DOT _min) (vint min) p;
       field_at Ews t_struct_node (DOT _max) (vint max) p).
 *)
Check Finite_Integer.
Check (vint _).
Check number2Z.
Definition insertOp_giveup_spec :=
  DECLARE _insertOp_giveup
    WITH x: Z, stt: Z,  v: val, p: val, tp: val, min: Z, max: Z, r: node_info, g: gname, gv: globals
  PRE [ tptr t_struct_node, tint, tptr tvoid, tint ]
  PROP (repable_signed min; repable_signed max; repable_signed x;
        is_pointer_or_null v; is_pointer_or_null v; is_pointer_or_null tp; key_in_range x r.1.2 = true)
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt))
  GLOBALS (gv)
  SEP (mem_mgr gv;
       match (Int.eq (Int.repr stt) (Int.repr 2%Z)) with
        | true => (!!(tp = nullval /\ (r.2 = Some None) ) && seplog.emp)
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
       (match (Int.eq (Int.repr stt) (Int.repr 2%Z)) with
        | true => (post_insert_giveup1 p pnt x v r.1.2 min max trl g)
        | _    => (post_insert_giveup2 p pnt tp x v (Finite_Integer x, Finite_Integer max) min
                   max trl r g)
        end)).

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;  
                             insertOp_giveup_spec; insertOp_spec;
                             surely_malloc_spec ]).

Check iter_sepcon.
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

Lemma insertOp_bst: semax_body Vprog Gprog f_insertOp_giveup insertOp_giveup_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_call (tarray (tptr tvoid) 1, gv). simpl. computable.
  Intros lst.
  forward.
  forward_call (t_struct_node, gv).
  Intros p1.
  forward.
  forward.
  forward_call (gv).
  Intros lock.
  forward.
  forward.
  forward.
  forward_call release_nonatomic (lock).
  forward_if(PROP (field_compatible t_struct_node (DOT _t) p)
     LOCAL (temp _t'20 p1; temp _t'19 lst; temp _l lock; temp _t'21 lst; temp _t'2 p1; temp _t'1 lst;
     temp _t'22 (Vlong (Int64.repr (Int.signed (Int.repr 1))));
     lvar _dlist (Tstruct _DList noattr) v_dlist; gvars gv; temp _p p; temp _x (vint x); 
     temp _value v; temp _status (vint stt))
     SEP ((match (Int.eq (Int.repr stt) (Int.repr 2%Z)) with
           | true => (EX (pnt: val),
                      (!!(pnt <> nullval) && seplog.emp) * node_rep_R pnt (Finite_Integer min, Finite_Integer max)  (Some (Some (x, v, [p1]))) g * data_at Ews (tptr t_struct_nodeds) pnt (field_address t_struct_node (DOT _t) p) * data_at Ews t_struct_node (nullval , (lock, (vint x, vint Int.max_signed))) p1)
           | false =>  (EX (pnt: val), (!!(pnt <> nullval) && seplog.emp) *
                                        node_rep_R tp (Finite_Integer x, Finite_Integer max) r.2 g *
                                      node_rep_R pnt (Finite_Integer min, Finite_Integer max) (Some (Some (x, v, [p1]))) g * data_at Ews (tptr t_struct_nodeds) pnt (field_address t_struct_node (DOT _t) p) * data_at Ews t_struct_node (tp, (lock, (vint x, vint max))) p1)
           end); atomic_int_at Ews (vint 0) lock; mem_mgr gv; malloc_token Ews t_struct_node p1;
     malloc_token Ews (tarray (tptr tvoid) 1) lst;
     data_at Ews (tarray (tptr tvoid) 1) [p1] lst;
     data_at Tsh (Tstruct _DList noattr) (lst, Vlong (Int64.repr (Int.signed (Int.repr 1)))) v_dlist;
     field_at Ews t_struct_node (DOT _min) (vint min) p;
     field_at Ews t_struct_node (DOT _max) (vint max) p)).
  - rewrite H6; simpl.
    Intros.
    forward. forward. forward.
    assert_PROP (field_compatible t_struct_node [] p1) by entailer!.
    assert_PROP(field_compatible t_struct_node (DOT _t) p) by entailer !.
    assert (field_address t_struct_node (DOT _t) p  = p) as I.
    rewrite ->  field_compatible_field_address, isptr_offset_val_zero; auto.
    (* call insertOp *)

    forward_call(x, stt, v, (field_address t_struct_node [StructField _t] p), v_dlist, lst, [p1] ,
                  (Finite_Integer min, Finite_Integer max), g, gv).
    {
      entailer !. simpl.
      change ((((0 + Z.pos (8 * 8) - 1) `div` Z.pos (8 * 8) * Z.pos (8 * 8)) `div` 8)) with 0.
      rewrite I isptr_offset_val_zero; auto.
      replace (vint stt) with (vint 2); f_equal; auto.
    }
    unfold_data_at (data_at _ _ _ v_dlist).
    cancel.
    entailer !. Check key_in_range.
    admit.
    Intros pnt.
    forward. forward. entailer !. list_solve.
    forward. forward. forward. entailer !. list_solve.
    forward.
    rewrite H7.
    entailer !.
    rewrite H6.
    simpl.
    Exists pnt . cancel.
    unfold_data_at (data_at _ _ _ v_dlist).
    entailer !.
    rewrite node_null.
    entailer !.
  - rewrite Int.eq_false; auto.
    Intros.
    forward. forward. forward. forward.
    forward. forward. forward. forward.
    forward. forward. forward. forward.
    assert_PROP (field_compatible t_struct_node [] p1) by entailer!.
    (* call insertOp *)
    assert_PROP(field_compatible t_struct_node (DOT _t) p) by entailer !.
    assert (field_address t_struct_node (DOT _t) p  = p) as I.
    rewrite -> field_compatible_field_address, isptr_offset_val_zero; auto.
    forward_call(x, stt, v, (field_address t_struct_node [StructField _t] p), v_dlist, lst, [p1] ,
                  (Finite_Integer min, Finite_Integer max) , g, gv).
    unfold_data_at (data_at _ _ _ v_dlist).
    entailer !.
    change (Vlong (Int64.repr 0)) with nullval.
    cancel. admit.
    rewrite Int.eq_false; auto.
    Intros pnt.
    Exists pnt.
    entailer !.
    unfold_data_at (data_at _ _ _ v_dlist).
    entailer !.
    eapply key_node_in_range; eauto.
    destruct r.1.2.
    
    Check range_incl.
    Check less_than_equal.
    assert (less_than_equal (Finite_Integer x) n). admit.
    unfold range_incl.
    
  - forward.
    assert (field_address t_struct_node (DOT _t) p = p) as I.
    {
      clear - H6.
      rewrite ->  field_compatible_field_address, isptr_offset_val_zero; auto.
      (* isptr p ; field_compatible t_struct_node (DOT _t) p *)
    }
    destruct (Int.eq (Int.repr stt) (Int.repr 2)).
    + subst. 
      Intros pnt.
      assert_PROP (pnt <> nullval). entailer !.
      forward_call (tarray (tptr tvoid) 1 , lst, gv).
      {
        assert_PROP (lst <> nullval) by entailer !.
        rewrite if_false; auto. cancel.
      }
      Exists pnt.
      unfold post_insert_giveup1.
      Exists [(p1, lock, vint x, (vint (Int.max_signed)))].
      unfold_data_at (data_at _ _ _ v_dlist).
      entailer.
      simpl.
      unfold_data_at (data_at _ _ _ p1).
      unfold_data_at(data_at_ Tsh (Tstruct _DList noattr) v_dlist).
      entailer !.
    + Intros pnt.
      assert_PROP (pnt <> nullval). entailer !.
      forward_call (tarray (tptr tvoid) 1 , lst, gv).
      {
        assert_PROP (lst <> nullval) by entailer !.
        rewrite if_false; auto. cancel.
      }
      Exists pnt.
      unfold post_insert_giveup2.
      Exists [(p1, lock, vint x, (vint max))].
      unfold_data_at (data_at _ _ _ v_dlist).
      entailer.
      simpl.
      unfold_data_at (data_at _ _ _ p1).
      unfold_data_at(data_at_ Tsh (Tstruct _DList noattr) v_dlist).
      entailer !.





      
  Admitted.
Qed.


