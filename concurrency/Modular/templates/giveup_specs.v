Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import bst.giveup_template. (* giveup_template.c *)
Require Import bst.puretree.
Require Import bst.data_struct.
Require Import bst.giveup_lib.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

#[global] Instance gmap_inhabited V : Inhabitant (gmap key V).
Proof. unfold Inhabitant; apply empty. Defined.

#[global] Instance number_inhabited: Inhabitant number.
Proof. unfold Inhabitant; apply Pos_Infinity. Defined.

Section give_up_specs.
  Context {N: NodeRep}.
  
Definition nodebox_rep (g : gname) (g_root : gname) (sh : share) (lock: val) (nb : val) :=
  EX (np: val) (lsh : share),
                data_at sh (tptr (t_struct_node)) np nb *
                (!!(field_compatible t_struct_node nil np /\ is_pointer_or_null lock) &&
                field_at lsh t_struct_node [StructField _lock] lock np) *
                in_tree g g_root np lock.

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


Lemma test (pt: enum * (val * (share * (gname * node_info )))) (pt1 : node_info): True.
  Proof.
    Check (((pt.2.2.2).2).1).2.
    Check pt.2.2.1. (*share *)
    Check ((((pt.2.2.2).2).1).1).2.
    Check ((pt1.1).1).2.
    Check (pt.2.2.2).2.
    Check (pt1.1).2.
    Check ((((pt.2.2.2).2).1).1).1.
    Check pt.2.2.2.2.
    Check ((pt1.1).1).1.
    Check (pt.2.2.2).2.
    Admitted.

Definition post_traverse (b: val) x (g: gname) (e: enum) (p: val) (sh: share) (g_in: gname) (n: node_info):=
  !!( key_in_range x (n.1).2 = true ∧
      repable_signed (number2Z (n.1).2.1) /\ repable_signed (number2Z (n.1).2.2) /\
      is_pointer_or_null (((n.1).1).2) /\
      (if Val.eq (enums e) (enums NN)
       then n.2 = Some None /\ ((n.1).1).1 = nullval
                          else ((n.1).1).1 <> nullval)
                        (* (match (pt.1 : enum) with
                         | NN => pt.2.2.2.2.2 = Some None /\ ((((pt.2.2.2).2).1).1).1 = nullval
                         | NF | F =>  ((((pt.2.2.2).2).1).1).1 <> nullval
                        (* | NF => ((((pt.2.2.2).2).1).1).1 <> nullval *)
                          end) *)  ) && seplog.emp * 
  data_at Ews t_struct_pn (p, p) b * in_tree g g_in p ((n.1).1).2 * node_lock_inv_pred g p g_in n.

(*
Program Definition traverse_spec :=
  DECLARE _traverse
          ATOMIC TYPE (rmaps.ConstType
                       (val * val * val * Z  * val * globals * gname * gname))
          OBJ M INVS ∅
  WITH b, n, lock, x, v, gv, g, g_root
  PRE [ tptr t_struct_pn, tint]
  PROP (and (Z.le (Int.min_signed) x) (Z.le x (Int.max_signed)); is_pointer_or_null v)
  PARAMS (b; Vint (Int.repr x)) GLOBALS (gv)
  SEP  (mem_mgr gv; 
        in_tree g g_root n lock;
        !!(is_pointer_or_null lock /\ is_pointer_or_null n) && seplog.emp;
        EX (p: val), data_at Ews (t_struct_pn) (p, n) b ) | (CSS g g_root M)
  POST [ tint ]
  EX  pt: enum * (val * (share * (gname * node_info ))) %type,
  PROP ()
  LOCAL (temp ret_temp (enums pt.1))
  SEP (mem_mgr gv; !!( key_in_range x (((pt.2.2.2).2).1).2 = true ∧
                         repable_signed (number2Z (((pt.2.2.2).2).1).2.1) ∧
                         repable_signed (number2Z (((pt.2.2.2).2).1).2.2) /\
                         is_pointer_or_null ((((pt.2.2.2).2).1).1).2
                       /\ (if Val.eq (enums pt.1) (enums NN) then
                            pt.2.2.2.2.2 = Some None /\ ((((pt.2.2.2).2).1).1).1 = nullval
                          else ((((pt.2.2.2).2).1).1).1 <> nullval)
                        (* (match (pt.1 : enum) with
                         | NN => pt.2.2.2.2.2 = Some None /\ ((((pt.2.2.2).2).1).1).1 = nullval
                         | NF | F =>  ((((pt.2.2.2).2).1).1).1 <> nullval
                        (* | NF => ((((pt.2.2.2).2).1).1).1 <> nullval *)
                          end) *)  ) && seplog.emp; 
        data_at Ews t_struct_pn (pt.2.1, pt.2.1) b;
        in_tree g pt.2.2.2.1 pt.2.1 ((((pt.2.2.2).2).1).1).2;
       node_lock_inv_pred g pt.2.1 pt.2.2.2.1 (pt.2.2.2).2)| (CSS g g_root M).
*)

Program Definition traverse_spec :=
  DECLARE _traverse
          ATOMIC TYPE (rmaps.ConstType
                       (val * val * val * Z  * val * globals * gname * gname))
          OBJ M INVS ∅
  WITH b, n, lock, x, v, gv, g, g_root
  PRE [ tptr t_struct_pn, tint]
  PROP (and (Z.le (Int.min_signed) x) (Z.le x (Int.max_signed)); is_pointer_or_null v)
  PARAMS (b; Vint (Int.repr x)) GLOBALS (gv)
  SEP  (mem_mgr gv; 
        in_tree g g_root n lock;
        !!(is_pointer_or_null lock /\ is_pointer_or_null n) && seplog.emp;
        EX (p: val), data_at Ews (t_struct_pn) (p, n) b  ) | (CSS g g_root M)
  POST [ tint ]
  EX  pt: enum * (val * (share * (gname * node_info ))) %type,
  PROP ()
  LOCAL (temp ret_temp (enums pt.1))
  SEP (mem_mgr gv; post_traverse b x g pt.1 pt.2.1 pt.2.2.1 pt.2.2.2.1 (pt.2.2.2).2)| (CSS g g_root M).


(* t_struct_node represents for the generic-struct rather specific-data-structure *)
(* Spec of inrange function *)
Definition inRange_spec :=
  DECLARE _inRange
    WITH x: Z, p: val, min: Z, max : Z, sh: share, gv: globals
  PRE [ tptr t_struct_node, tint]
          PROP (writable_share sh; repable_signed min; repable_signed max; repable_signed x)
          PARAMS (p; Vint (Int.repr x)) GLOBALS (gv)
          SEP (
              field_at sh (t_struct_node) [StructField _min] (Vint (Int.repr min)) p;
              field_at sh (t_struct_node) [StructField _max] (Vint (Int.repr max)) p)
  POST [ tint ]
  EX (succ: bool),
         PROP (match succ with
               | true => (and (Z.lt min x) (Z.lt x max))
               | false => (or (Z.le x min) (Z.le max x))
               end)
        LOCAL (temp ret_temp (Vint (if succ then Int.one else Int.zero)))
        SEP (
             field_at sh (t_struct_node) [StructField _min] (Vint (Int.repr min)) p;
              field_at sh (t_struct_node) [StructField _max] (Vint (Int.repr max)) p).

Lemma node_rep_saturate_local r p g g_current:
  node_rep p g g_current r |-- !! is_pointer_or_null p.
Proof. unfold node_rep; entailer !. Qed.
Local Hint Resolve node_rep_saturate_local: saturate_local.

Lemma node_rep_valid_pointer t g g_current p: node_rep p g g_current t |-- valid_pointer p.
Proof.
  unfold node_rep.
  Intros.
  iIntros "(((((H & ?) & ?) & ?) & ?) & ?)".
  iPoseProof (field_at_valid_ptr0 with "H") as "H"; try auto; simpl; try lia.
  iVST. entailer !.
Qed.
Local Hint Resolve node_rep_valid_pointer : valid_pointer.

(*
(* Spec of findnext function *)
(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)
Definition findnext_spec :=
  DECLARE _findNext
  WITH x: Z, p: val, n: val, n_pt : val, r : node_info, g: gname, sh: share, gv: globals
  PRE [ tptr tvoid, tptr (tptr tvoid), tint ]
          PROP (writable_share sh(*; is_pointer_or_null pa; is_pointer_or_null pb*) )
          PARAMS (p; n; Vint (Int.repr x)) GLOBALS (gv)
          SEP ((* data_at sh (t_struct_tree_t) (p, n) b *)
            node_rep_R r.1.1.1 r.1.2 r.2 g ;
               field_at sh (t_struct_node) [StructField _t] r.1.1.1 p;
               data_at sh (tptr t_struct_node) n_pt n)
  POST [ tint ]
  EX (stt: enum), EX (n' next : val),
         PROP (match stt with
               | F | NF => (n' = p)
               | NN => (n' = next)
               end)
        LOCAL (temp ret_temp (enums stt))
        SEP (match stt with
               | F | NF => data_at sh (tptr t_struct_node) n_pt n
               | NN => !!(n' ∈ extract_node_pn r) && data_at sh (tptr t_struct_node) next n
             end *
               node_rep_R r.1.1.1 r.1.2 r.2 g *
               field_at sh (t_struct_node) [StructField _t] r.1.1.1 p).
*)

(* Spec of findnext function *)
(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)
Definition findnext_spec :=
  DECLARE _findNext
  WITH x: Z, p: val, n: val, n_pt : val, r: node_info,
                g: gname, sh: share, gv: globals
  PRE [ tptr t_struct_nodeds, tptr (tptr tvoid), tint ]
          PROP (writable_share sh(*; is_pointer_or_null pa; is_pointer_or_null pb*) )
          PARAMS (p; n; Vint (Int.repr x)) GLOBALS (gv)
          SEP (node_rep_R r.1.1.1 r.2 g * (!!(p = r.1.1.1 /\ p <> nullval) && seplog.emp) *
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
               node_rep_R r.1.1.1 r.2 g) .

(** Insert giveup spec **)

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


Definition post_insert_giveup1 (p pnt : val) (x: Z) v
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
       node_rep_R pnt (Some (Some (x, v, (fst_list trl)))) g *
       field_at Ews t_struct_node (DOT _t) pnt p *
       field_at Ews t_struct_node (DOT _min) (vint min) p * 
       field_at Ews t_struct_node (DOT _max) (vint max) p.

Definition post_insert_giveup2 (p pnt tp: val) (x: Z) v 
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
       node_rep_R tp r.2 g * node_rep_R pnt (Some (Some (x, v, (fst_list trl)))) g *
       field_at Ews t_struct_node (DOT _t) pnt p * 
       field_at Ews t_struct_node (DOT _min) (vint min) p * 
         field_at Ews t_struct_node (DOT _max) (vint max) p.

Definition insertOp_giveup_spec :=
  DECLARE _insertOp_giveup
    WITH x: Z, stt: Z, v: val, p: val, tp: val, min: Z, max: Z, r: node_info, g: gname, gv: globals
  PRE [ tptr t_struct_node, tint, tptr tvoid, tint ]
  PROP (repable_signed min; repable_signed max; repable_signed x;
        is_pointer_or_null v; is_pointer_or_null v; is_pointer_or_null tp)
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
       node_rep_R tp r.2 g )
  POST[ tvoid ] (* triple (pointer, lock, min, max) *)
  EX (pnt : val) (trl : list (val * val * val * val)),
  PROP (pnt <> nullval)
  LOCAL ()
  SEP (mem_mgr gv;
       (match (Int.eq (Int.repr stt) (Int.repr 2%Z)) with
        | true => (post_insert_giveup1 p pnt x v min max trl g)
        | _    => (post_insert_giveup2 p pnt tp x v min
                   max trl r g)
        end)).


(* same as insertOp_giveup_spec, only renaming name *)
Definition insertOp_helper_spec :=
  DECLARE _insertOp_helper
    WITH x: Z, stt: Z,  v: val, p: val, tp: val, min: Z, max: Z, r: node_info, g: gname, gv: globals
  PRE [ tptr t_struct_node, tint, tptr tvoid, tint ]
  PROP (repable_signed min; repable_signed max; repable_signed x;
        is_pointer_or_null v; is_pointer_or_null v; is_pointer_or_null tp)
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
       node_rep_R tp r.2 g )
  POST[ tvoid ] (* triple (pointer, lock, min, max) *)
  EX (pnt : val) (trl : list (val * val * val * val)),
  PROP (pnt <> nullval)
  LOCAL ()
  SEP (mem_mgr gv;
       (match (Int.eq (Int.repr stt) (Int.repr 2%Z)) with
        | true => (post_insert_giveup1 p pnt x v min max trl g)
        | _    => (post_insert_giveup2 p pnt tp x v min
                   max trl r g)
        end)).


Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec; findnext_spec; insertOp_giveup_spec; 
                             inRange_spec; traverse_spec; 
                             surely_malloc_spec; insertOp_helper_spec ]).

Lemma insertOp_helper: semax_body Vprog Gprog f_insertOp_helper insertOp_helper_spec.
Proof.
  start_function.
  forward_call (x, stt, v, p, tp, min, max, r, g, gv).
  Intros pnt.
  Exists pnt.1.
  Exists pnt.2.
  entailer !.
Qed.

End give_up_specs.
