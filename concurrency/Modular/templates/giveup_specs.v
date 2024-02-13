Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import bst.giveup_template. (* giveup_template.c *)
Require Import bst.puretree.
(* Require Import bst.data_struct. *)
Require Export bst.giveup_lib.
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
  iIntros "((((((? & H) & ?) & ?) & ?) & ?) & ?)".
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


Definition post_insert_giveup1 (p pnt : val) (x: Z) v min max
  (trl : list (val * val * val * val)) g :=
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

Definition post_insert_giveup2 (p pnt tp: val) (x: Z) v min max
  (trl : list (val * val * val * val)) (r: node_info) g :=
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
       (match (Int.eq (Int.repr stt) (Int.repr 2%Z)) with
        | true => !!(tp = nullval /\ (r.2 = Some None)) 
        | false => !!(tp <> nullval)
       end) && seplog.emp *
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
       (match (Int.eq (Int.repr stt) (Int.repr 2%Z)) with
        | true => !!(tp = nullval /\ (r.2 = Some None)) 
        | false => !!(tp <> nullval)
       end) && seplog.emp *
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

Definition getLock_spec :=
  DECLARE _getLock
    WITH p: val, lk: val, lsh : share
  PRE [ tptr t_struct_node]
  PROP (readable_share lsh; is_pointer_or_null lk)
  PARAMS (p)
  GLOBALS ()
  SEP (field_at lsh t_struct_node (DOT _lock) lk p)
  POST[ tptr (Tstruct _atom_int noattr) ]
    PROP ()
    RETURN (lk)
    SEP (field_at lsh t_struct_node (DOT _lock) lk p ).

(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)

Definition post_traverse (b: val) x (g: gname) (e: enum) (p: val)
  (sh: share) (g_in: gname) (r: node_info):=
  !!( key_in_range x (r.1).2 = true ∧
      repable_signed (number2Z (r.1).2.1) /\ repable_signed (number2Z (r.1).2.2) /\
      is_pointer_or_null (((r.1).1).2) /\
        (match e with
         | NN => r.2 = Some None /\ ((r.1).1).1 = nullval
         | NF => ((r.1).1).1 <> nullval
         | F =>  r.2 = Some None /\ ((r.1).1).1 = nullval
         end)) && seplog.emp *
  data_at Ews t_struct_pn (p, p) b * in_tree g g_in p ((r.1).1).2 * node_lock_inv_pred g p g_in r.

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
  EX pt: enum * (val * (share * (gname * node_info ))) %type,
  PROP ()
  LOCAL (temp ret_temp (enums pt.1))
  SEP (mem_mgr gv; post_traverse b x g pt.1 pt.2.1 pt.2.2.1 pt.2.2.2.1 (pt.2.2.2).2)| (CSS g g_root M).

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

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec; findnext_spec;
                             insertOp_giveup_spec;
                             inRange_spec; traverse_spec; getLock_spec;
                             surely_malloc_spec; insertOp_helper_spec
         ]).

Lemma getLock: semax_body Vprog Gprog f_getLock getLock_spec.
Proof.
  start_function.
  forward. forward.
Qed.

Lemma insertOp_helper: semax_body Vprog Gprog f_insertOp_helper insertOp_helper_spec.
Proof.
  start_function.
  forward_call (x, stt, v, p, tp, min, max, r, g, gv).
  Intros pnt.
  Exists pnt.1.
  Exists pnt.2.
  entailer !.
Qed.

(*
(* traverse invariants *)
Definition traverse_inv (b: val) (n pnN': val) (sh: share)
                        (x : Z) (v: val) (g_root: gname) (lock: val) gv
                        (inv_names : invariants.invG) (g : gname) AS : environ -> mpred :=
  (EX (pnN p: val) (gN_in: gname) (lockN_in: val),
            PROP ()
            LOCAL (temp _p pnN'; temp _status (vint 2); temp _pn__2 b; temp _x (vint x);
                   (* temp _value v; *) gvars gv)
            SEP (data_at sh (t_struct_pn) (p, pnN) b;
                 in_tree g gN_in pnN lockN_in; in_tree g g_root pnN' lock;
                 !!(is_pointer_or_null lockN_in) && seplog.emp; AS; mem_mgr gv))%assert.

Definition traverse_inv_1 (b p: val) (sh: share) (x : Z) (g_root g_in g: gname) (r: node_info) :=
  data_at sh (t_struct_pn) (p, p) b * in_tree g g_in p r.1.1.2 *
  node_lock_inv_pred g p g_in r *
  (!!(key_in_range x r.1.2 = true (* /\ r.2 = Some None *) /\
      repable_signed (number2Z r.1.2.1) ∧
      repable_signed (number2Z r.1.2.2) /\ is_pointer_or_null r.1.1.2) && seplog.emp).

Definition traverse_inv_2 (b p: val) (sh : share) (x : Z) (g_root g_in g: gname) (r: node_info) :=
  data_at sh (t_struct_pn) (p, p) b *
  in_tree g g_in p r.1.1.2 *
  (* node_lock_inv_pred_1 g p g_in r x * *) (* modify it later*)
  (!!(repable_signed (number2Z r.1.2.1) ∧
      repable_signed (number2Z r.1.2.2) /\ is_pointer_or_null r.1.1.2) && seplog.emp).


(* PROVING traverse spec *)
Lemma traverse: semax_body Vprog Gprog f_traverse traverse_spec.
Proof.
  start_function.
  Intros p.
  forward.
  forward.
  set (AS := atomic_shift _ _ _ _ _ ).
  (* New pt: bool * (val * (share * (gname * node_info))) *)
  forward_loop (traverse_inv b n n Ews x v g_root lock gv inv_names g AS)
    break: (*consider to remove gsh *)
    (EX (flag: enum) (q : val) (gsh: share) (g_in: gname) (r: node_info),
     PROP() LOCAL(temp _status (enums flag))
     SEP((match flag with
            | F => ((traverse_inv_2 b q Ews x g_root g_in g r) *
                      (!!(r.1.1.1 <> nullval) && seplog.emp))
            | NF => ((traverse_inv_2 b q Ews x g_root g_in g r) *
                      (!!(r.1.1.1 <> nullval) && seplog.emp))
            | NN => ((traverse_inv_1 b q Ews x g_root g_in g r) *
                      (!!( r.1.1.1 = nullval) && seplog.emp)) end) *
                       Q (flag, (q, (gsh, (g_in, r)))) * mem_mgr gv)).
  - unfold traverse_inv.
    Exists n p g_root lock. sep_apply in_tree_duplicate. entailer !. 
  - (*go deeply into loop*) (*pre-condition*)
    unfold traverse_inv.
    Intros pn p1 g_in lock_in.
    gather_SEP AS (in_tree g g_in pn lock_in).
    viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in) *
                          (EX lsh, !!(readable_share lsh) &&
                                     field_at lsh t_struct_node (DOT _lock) lock_in pn)).
    { go_lower. apply lock_alloc. }
    Intros lsh.
    forward.
    forward.
    sep_apply in_tree_duplicate.
    (* acquire(pn->n->lock); *)
    forward_call acquire_inv_atomic (lock_in,
        AS  * (EX R, node_lock_inv_pred g pn g_in R)  ).
    {
      iIntros "[[[[[[HITlkin HITlkin1] HAS] H4] H5] HITlkin2] H7]".
      iCombine "HITlkin HAS" as "HITlkin".
      iCombine "HITlkin HITlkin1 H4 H5 HITlkin2 H7" as "HITAS".
      iVST.
      apply sepcon_derives; [| cancel_frame].
      unfold atomic_shift. iIntros "AU". iAuIntro; unfold atomic_acc; simpl.
      iDestruct "AU" as "[#HITlkin AU]".
      iMod "AU" as (m) "[Hm HClose]".
      iModIntro.
      iPoseProof (in_tree_inv g g_in g_root with "[$HITlkin $Hm]") as "InvLock".
      iDestruct "InvLock" as "(InvLock & _)".
      iDestruct "InvLock" as (r) "[H1 H2]".
      iExists _. iFrame.
      iSplit; iFrame.
      iIntros "H1".
      iSpecialize ("H2" with "H1").
      iFrame "HITlkin".
      iDestruct "HClose" as "[HClose _]".
      iSpecialize ("HClose" with "H2"); auto.
      iIntros (m') "((H1 & H1') & _)".
      iSpecialize ("H2" with "H1").
      iDestruct "HClose" as "[HClose _]".
      iSpecialize ("HClose" with "H2").
      iMod ("HClose").
      iFrame "HClose". by iExists _.
    }
    Intros r.
    forward.
    forward.
    unfold node_lock_inv_pred, node_rep.
    Intros.
    forward.
    (* inrange function *)
    forward_call(x, pn, (number2Z r.1.2.1), (number2Z r.1.2.2), Ews, gv).
    Intros succ1.
    assert_PROP(is_pointer_or_null r.1.1.1). entailer !.
    destruct succ1.
    + forward_if.
      forward.
      forward.
      (*tp = nullval --- pn->p->t == NULL; break*)
      forward_if.
      (* prove r.1.1.2 = lock_in *)
      gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
      assert_PROP (r.1.1.2 = lock_in) as Hlk.
      { sep_apply in_tree_equiv; entailer !. }
      Intros.
      rewrite Hlk.
      (* push back lock into invariant *)
      gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
      viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
      {
        go_lower.
        iIntros "((AU & #H) & H1)".
        iMod "AU" as (m) "[Hm HClose]".
        iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
        iDestruct "InvLock" as "(_ & InvLock)".
        iDestruct "InvLock" as (R) "[H1' H2']".
        unfold ltree.
        iDestruct "H1'" as (lsh1) "(%H12 & (H12 & H13))".
        iAssert(EX lsh0 : share,
           !! (field_compatible t_struct_node [] pn ∧ readable_share lsh0 ) &&
           (@field_at CompSpecs lsh0 t_struct_node (DOT _lock) lock_in pn *
               inv_for_lock lock_in R))
               with "[H1 H12 H13]" as "H1'".
        {
          destruct H12 as (Hf & Hrs).
          iPoseProof (lock_join with "[H1 H12]") as "H1".
          { iSplitL "H1"; iFrame; iPureIntro; auto. }
          iDestruct "H1" as (Lsh) "(% & H1)".
          iExists _. iFrame; iPureIntro; repeat (split; auto).
        }
        iSpecialize ("H2'" with "H1'").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2'").
        iMod "HClose". by iFrame.
      }
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                               (!!(y = (NN, (pn, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (NN, (pn, (Ews, (g_in, r))))).
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm".
        iFrame "Hm".
        iModIntro. iExists _.
        by iFrame "Hm".
      }
      (*proving it satisfies with the post condition of traverse *)
      Intros y.
      forward.
      forward.
      Exists NN pn Ews g_in r.
      unfold traverse_inv_1.
      unfold node_lock_inv_pred, node_rep.
      entailer !.
      destruct (r.1.2).
      eapply key_range; auto.
      by iIntros "(H & _)". 
      forward.
      assert_PROP(field_compatible t_struct_pn (DOT _n) b). entailer !.
      forward.
      (* findNext *)
      forward_call(x, r.1.1.1, (field_address t_struct_pn [StructField _n] b),
                   pn, r, g, Ews, gv).
      { unfold_data_at (data_at Ews t_struct_pn _ b). cancel. entailer !. }
      {
        Intros succ.
        (* assert_PROP(r.1.1.1 <> nullval) by entailer !. *)
        destruct succ.1.1; last first.
        Intros. 
        * (* NN => succ.1.2 = succ.2  *)
          (* not found and find the next point *)
          forward.
          forward_if.
          easy. (* contradiction *)
          forward_if.
          easy. (* contradiction *)
          forward.
          gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
          assert_PROP (r.1.1.2 = lock_in) as Hlk.
          { sep_apply in_tree_equiv; entailer !. }
          rewrite Hlk.
          Intros.
          forward.
          (* push back lock into invariant *)
          gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
          viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
          { go_lower.
            apply push_lock_back; auto.  }
          (* make in_tree of next node : in_tree g succ.2 pnext lknext *)
          Intros.
          gather_SEP AS (in_tree g g_in pn lock_in) (node_rep_R r.1.1.1 r.1.2 r.2 g)
                        (field_at _ _ _ _ pn)
                        (field_at Ews t_struct_node _ _ pn)
                        (field_at Ews t_struct_node _ _ pn)
                        (malloc_token Ews t_struct_node pn) (my_half g_in Tsh r).
          viewshift_SEP 0 (EX g_in1 lock1, AS * (node_lock_inv_pred g pn g_in r ) *
                                           (in_tree g g_in1 succ.2 lock1)).
          {
            go_lower.
            iIntros "(((((((AU & #H) & HNode) & H2) & H3) & H4) & H5) & H6)".
            iMod "AU" as (m) "[Hm HClose]".
            iPoseProof (ghost_update_step g g_in g_root pn succ.1.2 lock_in m r
                         with "[$H $Hm $HNode $H2 $H3 $H4 $H5 $H6]")
              as (g_in1 lock1) "((Inv & H1) & H2)".
            { rewrite <- Hlk. iFrame "H". done. }
            iExists g_in1, lock1.
            iSpecialize ("HClose" with "H1").
            rewrite H11.
            by iFrame "Inv H2".
          }
          (*Now we have in_tree g succ.2 pnext lknext *)
          Intros gnext lknext.
          (* _release(_t'8);) *)
          forward_call release_inv (lock_in, node_lock_inv_pred g pn g_in r, AS).
          {
            lock_props.
            iIntros "(((((((HAS & H1) & H2) & H3) & H4) & H5) & H6) & H7)".
            iCombine "HAS H1 H3 H2 H4 H5 H6 H7" as "Hnode_inv_pred".
            iVST.
            rewrite <- H11.
            rewrite <- 2sepcon_assoc; rewrite <- 2sepcon_comm.
            apply sepcon_derives; [| cancel_frame].
            unfold atomic_shift;
              iIntros "((AU & H1) & #H2)";

              iAuIntro; unfold atomic_acc; simpl.
            iMod "AU" as (m) "[Hm HClose]".
            iModIntro.
            iExists tt.
            iPoseProof (in_tree_inv' g g_in g_root pn (r.1.1.2) m r
                         with "[H2 H1 $Hm]") as "(HI1 & HI2)".
            { rewrite Hlk. iFrame "H1 H2". }
            iDestruct "HI1" as "(HI1' & HI1)".
            rewrite Hlk.
            iFrame "HI1' HI1".
            iSplit.
            {
              iIntros "(Hnode_Iinv & InvLock)".
              iSpecialize ("HI2" with "InvLock").
              iDestruct "HClose" as "[HClose _]".
              iFrame "Hnode_Iinv".
              iSpecialize ("HClose" with "HI2").
              iFrame.
            }
            iIntros (_) "(H & _)".
            iSpecialize ("HI2" with "H").
            iDestruct "HClose" as "[HClose _]". 
            by iSpecialize ("HClose" with "HI2").
         }
         (* proving |--  traverse_inv *)
         unfold traverse_inv.
         Exists succ.1.2 pn gnext lknext.
         entailer !. admit. (* is_pointer_or_null lknext *)
         unfold_data_at (data_at Ews t_struct_pn _ b).
         cancel. 
       * (* NF case *)
         forward.
         forward_if.
         forward.
         easy.
         forward_if.
         gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
         assert_PROP (r.1.1.2 = lock_in) as Hlk.
         { sep_apply in_tree_equiv; entailer !. }
         Intros.
         rewrite Hlk.
         (* push back lock into invariant *)
         gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
         viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
         {
           go_lower.
           iIntros "((AU & #H) & H1)".
           iMod "AU" as (m) "[Hm HClose]".
           iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
           iDestruct "InvLock" as "(_ & InvLock)".
           iDestruct "InvLock" as (R) "[H1' H2']".
           unfold ltree.
           iDestruct "H1'" as (lsh1) "(%K12 & (H12 & H13))".
           iAssert(EX lsh0 : share,
                      !! (field_compatible t_struct_node [] pn ∧ readable_share lsh0 ) &&
                        (@field_at CompSpecs lsh0 t_struct_node (DOT _lock) lock_in pn *
               inv_for_lock lock_in R))
               with "[H1 H12 H13]" as "H1'".
        {
          destruct K12 as (Hf & Hrs).
          iPoseProof (lock_join with "[H1 H12]") as "H1".
          { iSplitL "H1"; iFrame; iPureIntro; auto. }
          iDestruct "H1" as (Lsh) "(% & H1)".
          iExists _. iFrame; iPureIntro; repeat (split; auto).
        }
        iSpecialize ("H2'" with "H1'").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2'").
        iMod "HClose". by iFrame.
      }
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                               (!!(y = (NF, (succ.1.2, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (NF, (succ.1.2, (Ews, (g_in, r))))).
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm".
        iFrame "Hm".
        iModIntro. iExists _.
        by iFrame "Hm".
      }
      Intros y.
      rewrite <- H11.
      forward.
      forward.
      Exists NF succ.1.2 Ews g_in r.
      unfold traverse_inv_2.
      entailer !.
      unfold_data_at (data_at Ews t_struct_pn _ b).
      cancel.
      admit.
      (* re-modify traverse_inv_2 *)
      (* contradiction *)
      easy.
    * forward.
      forward_if.
      gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
      assert_PROP (r.1.1.2 = lock_in) as Hlk.
      { sep_apply in_tree_equiv; entailer !. }
      Intros.
      rewrite Hlk.
      (* push back lock into invariant *)
      gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
      viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
      {
        go_lower.
        iIntros "((AU & #H) & H1)".
        iMod "AU" as (m) "[Hm HClose]".
        iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
        iDestruct "InvLock" as "(_ & InvLock)".
        iDestruct "InvLock" as (R) "[H1' H2']".
        unfold ltree.
        iDestruct "H1'" as (lsh1) "(%K12 & (H12 & H13))".
        iAssert(EX lsh0 : share,
                      !! (field_compatible t_struct_node [] pn ∧ readable_share lsh0 ) &&
                        (@field_at CompSpecs lsh0 t_struct_node (DOT _lock) lock_in pn *
               inv_for_lock lock_in R))
               with "[H1 H12 H13]" as "H1'".
        {
          destruct K12 as (Hf & Hrs).
          iPoseProof (lock_join with "[H1 H12]") as "H1".
          { iSplitL "H1"; iFrame; iPureIntro; auto. }
          iDestruct "H1" as (Lsh) "(% & H1)".
          iExists _. iFrame; iPureIntro; repeat (split; auto).
        }
        iSpecialize ("H2'" with "H1'").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2'").
        iMod "HClose". by iFrame.
      }
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                               (!!(y = (F, (succ.1.2, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (F, (succ.1.2, (Ews, (g_in, r))))).
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm".
        iFrame "Hm".
        iModIntro. iExists _.
        by iFrame "Hm".
      }
      Intros y.
      rewrite <- H11.
      forward.
      forward.
      Exists F succ.1.2 Ews g_in r.
      unfold traverse_inv_2.
      (* re-modify traverse_inv_2 *)
      admit.
      (* contradiction *)
      easy.
    }
    easy.
  + forward_if.
    easy.
    forward.
    forward.
    gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
    assert_PROP (r.1.1.2 = lock_in) as Hlk.
    { sep_apply in_tree_equiv; entailer !. }
    rewrite Hlk.
    Intros.
      (* push back lock into invariant *)
    gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
    viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
    { go_lower; apply push_lock_back; auto. }
    Intros.
    gather_SEP AS (in_tree g g_in pn lock_in) (node_rep_R r.1.1.1 r.1.2 r.2 g)
                        (field_at _ _ _ _ pn)
                        (field_at Ews t_struct_node _ _ pn)
                        (field_at Ews t_struct_node _ _ pn)
                        (malloc_token Ews t_struct_node pn) (my_half g_in Tsh r).
    viewshift_SEP 0 (AS * (node_lock_inv_pred g pn g_in r )).
    {
            go_lower.
            iIntros "(((((((AU & #H) & HNode) & H2) & H3) & H4) & H5) & H6)".
            iFrame.
            rewrite <- Hlk. iFrame "H". done.
    }
    forward_call release_inv (lock_in, node_lock_inv_pred g pn g_in r, AS).
    {
        lock_props.
        iIntros "(((((HAS & H1) & H2) & H3) & H4) & H5)".
        iCombine "HAS H1 H2 H3 H4 H5" as "Hnode_inv_pred".
        iVST.
        rewrite <- 2sepcon_assoc; rewrite <- 2sepcon_comm.
        apply sepcon_derives; [| cancel_frame].
        unfold atomic_shift; iIntros "((AU & H1) & #H2)";

              iAuIntro; unfold atomic_acc; simpl.
        iMod "AU" as (m) "[Hm HClose]".
        iModIntro.
        iExists tt.
        iPoseProof (in_tree_inv' g g_in g_root pn (r.1.1.2) m r
                         with "[H2 H1 $Hm]") as "(HI1 & HI2)".
        { rewrite Hlk. iFrame "H1 H2". }
          iDestruct "HI1" as "(HI1' & HI1)".
          rewrite Hlk.
          iFrame "HI1' HI1".
          iSplit.
          {
            iIntros "(Hnode_Iinv & InvLock)".
            iSpecialize ("HI2" with "InvLock").
            iDestruct "HClose" as "[HClose _]".
            iFrame "Hnode_Iinv".
            iSpecialize ("HClose" with "HI2").
              iFrame.
          }
          iIntros (_) "(H & _)".
          iSpecialize ("HI2" with "H").
          iDestruct "HClose" as "[HClose _]". 
          by iSpecialize ("HClose" with "HI2").
     }
     (* proving |--  traverse_inv *)
       forward.
       unfold traverse_inv.
       Exists n pn g_root lock.
       sep_apply (in_tree_duplicate g g_root n).
       entailer !. 
    - (* semax Delta (PROP ( )  RETURN ( ) SEP ()) (return _flag;) POSTCONDITION *)
       Intros flag.
       Intros pn gsh g_in r.
       unfold traverse_inv_1, traverse_inv_2.
       destruct flag.
       (*
       + simpl.
         autorewrite with norm.
         forward.
         unfold post_traverse.
         Exists (true, (pn, (gsh, (g_in, r)))).
         simpl. entailer !. 
       + forward.
         Exists (false, (pn, (gsh, (g_in, r)))).
         simpl.
         unfold node_lock_inv_pred_1, node_rep_1 at 1, tree_rep_R_1 at 1.
         Intros g1 g2 v1 p1 p2 l1 l2.
         rewrite H7.
         entailer !.
         exists v1, g1, g2; auto.
         unfold node_lock_inv_pred, node_rep, tree_rep_R.
         rewrite -> if_false; auto.
         simpl.
         Exists g1 g2 x v1 p1 p2 l1 l2.
         entailer !. apply derives_refl.
Qed.
*)
*)

End give_up_specs.
