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

Check t_struct_node.

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

Check fst_snd_list.

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



Definition insertOp_giveup_spec :=
  DECLARE _insertOp_giveup
    WITH x: Z, stt: Z,  v: val, p: val, tp: val, min: Z, max: Z, r: node_info, g: gname, gv: globals
  PRE [ tptr t_struct_node, tint, tptr tvoid, tint ]
  PROP (repable_signed min; repable_signed max; repable_signed x;
        is_pointer_or_null v; key_in_range x r.1.2 = true; tp = nullval )
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt))
  GLOBALS (gv)
  SEP (mem_mgr gv;
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

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;  
                             insertOp_giveup_spec; 
                             surely_malloc_spec ]).

Lemma data_at_array_singleton: forall sh t v p, data_at sh (tarray t 1) [v] p |-- data_at sh t v p.
Proof.
  intros.
  unfold data_at, field_at; simpl; entailer!.
  { destruct H as (? & ? & Hsize & Halign & ?); split3; auto.
    destruct p; try discriminate; simpl in *; split3; auto.
    * rewrite Z.mul_1_r in Hsize; auto.
    * inv Halign; try discriminate.
      specialize (H6 0); rewrite Z.mul_0_r Z.add_0_r in H6; apply H6; lia. }
  unfold at_offset; unfold data_at_rec at 1; simpl.
  unfold array_pred, aggregate_pred.array_pred; simpl.
  unfold at_offset; entailer!.
  rewrite Z.mul_0_r; simpl.
  rewrite Znth_0_cons isptr_offset_val_zero; auto.
  auto.
  apply derives_refl.
Qed.

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
  assert_PROP (field_compatible t_struct_node (DOT _t) p). entailer !.
  forward.
  forward.
  simpl.
  forward_call (tarray t_struct_node 2, gv).
  simpl.
  computable.
  Intros pp1.
  forward.
  forward.
  rewrite data_at__Tarray.
  Check (reptype t_struct_node).
  assert_PROP (force_val (sem_add_ptr_int (tptr tvoid) Signed pp1 (vint 0)) = field_address (tarray t_struct_node 2) [] pp1).
  erewrite (split2_data_at_Tarray Ews t_struct_node 2 1 (Zrepeat (default_val t_struct_node) 2) _ _ _ pp1).
  change (2 - 1) with 1.
  Search tarray Tarray.
  change (Tarray t_struct_node 1 noattr) with (tarray t_struct_node 1).
  sep_apply (data_at_array_singleton Ews t_struct_node _ pp1).
  forward.
    with (p:= pp1).
  



  assert_PROP (force_val (sem_add_ptr_int (tptr tvoid) Signed pp1 (vint 0)) = field_address (tarray t_struct_node 2) [] pp1).
  entailer !. simpl. admit.
  Check data_at__Tarray.
  rewrite data_at__Tarray.
  Check split2_data_at_Tarray Ews t_struct_node 2 1 (Zrepeat (default_val t_struct_node) 2)  _ .
  erewrite (split2_data_at_Tarray Ews t_struct_node 2 1 (Zrepeat (default_val t_struct_node) 2) _ []).
  simpl.
  sep_apply (data_at_array_singleton Ews (Tarray t_struct_node 1 noattr))  .

  unfold_data_at (data_at Ews _ _ pp1).
  forward.
  Intros.
  forward.
  unfold_data_at (data_at_ _ _ pp1).
  Print field_address .
  Search field_address field_compatible.
  rewrite field_address_offset. simpl. auto. admit. admit.
  forward.


  
  forward_call(x, stt, v, p, p1, p2, r, g, gv).
  entailer !.
  rewrite field_at_data_at'. simpl.
  entailer !.
  Intros pnt.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  Exists pnt.
  Exists [(p1, lock1, vint min, vint x); (p2, lock2, vint x, vint max)].
  entailer !.
  rewrite field_at_data_at'. simpl.
  unfold_data_at (data_at Ews _  _ p1).
  unfold_data_at (data_at Ews _  _ p2).
  entailer !.
Qed.


