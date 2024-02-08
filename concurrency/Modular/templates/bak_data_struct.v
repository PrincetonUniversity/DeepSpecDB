Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.puretree.
(* Require Import bst.give_up_template. 
 Require Import bst.bst_inst. *)
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

(*
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.
*)

(* Definition t_struct_tree := Tstruct _node noattr.
Definition t_struct_tree_t := Tstruct _node_t noattr. 
Definition t_struct_node := Tstruct _node_t noattr.
Definition t_struct_pn := Tstruct _pn noattr. *)

Definition number2Z (x : number) : Z :=
  match x with
    | Finite_Integer y => y
    | Neg_Infinity => Int.min_signed
    | Pos_Infinity => Int.max_signed
  end.

(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)
(* FOUND = F, NOTFOUND = NF, NULLNEXT = NN *)
Inductive enum : Type := F | NF | NN.

Definition enums x : val :=
  match x with
  | F => Vint Int.zero
  | NF => Vint Int.one
  | NN => Vint (Int.repr 2%Z)
  end.

#[global] Instance enum_inhabited : Inhabitant (enum).
Proof.
  unfold Inhabitant; apply F.
Defined.

#[export] Instance pointer_lock : Ghost := discrete_PCM (val * val * range).
Definition ghost_info : Type := (key * val * (list val))%type.

(* This allows the range to be outdated while the ghost_info may be present or absent. *)
#[export] Instance node_ghost : Ghost := prod_PCM pointer_lock (exclusive_PCM (option ghost_info)).
Notation node_info := (@G node_ghost).

Definition in_tree (g: gname) (g1 : gname) (pn: val) (lock: val):=
      ghost_snap (P := gmap_ghost (K := gname)(A := discrete_PCM (val * val)) )
        ({[g1 := (pn, lock)]}) g.

Lemma in_tree_equiv g g_in p1 p2 lk1 lk2:
  in_tree g g_in p1 lk1 * in_tree g g_in p2 lk2 |-- !!((p1 = p2) /\ (lk1 = lk2)) .
Proof.
  iIntros "H".
  iPoseProof(ghost_snap_join' with "H") as (v') "(%H & _)".
  iPureIntro.
  specialize (H g_in).
  rewrite ! lookup_insert in H.
  inversion H; subst; inversion H3; inversion H0; auto.
Qed.

Lemma in_tree_duplicate g gin pn lock:
  in_tree g gin pn lock |-- in_tree g gin pn lock * in_tree g gin pn lock.
Proof. by rewrite - bi.persistent_sep_dup. Qed.

Section NodeRep.
  Class NodeRep : Type := {
      node_rep_R : val -> range -> option (option ghost_info) -> gname -> mpred;
      node_rep_R_valid_pointer: forall tp r g_in g, node_rep_R tp r g_in g |-- valid_pointer tp;
      node_rep_R_pointer_null: forall tp r g_in g, node_rep_R tp r g_in g |-- !! is_pointer_or_null tp;
      node_size: nat;
      node_null: forall r g_info, node_rep_R nullval r g_info = !!(g_info = Some None) && seplog.emp;
      key_node_in_range: forall tp x r1 r2 g_info, key_in_range x r1 -> range_incl r1 r2 = true -> node_rep_R tp r1 g_info |-- node_rep_R tp r2 g_info;
  }.
End NodeRep.
