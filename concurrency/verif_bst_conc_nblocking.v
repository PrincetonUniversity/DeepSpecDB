Require Import bst.bst_conc_lemmas.
Require Import bst.bst_conc_nblocking_spec.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import bst.bst_conc_nblocking.
Require Import VST.atomics.general_locks.
Require Import VST.progs.conclib.

Section Proofs.

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
start_function. 
forward.
forward_call ( (tptr t_struct_tree), gv).
{ simpl. repeat (split; auto); rep_omega. }
Intros ref. 
forward.

Admitted.

Fixpoint ghost_snap_tree (t: @ ghost_tree val ) (x:Z) (g_current:gname) (depth: Z) range : mpred := 
 match t, range with
 | E_ghost , _ => ghost_snap (range,  (@None ghost_info) ) g_current
 | (T_ghost a ga k v b gb ), (l, r) =>  ghost_snap  (range, (@Some ghost_info (x,v,ga,gb))) g_current *
   if (depth <> 0) then if(k<?x) then ghost_snap_tree a x ga (depth -1) (l, Finite_Integer x) else if(k >?x) then ghost_snap_tree b x gb (depth -1) (Finite_Integer x, r) else emp
 end.

 Definition insert_inv (b: val) (sh: share) (x: Z) (v: val) ( g_root:gname) gv (g:gname)  (inv_names : invG) (Q:mpred) (ref:val): environ -> mpred :=
( EX np: val, EX g_current:gname, EX tg: (@ghost_tree val), EX depth: Z,
PROP ( )
LOCAL (temp _ref ref; temp _temp np; temp _t b; temp _x (vint x); temp _value v; gvars gv)
SEP ( mem_mgr gv; malloc_token Ews (tptr t_struct_tree) ref * data_at_ Ews (tptr t_struct_tree) ref;
   atomic_shift (λ BST : tree, !! sorted_tree BST && tree_rep2 g g_root b sh BST) ∅ ⊤
     (λ (BST : tree) (_ : ()), fold_right_sepcon
          [!! sorted_tree (bst_conc_lemmas.insert x v BST) &&
          tree_rep2 g g_root b sh (bst_conc_lemmas.insert x v BST)]) (λ _ : (), Q);
         nodebox_rep sh b; ghost_snap_tree tg x g_current (Neg_Infinity, Pos_Infinity) ))%assert.

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
start_function.
Admitted.



End Proofs.