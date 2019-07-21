Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.progs.conclib.
Require Import btrees.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import btrees_functional.
Require Import btrees_sep.

Require Import Program.Basics. Require Import Program.Combinators.

Definition new_btree_spec : ident * funspec :=
  DECLARE _new_btree
  WITH gv: globals
  PRE [ ]
         PROP ()
         LOCAL (gvars gv)
         SEP (mem_mgr gv)
  POST [ tptr tbtree ]
    EX p:val, EX p_root: val,
         PROP ()
         LOCAL (temp ret_temp p)
         SEP (mem_mgr gv; btree_rep (leaf [] p_root) balanced_leaf p).

Definition ptr_at_spec : ident * funspec :=
  DECLARE _ptr_at
  WITH gv: globals, n: node, i: Z
  PRE [ _n OF tptr tnode, _i OF tint ]
         PROP (Int.min_signed <= i <= Int.max_signed;
              num_keys n <= 2*param)
         LOCAL (gvars gv; temp _n (node_address n); temp _i (vint i))
         SEP (mem_mgr gv; node_rep n)
  POST [ tptr tvoid ]
  let res :=
  match n with
  | leaf l p => proj1_sig (snd (Znth i l))
  | internal ptr0 l p => if i <? 0 then node_address ptr0 else node_address (snd (Znth i l))
  end in
         PROP ()
         LOCAL (temp ret_temp res)
         SEP (mem_mgr gv; node_rep n).

Definition move_to_key_spec : ident * funspec :=
  DECLARE _move_to_key
  WITH gv: globals, pc: val, root: node, old_k: K, k: K, depth: Z
  PRE [ _c OF tptr tcursor, _k OF tuint ]
         PROP (depth < 20; balanced depth root)
         LOCAL (gvars gv; temp _c pc; temp _k (vint k))
         SEP (mem_mgr gv; cursor_rep old_k root pc; node_rep root)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (mem_mgr gv; cursor_rep k root pc; node_rep root).

(*
Definition down_to_first_spec : ident * funspec :=
  DECLARE _down_to_first
  WITH gv: globals, pc: val, c_sigT: { root: node & cursor root }
  PRE [ _c OF tptr tcursor ]
         PROP (balanced depth (projT1 root_sigT))
         LOCAL (gvars gv; temp _c pc)
         SEP (mem_mgr gv; cursor_rep level (projT2 root_sigT) pc; node_rep (projT1 root_sigT))
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (mem_mgr gv; cursor_rep depth (down_to_first (projT2 root_sigT)); node_rep (projT1 rc)).
*)
Definition Gprog : funspecs :=
        ltac:(with_library prog [ new_btree_spec; ptr_at_spec; move_to_key_spec ]).

Set Default Timeout 20.
Arguments proj_reptype _ _ _ v: simpl never.

Lemma body_move_to_key: semax_body Vprog Gprog f_move_to_key move_to_key_spec.
Proof.
  start_function.
  forward_loop
    (EX level: Z,
     PROP (0 <= level <= Zlength (find_path old_k root) - 1)
     LOCAL (gvars gv; temp _c pc)
     SEP (mem_mgr gv; partial_cursor_rep old_k root level pc; node_rep root))
    break: (EX level: Z,
            PROP (level <= 0 \/ sublist 0 (level + 1) (find_path old_k root) = sublist 0 (level + 1) (find_path k root))
            LOCAL ()
            SEP (partial_cursor_rep old_k root level pc)).
  + Exists (Zlength (find_path old_k root) - 1). entailer!. rewrite (find_path_Zlength _ _ _ H0).
    apply depth_nonneg in H0. omega. apply derives_refl.
  + unfold partial_cursor_rep. Intros level ptree.
    forward.
    forward_if (PROP ()
                LOCAL (gvars gv; temp _c pc)
                SEP (mem_mgr gv;
                data_at Ews tcursor
                        (ptree,
                         (vint level,
                          complete max_depth (map (fun '(i0, n) => (vint i0, node_address n)) (find_path old_k root)))) pc; node_rep root)).
  - forward. forward. rewrite (find_path_Zlength _ _ _ H0) in H1. entailer!.
    entailer!.

Lemma body_ptr_at: semax_body Vprog Gprog f_ptr_at ptr_at_spec.
Proof.
  start_function.
  forward_if.
  + destruct n; unfold node_address, node_rep; fold node_rep;
    Intros; do 2 forward.
    { apply prop_right. rewrite Znth_underflow. reflexivity. rep_omega. }
    { entailer!. rewrite Zaux.Zlt_bool_true by assumption. reflexivity.
    unfold node_rep; fold node_rep. entailer!. }
  + assert (Int.min_signed <= num_keys n <= Int.max_signed).
    { split. destruct n; simpl num_keys; rep_omega. rep_omega. }

    destruct n; simpl node_rep; simpl node_address; simpl in H0; Intros.
    - forward. forward_if.
      ++ forward. apply prop_right.
         rewrite Znth_overflow by assumption. reflexivity.
      ++ assert (h: snd (Znth i (complete 17 (map (fun '(k, ptr) => (vint k, proj1_sig ptr)) records))) = proj1_sig (snd (Znth i records))).
           { rewrite Znth_complete, Znth_map by
                 (try rewrite Zlength_map; fold K V; rep_omega).  now destruct Znth. }
         forward.
         entailer. apply prop_right. setoid_rewrite h. now destruct (snd (Znth i records)).
         forward.
    - forward. forward_if.
      ++ forward. simpl node_rep. entailer!.
         rewrite Znth_overflow by assumption. rewrite Zaux.Zlt_bool_false by rep_omega.
         reflexivity.
      ++ assert (h: snd (Znth i (complete 17 (map (fun '(k, child) => (vint k, node_address child)) children))) = node_address (snd (Znth i children))).
           { rewrite Znth_complete, Znth_map by
                 (try rewrite Zlength_map; fold K V; rep_omega). now destruct Znth. }
         forward.
         entailer. setoid_rewrite h.
         rewrite iter_sepcon_Znth with (i0 := i) by rep_omega.
         unfold compose. destruct (snd (Znth i children)); simpl; entailer.
         forward. setoid_rewrite h. rewrite Zaux.Zlt_bool_false by omega. simpl. entailer!.
Qed.

Lemma body_new_btree: semax_body Vprog Gprog f_new_btree new_btree_spec.
Proof.
  start_function.
  forward_call (tbtree, gv).
  easy.
  Intro p.
  forward.
  forward_if
    (PROP ( )
     LOCAL (temp _t p; temp _t'2 p; gvars gv)
     SEP (mem_mgr gv; malloc_token Ews tbtree p; data_at_ Ews tbtree p)).
  + destruct eq_dec; entailer!.
  + subst. rewrite eq_dec_refl. forward_call tt. contradiction.
  + rewrite if_false by assumption.
    forward.
    entailer!.
  + forward_call (tnode, gv).
    easy.
    Intros p_root.
    forward.
    forward_if
     (PROP ( )
     LOCAL (temp _t'4 p_root; temp _t p; temp _t'2 p; gvars gv)
     SEP (mem_mgr gv; malloc_token Ews tnode p_root; data_at_ Ews tnode p_root;
     malloc_token Ews tbtree p; data_at Ews tbtree (p_root, (Vundef, Vundef)) p)).
  - destruct eq_dec; entailer.
  - subst; rewrite eq_dec_refl. forward_call tt. contradiction.
  - rewrite if_false by assumption.
    forward. entailer!.
  - do 9 forward.
    unfold btree_rep, node_rep, node_address.
    Exists p p_root.
    entailer!.
Qed.
n
