Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.progs.conclib.
Require Import btrees.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import btrees_functional.
Require Import btrees_sep.

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
         PROP (Int.min_signed <= i <= Int.max_signed; i < num_keys n <= 2*param)
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

Definition Gprog : funspecs :=
        ltac:(with_library prog [ new_btree_spec ]).

Set Default Timeout 20.
Arguments proj_reptype _ _ _ v: simpl never.
Arguments force_lengthn A n xs default: simpl never.

Lemma body_ptr_at: semax_body Vprog Gprog f_ptr_at ptr_at_spec.
Proof.
  start_function.
  forward_if.
  + destruct n; unfold node_address, node_rep; fold node_rep;
    Intros; do 2 forward.
    { apply prop_right. rewrite Znth_underflow. reflexivity. rep_omega. }
    { entailer!. rewrite Zaux.Zlt_bool_true by assumption. reflexivity.
    unfold node_rep; fold node_rep. entailer!. }
  + forward_if.
    - forward.
    - destruct n; unfold node_address, node_rep; fold node_rep;
      Intros.
      { assert (h: snd (Znth i (complete 17 (map (fun '(k, ptr) => (vint k, proj1_sig ptr)) records))) = proj1_sig (snd (Znth i records))).
        { simpl in H0. destruct H0.
          rewrite Znth_complete, Znth_map by
          (try rewrite Zlength_map; fold K V; rep_omega).  now destruct Znth. }
        forward. entailer!. setoid_rewrite h. now destruct (snd (Znth i records)).
        forward. }
      { simpl in H0. destruct H0.
        assert (h: snd (Znth i (complete 17 (map (fun '(k, ptr) => (vint k, node_address ptr)) children))) = node_address (snd (Znth i children))).
        { rewrite Znth_complete, Znth_map by
              (try rewrite Zlength_map; fold K V; rep_omega).  now destruct Znth. }
        forward. entailer. setoid_rewrite h.
        rewrite iter_sepcon_Znth with (i0 := i) by rep_omega. cbn. entailer.
        forward.
        setoid_rewrite h. rewrite Zaux.Zlt_bool_false by omega. cbn.
        entailer!.
      }
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
