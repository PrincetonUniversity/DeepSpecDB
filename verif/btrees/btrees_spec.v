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
  POST [ tptr t_btree ]
    EX p:val, EX p_root: val,
         PROP ()
         LOCAL (temp ret_temp p)
         SEP (mem_mgr gv; btree_rep (leaf [] p_root) p).

Definition Gprog : funspecs :=
        ltac:(with_library prog [ new_btree_spec ]).

Set Default Timeout 30.

Lemma body_new_btree: semax_body Vprog Gprog f_new_btree new_btree_spec.
Proof.
  start_function.
  forward_call (t_btree, gv).
  easy.
  Intro p.
  forward.
  forward_if
    (PROP ( )
     LOCAL (temp _t p; temp _t'2 p; gvars gv)
     SEP (mem_mgr gv; malloc_token Ews t_btree p; data_at_ Ews t_btree p)).
  + destruct eq_dec; entailer!.
  + subst. rewrite eq_dec_refl. forward_call tt. contradiction.
  + rewrite if_false by assumption.
    forward.
    entailer!.
  + forward_call (t_node, gv).
    easy.
    Intro p_root.
    forward. simpl.
    forward_if
     (PROP ( )
     LOCAL (temp _t'4 p_root; temp _t p; temp _t'2 p; gvars gv)
     SEP (mem_mgr gv; malloc_token Ews t_node p_root; data_at_ Ews t_node p_root;
     malloc_token Ews t_btree p; data_at Ews t_btree (p_root, (Vundef, Vundef)) p)).
  - destruct eq_dec; entailer.
  - subst; rewrite eq_dec_refl. forward_call tt. contradiction.
  - rewrite if_false by assumption.
    forward. entailer!.
  - do 9 forward.
    unfold btree_rep, node_rep.
    Exists p p_root (Vint (Int.zero_ext 8 (Int.repr 1))).
    change Vnullptr with (vint 0). entailer.
    simpl. rewrite Zlength_nil. simpl nested_field_type. simpl nested_field_offset. cancel.
Qed.
