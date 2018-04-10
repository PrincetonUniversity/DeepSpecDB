(** * verif_isvalid.v : Correctness proof of isValid, isFirst and RL_CursorIsValid *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import relation_mem.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.
Require Import btrees.
Require Import btrees_sep.
Require Import btrees_spec.
Require Import verif_currnode.
Require Import verif_entryindex.

Lemma body_isValid: semax_body Vprog Gprog f_isValid isValid_spec.
Proof.
  start_function.
  forward_call(r,pr,c,pc).      (* t'1=entryIndex(cursor) *)
  forward_call(r,pr,c,pc).      (* t'2=currNode *)
  unfold cursor_correct_rel in H0.
  apply cursor_subnode in H0.
  unfold relation_rep.
  destruct r as [[[root numRec] depth] prel]. autorewrite with norm.
  pose (r:=(root,numRec,depth,prel)).
  Intros proot. rewrite subnode_rep with (n:=currNode c (root,numRec,depth,prel)) by auto.
  Intros pcurr. subst. rewrite btnode_rep_getval at 1. normalize.
  pose (pcurr:=(getval (currNode c (root, numRec, depth, pr)))).
  rewrite unfold_btnode_rep at 1. fold pcurr.
  destruct (currNode c (root,numRec,depth,pr)) as [ptr0 le b First Last x]. Intros.
  pose (currnode:= btnode val ptr0 le b First Last x).
  forward.                      (* t'5=t'2->numKeys *)
  simpl in pcurr.

  forward_if (
     (PROP ( )
     LOCAL (temp _t'5 (Vint (Int.repr (Z.of_nat (numKeys (btnode val ptr0 le b First Last x)))));
            temp _t'2 pcurr; temp _t'1 (rep_index (entryIndex c)); temp _cursor pc;
            temp _t'3 (Val.of_bool (isValid c)) (* new local *)
           )
     SEP (field_at Tsh trelation [StructField _root] proot pr; malloc_token Tsh tbtnode pcurr;
     field_at Tsh tbtnode [StructField _numKeys]
       (Vint (Int.repr (Z.of_nat (numKeys (btnode val ptr0 le b First Last x))))) pcurr;
     field_at Tsh tbtnode [StructField _isLeaf] (Val.of_bool b) pcurr;
     field_at Tsh tbtnode [StructField _FirstLeaf] (Val.of_bool First) pcurr;
     field_at Tsh tbtnode [StructField _LastLeaf] (Val.of_bool Last) pcurr;
     match ptr0 with
     | Some (@btnode _ _ _ _ _ _ p' as n') =>
         field_at Tsh tbtnode [StructField _ptr0] p' pcurr * btnode_rep n' p'
     | None => field_at Tsh tbtnode [StructField _ptr0] nullval pcurr
     end; field_at Tsh tbtnode [StructField _entries] (le_to_list_complete le) pcurr;
     le_iter_sepcon le; btnode_rep (btnode val ptr0 le b First Last x) pcurr -* btnode_rep root proot;
     field_at Tsh trelation [StructField _numRecords] (Vint (Int.repr (Z.of_nat numRec))) pr;
     field_at Tsh trelation [StructField _depth] (Vint (Int.repr (Z.of_nat depth))) pr;
     malloc_token Tsh trelation pr; cursor_rep c (root, numRec, depth, pr) pc; emp)))%assert.

  - forward_call(r,pr,c,pc).
    + admit.
    + admit.
  - forward.                    (* t'3=0 *)
    admit.
  - admit.
Admitted.
  
Lemma body_RL_CursorIsValid: semax_body Vprog Gprog f_RL_CursorIsValid RL_CursorIsValid_spec.
Proof.
  start_function.
  forward_if (
      (PROP (pc<>nullval)  LOCAL (temp _cursor pc)  SEP (relation_rep r pr; cursor_rep c r pc))).
  - forward. entailer!.
  - subst. assert_PROP(False).
    entailer!. inv H1.
  - forward_call(r,pr,c,pc).
    Intros vret. forward.
    entailer!. unfold force_val, sem_cast_pointer.
    destruct (isValid c); simpl; auto.
Qed.

Lemma body_isFirst: semax_body Vprog Gprog f_isFirst isFirst_spec.
Proof.
  start_function.
  (* proof should be similar to isvalid *)
Admitted.
 