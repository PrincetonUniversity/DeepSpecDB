(** * verif_findindex.v : Correctness proof of findChildIndex and findRecordIndex *)

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
Require Import index.

Lemma body_findChildIndex: semax_body Vprog Gprog f_findChildIndex findChildIndex_spec.
Proof.
  start_function.
  forward.                      (* i=0 *)
  destruct n as [ptr0 le isLeaf First Last x].
  pose (n:= btnode val ptr0 le isLeaf First Last x). fold n.
  rewrite unfold_btnode_rep. unfold n. Intros. subst x.  
  forward.                      (* t'7=node->numKeys *)
  simpl in H. destruct isLeaf; try inv H.

  forward_if(PROP ( )
     LOCAL (temp _t'7 (Vint (Int.repr (Z.of_nat (numKeys (btnode val ptr0 le false First Last p)))));
     temp _i (Vint (Int.repr 0)); temp _node p; temp _key (Vint (Int.repr key)))
     SEP (malloc_token Tsh tbtnode p;
     field_at Tsh tbtnode [StructField _numKeys]
       (Vint (Int.repr (Z.of_nat (numKeys (btnode val ptr0 le false First Last p))))) p;
     field_at Tsh tbtnode [StructField _isLeaf] (Val.of_bool false) p;
     field_at Tsh tbtnode [StructField _FirstLeaf] (Val.of_bool First) p;
     field_at Tsh tbtnode [StructField _LastLeaf] (Val.of_bool Last) p;
     match ptr0 with
     | Some (@btnode _ _ _ _ _ _ p' as n') =>
         field_at Tsh tbtnode [StructField _ptr0] p' p * btnode_rep n' p'
     | None => field_at Tsh tbtnode [StructField _ptr0] nullval p
     end; field_at Tsh tbtnode [StructField _entries] (le_to_list_complete le) p; 
     le_iter_sepcon le)).

  - forward.                    (* skip *)
    entailer!. apply derives_refl.
  - admit.
    (* we need a theorem that says that because we are intern node, le isn't nil *)
  -  destruct le as [|e le'] eqn:HLE.
     admit.                    (* empty le not possible on intern leaves *)
     destruct e eqn:HE.
     admit.                    (* keyval should not be possible in an intern node *)
    forward.                    (* t'6=node->entries[0]->key *)
    forward_if.
    + forward.                  (* return *)
      entailer!. unfold findChildIndex'. simpl.
      assert (key <? k = true).
      admit.                    (* true because of H *)
      rewrite H11. auto.
      apply derives_refl.
    + forward.                  (* skip *)
      forward.                  (* i=0 *)
      gather_SEP 0 1 2 3 4 5 6 7 8.
      replace_SEP 0 (btnode_rep n p).
      entailer!. apply derives_refl. deadvars!.
      
{ forward_loop (EX i:Z, PROP(i<=idx_to_Z (findChildIndex n key)) LOCAL(temp _i (Vint(Int.repr i)); temp _node p; temp _key (Vint(Int.repr key))) SEP(btnode_rep n p))
                   break:(EX i:Z, PROP(i=idx_to_Z (findChildIndex n key)) LOCAL(temp _i (Vint(Int.repr i)); temp _node p; temp _key (Vint(Int.repr key))) SEP(btnode_rep n p)).

  - Exists 0. entailer!.
    assert (key <? k = false). admit.   (* true from H *)
    rewrite H10.
    admit.                      (* OK because fCI' is called with ip 0 *)
  - Intros i.
    rewrite unfold_btnode_rep. unfold n. Intros.
    forward.                    (* t'5=node->numKeys *)
    gather_SEP 0 1 2 3 4 5 6 7 8.
    replace_SEP 0 (btnode_rep n p).
    entailer!.
    assert((numKeys (btnode val ptr0 (cons val (keychild val k n0) le') false First Last p)) = S (numKeys_le le')). simpl. auto.
    rewrite H1.
    forward_if.
    (* why is this forward_if so long? *)

Admitted.


Lemma body_findRecordIndex: semax_body Vprog Gprog f_findRecordIndex findRecordIndex_spec.
Proof.
  start_function.
Admitted.

