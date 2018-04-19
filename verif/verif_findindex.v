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
    unfold abbreviate in POSTCONDITION.
    

    Locate Z.pos.
  check_Delta; check_POSTCONDITION;
 repeat apply -> semax_seq_skip;
 repeat (apply seq_assoc1; try apply -> semax_seq_skip).
  apply semax_if_seq.
match goal with
| |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Sifthenelse ?e ?c1 ?c2) _ =>
   let HRE := fresh "H" in let v := fresh "v" in
    evar (v: val);
    do_compute_expr Delta P Q R e v HRE;
    simpl in v;
    apply (semax_ifthenelse_PQR' _ v);
    [ reflexivity
      | ..(* | entailer | assumption *)
(*      | clear HRE; subst v; apply semax_extract_PROP; intro HRE; *)
(*        do_repr_inj HRE; *)
(*        repeat (apply semax_extract_PROP; intro); *)
(*        try rewrite Int.signed_repr in HRE by rep_omega; *)
(*        abbreviate_semax *)
(*      | clear HRE; subst v; apply semax_extract_PROP; intro HRE; *)
(*        do_repr_inj HRE; *)
(*        repeat (apply semax_extract_PROP; intro); *)
(*        try rewrite Int.signed_repr in HRE by rep_omega; *)
(*        abbreviate_semax*)
     ]
(* | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Ssequence (Sifthenelse ?e ?c1 ?c2) _) _ => *)
(*     tryif (unify (orb (quickflow c1 nofallthrough) (quickflow c2 nofallthrough)) true) *)
(*     then (apply semax_if_seq; forward_if'_new) *)
(*     else fail 100 "Because your if-statement is followed by another statement, you need to do 'forward_if Post', where Post is a postcondition of type (environ->mpred) or of type Prop" *)
(* | |- semax _ (@exp _ _ _ _) _ _ => *)
(*       fail 100 "First use Intros ... to take care of the EXistentially quantified variables in the precondition" *)
(* | |- semax _ _ (Sswitch _ _) _ => *)
(*   forward_switch' *)
(* | |- semax _ _ (Ssequence (Sifthenelse _ _ _) _) _ =>  *)
(*      fail 100 "forward_if failed for some unknown reason, perhaps your precondition is not in canonical form" *)
(* | |- semax _ _ (Ssequence (Sswitch _ _) _) _ =>  *)
(*      fail 100 "Because your switch statement is followed by another statement, you need to do 'forward_if Post', where Post is a postcondition of type (environ->mpred) or of type Prop" *)
end.
Ltac try_conjuncts_solver ::=
  lazymatch goal with H:_ |- ?A =>
         no_evars A;
         clear H; try immediate; auto; prove_it_now; fail
  end.

clear. simpl tc_expr. go_lower. clear.


 intros;
 try match goal with POSTCONDITION := @abbreviate ret_assert _ |- _ =>
        clear POSTCONDITION
      end;
 try match goal with MORE_COMMANDS := @abbreviate statement _ |- _ =>
        clear MORE_COMMANDS
      end;
 match goal with
 | |- local _ && ?P |-- _ => go_lower; try simple apply empTrue
 | |- ?P |-- _ =>
    match type of P with
    | ?T => unify T mpred; pull_out_props
    end
 | |- _ => fail "The entailer tactic works only on entailments  _ |-- _ "
 end.
 saturate_local.
 ent_iter.
 simple apply prop_right. simpl. clear.
 rewrite ?isptr_force_ptr by auto.
 let H := fresh in eapply my_auto_lem.
 intro H.
 instantiate (1:=True) in H.
 rewrite ?intsigned_intrepr_bytesigned.
 {
Locate rep_omega.

 repeat match goal with
            |  x:= _ : Z |- _ => subst x
            |  x:= _ : nat |- _ => subst x
            |  x:= _ |- _ => clearbody x
            end;
  try autorewrite with rep_omega in *.
  unfold repable_signed in *.
  pose_Zlength_nonneg.
  pose_lemmas Byte.unsigned byte_unsigned' Byte.unsigned_range.
  pose_lemmas Byte.signed byte_signed' Byte.signed_range.
  pose_lemmas Int.unsigned int_unsigned' Int.unsigned_range.
  Locate pose_lemmas.
  match goal with
    |- context [Int.signed ?A] =>
    match type of (Int.signed_range A) with ?T =>
                                            pose proof (Int.signed_range A)
    end
  end.

  forget (numKeys_le le') as x.
(* change (Int.signed (Int.repr (Z.pos (Pos.of_succ_nat (numKeys_le le'))))) with (int_signed' (Int.repr (Z.pos (Pos.of_succ_nat (numKeys_le le'))))). *)
  clear. split.
  Locate int_signed'.
  {
    Set Printing Implicit.
    
   (* match goal with *)
   (*   |- context [Int.signed ?A] => *)
   (*   change (Int.signed A) with (int_signed' A) in * *)
  (* end. *)
  admit. 
}
  admit.
 }
 admit.
 admit.
 admit.
 admit.
  - admit.
}
Admitted.


Lemma body_findRecordIndex: semax_body Vprog Gprog f_findRecordIndex findRecordIndex_spec.
Proof.
  start_function.
  forward.                      (* i=0 *)
  destruct n as [ptr0 le isLeaf First Last x].
  pose (n:= btnode val ptr0 le isLeaf First Last x). fold n.
  forward_if (PROP ( ) LOCAL (temp _i (Vint (Int.repr 0)); temp _node p; temp _key (Vint (Int.repr key))) SEP (btnode_rep n p)).
  - apply denote_tc_test_eq_split.
    admit.
    entailer!.
  - forward.                    (* skip *)
    entailer!.
  - assert_PROP(False). unfold btnode_rep. entailer!.
    admit.                      (* offset_val 20 p = nullval should be a contradiction? *)
    contradiction.
  - rewrite unfold_btnode_rep. unfold n. Intros. subst x.
    forward.                    (* t'5=node->numKeys *)
    gather_SEP 0 1 2 3 4 5 6 7.
    replace_SEP 0 (btnode_rep n p).
    entailer!.
    { forward_if(PROP ( ) LOCAL (temp _t'5 (Vint (Int.repr (Z.of_nat (numKeys (btnode val ptr0 le isLeaf First Last p))))); temp _i (Vint (Int.repr 0)); temp _node p; temp _key (Vint (Int.repr key))) SEP (btnode_rep n p)).
      - forward.                (* skip *)
        entailer!.
      - admit.
        (* contradiction in H0 *)
      - rewrite unfold_btnode_rep. unfold n. Intros.
        forward.                (* t'4=node->numKeys *)
        forward_if.
        + forward.              (* return *)
          entailer!.
          assert(le= nil val). admit. (* true from H0 *)
          rewrite H12. simpl. auto.
        + forward.              (* skip *)
          forward.              (* i=0 *)
          gather_SEP 0 1 2 3 4 5 6 7.
          replace_SEP 0 (btnode_rep n p).
          entailer!. deadvars!.
{ forward_loop (EX i:Z, (PROP (i<= Z.of_nat (numKeys_le le))
     LOCAL (temp _i (Vint (Int.repr i)); temp _node p; temp _key (Vint (Int.repr key)))
     SEP (btnode_rep n p)))
               break:(EX i:Z, (PROP (i= Z.of_nat(numKeys_le le))
     LOCAL (temp _i (Vint (Int.repr i)); temp _node p; temp _key (Vint (Int.repr key)))
     SEP (btnode_rep n p))).
  - Exists 0. entailer!.
  - Intros i. rewrite unfold_btnode_rep. unfold n. Intros.
    forward.                    (* t'3=node->numKeys *)
    (* forward_if. => this one is stuck too*)
    admit.
  - Intros i. rewrite unfold_btnode_rep. unfold n. Intros.
    forward.                    (* t'1=node->numKeys *)
    forward.                    (* return *)
    entailer!.
    admit.                      (* loop invariant isn't strong enough *) } }
Admitted.