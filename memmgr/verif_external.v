Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import malloc_lemmas.
(* Require Import mmap0. *)
Require Import spec_malloc.
Require Import linking.
Require Import spec_external.

Definition Gprog : funspecs := [placeholder_spec].

(*
Lemma body_placeholder: semax_body Vprog Gprog f_placeholder spec_external.placeholder_spec.
Proof.
start_function.
contradiction.
Qed.
*)

Parameter body_mmap0:
 forall {Espec: OracleKind} {cs: compspecs},
  VST.floyd.library.body_lemma_of_funspec
    (EF_external "mmap0"
       {| sig_args := AST.Tptr :: AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tlong::nil;
          sig_res := Some AST.Tint; sig_cc := cc_default |})
    (snd mmap0_spec).

Parameter body_munmap:
 forall {Espec: OracleKind} {cs: compspecs},
  VST.floyd.library.body_lemma_of_funspec
    (EF_external "munmap"
       {| sig_args := AST.Tptr :: AST.Tint :: nil; (* TODO Tint for size_t *)
          sig_res := Some AST.Tint; 
          sig_cc := cc_default |})
    (snd munmap_spec).

Lemma tcret_mmap0: tcret_proof (tptr tvoid) (rmaps.ConstType Z)
  (fun (_ : list Type) (n : Z) =>
   (EX p:val, 
     PROP ( if eq_dec p nullval
            then True else malloc_compatible n p )
     LOCAL (temp ret_temp p)
     SEP ( if eq_dec p nullval
           then emp else memory_block Tsh n p))%assert).
Proof. (* This proof is horrible, this whole concept should be systematized. *)
 red. intros.
 rewrite exp_unfold. Intros p.
 rewrite <- insert_local.
 rewrite lower_andp.
 apply derives_extract_prop; intro.
 destruct H0; unfold_lift in H0. rewrite retval_ext_rval in H0.
 subst p.
 if_tac.
 destruct ret; inv H0.
 simpl in H2. rewrite H2.
 entailer!.
 renormalize. entailer!.
 destruct ret; try contradiction.
 simpl in H3. destruct v; try contradiction. 
 hnf; simpl; auto.
Qed.

Lemma tcret_munmap: tcret_proof tint (rmaps.ConstType (val * Z))
  (fun (_ : list Type) (x : val * Z) =>
   let (p,n) := x in 
   (EX res: Z,
     PROP () 
     LOCAL (temp ret_temp (Vint (Int.repr res)))
     SEP ( emp ) )%assert).
Proof. (* This proof is horrible, this whole concept should be systematized. *)
 red. intros. destruct x.
 rewrite exp_unfold. Intros p.
 rewrite <- insert_local.
 rewrite lower_andp.
 apply derives_extract_prop; intro.
 destruct H0; unfold_lift in H0. rewrite retval_ext_rval in H0.
 destruct ret; inv H0.
 destruct v0; inv H2.
 entailer!.
Qed.


Existing Instance NullExtension.Espec.

Definition module : list semax_body_proof := 
 [mk_external mmap0._mmap0 (tptr tvoid) tcret_mmap0 body_mmap0;
  mk_external mmap0._munmap tint tcret_munmap body_munmap
 (* ;  mk_body body_placeholder *)].

