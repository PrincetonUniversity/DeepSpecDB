Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import malloc_lemmas.
Require Import mmap0.
Require Import spec_malloc.
Require Import linking.


Parameter body_mmap0:
 forall {Espec: OracleKind} {cs: compspecs},
  VST.floyd.library.body_lemma_of_funspec
    (EF_external "mmap0"
(* TODO Tint for size_t and off_t *)
       {| sig_args := AST.Tptr :: AST.Tint::AST.Tint::AST.Tint::AST.Tint::AST.Tint::nil;
          sig_res := None; sig_cc := cc_default |})
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
Admitted.

Lemma tcret_munmap: tcret_proof tint (rmaps.ConstType (val * Z))
  (fun (_ : list Type) (x : val * Z) =>
   let (p,n) := x in 
   (EX res: Z,
     PROP () 
     LOCAL (temp ret_temp (Vint (Int.repr res)))
     SEP ( emp ) )%assert).
Admitted.


Existing Instance NullExtension.Espec.

Definition module : list semax_body_proof := 
 [mk_external mmap0._mmap0 (tptr tvoid) tcret_mmap0 body_mmap0;
  mk_external mmap0._munmap tint tcret_munmap body_munmap].

