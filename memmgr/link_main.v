Require Import VST.floyd.proofauto.
Require Import linking.
Require main.
Require verif_malloc_free. 
Require verif_malloc_large.
Require verif_malloc_small. 
Require verif_free_small. 
Require verif_fill_bin.
Require verif_bin2size2bin. 
Require verif_external.
Require spec_main.
Require verif_main.


Definition allmodules := 
  verif_main.module ++ 
  verif_malloc_free.module ++
  verif_malloc_large.module ++
  verif_malloc_small.module ++
  verif_free_small.module ++
  verif_fill_bin.module ++
  verif_bin2size2bin.module ++ 
  verif_external.module ++ nil.

Definition Gprog := ltac:
  (let x := constr:(merge_Gprogs_of allmodules) in
   let x := eval hnf in x in
   let x := eval simpl in x in 
   exact x).

Ltac ifneeded_assert assertion prover :=
lazymatch goal with
| H: assertion |- _ => idtac
| _ => assert assertion by prover
end.

Ltac prove_cspecs_sub :=
 split3;
  repeat red; apply @sub_option_get; 
     repeat (apply Forall_cons; [reflexivity | ]);  apply Forall_nil.

Ltac assert_cspecs_sub L :=
 try match goal with 
| |- @semax_func _ _ _ ?cs _ _ _ =>
     match type of L with
     | @semax_body _ _ ?cs' _ _ =>
        ifneeded_assert (cspecs_sub cs' cs) prove_cspecs_sub
 end end.

Ltac semax_func_cons' L H ::=
 repeat (eapply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | LookupID | LookupB |]);
 assert_cspecs_sub L; 
 first [eapply semax_func_cons;
           [ reflexivity
           | repeat apply Forall_cons; try apply Forall_nil; try computable; reflexivity
           | unfold var_sizes_ok; repeat constructor; try (simpl; rep_omega)
           | reflexivity | LookupID | LookupB
           | apply_semax_body L
           | ]
        | eapply semax_func_cons_ext;
             [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
             | apply H | LookupID | LookupB | apply L |
             ]
        ];
 repeat (eapply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | LookupID | LookupB |]).

Ltac apply_semax_body L ::=
eapply (@semax_body_subsumption' _ _ _ _ _ _ _ _ L);
 [ (solve[auto] || fail 99 "cspecs_sub failed")
 | repeat (apply Forall_cons; [ reflexivity | ]); apply Forall_nil
 | simple apply tycontext_sub_refl ||
  (apply tycontext_sub_i99;
  [ apply sub_option_get;  repeat (apply Forall_cons; [reflexivity | ]);  apply Forall_nil
  | apply subsume_spec_get;
    repeat (apply Forall_cons; [apply subsumespec_refl | ]); apply Forall_nil])].

Lemma prog_correct:
  semax_prog spec_main.linked_prog spec_main.Vprog Gprog.
Proof.
unfold Gprog.
  prove_semax_prog.
  do_semax_body_proofs (SortBodyProof.sort allmodules).
Admitted.
