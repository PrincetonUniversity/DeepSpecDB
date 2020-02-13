Require Import VST.floyd.proofauto.
Require Import linking.
Require main.
Require verif_malloc_free. 
Require verif_malloc_large.
Require verif_malloc_small. 
Require verif_free_large.
Require verif_free_small. 
Require verif_list_from_block.
Require verif_pre_fill.
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
  verif_free_large.module ++
  verif_free_small.module ++
  verif_list_from_block.module ++
  verif_pre_fill.module ++
  verif_fill_bin.module ++
  verif_bin2size2bin.module ++ 
  verif_external.module ++ nil.

Definition Gprog := ltac:
  (let x := constr:(merge_Gprogs_of allmodules) in
   let x := eval hnf in x in
   let x := eval simpl in x in 
   exact x).

Lemma prog_correct:
  semax_prog spec_main.linked_prog tt spec_main.Vprog Gprog.
Proof.
unfold Gprog.
  prove_semax_prog.
  do_semax_body_proofs (SortBodyProof.sort allmodules).


eapply semax_func_cons;
    [ reflexivity
           | repeat apply Forall_cons; try apply Forall_nil; try computable; reflexivity
           | unfold var_sizes_ok; repeat constructor; try (simpl; rep_omega)
           | reflexivity | LookupID | LookupB |
 .. (*
               apply_semax_body L
           | 
*)
].


eapply (@semax_body_subsumption' _ _ _ _ _ _ _ _ verif_pre_fill.body_pre_fill);
 [first [ apply cspecs_sub_refl
          | split3; red; apply @sub_option_get; 
            repeat (apply Forall_cons; [reflexivity | ]);  apply Forall_nil ]
 | repeat (apply Forall_cons; [ reflexivity | ]); apply Forall_nil
 | simple apply tycontext_sub_refl ||
  (apply tycontext_sub_i99;
  [ apply sub_option_get;  repeat (apply Forall_cons; [reflexivity | ]);  apply Forall_nil
  | apply subsume_spec_get;
idtac (*
    repeat (apply Forall_cons; [apply subsumespec_refl | ]); 
    apply Forall_nil
*) ])
].

{
repeat apply Forall_cons; try apply Forall_nil.
all: try apply subsumespec_refl.
simpl fst. simpl snd.
simpl PTree.get.

Qed.

