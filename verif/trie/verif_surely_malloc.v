(** * verif_surely_malloc.v: Correctness proof of surely malloc *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import surely_malloc.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Search (_ <= _ -> _ <= _ -> _ <= _ )%nat.

Definition surely_malloc_spec: ident * funspec :=
  DECLARE _surely_malloc
  WITH t:type
  PRE [ _n OF tuint ]
    PROP (0 <= sizeof t <= Int.max_unsigned;
          complete_legal_cosu_type t = true;
          natural_aligned natural_alignment t = true)
    LOCAL (temp _n (Vint (Int.repr (sizeof t))))
    SEP ()
  POST [ tptr tvoid ] EX p:_,
    PROP ()
    LOCAL (temp ret_temp p)
    SEP (malloc_token Tsh t p * data_at_ Tsh t p).

Definition Gprog : funspecs :=
  ltac:(with_library prog [
                       surely_malloc_spec
       ]).

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call t.
  Intros p.
  forward_if (p <> nullval).
  if_tac; entailer!.
  - forward_call tt.
    entailer!.
  - forward.
    entailer!.
  - Intros.
    rewrite if_false by auto.
    forward.
    Exists p.
    entailer!.
Qed.
