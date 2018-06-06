(** * bordernode_rep.v : Formalization for representation relationship of bordernode *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import DB.common.

(* seplog part *)
Require Import DB.representation.string.

(* program part *)
Require Import DB.prog.

Definition tkey: type := Tstruct _KVKey noattr.
Definition tkeybox: type := tptr tkey.

Definition key_rep (sh: share) (key: string) (p: val) (p':val) :=
  data_at sh tkey (p', Vint (Int.repr (Zlength key))) p *
  malloc_token Tsh (tarray tschar (Zlength key)) p' *
  cstring_len Tsh key p'.

Definition keybox_rep (sh: share) (key: option string) (p: val) :=
  match key with
  | Some key =>
    EX k: val, EX k': val, data_at sh tkeybox k p * key_rep Tsh key k k' * malloc_token Tsh tkey k 
  | None =>
    data_at sh tkeybox nullval p
  end.

Lemma keyrep_local_facts (sh: share) (key: string) (p p': val):
  key_rep sh key p p' |-- !! (isptr p /\ isptr p').
Proof.
  unfold key_rep.
  entailer!.
Qed.
Hint Resolve keyrep_local_facts: saturate_local.

Lemma keyrep_fold (sh: share) (key: string) (p: val) (p': val):
  data_at sh tkey (p', Vint (Int.repr (Zlength key))) p * malloc_token Tsh (tarray tschar (Zlength key)) p' * cstring_len Tsh key p' |--
  key_rep sh key p p'.
Proof.
  unfold key_rep.
  cancel.
Qed.

Ltac fold_keyrep :=
  try fold_cstring_len;
  match goal with
  | |- context [data_at ?sh tkey (?p', Vint (Int.repr ?len)) ?p] =>
    match goal with
    | |- context [cstring_len Tsh ?key p'] =>
      match goal with
      | |- context [malloc_token Tsh (tarray tschar ?len') p'] =>
        replace len with (Zlength key) by list_solve;
        replace len' with (Zlength key) by list_solve;
        sep_apply (keyrep_fold sh key p p')
      end
    end
  end.

Lemma fold_keyrep_example (sh: share) (key1 key2: string) (p: val) (p': val):
  0 < Zlength key1 + Zlength key2 <= Int.max_unsigned ->
  data_at sh tkey (p', Vint (Int.repr (Zlength key1 + Zlength key2))) p * data_at Tsh (tarray tschar (Zlength (key1 ++ key2))) (map Vbyte key1 ++ map Vbyte key2) p' * malloc_token Tsh (tarray tschar (Zlength key1 + Zlength key2)) p' |-- key_rep sh (key1 ++ key2) p p'.
Proof.
  intros.
  rewrite <- map_app.
  fold_keyrep.
Abort.
