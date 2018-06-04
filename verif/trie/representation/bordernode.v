(** * bordernode_rep.v : Formalization for representation relationship of bordernode *)
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import deepDB.common.

(* functional part *)
Require Import deepDB.functional.keyslice.
Require Import deepDB.functional.bordernode.

(* seplogic part *)
Require Import deepDB.representation.string.

(* program part *)
Require Import deepDB.prog.

Lemma iter_sepcon_upd_Znth {A: Type} {Inh: Inhabitant A} (l: list A) (P: A -> mpred) (a: A) (k: Z):
  0 <= k < Zlength l ->
  iter_sepcon l P * P a = iter_sepcon (upd_Znth k l a) P * P (Znth k l).
Proof.
  intros.
  rewrite <- (sublist_same 0 (Zlength l) l) by reflexivity.
  rewrite sublist_same at 3 by reflexivity.
  rewrite (sublist_split 0 k (Zlength l) l) by list_solve.
  rewrite (sublist_split k (k + 1) (Zlength l) l) by list_solve.
  rewrite upd_Znth_app2 by list_solve.
  rewrite upd_Znth_app1 by list_solve.
  rewrite ?iter_sepcon_app.
  rewrite sublist_len_1 by list_solve.
  rewrite Zlength_sublist by list_solve.
  replace (k - (k - 0)) with 0 by omega.
  rewrite upd_Znth0.
  simpl.
  rewrite ?sepcon_emp.
  rewrite <- ?sepcon_assoc.
  pull_right (P a); f_equal;
    pull_right (P (Znth k l)); f_equal.
Qed.

Module BorderNodeValue <: DEC_VALUE_TYPE.
  Definition type := val.
  Definition default := nullval.
  Definition inhabitant_value := Vundef.
  Definition EqDec_value := EqDec_val.
End BorderNodeValue.

Module BorderNode := BorderNode BorderNodeValue.

Definition tbordernode := Tstruct _BorderNode noattr.

Import BorderNode.

Definition bordernode_rep (sh: share) (s: store) (p: val): mpred :=
  match s with
  | (prefixes, suffix, value) =>
    !! (Forall (fun p => is_pointer_or_null p) (prefixes)) &&
       !! (is_pointer_or_null value) &&
       malloc_token sh tbordernode p *
    field_at sh tbordernode [StructField _prefixLinks] prefixes p *
    field_at sh tbordernode [StructField _suffixLink] value p *
    match suffix with
    | Some k =>
      EX p': val,
             field_at sh tbordernode [StructField _keySuffix] p' p *
             field_at sh tbordernode [StructField _keySuffixLength] (Vint (Int.repr (Zlength k))) p *
             cstring_len Tsh k p' *
             malloc_token Tsh (tarray tschar (Zlength k)) p'
    | None =>
      field_at sh tbordernode [StructField _keySuffix] nullval p *
      field_at sh tbordernode [StructField _keySuffixLength] (Vint Int.zero) p
    end
  end.

Theorem bordernoderep_invariant (s: store): forall sh p,
    bordernode_rep sh s p |-- !! invariant s.
Proof.
  intros.
  unfold invariant.
  unfold bordernode_rep.
  destruct s as [[]].
  simpl.
  entailer!.
  destruct H2 as [? _].
  change (Z.max 0 4) with 4 in H2.
  assumption.
Qed.

Hint Resolve bordernoderep_invariant: saturate_local.

Definition bordernode_value_rep (P: value -> mpred) (s: store) : mpred :=
  iter_sepcon (fst (fst s)) P * P (snd s). 

Theorem put_prefix_value_rep (P: value -> mpred) (s: store) (k: prefix_key) (v: value):
  invariant s ->
  0 <= k < keyslice_length ->
  bordernode_value_rep P s * P v |-- bordernode_value_rep P (put_prefix k v s) * P (get_prefix k s).
Proof.
  intros.
  unfold bordernode_value_rep.
  unfold invariant in H.
  destruct s as [[]].
  simpl in *.
  cancel.
  sep_apply (iter_sepcon_upd_Znth l P v k ltac:(rep_omega)).
  apply derives_refl.
Qed.

Theorem put_suffix_value_rep (P: value -> mpred) (s: store) (k: suffix_key) (v: value):
  bordernode_value_rep P s * P v |-- bordernode_value_rep P (put_suffix k v s) * P (snd (get_suffix_pair s)).
Proof.
  intros.
  unfold bordernode_value_rep.
  destruct s as [[]].
  simpl.
  cancel.
Qed.

Definition tbordernode_fold: forall sh p prefixes v p' len,
  field_at sh tbordernode [StructField _prefixLinks] prefixes p *
  field_at sh tbordernode [StructField _suffixLink] v p *
  field_at sh tbordernode [StructField _keySuffix] p' p *
  field_at sh tbordernode [StructField _keySuffixLength] len p =
           data_at sh tbordernode (prefixes, (v, (p', len))) p.
Proof.
  intros.
  unfold_data_at 1%nat.
  do 2 rewrite <- sepcon_assoc.
  reflexivity.
Qed.

Ltac fold_tbordernode' lemma patterns :=
  match patterns with
  | nil => sep_apply lemma
  | ?hd :: ?tl => match goal with
                 | |- context [field_at _ _ [_ hd] ?t _] =>
                   fold_tbordernode' (lemma t) tl
                 | _ => fail 1 "pattern not found"
                 end
  end.

Ltac fold_tbordernode :=
  match goal with
  | |- context [field_at ?sh tbordernode _ _ ?p] =>
    fold_tbordernode' (tbordernode_fold sh p) [_prefixLinks; _suffixLink; _keySuffix; _keySuffixLength]
  end.
