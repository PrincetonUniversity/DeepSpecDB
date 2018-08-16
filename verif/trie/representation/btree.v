(** * rep/trie.v : Formalization for representation relation of trie *)
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.

Require Export VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import DB.common.

(* functional part *)
Require Import DB.functional.keyslice.
Require Import DB.functional.cursored_kv.
Require Import DB.functional.btree.

Require Import DB.representation.string.

Require Import DB.prog.

Module KeysliceType := Z_as_OT.

Module BTree <: FLATTENABLE_TABLE KeysliceType.
  Module AbstractMod := (DB.functional.btree.BTree KeysliceType).
  Include AbstractMod.

  Definition tcursor: type := tvoid.
  Definition tindex: type := tvoid.

  Parameter table_rep: table val -> val -> mpred.
  Parameter cursor_rep: cursor val -> val -> mpred.

  Parameter table_rep_local_facts: forall t pt,
      table_rep t pt |-- !! isptr pt.

  Hint Resolve table_rep_local_facts: saturate_local.

  Parameter table_rep_valid_pointer: forall t pt,
      table_rep t pt |-- valid_pointer pt.

  Hint Resolve table_rep_local_facts: valid_pointer.
End BTree.

Module BTreeFacts := FlattenableTableFacts KeysliceType BTree.
