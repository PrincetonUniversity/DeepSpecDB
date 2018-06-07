Require Import VST.floyd.functional_base.
Require Import common.

Require Import DB.functional.kv.
Require Import DB.functional.keyslice.
Require Import DB.functional.bordernode.

Import Lists.List.ListNotations.

Module TrieKey: KEY_TYPE.
  Definition type: Type := string.
End TrieKey.

Module Trie.
  Definition key: Type := TrieKey.type.
  Variable value: Type.

  Inductive trie: Type :=
  | trienode_of: list (keyslice * (list link * option string * link)) -> trie
  with
  link: Type :=
  | value_of: value -> link
  | trie_of: trie -> link
  | nil: link.

  Module BorderNodeValue: VALUE_TYPE.
    Definition type := link.
    Definition default := nil.
    Definition inhabitant_value := nil.
  End BorderNodeValue.
  Module BorderNode := BorderNode BorderNodeValue.

  Definition empty: trie := trienode_of [].
End Trie.
