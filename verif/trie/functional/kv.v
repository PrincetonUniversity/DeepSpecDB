(** * kvfun.v : Functional model KV Store *)
Require Import VST.floyd.functional_base.
Require Import common.

Module Type KEY_TYPE.
  Parameter type: Type.
End KEY_TYPE.

Module Type KV_STORE (KeyType: KEY_TYPE).
  Parameter store: Type -> Type.
  Definition key: Type := KeyType.type.
  Variable value: Type.
  Parameter empty: store value.
  Parameter get: key -> store value -> option value.
  Parameter put: key -> value -> store value -> store value.
  Axiom get_empty: forall k,
      get k empty = None.
  Axiom get_put_same: forall k v s,
      get k (put k v s) = Some v.
  Axiom get_put_diff: forall k1 k2 v s,
      k1 <> k2 -> get k1 (put k2 v s) = get k1 s.
End KV_STORE.

(* TODO: An functional implementation of [KV_STORE] *)
