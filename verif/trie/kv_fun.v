(** * kvfun.v : Functional model KV Store *)
Require Import VST.floyd.functional_base.

Module Type KV_STORE.
  Parameter store: Type.
  Parameter key: Type.
  Parameter value: Type.
  Parameter default_val: value.
  Parameter empty: store.
  Parameter get: key -> store -> value.
  Parameter put: key -> value -> store -> store.
  Axiom get_empty: forall k,
      get k empty = default_val.
  Axiom get_put_same: forall k v s,
      get k (put k v s) = v.
  Axiom get_put_diff: forall k1 k2 v s,
      k1 <> k2 -> get k1 (put k2 v s) = get k1 s.
End KV_STORE.

(* TODO: An functional implementation of [KV_STORE] *)
