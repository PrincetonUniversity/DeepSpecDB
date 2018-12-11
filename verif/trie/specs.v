(** * specs.v : Collection of all related specs *)
Require Import VST.floyd.library.
Require Import DB.common.

(* functional definitions *)
Require Import DB.functional.keyslice.
Require Import DB.functional.bordernode.
Require Import DB.functional.trie.

(* spatial definitions *)
Require Import DB.representation.key.
Require Import DB.representation.string.
Require Import DB.representation.btree.
Require Import DB.representation.trie.

Require Export DB.prog.

Import List.
Import common.

(* Specification for auxilary functions *)

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
    SEP (malloc_token Ews t p * data_at_ Ews t p).

Definition UTIL_GetNextKeySlice_spec: ident * funspec :=
  DECLARE _UTIL_GetNextKeySlice
  WITH sh: share, str: val, key: string
  PRE [ _str OF tptr tschar, _len OF tuint ]
  PROP (readable_share sh)
  LOCAL (temp _str str;
         temp _len (Vint (Int.repr (Zlength key))))
  SEP (cstring_len sh key str)
  POST [ (if Archi.ptr64 then tulong else tuint) ]
  PROP ()
  LOCAL (temp ret_temp (Vint (Int.repr (get_keyslice key)))) (* machine dependent spec *)
  SEP (cstring_len sh key str).

Definition UTIL_StrEqual_spec: ident * funspec :=
  DECLARE _UTIL_StrEqual
  WITH sh1: share, s1: val, str1: string,
       sh2: share, s2: val, str2: string
  PRE [ _a OF tptr tschar, _lenA OF tuint, _b OF tptr tschar, _lenB OF tuint ]
  PROP (readable_share sh1;
        readable_share sh2)
  LOCAL (temp _a s1;
         temp _lenA (Vint (Int.repr (Zlength str1)));
         temp _b s2;
         temp _lenB (Vint (Int.repr (Zlength str2))))
  SEP (cstring_len sh1 str1 s1;
       cstring_len sh2 str2 s2)
  POST [ tint ]
  PROP ()
  LOCAL (temp ret_temp (Vint (if eq_dec str1 str2 then Int.one else Int.zero)))
  SEP (cstring_len sh1 str1 s1;
       cstring_len sh2 str2 s2).

Definition BN_NewBorderNode_spec: ident * funspec :=
  DECLARE _BN_NewBorderNode
  WITH tt: unit
  PRE [ ]
  PROP ()
  LOCAL ()
  SEP ()
  POST [ tptr Trie.tbordernode ] EX p:val,
  PROP ()
  LOCAL (temp ret_temp p)
  SEP (Trie.bnode_rep (p, BorderNode.empty)).

Definition BN_FreeBorderNode_spec: ident * funspec :=
  DECLARE _BN_FreeBorderNode
  WITH bnode: Trie.bordernode val, p: val
  PRE [ _bordernode OF tptr Trie.tbordernode]
  PROP ()
  LOCAL (temp _bordernode p)
  SEP (Trie.bnode_rep (p, bnode); malloc_token Ews Trie.tbordernode p)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP ().

Definition BN_SetPrefixValue_spec: ident * funspec :=
  DECLARE _BN_SetPrefixValue
  WITH key: Z, bnode: Trie.bordernode val, p: val, value: val
  PRE [ _bn OF tptr Trie.tbordernode, _i OF tint, _val OF tptr tvoid ]
  PROP (0 < key <= keyslice_length)
  LOCAL (temp _i (Vint (Int.repr key));
         temp _bn p;
         temp _val value)
  SEP (Trie.bnode_rep (p, bnode))
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP (Trie.bnode_rep (p, (BorderNode.put_prefix key value bnode))).

Definition BN_GetPrefixValue_spec: ident * funspec :=
  DECLARE _BN_GetPrefixValue
  WITH key: Z, bnode: Trie.bordernode val, p: val,
       pret: val, sh_ret: share
  PRE [ _bn OF tptr Trie.tbordernode, _i OF tint, _val OF tptr (tptr tvoid) ]
  PROP (0 < key <= keyslice_length; writable_share sh_ret)
  LOCAL (temp _i (Vint (Int.repr key));
         temp _bn p;
         temp _val pret)
  SEP (Trie.bnode_rep (p, bnode); data_at_ sh_ret (tptr tvoid) pret)
  POST [ tint ]
  PROP ()
  LOCAL (temp ret_temp (if (BorderNode.get_prefix key bnode) then (vint 1) else (vint 0)))
  SEP (Trie.bnode_rep (p, bnode); data_at sh_ret (tptr tvoid) (force_val (BorderNode.get_prefix key bnode)) pret).

Definition BN_SetSuffixValue_spec: ident * funspec :=
  DECLARE _BN_SetSuffixValue
  WITH sh_string: share, key: string, s: val,
       bnode: Trie.bordernode val, p: val,
       value: val
  PRE [ _bn OF tptr Trie.tbordernode, _suffix OF tptr tschar, _len OF tuint, _val OF tptr tvoid ]
  PROP (readable_share sh_string)
  LOCAL (temp _bn p;
         temp _suffix s;
         temp _len (Vint (Int.repr (Zlength key)));
         temp _val value)
  SEP (cstring_len sh_string key s;
       Trie.bnode_rep (p, bnode))
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP (cstring_len sh_string key s;
       Trie.bnode_rep (p, (BorderNode.put_suffix key value bnode))).

Definition BN_GetSuffixValue_spec: ident * funspec :=
  DECLARE _BN_GetSuffixValue
  WITH sh_string: share, key: string, s: val,
       bnode: Trie.bordernode val, p: val,
       pret: val, sh_ret: share
  PRE [ _bn OF tptr Trie.tbordernode, _suf OF tptr tschar, _len OF tuint, _val OF tptr (tptr tvoid)]
  PROP (readable_share sh_string;
        writable_share sh_ret)
  LOCAL (temp _bn p;
         temp _suf s;
         temp _len (Vint (Int.repr (Zlength key)));
         temp _val pret)
  SEP (cstring_len sh_string key s;
       Trie.bnode_rep (p, bnode);
       data_at_ sh_ret (tptr tvoid) pret)
  POST [ tptr tvoid ]
  PROP ()
  LOCAL (temp ret_temp (if (BorderNode.get_suffix key bnode) then (vint 1) else (vint 0)))
  SEP (cstring_len sh_string key s;
       Trie.bnode_rep (p, bnode);
       data_at sh_ret (tptr tvoid) (force_val (BorderNode.get_suffix key bnode)) pret).

Definition BN_TestSuffix_spec: ident * funspec :=
  DECLARE _BN_TestSuffix
  WITH sh_key: share, key: string, k: val,
       bnode: Trie.bordernode val, p: val
  PRE [ _bn OF tptr Trie.tbordernode, _key OF tptr tkey ]                                    
  PROP (readable_share sh_key;
        Zlength key > keyslice_length)
  LOCAL (temp _bn p;
         temp _key k)
  SEP (key_rep sh_key key k;
       Trie.bnode_rep (p, bnode))
  POST [ tint ]
  PROP ()
  LOCAL (temp ret_temp (if BorderNode.test_suffix (get_suffix key) bnode then (vint 1) else (vint 0)))
  SEP (key_rep sh_key key k;
       Trie.bnode_rep (p, bnode)).

Definition BN_CompareSuffix_spec: ident * funspec :=
  DECLARE _BN_CompareSuffix
  WITH sh_key: share, key: string, k: val,
       bnode: Trie.bordernode val, p: val
  PRE [ _bn OF tptr Trie.tbordernode, _key OF tptr tkey ]                                    
  PROP (readable_share sh_key;
        Zlength key > keyslice_length)
  LOCAL (temp _bn p;
         temp _key k)
  SEP (key_rep sh_key key k;
       Trie.bnode_rep (p, bnode))
  POST [ tint ]
  PROP ()
  LOCAL (temp ret_temp (
                match bnode with
                | (_, Some (inl (k', _))) =>
                  if (functional.key.TrieKeyFacts.lt_dec k' (get_suffix key)) then
                    (vint 0)
                  else
                    (vint 1)
                | _ =>
                  Vundef
                end))
  SEP (key_rep sh_key key k;
       Trie.bnode_rep (p, bnode)).

Definition BN_ExportSuffixValue_spec: ident * funspec :=
  DECLARE _BN_ExportSuffixValue
  WITH bnode: Trie.bordernode val, p: val,
       sh_keybox: share, pk: val,
       sh_ret: share, pret: val
  PRE [ _bn OF tptr Trie.tbordernode, _key OF tptr tkeybox, _val OF tptr (tptr tvoid) ]
  PROP (writable_share sh_keybox; BorderNode.get_suffix_pair bnode <> None; writable_share sh_ret)
  LOCAL (temp _bn p;
         temp _key pk)
  SEP (Trie.bnode_rep (p, bnode);
         data_at_ sh_keybox tkeybox pk;
         data_at_ sh_ret (tptr tvoid) pret)
  POST [ tint ]
  PROP ()
  LOCAL (temp ret_temp (vint 1))
  SEP (Trie.bnode_rep (p, (fst bnode, None));
       match BorderNode.get_suffix_pair bnode with
       | Some (k, v) =>
         keybox_rep sh_keybox (Some k) pk * data_at sh_ret (tptr tvoid) v pret
       | None =>
         FF
       end).

Definition BN_GetLink_spec: ident * funspec :=
  DECLARE _BN_GetLink
  WITH bnode: Trie.bordernode val, p: val,
       pret: val, sh_ret: share                                             
  PRE [ _bn OF tptr Trie.tbordernode, _val OF tptr (tptr tvoid) ]
  PROP (writable_share sh_ret)
  LOCAL (temp _bn p; temp _val pret)
  SEP (Trie.bnode_rep (p, bnode); data_at_ sh_ret (tptr tvoid) pret)
  POST [ tint ]
  PROP ()
  LOCAL (temp ret_temp (if (BorderNode.get_link bnode) then (vint 1) else (vint 0)))
  SEP (Trie.bnode_rep (p, bnode);
       data_at sh_ret (tptr tvoid) match (BorderNode.get_link bnode) with
                                   | Some t' => (Trie.addr_of_trie t')
                                   | None => nullval
                                   end pret).

Definition BN_SetLink_spec: ident * funspec :=
  DECLARE _BN_SetLink
  WITH bnode: Trie.bordernode val, p: val, t: Trie.trie val
  PRE [ _bn OF tptr Trie.tbordernode, _val OF tptr tvoid ]
  PROP ()
  LOCAL (temp _bn p;
         temp _val (Trie.addr_of_trie t))
  SEP (Trie.bnode_rep (p, bnode); Trie.trie_rep t)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP (Trie.bnode_rep (p, BorderNode.put_link t bnode);
         match BorderNode.get_link bnode with
         | Some t' => Trie.trie_rep t'
         | None => emp
         end).

Definition BN_HasSuffix_spec: ident * funspec :=
  DECLARE _BN_HasSuffix
  WITH bnode: Trie.bordernode val, p: val
  PRE [ _bn OF tptr Trie.tbordernode ]
  PROP ()
  LOCAL (temp _bn p)
  SEP (Trie.bnode_rep (p, bnode))
  POST [ tint ]
  PROP ()
  LOCAL (temp ret_temp (if BorderNode.get_suffix_pair bnode then (vint 1) else (vint 0)))
  SEP (Trie.bnode_rep (p, bnode)).

Definition BN_SetValue_spec: ident * funspec :=
  DECLARE _BN_SetValue
  WITH sh_key: share, key: string, k: val,
       bnode: Trie.bordernode val, p: val,
       v: val
  PRE [ _bn OF tptr Trie.tbordernode, _key OF tptr tkey, _val OF tptr tvoid ]
  PROP (readable_share sh_key)
  LOCAL (temp _bn p;
         temp _key k;
         temp _val v)
  SEP (Trie.bnode_rep (p, bnode);
       key_rep sh_key key k)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP (Trie.bnode_rep (p, BorderNode.put_value key v bnode);
       key_rep sh_key key k).

Definition bordernode_next_cursor_spec: ident * funspec :=
  DECLARE _bordernode_next_cursor
  WITH bnode: Trie.bordernode val, pbnode: val,
       bnode_cursor: BorderNode.cursor
  PRE [ _bnode_cursor OF tuint, _bn OF tptr Trie.tbordernode ]
  PROP (BorderNode.cursor_correct bnode_cursor)
  LOCAL (temp _bnode_cursor (Vint (Int.repr (BorderNode.cursor_to_int bnode_cursor)));
         temp _bn pbnode)
  SEP (Trie.bnode_rep (pbnode, bnode))
  POST [ tuint ]
  PROP ()
  LOCAL (temp ret_temp (Vint (Int.repr (BorderNode.cursor_to_int (BorderNode.next_cursor bnode_cursor bnode)))))
  SEP (Trie.bnode_rep (pbnode, bnode)).

Definition move_key_spec: ident * funspec :=
  DECLARE _move_key
  WITH key: string, s: val 
  PRE [ _str OF tptr tschar, _len OF tuint ]
  PROP ()
  LOCAL (temp _str s;
         temp _len (Vint (Int.repr (Zlength key))))
  SEP (cstring_len Ews key s;
       malloc_token Ews (tarray tschar (Zlength key)) s)
  POST [ tptr tkey ] EX k:val,
  PROP ()
  LOCAL (temp ret_temp k)
  SEP (key_rep Ews key k;
       malloc_token Ews tkey k).

Definition new_key_spec: ident * funspec :=
  DECLARE _new_key
  WITH key: string, s: val 
  PRE [ _str OF tptr tschar, _len OF tuint ]
  PROP ()
  LOCAL (temp _str s;
         temp _len (Vint (Int.repr (Zlength key))))
  SEP (cstring_len Ews key s)
  POST [ tptr tkey ] EX k:val,
  PROP ()
  LOCAL (temp ret_temp k)
  SEP (key_rep Ews key k;
       malloc_token Ews tkey k;
       cstring_len Ews key s).

Definition free_key_spec: ident * funspec :=
  DECLARE _free_key
  WITH key: string, k: val 
  PRE [ _key OF tptr tkey ]
  PROP ()
  LOCAL (temp _key k)
  SEP (key_rep Ews key k;
       malloc_token Ews tkey k)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP ().

Definition new_cursor_spec: ident * funspec :=
  DECLARE _new_cursor
  WITH tt: unit
  PRE [ ]
  PROP ()
  LOCAL ()
  SEP ()
  POST [ tptr Trie.tcursor ] EX pc: val,
  PROP ()
  LOCAL (temp ret_temp pc)
  SEP (Trie.cursor_rep [] pc).

Definition push_cursor_spec: ident * funspec :=
  DECLARE _push_cursor
  WITH cs: (Trie.trie val * @BTree.cursor val * Trie.bordernode val * BorderNode.cursor),
       pnode: val, pnode_cursor: val, bnode_cursor: val,
       c: Trie.cursor val, pc: val
  PRE [ _node OF tptr Trie.ttrie, _node_cursor OF tptr BTree.tcursor, _bnode_cursor OF tuint, _cursor OF tptr Trie.tcursor ]
  PROP ()
  LOCAL (temp _node_cursor pnode_cursor; temp _bnode_cursor bnode_cursor; temp _cursor pc)
  SEP (Trie.cursor_slice_rep cs (pnode, (pnode_cursor, bnode_cursor)); Trie.cursor_rep c pc)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP (Trie.cursor_rep (c ++ [cs]) pc).

Definition pop_cursor_spec: ident * funspec :=
  DECLARE _pop_cursor
  WITH c: Trie.cursor val, pc: val
  PRE [ _cursor OF tptr Trie.tcursor ]
  PROP ()
  LOCAL (temp _cursor pc)
  SEP (Trie.cursor_rep c pc)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP (Trie.cursor_rep (removelast c) pc).

Definition make_cursor_spec: ident * funspec :=
  DECLARE _make_cursor
  WITH c: Trie.cursor val, pc: val,
       k: string, pk: val,
       t: Trie.trie val
  PRE [ _key OF tptr tkey, _index OF tptr Trie.ttrie, _cursor OF tptr Trie.tcursor ]
  PROP (Trie.trie_correct t)
  LOCAL (temp _key pk; temp _index (Trie.addr_of_trie t); temp _cursor pc)
  SEP (Trie.trie_rep t; key_rep Ews k pk; Trie.cursor_rep c pc)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP (Trie.trie_rep t; key_rep Ews k pk; Trie.cursor_rep (c ++ (Trie.make_cursor k t)) pc).

Definition strict_first_cursor_spec: ident * funspec :=
  DECLARE _strict_first_cursor
  WITH c: Trie.cursor val, pc: val,
       t: Trie.trie val
  PRE [ _index OF tptr Trie.ttrie, _cursor OF tptr Trie.tcursor ]
  PROP (Trie.trie_correct t)
  LOCAL (temp _index (Trie.addr_of_trie t); temp _cursor pc)
  SEP (Trie.trie_rep t; Trie.cursor_rep c pc)
  POST [ tint ]
  PROP ()
  LOCAL (temp ret_temp (if Trie.strict_first_cursor t then Vint Int.one else Vint Int.zero))
  SEP (Trie.trie_rep t; Trie.cursor_rep (c ++
                                           match Trie.strict_first_cursor t with
                                           | Some c' => c'
                                           | None => []
                                           end) pc).

Definition Iempty_spec: ident * funspec :=
  DECLARE _Iempty
  WITH tt: unit
  PRE [ ]
  PROP ()
  LOCAL ()
  SEP ()
  POST [ tptr BTree.tindex ] EX t: @BTree.table val, EX pt: val,
  PROP (BTree.empty t)
  LOCAL (temp ret_temp pt)
  SEP (BTree.table_rep t pt).

Definition Iput_spec: ident * funspec :=
  DECLARE _Iput
  WITH k: Z, v: val,
       t: @BTree.table val, pt: val,
       c: @BTree.cursor val, pc: val
  PRE [ _key OF tuint, _value OF tptr tvoid, _cursor OF tptr BTree.tcursor, _index OF tptr BTree.tindex ]
  PROP (BTree.abs_rel c t)
  LOCAL (temp _key (Vint (Int.repr k)); temp _value v;
         temp _cursor pc; temp _index pt)
  SEP (BTree.table_rep t pt; BTree.cursor_rep c pc)
  POST [ tvoid ]
  EX new_t: @BTree.table val, EX new_c: @BTree.cursor val,
  PROP (BTree.put k v c t new_c new_t)
  LOCAL ()
  SEP (BTree.table_rep new_t pt; BTree.cursor_rep new_c pc).

Definition create_pair_spec: ident * funspec :=
  DECLARE _create_pair
  WITH k1: string, k2: string, pk1: val, pk2: val, v1: val, v2: val
  PRE [ _key1 OF tptr tschar, _len1 OF tuint, _key2 OF tptr tschar, _len2 OF tuint,
        _v1 OF tptr tvoid, _v2 OF tptr tvoid ]
  PROP (0 < Zlength k1; 0 < Zlength k2; isptr v1; isptr v2)
  LOCAL (temp _key1 pk1; temp _key2 pk2;
         temp _len1 (Vint (Int.repr (Zlength k1))); temp _len2 (Vint (Int.repr (Zlength k2)));
         temp _v1 v1; temp _v2 v2)
  SEP (cstring_len Ews k1 pk1; cstring_len Ews k2 pk2)
  POST [ tptr Trie.ttrie ]
  EX t: Trie.trie val, EX c: Trie.cursor val,
  PROP (Trie.create_pair k1 k2 v1 v2 c t)
  LOCAL (temp ret_temp (Trie.addr_of_trie t))
  SEP (cstring_len Ews k1 pk1; cstring_len Ews k2 pk2; Trie.trie_rep t).

Definition put_spec: ident * funspec :=
  DECLARE _put
  WITH k: string, pk: val, v: val,
       t: Trie.trie val,
       c: Trie.cursor val
  PRE [ _key OF tptr tschar, _len OF tuint, _v OF tptr tvoid, _index OF tptr Trie.ttrie ]
  PROP (0 < Zlength k; isptr v; Trie.trie_correct t)
  LOCAL (temp _key pk;
         temp _len (Vint (Int.repr (Zlength k)));
         temp _v v;
         temp _index (Trie.addr_of_trie t))
  SEP (cstring_len Ews k pk; Trie.trie_rep t)
  POST [ tvoid ]
  EX new_t: @Trie.trie val, EX new_c: @Trie.cursor val,
  PROP (Trie.put k v c t new_c new_t)
  LOCAL ()
  SEP (cstring_len Ews k pk; Trie.trie_rep new_t).

Definition Imake_cursor_spec: ident * funspec :=
  DECLARE _Imake_cursor
  WITH k: Z,
       t: @BTree.table val, pt: val
  PRE [ _key OF tuint, _index OF tptr BTree.tindex ]
  PROP (0 <= k <= Int.max_unsigned; BTree.table_correct t)
  LOCAL (temp _key (Vint (Int.repr k)); temp _index pt)
  SEP (BTree.table_rep t pt)
  POST [ tptr BTree.tcursor ] EX pc: val,
  PROP ()
  LOCAL (temp ret_temp pc)
  SEP (BTree.table_rep t pt; BTree.cursor_rep (BTree.make_cursor k t) pc).

Definition Ifirst_cursor_spec: ident * funspec :=
  DECLARE _Ifirst_cursor
  WITH t: @BTree.table val, pt: val
  PRE [ _index OF tptr BTree.tindex ]
  PROP (BTree.table_correct t)
  LOCAL (temp _index pt)
  SEP (BTree.table_rep t pt)
  POST [ tptr BTree.tcursor ] EX pc: val,
  PROP ()
  LOCAL (temp ret_temp pc)
  SEP (BTree.table_rep t pt; BTree.cursor_rep (BTree.first_cursor t) pc).

Definition Ifree_cursor_spec: ident * funspec :=
  DECLARE _Ifree_cursor
  WITH c: @BTree.cursor val, pc: val
  PRE [ _cursor OF tptr BTree.tcursor ]
  PROP ()
  LOCAL (temp _cursor pc)
  SEP (BTree.cursor_rep c pc)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP ().

Definition Iget_key_spec: ident * funspec :=
  DECLARE _Iget_key
  WITH c: @BTree.cursor val, pc: val,
       t: @BTree.table val, pt: val,
       pk: val, ret_sh: share
  PRE [ _cursor OF tptr BTree.tcursor, _index OF tptr BTree.tindex, _key OF tptr tuint ]
  PROP (BTree.abs_rel c t; writable_share ret_sh)
  LOCAL (temp _cursor pc; temp _index pt; temp _key pk)
  SEP (BTree.table_rep t pt; BTree.cursor_rep c pc; data_at_ ret_sh tuint pk)
  POST [ tint ]
  PROP ()
  LOCAL (temp ret_temp (if BTree.get_key c t then (Vint Int.one) else (Vint Int.zero)))
  SEP (BTree.table_rep t pt; BTree.cursor_rep c pc;
       data_at ret_sh tuint match BTree.get_key c t with
                         | Some k => (Vint (Int.repr k))
                         | None => Vundef
                         end pk).

Definition Iget_value_spec: ident * funspec :=
  DECLARE _Iget_value
  WITH c: @BTree.cursor val, pc: val,
       t: @BTree.table val, pt: val,
       pv: val, ret_sh: share
  PRE [ _cursor OF tptr BTree.tcursor, _index OF tptr BTree.tindex, _value OF tptr (tptr tvoid) ]
  PROP (BTree.abs_rel c t; writable_share ret_sh)
  LOCAL (temp _cursor pc; temp _index pt; temp _value pv)
  SEP (BTree.table_rep t pt; BTree.cursor_rep c pc; data_at_ ret_sh (tptr tvoid) pv)
  POST [ tint ]
  PROP ()
  LOCAL (temp ret_temp (if BTree.get_value c t then (Vint Int.one) else (Vint Int.zero)))
  SEP (BTree.table_rep t pt; BTree.cursor_rep c pc;
       data_at ret_sh (tptr tvoid) match BTree.get_value c t with
                                | Some v => v
                                | None => Vundef
                                end pv).
