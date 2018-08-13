(** * specs.v : Collection of all related specs *)
Require Import VST.floyd.library.
Require Import DB.common.

(* functional definitions *)
Require Import DB.functional.keyslice.
Require Import DB.functional.bordernode.

(* spatial definitions *)
Require Import DB.representation.bordernode.
Require Import DB.representation.key.
Require Import DB.representation.string.
Require Import DB.representation.btree.
Require Import DB.representation.trie.

Require Export DB.prog.

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
    SEP (malloc_token Tsh t p * data_at_ Tsh t p).

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
  POST [ tptr tbordernode ] EX p:val,
  PROP ()
  LOCAL (temp ret_temp p)
  SEP (bordernode_rep Tsh BorderNode.empty p * malloc_token Tsh tbordernode p).

Definition BN_FreeBorderNode_spec: ident * funspec :=
  DECLARE _BN_FreeBorderNode
  WITH bordernode: BorderNode.table, p: val
  PRE [ _bordernode OF tptr tbordernode]
  PROP ()
  LOCAL (temp _bordernode p)
  SEP (bordernode_rep Tsh bordernode p; malloc_token Tsh tbordernode p)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP ().

Definition BN_SetPrefixValue_spec: ident * funspec :=
  DECLARE _BN_SetPrefixValue
  WITH sh: share, key: Z, bordernode: BorderNode.table, p: val, value: val
  PRE [ _bn OF tptr tbordernode, _i OF tint, _val OF tptr tvoid ]
  PROP (0 < key <= keyslice_length;
        writable_share sh)
  LOCAL (temp _i (Vint (Int.repr key));
         temp _bn p;
         temp _val value)
  SEP (bordernode_rep sh bordernode p)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP (bordernode_rep sh (BorderNode.put_prefix key value bordernode) p).

Definition BN_GetPrefixValue_spec: ident * funspec :=
  DECLARE _BN_GetPrefixValue
  WITH sh: share, key: Z, bordernode: BorderNode.table, p: val
  PRE [ _bn OF tptr tbordernode, _i OF tint ]
  PROP (0 < key <= keyslice_length;
        readable_share sh)
  LOCAL (temp _i (Vint (Int.repr key));
         temp _bn p)
  SEP (bordernode_rep sh bordernode p)
  POST [ tptr tvoid ]
  PROP ()
  LOCAL (temp ret_temp (BorderNode.get_prefix key bordernode))
  SEP (bordernode_rep sh bordernode p).

Definition BN_SetSuffixValue_spec: ident * funspec :=
  DECLARE _BN_SetSuffixValue
  WITH sh_string: share, key: string, s: val,
       sh_bordernode: share, bordernode: BorderNode.table, p: val,
       value: val
  PRE [ _bn OF tptr tbordernode, _suffix OF tptr tschar, _len OF tuint, _val OF tptr tvoid ]
  PROP (readable_share sh_string;
        writable_share sh_bordernode)
  LOCAL (temp _bn p;
         temp _suffix s;
         temp _len (Vint (Int.repr (Zlength key)));
         temp _val value)
  SEP (cstring_len sh_string key s;
       bordernode_rep sh_bordernode bordernode p)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP (cstring_len sh_string key s;
       bordernode_rep sh_bordernode (BorderNode.put_suffix (Some key) value bordernode) p).

Definition BN_GetSuffixValue_spec: ident * funspec :=
  DECLARE _BN_GetSuffixValue
  WITH sh_string: share, key: string, s: val,
       sh_bordernode: share, bordernode: BorderNode.table, p: val
  PRE [ _bn OF tptr tbordernode, _suf OF tptr tschar, _len OF tuint ]
  PROP (readable_share sh_string;
        readable_share sh_bordernode)
  LOCAL (temp _bn p;
         temp _suf s;
         temp _len (Vint (Int.repr (Zlength key))))
  SEP (cstring_len sh_string key s;
       bordernode_rep sh_bordernode bordernode p)
  POST [ tptr tvoid ]
  PROP ()
  LOCAL (temp ret_temp (BorderNode.get_suffix (Some key) bordernode))
  SEP (cstring_len sh_string key s;
       bordernode_rep sh_bordernode bordernode p).

Definition BN_TestSuffix_spec: ident * funspec :=
  DECLARE _BN_TestSuffix
  WITH sh_key: share, key: string, k: val,
       sh_node: share, bordernode: BorderNode.table, p: val
  PRE [ _bn OF tptr tbordernode, _key OF tptr tkey ]                                    
  PROP (readable_share sh_key;
        readable_share sh_node;
        Zlength key > keyslice_length)
  LOCAL (temp _bn p;
         temp _key k)
  SEP (key_rep sh_key key k;
       bordernode_rep sh_node bordernode p)
  POST [ tint ]
  PROP ()
  LOCAL (temp ret_temp (if BorderNode.test_suffix (Some (get_suffix key)) bordernode then Vint Int.one else Vint Int.zero))
  SEP (key_rep sh_key key k;
       bordernode_rep sh_node bordernode p).

Definition BN_ExportSuffixValue_spec: ident * funspec :=
  DECLARE _BN_ExportSuffixValue
  WITH sh_bordernode: share, bordernode: BorderNode.table, p: val,
       sh_keybox: share, k: val
  PRE [ _bn OF tptr tbordernode, _key OF tptr tkeybox ]
  PROP (writable_share sh_bordernode;
        writable_share sh_keybox)
  LOCAL (temp _bn p;
         temp _key k)
  SEP (bordernode_rep sh_bordernode bordernode p;
       data_at_ sh_keybox tkeybox k)
  POST [ tptr tvoid ] EX k':val,
  PROP ()
  LOCAL (temp ret_temp (snd (BorderNode.get_suffix_pair bordernode)))
  SEP (bordernode_rep sh_bordernode (BorderNode.put_suffix None nullval bordernode) p;
       keybox_rep sh_keybox (fst (BorderNode.get_suffix_pair bordernode)) k).

Definition BN_GetLink_spec: ident * funspec :=
  DECLARE _BN_GetLink
  WITH sh_bordernode: share, bordernode: BorderNode.table, p: val
  PRE [ _bn OF tptr tbordernode ]
  PROP (readable_share sh_bordernode)
  LOCAL (temp _bn p)
  SEP (bordernode_rep sh_bordernode bordernode p)
  POST [ tptr tvoid ]
  PROP ()
  LOCAL (temp ret_temp (BorderNode.get_suffix None bordernode))
  SEP (bordernode_rep sh_bordernode bordernode p).

Definition BN_SetLink_spec: ident * funspec :=
  DECLARE _BN_SetLink
  WITH sh_bordernode: share, bordernode: BorderNode.table, p: val, value: val
  PRE [ _bn OF tptr tbordernode, _val OF tptr tvoid ]
  PROP (writable_share sh_bordernode)
  LOCAL (temp _bn p;
         temp _val value)
  SEP (bordernode_rep sh_bordernode bordernode p)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP (bordernode_rep sh_bordernode (BorderNode.put_suffix None value bordernode) p).

Definition BN_HasSuffix_spec: ident * funspec :=
  DECLARE _BN_HasSuffix
  WITH sh_bordernode: share, bordernode: BorderNode.table, p: val
  PRE [ _bn OF tptr tbordernode ]
  PROP (readable_share sh_bordernode)
  LOCAL (temp _bn p)
  SEP (bordernode_rep sh_bordernode bordernode p)
  POST [ tint ]
  PROP ()
  LOCAL (temp ret_temp (Vint ((if BorderNode.is_link bordernode then Int.zero else Int.one))))
  SEP (bordernode_rep sh_bordernode bordernode p).

Definition BN_SetValue_spec: ident * funspec :=
  DECLARE _BN_SetValue
  WITH sh_key: share, key: string, k: val,
       sh_node: share, bordernode: BorderNode.table, p: val,
       v: val
  PRE [ _bn OF tptr tbordernode, _key OF tptr tkey, _val OF tptr tvoid ]
  PROP (readable_share sh_key;
        writable_share sh_node)
  LOCAL (temp _bn p;
         temp _key k;
         temp _val v)
  SEP (bordernode_rep sh_node bordernode p;
         key_rep sh_key key k)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP (bordernode_rep sh_node (BorderNode.put_value key v bordernode) p;
       key_rep sh_key key k).

Definition move_key_spec: ident * funspec :=
  DECLARE _move_key
  WITH key: string, s: val 
  PRE [ _str OF tptr tschar, _len OF tuint ]
  PROP ()
  LOCAL (temp _str s;
         temp _len (Vint (Int.repr (Zlength key))))
  SEP (cstring_len Tsh key s;
       malloc_token Tsh (tarray tschar (Zlength key)) s)
  POST [ tptr tkey ] EX k:val,
  PROP ()
  LOCAL (temp ret_temp k)
  SEP (key_rep Tsh key k;
       malloc_token Tsh tkey k).

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
  WITH cs: (@Trie.table val * @BTree.cursor val * @BorderNode.table (@Trie.link val) * BorderNode.cursor),
       pnode_cursor: val, bnode_cursor: val,
       c: Trie.cursor, pc: val
  PRE [ _node_cursor OF tptr BTree.tcursor, _bnode_cursor OF tuint, _cursor OF tptr Trie.tcursor ]
  PROP ()
  LOCAL (temp _node_cursor pnode_cursor; temp _bnode_cursor bnode_cursor; temp _cursor pc)
  SEP (Trie.cursor_slice_rep cs (pnode_cursor, bnode_cursor); Trie.cursor_rep c pc)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP (Trie.cursor_rep (c ++ [cs]) pc).

Definition pop_cursor_spec: ident * funspec :=
  DECLARE _pop_cursor
  WITH c: Trie.cursor, pc: val
  PRE [ _cursor OF tptr Trie.tcursor ]
  PROP ()
  LOCAL (temp _cursor pc)
  SEP (Trie.cursor_rep c pc)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP (Trie.cursor_rep (removelast c) pc).

Definition _make_cursor_spec: ident * funspec :=
  DECLARE __make_cursor
  WITH c: @Trie.cursor val, pc: val,
       k: string, pk: val,
       t: @Trie.table val, pt: val
  PRE [ _key OF tptr tkey, _index OF tptr Trie.tindex, _cursor OF tptr Trie.tcursor ]
  PROP (Trie.table_correct t)
  LOCAL (temp _key pk; temp _index pt; temp _cursor pc)
  SEP (Trie.table_rep t pt; key_rep Tsh k pk; Trie.cursor_rep c pc)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP (Trie.table_rep t pt; key_rep Tsh k pk; Trie.cursor_rep (c ++ (Trie.make_cursor k t)) pc).

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
       pk: val
  PRE [ _cursor OF tptr BTree.tcursor, _index OF tptr BTree.tindex, _key OF tptr tuint ]
  PROP (BTree.abs_rel c t)
  LOCAL (temp _cursor pc; temp _index pt; temp _key pk)
  SEP (BTree.table_rep t pt; BTree.cursor_rep c pc; data_at_ Tsh tuint pk)
  POST [ tint ]
  PROP ()
  LOCAL (temp ret_temp (if BTree.get_key c t then (Vint Int.one) else (Vint Int.zero)))
  SEP (BTree.table_rep t pt; BTree.cursor_rep c pc;
       match BTree.get_key c t with
       | Some k => data_at Tsh tuint (Vint (Int.repr k)) pk
       | None => data_at_ Tsh tuint pk
       end).

Definition Iget_value_spec: ident * funspec :=
  DECLARE _Iget_value
  WITH c: @BTree.cursor val, pc: val,
       t: @BTree.table val, pt: val,
       pv: val
  PRE [ _cursor OF tptr BTree.tcursor, _index OF tptr BTree.tindex, _value OF tptr (tptr tvoid) ]
  PROP (BTree.abs_rel c t)
  LOCAL (temp _cursor pc; temp _index pt; temp _value pv)
  SEP (BTree.table_rep t pt; BTree.cursor_rep c pc; data_at_ Tsh (tptr tvoid) pv)
  POST [ tint ]
  PROP ()
  LOCAL (temp ret_temp (if BTree.get_value c t then (Vint Int.one) else (Vint Int.zero)))
  SEP (BTree.table_rep t pt; BTree.cursor_rep c pc;
       match BTree.get_value c t with
       | Some v => data_at Tsh (tptr tvoid) v pv
       | None => data_at_ Tsh (tptr tvoid) pv
       end).

(* Definition new_key. *)

(* Definition BN_CompareSuffix. *)
