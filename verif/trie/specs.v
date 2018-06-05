(** * specs.v : Collection of all related specs *)
Require Import VST.floyd.library.
Require Import DB.common.

(* functional definitions *)
Require Import DB.functional.keyslice.
Require Import DB.representation.bordernode.
Require Import DB.representation.key.
Require Import DB.representation.string.

Require Export DB.prog.

(* Specification for [surely_malloc.c] *)

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

(* Specification for [util.c] *)

Definition UTIL_GetNextKeySlice_spec: ident * funspec :=
  DECLARE _UTIL_GetNextKeySlice
  WITH sh: share, str: val, key: string
  PRE [ _str OF tptr tschar, _len OF tint ]
  PROP (readable_share sh;
        0 <= Zlength key <= keyslice_length)
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

(* Specification for [bordernode.c] *)

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
  SEP (bordernode_rep Tsh BorderNode.empty p).

Definition BN_SetPrefixValue_spec: ident * funspec :=
  DECLARE _BN_SetPrefixValue
  WITH sh: share, key: Z, bordernode: BorderNode.store, p: val, value: val
  PRE [ _bn OF tptr tbordernode, _i OF tint, _val OF tptr tvoid ]
  PROP (0 <= key < keyslice_length;
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
  WITH sh: share, key: Z, bordernode: BorderNode.store, p: val
  PRE [ _bn OF tptr tbordernode, _i OF tint ]
  PROP (0 <= key < keyslice_length;
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
       sh_bordernode: share, bordernode: BorderNode.store, p: val,
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
       sh_bordernode: share, bordernode: BorderNode.store, p: val
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
  WITH sh_key: share, key: string, k: val, k':val,
       sh_node: share, bordernode: BorderNode.store, p: val
  PRE [ _bn OF tptr tbordernode, _key OF tptr tkey ]                                    
  PROP (readable_share sh_key;
        readable_share sh_node;
        Zlength key > keyslice_length)
  LOCAL (temp _bn p;
         temp _key k)
  SEP (key_rep sh_key key k k';
       bordernode_rep sh_node bordernode p)
  POST [ tint ]
  PROP ()
  LOCAL (temp ret_temp (if BorderNode.test_suffix (Some (get_suffix key)) bordernode then Vint Int.one else Vint Int.zero))
  SEP (key_rep sh_key key k k';
       bordernode_rep sh_node bordernode p).

Definition BN_ExportSuffixValue_spec: ident * funspec :=
  DECLARE _BN_ExportSuffixValue
  WITH sh_bordernode: share, bordernode: BorderNode.store, p: val,
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
  WITH sh_bordernode: share, bordernode: BorderNode.store, p: val
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
  WITH sh_bordernode: share, bordernode: BorderNode.store, p: val, value: val
  PRE [ _bn OF tptr tbordernode, _val OF tptr tvoid ]
  PROP (writable_share sh_bordernode)
  LOCAL (temp _bn p;
         temp _val value)
  SEP (bordernode_rep sh_bordernode bordernode p)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP (bordernode_rep sh_bordernode (BorderNode.put_suffix None value bordernode) p).

(* Specification for [kvstore.c] *)

Definition KV_GetCharArray_spec: ident * funspec :=
  DECLARE _KV_GetCharArray
  WITH sh: share, key: string, p: val, p':val
  PRE [ _key OF tptr tkey ]
  PROP (readable_share sh)
  LOCAL (temp _key p)
  SEP (key_rep sh key p p')
  POST [tptr tschar]
  PROP ()
  LOCAL (temp ret_temp p')
  SEP (key_rep sh key p p').

Definition KV_GetCharArraySize_spec: ident * funspec :=
  DECLARE _KV_GetCharArraySize
  WITH sh: share, key: string, p: val, p': val
  PRE [ _key OF tptr tkey ]
  PROP (readable_share sh)
  LOCAL (temp _key p)
  SEP (key_rep sh key p p')
  POST [tuint]
  PROP ()
  LOCAL (temp ret_temp (Vint (Int.repr (Zlength key))))
  SEP (key_rep sh key p p').

Definition KV_MoveKey_spec: ident * funspec :=
  DECLARE _KV_MoveKey
  WITH key: string, s: val 
  PRE [ _str OF tptr tschar, _len OF tuint ]
  PROP ()
  LOCAL (temp _str s;
         temp _len (Vint (Int.repr (Zlength key))))
  SEP (cstring_len Tsh key s;
       malloc_token Tsh (tarray tschar (Zlength key)) s)
  POST [ tptr tkey ] EX k:val, EX k':val,
  PROP ()
  LOCAL (temp ret_temp k)
  SEP (key_rep Tsh key k k';
       malloc_token Tsh tkey k).
