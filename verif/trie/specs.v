(** * specs.v : Collection of all related specs *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import common.
(* clight files *)
Require Import surely_malloc.
Require Import util.
Require Import bordernode.
Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* functional definitions *)
Require Import keyslice_fun.
Require Import bordernode_fun.

Definition tbordernode: type := Tstruct _BorderNode noattr.

Definition cstring_len (sh: share) (str: string) (s: val) :=
  data_at sh (tarray tschar (Zlength str)) (map Vbyte (str)) s && !! (0 < Zlength str <= Int.max_unsigned).

Module BorderNodeValue <: VALUE_TYPE.
  Definition type := val.
  Definition default := nullval.
  Definition inhabitant_value := Vundef.
End BorderNodeValue.

Module BorderNode := BorderNode BorderNodeValue.

Definition bordernode_rep (sh: share) (s: BorderNode.store) (p: val): mpred :=
  let (prefixes, suffix_val) := s in
  !! (Forall (fun p => is_pointer_or_null p) (prefixes)) &&
  malloc_token sh tbordernode p *
  field_at sh tbordernode [StructField _prefixLinks] prefixes p *
  match suffix_val with
  | Some (k, v) =>
    EX p': val,
      field_at sh tbordernode [StructField _suffixLink] v p *
      field_at sh tbordernode [StructField _keySuffix] p' p *
      field_at sh tbordernode [StructField _keySuffixLength] (Vint (Int.repr (Zlength k))) p *
      cstring_len Tsh k p' *
      malloc_token Tsh (tarray tschar (Zlength k)) p' &&
      !! (is_pointer_or_null v)
  | None =>
      field_at sh tbordernode [StructField _suffixLink] nullval p *
      field_at sh tbordernode [StructField _keySuffix] nullval p *
      field_at sh tbordernode [StructField _keySuffixLength] (Vint Int.zero) p
  end.

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
  LOCAL (temp ret_temp (BorderNode.get_suffix key bordernode))
  SEP (cstring_len sh_string key s;
       bordernode_rep sh_bordernode bordernode p).

Definition BN_SetSuffixValue_spec: ident * funspec :=
  DECLARE _BN_SetSuffixValue
  WITH sh_string: share, key: string, s: val,
       sh_bordernode: share, bordernode: BorderNode.store, p: val,
       value: val
  PRE [ _bn OF tptr tbordernode, _suf OF tptr tschar, _len OF tuint, _val OF tptr tvoid ]
  PROP (readable_share sh_string;
        writable_share sh_bordernode)
  LOCAL (temp _bn p;
         temp _suf s;
         temp _len (Vint (Int.repr (Zlength key)));
         temp _val value)
  SEP (cstring_len sh_string key s;
       bordernode_rep sh_bordernode bordernode p)
  POST [ tvoid ]
  PROP ()
  LOCAL ()
  SEP (cstring_len sh_string key s;
       bordernode_rep sh_bordernode (BorderNode.put_suffix key value bordernode) p).
