From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Definition _BN_ExportSuffixValue : ident := 116%positive.
Definition _BN_FreeBorderNode : ident := 97%positive.
Definition _BN_GetLink : ident := 118%positive.
Definition _BN_GetPrefixValue : ident := 105%positive.
Definition _BN_GetSuffixValue : ident := 113%positive.
Definition _BN_HasSuffix : ident := 119%positive.
Definition _BN_NewBorderNode : ident := 96%positive.
Definition _BN_SetLink : ident := 117%positive.
Definition _BN_SetPrefixValue : ident := 103%positive.
Definition _BN_SetSuffixValue : ident := 107%positive.
Definition _BN_SetValue : ident := 120%positive.
Definition _BN_TestSuffix : ident := 111%positive.
Definition _BorderNode : ident := 16%positive.
Definition _Cursor : ident := 10%positive.
Definition _KVKey : ident := 3%positive.
Definition _KVNode : ident := 4%positive.
Definition _KVStore : ident := 7%positive.
Definition _KV_FreeKey : ident := 134%positive.
Definition _KV_Get : ident := 164%positive.
Definition _KV_GetCharArray : ident := 110%positive.
Definition _KV_GetCharArraySize : ident := 109%positive.
Definition _KV_KeyEqual : ident := 132%positive.
Definition _KV_MoveKey : ident := 115%positive.
Definition _KV_NewKVStore : ident := 138%positive.
Definition _KV_NewKey : ident := 125%positive.
Definition _KV_NumKeys : ident := 166%positive.
Definition _KV_Put : ident := 159%positive.
Definition _RL_DeleteRelation : ident := 75%positive.
Definition _RL_GetRecord : ident := 79%positive.
Definition _RL_MoveToKey : ident := 78%positive.
Definition _RL_NewCursor : ident := 76%positive.
Definition _RL_NewRelation : ident := 74%positive.
Definition _RL_PutRecord : ident := 77%positive.
Definition _Relation : ident := 8%positive.
Definition _UTIL_GetNextKeySlice : ident := 94%positive.
Definition _UTIL_Min : ident := 73%positive.
Definition _UTIL_StrEqual : ident := 88%positive.
Definition ___assert_fail : ident := 69%positive.
Definition ___builtin_ais_annot : ident := 17%positive.
Definition ___builtin_annot : ident := 24%positive.
Definition ___builtin_annot_intval : ident := 25%positive.
Definition ___builtin_bswap : ident := 18%positive.
Definition ___builtin_bswap16 : ident := 20%positive.
Definition ___builtin_bswap32 : ident := 19%positive.
Definition ___builtin_bswap64 : ident := 50%positive.
Definition ___builtin_clz : ident := 51%positive.
Definition ___builtin_clzl : ident := 52%positive.
Definition ___builtin_clzll : ident := 53%positive.
Definition ___builtin_ctz : ident := 54%positive.
Definition ___builtin_ctzl : ident := 55%positive.
Definition ___builtin_ctzll : ident := 56%positive.
Definition ___builtin_debug : ident := 68%positive.
Definition ___builtin_fabs : ident := 21%positive.
Definition ___builtin_fmadd : ident := 59%positive.
Definition ___builtin_fmax : ident := 57%positive.
Definition ___builtin_fmin : ident := 58%positive.
Definition ___builtin_fmsub : ident := 60%positive.
Definition ___builtin_fnmadd : ident := 61%positive.
Definition ___builtin_fnmsub : ident := 62%positive.
Definition ___builtin_fsqrt : ident := 22%positive.
Definition ___builtin_membar : ident := 26%positive.
Definition ___builtin_memcpy_aligned : ident := 23%positive.
Definition ___builtin_nop : ident := 67%positive.
Definition ___builtin_read16_reversed : ident := 63%positive.
Definition ___builtin_read32_reversed : ident := 64%positive.
Definition ___builtin_va_arg : ident := 28%positive.
Definition ___builtin_va_copy : ident := 29%positive.
Definition ___builtin_va_end : ident := 30%positive.
Definition ___builtin_va_start : ident := 27%positive.
Definition ___builtin_write16_reversed : ident := 65%positive.
Definition ___builtin_write32_reversed : ident := 66%positive.
Definition ___compcert_i64_dtos : ident := 35%positive.
Definition ___compcert_i64_dtou : ident := 36%positive.
Definition ___compcert_i64_sar : ident := 47%positive.
Definition ___compcert_i64_sdiv : ident := 41%positive.
Definition ___compcert_i64_shl : ident := 45%positive.
Definition ___compcert_i64_shr : ident := 46%positive.
Definition ___compcert_i64_smod : ident := 43%positive.
Definition ___compcert_i64_smulh : ident := 48%positive.
Definition ___compcert_i64_stod : ident := 37%positive.
Definition ___compcert_i64_stof : ident := 39%positive.
Definition ___compcert_i64_udiv : ident := 42%positive.
Definition ___compcert_i64_umod : ident := 44%positive.
Definition ___compcert_i64_umulh : ident := 49%positive.
Definition ___compcert_i64_utod : ident := 38%positive.
Definition ___compcert_i64_utof : ident := 40%positive.
Definition ___compcert_va_composite : ident := 34%positive.
Definition ___compcert_va_float64 : ident := 33%positive.
Definition ___compcert_va_int32 : ident := 31%positive.
Definition ___compcert_va_int64 : ident := 32%positive.
Definition ___func__ : ident := 89%positive.
Definition ___func____1 : ident := 98%positive.
Definition ___func____10 : ident := 165%positive.
Definition ___func____2 : ident := 104%positive.
Definition ___func____3 : ident := 121%positive.
Definition ___func____4 : ident := 126%positive.
Definition ___func____5 : ident := 127%positive.
Definition ___func____6 : ident := 129%positive.
Definition ___func____7 : ident := 133%positive.
Definition ___func____8 : ident := 141%positive.
Definition ___func____9 : ident := 160%positive.
Definition ___stringlit_1 : ident := 91%positive.
Definition ___stringlit_10 : ident := 157%positive.
Definition ___stringlit_11 : ident := 158%positive.
Definition ___stringlit_2 : ident := 92%positive.
Definition ___stringlit_3 : ident := 93%positive.
Definition ___stringlit_4 : ident := 101%positive.
Definition ___stringlit_5 : ident := 102%positive.
Definition ___stringlit_6 : ident := 124%positive.
Definition ___stringlit_7 : ident := 128%positive.
Definition ___stringlit_8 : ident := 155%positive.
Definition ___stringlit_9 : ident := 156%positive.
Definition _a : ident := 83%positive.
Definition _b : ident := 85%positive.
Definition _bn : ident := 99%positive.
Definition _borderNode : ident := 149%positive.
Definition _bordernode : ident := 95%positive.
Definition _btree : ident := 148%positive.
Definition _btreeCursor : ident := 147%positive.
Definition _btreeStatus : ident := 146%positive.
Definition _currNode : ident := 145%positive.
Definition _cursor : ident := 11%positive.
Definition _exit : ident := 72%positive.
Definition _free : ident := 71%positive.
Definition _getNodeCursor : ident := 140%positive.
Definition _getValueOfPartialKey : ident := 163%positive.
Definition _i : ident := 87%positive.
Definition _key : ident := 108%positive.
Definition _key1 : ident := 130%positive.
Definition _key2 : ident := 131%positive.
Definition _keySlice : ident := 168%positive.
Definition _keySuffix : ident := 14%positive.
Definition _keySuffixLength : ident := 15%positive.
Definition _kvStore : ident := 142%positive.
Definition _len : ident := 2%positive.
Definition _lenA : ident := 84%positive.
Definition _lenB : ident := 86%positive.
Definition _link : ident := 151%positive.
Definition _main : ident := 169%positive.
Definition _malloc : ident := 70%positive.
Definition _n : ident := 80%positive.
Definition _newKVNode : ident := 137%positive.
Definition _newKey : ident := 123%positive.
Definition _newStr : ident := 122%positive.
Definition _nextKeySlice : ident := 150%positive.
Definition _node : ident := 139%positive.
Definition _numKeys : ident := 6%positive.
Definition _p : ident := 81%positive.
Definition _partialKey : ident := 167%positive.
Definition _prefixLinks : ident := 12%positive.
Definition _putCompleted : ident := 144%positive.
Definition _res : ident := 90%positive.
Definition _ret_temp : ident := 114%positive.
Definition _root : ident := 136%positive.
Definition _rootNode : ident := 5%positive.
Definition _sndKey : ident := 152%positive.
Definition _sndKeySlice : ident := 154%positive.
Definition _sndValue : ident := 153%positive.
Definition _store : ident := 135%positive.
Definition _str : ident := 1%positive.
Definition _suf : ident := 112%positive.
Definition _suffix : ident := 106%positive.
Definition _suffixLink : ident := 13%positive.
Definition _surely_malloc : ident := 82%positive.
Definition _totalKey : ident := 161%positive.
Definition _totalKeyLength : ident := 162%positive.
Definition _tree : ident := 9%positive.
Definition _val : ident := 100%positive.
Definition _value : ident := 143%positive.
Definition _t'1 : ident := 170%positive.
Definition _t'10 : ident := 179%positive.
Definition _t'11 : ident := 180%positive.
Definition _t'12 : ident := 181%positive.
Definition _t'13 : ident := 182%positive.
Definition _t'14 : ident := 183%positive.
Definition _t'15 : ident := 184%positive.
Definition _t'16 : ident := 185%positive.
Definition _t'17 : ident := 186%positive.
Definition _t'18 : ident := 187%positive.
Definition _t'19 : ident := 188%positive.
Definition _t'2 : ident := 171%positive.
Definition _t'20 : ident := 189%positive.
Definition _t'21 : ident := 190%positive.
Definition _t'22 : ident := 191%positive.
Definition _t'23 : ident := 192%positive.
Definition _t'24 : ident := 193%positive.
Definition _t'25 : ident := 194%positive.
Definition _t'26 : ident := 195%positive.
Definition _t'27 : ident := 196%positive.
Definition _t'28 : ident := 197%positive.
Definition _t'29 : ident := 198%positive.
Definition _t'3 : ident := 172%positive.
Definition _t'30 : ident := 199%positive.
Definition _t'31 : ident := 200%positive.
Definition _t'32 : ident := 201%positive.
Definition _t'33 : ident := 202%positive.
Definition _t'34 : ident := 203%positive.
Definition _t'35 : ident := 204%positive.
Definition _t'36 : ident := 205%positive.
Definition _t'37 : ident := 206%positive.
Definition _t'38 : ident := 207%positive.
Definition _t'39 : ident := 208%positive.
Definition _t'4 : ident := 173%positive.
Definition _t'40 : ident := 209%positive.
Definition _t'41 : ident := 210%positive.
Definition _t'42 : ident := 211%positive.
Definition _t'43 : ident := 212%positive.
Definition _t'44 : ident := 213%positive.
Definition _t'45 : ident := 214%positive.
Definition _t'46 : ident := 215%positive.
Definition _t'47 : ident := 216%positive.
Definition _t'48 : ident := 217%positive.
Definition _t'49 : ident := 218%positive.
Definition _t'5 : ident := 174%positive.
Definition _t'50 : ident := 219%positive.
Definition _t'51 : ident := 220%positive.
Definition _t'52 : ident := 221%positive.
Definition _t'53 : ident := 222%positive.
Definition _t'54 : ident := 223%positive.
Definition _t'55 : ident := 224%positive.
Definition _t'56 : ident := 225%positive.
Definition _t'57 : ident := 226%positive.
Definition _t'58 : ident := 227%positive.
Definition _t'59 : ident := 228%positive.
Definition _t'6 : ident := 175%positive.
Definition _t'7 : ident := 176%positive.
Definition _t'8 : ident := 177%positive.
Definition _t'9 : ident := 178%positive.

Definition v___stringlit_11 := {|
  gvar_info := (tarray tschar 10);
  gvar_init := (Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 33) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_9 := {|
  gvar_info := (tarray tschar 31);
  gvar_init := (Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 33) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 124) :: Init_int8 (Int.repr 124) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_8 := {|
  gvar_info := (tarray tschar 13);
  gvar_init := (Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 33) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_10 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 33) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 13);
  gvar_init := (Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 33) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 35);
  gvar_init := (Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_7 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 33) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 16);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 77) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 88) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 90) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_surely_malloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Etempvar _n tuint) :: nil))
    (Sset _p (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr tvoid)) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Sreturn (Some (Etempvar _p (tptr tvoid))))))
|}.

Definition f_UTIL_StrEqual := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tschar)) :: (_lenA, tuint) ::
                (_b, (tptr tschar)) :: (_lenB, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_t'2, tschar) :: (_t'1, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _lenA tuint) (Etempvar _lenB tuint)
                 tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _lenA tuint)
                         tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd (Etempvar _a (tptr tschar)) (Etempvar _i tuint)
                  (tptr tschar)) tschar))
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Etempvar _b (tptr tschar))
                    (Etempvar _i tuint) (tptr tschar)) tschar))
              (Sifthenelse (Ebinop One (Etempvar _t'1 tschar)
                             (Etempvar _t'2 tschar) tint)
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                Sskip))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
|}.

Definition v___func__ := {|
  gvar_info := (tarray tschar 21);
  gvar_init := (Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_UTIL_GetNextKeySlice := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: (_len, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, tuint) :: (_i, tint) :: (_t'1, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _res (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sifthenelse (Ebinop Oge (Etempvar _len tint)
                     (Econst_int (Int.repr 0) tint) tint)
        Sskip
        (Scall None
          (Evar ___assert_fail (Tfunction
                                 (Tcons (tptr tschar)
                                   (Tcons (tptr tschar)
                                     (Tcons tuint (Tcons (tptr tschar) Tnil))))
                                 tvoid cc_default))
          ((Evar ___stringlit_2 (tarray tschar 9)) ::
           (Evar ___stringlit_1 (tarray tschar 13)) ::
           (Econst_int (Int.repr 36) tint) ::
           (Evar ___func__ (tarray tschar 21)) :: nil)))
      (Ssequence
        (Sifthenelse (Ebinop Ole (Etempvar _len tint)
                       (Ecast (Esizeof tuint tuint) tint) tint)
          Sskip
          (Scall None
            (Evar ___assert_fail (Tfunction
                                   (Tcons (tptr tschar)
                                     (Tcons (tptr tschar)
                                       (Tcons tuint
                                         (Tcons (tptr tschar) Tnil)))) tvoid
                                   cc_default))
            ((Evar ___stringlit_3 (tarray tschar 35)) ::
             (Evar ___stringlit_1 (tarray tschar 13)) ::
             (Econst_int (Int.repr 37) tint) ::
             (Evar ___func__ (tarray tschar 21)) :: nil)))
        (Ssequence
          (Swhile
            (Ebinop Olt (Etempvar _i tint) (Etempvar _len tint) tint)
            (Ssequence
              (Sset _res
                (Ebinop Oshl (Etempvar _res tuint)
                  (Econst_int (Int.repr 8) tint) tuint))
              (Ssequence
                (Ssequence
                  (Sset _t'1 (Ederef (Etempvar _str (tptr tschar)) tschar))
                  (Sset _res
                    (Ebinop Oor (Etempvar _res tuint)
                      (Ebinop Oand (Ecast (Etempvar _t'1 tschar) tuint)
                        (Econst_int (Int.repr 255) tint) tuint) tuint)))
                (Ssequence
                  (Sset _str
                    (Ebinop Oadd (Etempvar _str (tptr tschar))
                      (Econst_int (Int.repr 1) tint) (tptr tschar)))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint))))))
          (Ssequence
            (Swhile
              (Ebinop Olt (Etempvar _i tint)
                (Ecast (Esizeof tuint tuint) tint) tint)
              (Ssequence
                (Sset _res
                  (Ebinop Oshl (Etempvar _res tuint)
                    (Econst_int (Int.repr 8) tint) tuint))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Sreturn (Some (Etempvar _res tuint)))))))))
|}.

Definition f_BN_NewBorderNode := {|
  fn_return := (tptr (Tstruct _BorderNode noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_bordernode, (tptr (Tstruct _BorderNode noattr))) ::
               (_i, tint) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _BorderNode noattr) tuint) :: nil))
    (Sset _bordernode
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _BorderNode noattr)))))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Econst_int (Int.repr 4) tint) tint)
            Sskip
            Sbreak)
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
                    (Tstruct _BorderNode noattr)) _prefixLinks
                  (tarray (tptr tvoid) 4)) (Etempvar _i tint)
                (tptr (tptr tvoid))) (tptr tvoid))
            (Econst_int (Int.repr 0) tint)))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid))
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef
              (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
                (Tstruct _BorderNode noattr)) _keySuffixLength tuint)
            (Econst_int (Int.repr 0) tint))
          (Sreturn (Some (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr))))))))))
|}.

Definition f_BN_FreeBorderNode := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bordernode, (tptr (Tstruct _BorderNode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr tschar)) :: (_t'1, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
      (Sifthenelse (Ebinop One (Etempvar _t'1 (tptr tschar))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef
                (Etempvar _bordernode (tptr (Tstruct _BorderNode noattr)))
                (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
          (Scall None
            (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default))
            ((Etempvar _t'2 (tptr tschar)) :: nil)))
        Sskip))
    (Ssequence
      (Scall None
        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Etempvar _bordernode (tptr (Tstruct _BorderNode noattr))) :: nil))
      (Sreturn None))))
|}.

Definition v___func____1 := {|
  gvar_info := (tarray tschar 18);
  gvar_init := (Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 86) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_BN_SetPrefixValue := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) :: (_i, tint) ::
                (_val, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oge (Etempvar _i tint) (Econst_int (Int.repr 0) tint)
                 tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_4 (tarray tschar 7)) ::
       (Evar ___stringlit_1 (tarray tschar 13)) ::
       (Econst_int (Int.repr 91) tint) ::
       (Evar ___func____1 (tarray tschar 18)) :: nil)))
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                   (Econst_int (Int.repr 4) tint) tint)
      Sskip
      (Scall None
        (Evar ___assert_fail (Tfunction
                               (Tcons (tptr tschar)
                                 (Tcons (tptr tschar)
                                   (Tcons tuint (Tcons (tptr tschar) Tnil))))
                               tvoid cc_default))
        ((Evar ___stringlit_5 (tarray tschar 16)) ::
         (Evar ___stringlit_1 (tarray tschar 13)) ::
         (Econst_int (Int.repr 92) tint) ::
         (Evar ___func____1 (tarray tschar 18)) :: nil)))
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _prefixLinks
            (tarray (tptr tvoid) 4)) (Etempvar _i tint) (tptr (tptr tvoid)))
        (tptr tvoid)) (Etempvar _val (tptr tvoid)))))
|}.

Definition v___func____2 := {|
  gvar_info := (tarray tschar 18);
  gvar_init := (Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 86) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_BN_GetPrefixValue := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) :: (_i, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oge (Etempvar _i tint) (Econst_int (Int.repr 0) tint)
                 tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_4 (tarray tschar 7)) ::
       (Evar ___stringlit_1 (tarray tschar 13)) ::
       (Econst_int (Int.repr 97) tint) ::
       (Evar ___func____2 (tarray tschar 18)) :: nil)))
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                   (Econst_int (Int.repr 4) tint) tint)
      Sskip
      (Scall None
        (Evar ___assert_fail (Tfunction
                               (Tcons (tptr tschar)
                                 (Tcons (tptr tschar)
                                   (Tcons tuint (Tcons (tptr tschar) Tnil))))
                               tvoid cc_default))
        ((Evar ___stringlit_5 (tarray tschar 16)) ::
         (Evar ___stringlit_1 (tarray tschar 13)) ::
         (Econst_int (Int.repr 98) tint) ::
         (Evar ___func____2 (tarray tschar 18)) :: nil)))
    (Ssequence
      (Sset _t'1
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                (Tstruct _BorderNode noattr)) _prefixLinks
              (tarray (tptr tvoid) 4)) (Etempvar _i tint)
            (tptr (tptr tvoid))) (tptr tvoid)))
      (Sreturn (Some (Etempvar _t'1 (tptr tvoid)))))))
|}.

Definition f_BN_SetSuffixValue := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_suffix, (tptr tschar)) :: (_len, tuint) ::
                (_val, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_t'1, (tptr tvoid)) ::
               (_t'5, (tptr tschar)) :: (_t'4, (tptr tschar)) ::
               (_t'3, tschar) :: (_t'2, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'4
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
    (Sifthenelse (Ebinop One (Etempvar _t'4 (tptr tschar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Etempvar _t'5 (tptr tschar)) :: nil)))
      Sskip))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                               cc_default))
        ((Ebinop Omul (Esizeof tschar tuint) (Etempvar _len tuint) tuint) ::
         nil))
      (Sassign
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
        (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tschar))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                           (Etempvar _len tuint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                    (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd (Etempvar _suffix (tptr tschar))
                      (Etempvar _i tuint) (tptr tschar)) tschar))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'2 (tptr tschar))
                      (Etempvar _i tuint) (tptr tschar)) tschar)
                  (Etempvar _t'3 tschar)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _keySuffixLength tuint)
          (Etempvar _len tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid))
          (Etempvar _val (tptr tvoid)))))))
|}.

Definition f_BN_TestSuffix := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_key, (tptr (Tstruct _KVKey noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tint) :: (_t'2, tuint) :: (_t'1, (tptr tschar)) ::
               (_t'6, tuint) :: (_t'5, (tptr tschar)) ::
               (_t'4, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'4
    (Efield
      (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
        (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
  (Sifthenelse (Ebinop One (Etempvar _t'4 (tptr tschar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _KV_GetCharArray (Tfunction
                                     (Tcons (tptr (Tstruct _KVKey noattr))
                                       Tnil) (tptr tschar) cc_default))
            ((Etempvar _key (tptr (Tstruct _KVKey noattr))) :: nil))
          (Scall (Some _t'2)
            (Evar _KV_GetCharArraySize (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _KVKey noattr))
                                           Tnil) tuint cc_default))
            ((Etempvar _key (tptr (Tstruct _KVKey noattr))) :: nil)))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                  (Tstruct _BorderNode noattr)) _keySuffixLength tuint))
            (Scall (Some _t'3)
              (Evar _UTIL_StrEqual (Tfunction
                                     (Tcons (tptr tschar)
                                       (Tcons tuint
                                         (Tcons (tptr tschar)
                                           (Tcons tuint Tnil)))) tint
                                     cc_default))
              ((Ebinop Oadd (Etempvar _t'1 (tptr tschar))
                 (Ecast (Esizeof tuint tuint) tint) (tptr tschar)) ::
               (Ebinop Osub (Etempvar _t'2 tuint)
                 (Ecast (Esizeof tuint tuint) tint) tuint) ::
               (Etempvar _t'5 (tptr tschar)) :: (Etempvar _t'6 tuint) :: nil)))))
      (Sreturn (Some (Etempvar _t'3 tint))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_BN_GetSuffixValue := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_suf, (tptr tschar)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'5, (tptr tschar)) :: (_t'4, tuint) ::
               (_t'3, (tptr tschar)) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'5
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'5 (tptr tschar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _keySuffixLength tuint))
        (Scall (Some _t'1)
          (Evar _UTIL_StrEqual (Tfunction
                                 (Tcons (tptr tschar)
                                   (Tcons tuint
                                     (Tcons (tptr tschar) (Tcons tuint Tnil))))
                                 tint cc_default))
          ((Etempvar _suf (tptr tschar)) :: (Etempvar _len tuint) ::
           (Etempvar _t'3 (tptr tschar)) :: (Etempvar _t'4 tuint) :: nil))))
    (Sifthenelse (Etempvar _t'1 tint)
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid)))
        (Sreturn (Some (Etempvar _t'2 (tptr tvoid)))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_BN_ExportSuffixValue := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_key, (tptr (tptr (Tstruct _KVKey noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret_temp, (tptr tvoid)) ::
               (_t'1, (tptr (Tstruct _KVKey noattr))) :: (_t'4, tuint) ::
               (_t'3, (tptr tschar)) :: (_t'2, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
    (Sifthenelse (Ebinop One (Etempvar _t'2 (tptr tschar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                  (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                    (Tstruct _BorderNode noattr)) _keySuffixLength tuint))
              (Scall (Some _t'1)
                (Evar _KV_MoveKey (Tfunction
                                    (Tcons (tptr tschar) (Tcons tuint Tnil))
                                    (tptr (Tstruct _KVKey noattr))
                                    cc_default))
                ((Etempvar _t'3 (tptr tschar)) :: (Etempvar _t'4 tuint) ::
                 nil))))
          (Sassign
            (Ederef (Etempvar _key (tptr (tptr (Tstruct _KVKey noattr))))
              (tptr (Tstruct _KVKey noattr)))
            (Etempvar _t'1 (tptr (Tstruct _KVKey noattr)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
            (Econst_int (Int.repr 0) tint))
          (Sassign
            (Efield
              (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
                (Tstruct _BorderNode noattr)) _keySuffixLength tuint)
            (Econst_int (Int.repr 0) tint))))
      (Sassign
        (Ederef (Etempvar _key (tptr (tptr (Tstruct _KVKey noattr))))
          (tptr (Tstruct _KVKey noattr))) (Econst_int (Int.repr 0) tint))))
  (Ssequence
    (Sset _ret_temp
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid))
        (Econst_int (Int.repr 0) tint))
      (Sreturn (Some (Etempvar _ret_temp (tptr tvoid)))))))
|}.

Definition f_BN_SetLink := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_val, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr tschar)) :: (_t'1, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
    (Sifthenelse (Ebinop One (Etempvar _t'1 (tptr tschar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
              (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Etempvar _t'2 (tptr tschar)) :: nil)))
      Sskip))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar))
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _keySuffixLength tuint)
        (Econst_int (Int.repr 0) tint))
      (Sassign
        (Efield
          (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
            (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid))
        (Etempvar _val (tptr tvoid))))))
|}.

Definition f_BN_GetLink := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr tschar)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
    (Sifthenelse (Ebinop One (Etempvar _t'2 (tptr tschar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
          (Tstruct _BorderNode noattr)) _suffixLink (tptr tvoid)))
    (Sreturn (Some (Etempvar _t'1 (tptr tvoid))))))
|}.

Definition f_BN_HasSuffix := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _bn (tptr (Tstruct _BorderNode noattr)))
        (Tstruct _BorderNode noattr)) _keySuffix (tptr tschar)))
  (Sreturn (Some (Ebinop One (Etempvar _t'1 (tptr tschar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint))))
|}.

Definition f_BN_SetValue := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr (Tstruct _BorderNode noattr))) ::
                (_key, (tptr (Tstruct _KVKey noattr))) ::
                (_val, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tuint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'4)
    (Evar _KV_GetCharArraySize (Tfunction
                                 (Tcons (tptr (Tstruct _KVKey noattr)) Tnil)
                                 tuint cc_default))
    ((Etempvar _key (tptr (Tstruct _KVKey noattr))) :: nil))
  (Sifthenelse (Ebinop Oge (Etempvar _t'4 tuint)
                 (Ecast (Esizeof tuint tuint) tint) tint)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _KV_GetCharArray (Tfunction
                                   (Tcons (tptr (Tstruct _KVKey noattr))
                                     Tnil) (tptr tschar) cc_default))
          ((Etempvar _key (tptr (Tstruct _KVKey noattr))) :: nil))
        (Scall (Some _t'2)
          (Evar _KV_GetCharArraySize (Tfunction
                                       (Tcons (tptr (Tstruct _KVKey noattr))
                                         Tnil) tuint cc_default))
          ((Etempvar _key (tptr (Tstruct _KVKey noattr))) :: nil)))
      (Scall None
        (Evar _BN_SetSuffixValue (Tfunction
                                   (Tcons (tptr (Tstruct _BorderNode noattr))
                                     (Tcons (tptr tschar)
                                       (Tcons tuint
                                         (Tcons (tptr tvoid) Tnil)))) tvoid
                                   cc_default))
        ((Etempvar _bn (tptr (Tstruct _BorderNode noattr))) ::
         (Ebinop Oadd (Etempvar _t'1 (tptr tschar))
           (Ecast (Esizeof tuint tuint) tint) (tptr tschar)) ::
         (Ebinop Osub (Etempvar _t'2 tuint)
           (Ecast (Esizeof tuint tuint) tint) tuint) ::
         (Etempvar _val (tptr tvoid)) :: nil)))
    (Ssequence
      (Scall (Some _t'3)
        (Evar _KV_GetCharArraySize (Tfunction
                                     (Tcons (tptr (Tstruct _KVKey noattr))
                                       Tnil) tuint cc_default))
        ((Etempvar _key (tptr (Tstruct _KVKey noattr))) :: nil))
      (Scall None
        (Evar _BN_SetPrefixValue (Tfunction
                                   (Tcons (tptr (Tstruct _BorderNode noattr))
                                     (Tcons tint (Tcons (tptr tvoid) Tnil)))
                                   tvoid cc_default))
        ((Etempvar _bn (tptr (Tstruct _BorderNode noattr))) ::
         (Etempvar _t'3 tuint) :: (Etempvar _val (tptr tvoid)) :: nil)))))
|}.

Definition v___func____3 := {|
  gvar_info := (tarray tschar 10);
  gvar_init := (Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 86) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_KV_NewKey := {|
  fn_return := (tptr (Tstruct _KVKey noattr));
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_newStr, (tptr tschar)) ::
               (_newKey, (tptr (Tstruct _KVKey noattr))) :: (_i, tuint) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'3, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _newStr (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _newKey
      (Ecast (Econst_int (Int.repr 0) tint) (tptr (Tstruct _KVKey noattr))))
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sifthenelse (Ebinop Ogt (Etempvar _len tuint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Ssequence
            (Sifthenelse (Ebinop One (Etempvar _str (tptr tschar))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              Sskip
              (Scall None
                (Evar ___assert_fail (Tfunction
                                       (Tcons (tptr tschar)
                                         (Tcons (tptr tschar)
                                           (Tcons tuint
                                             (Tcons (tptr tschar) Tnil))))
                                       tvoid cc_default))
                ((Evar ___stringlit_6 (tarray tschar 9)) ::
                 (Evar ___stringlit_1 (tarray tschar 13)) ::
                 (Econst_int (Int.repr 196) tint) ::
                 (Evar ___func____3 (tarray tschar 10)) :: nil)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar _surely_malloc (Tfunction (Tcons tuint Tnil)
                                         (tptr tvoid) cc_default))
                  ((Ebinop Omul (Esizeof tschar tuint) (Etempvar _len tuint)
                     tuint) :: nil))
                (Sset _newStr
                  (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tschar))))
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Etempvar _newStr (tptr tschar))
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) tint)
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                  Sskip)
                (Ssequence
                  (Sset _i (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                     (Etempvar _len tuint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sset _t'3
                          (Ederef
                            (Ebinop Oadd (Etempvar _str (tptr tschar))
                              (Etempvar _i tuint) (tptr tschar)) tschar))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _newStr (tptr tschar))
                              (Etempvar _i tuint) (tptr tschar)) tschar)
                          (Etempvar _t'3 tschar))))
                    (Sset _i
                      (Ebinop Oadd (Etempvar _i tuint)
                        (Econst_int (Int.repr 1) tint) tuint)))))))
          Sskip)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                     cc_default))
              ((Esizeof (Tstruct _KVKey noattr) tuint) :: nil))
            (Sset _newKey
              (Ecast (Etempvar _t'2 (tptr tvoid))
                (tptr (Tstruct _KVKey noattr)))))
          (Ssequence
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _newKey (tptr (Tstruct _KVKey noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Ssequence
                (Scall None
                  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                cc_default))
                  ((Etempvar _newStr (tptr tschar)) :: nil))
                (Sreturn (Some (Econst_int (Int.repr 0) tint))))
              Sskip)
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _newKey (tptr (Tstruct _KVKey noattr)))
                    (Tstruct _KVKey noattr)) _str (tptr tschar))
                (Etempvar _newStr (tptr tschar)))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _newKey (tptr (Tstruct _KVKey noattr)))
                      (Tstruct _KVKey noattr)) _len tuint)
                  (Etempvar _len tuint))
                (Sreturn (Some (Etempvar _newKey (tptr (Tstruct _KVKey noattr)))))))))))))
|}.

Definition v___func____4 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 86) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 75) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_KV_MoveKey := {|
  fn_return := (tptr (Tstruct _KVKey noattr));
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_newKey, (tptr (Tstruct _KVKey noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _newKey
    (Ecast (Econst_int (Int.repr 0) tint) (tptr (Tstruct _KVKey noattr))))
  (Ssequence
    (Sifthenelse (Ebinop Ogt (Etempvar _len tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sifthenelse (Ebinop One (Etempvar _str (tptr tschar))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        Sskip
        (Scall None
          (Evar ___assert_fail (Tfunction
                                 (Tcons (tptr tschar)
                                   (Tcons (tptr tschar)
                                     (Tcons tuint (Tcons (tptr tschar) Tnil))))
                                 tvoid cc_default))
          ((Evar ___stringlit_6 (tarray tschar 9)) ::
           (Evar ___stringlit_1 (tarray tschar 13)) ::
           (Econst_int (Int.repr 224) tint) ::
           (Evar ___func____4 (tarray tschar 11)) :: nil)))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                 cc_default))
          ((Esizeof (Tstruct _KVKey noattr) tuint) :: nil))
        (Sset _newKey
          (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _KVKey noattr)))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _newKey (tptr (Tstruct _KVKey noattr)))
              (Tstruct _KVKey noattr)) _str (tptr tschar))
          (Etempvar _str (tptr tschar)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _newKey (tptr (Tstruct _KVKey noattr)))
                (Tstruct _KVKey noattr)) _len tuint) (Etempvar _len tuint))
          (Sreturn (Some (Etempvar _newKey (tptr (Tstruct _KVKey noattr))))))))))
|}.

Definition v___func____5 := {|
  gvar_info := (tarray tschar 16);
  gvar_init := (Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 86) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_KV_GetCharArray := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr (Tstruct _KVKey noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_7 (tarray tschar 9)) ::
       (Evar ___stringlit_1 (tarray tschar 13)) ::
       (Econst_int (Int.repr 235) tint) ::
       (Evar ___func____5 (tarray tschar 16)) :: nil)))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _key (tptr (Tstruct _KVKey noattr)))
          (Tstruct _KVKey noattr)) _str (tptr tschar)))
    (Sreturn (Some (Etempvar _t'1 (tptr tschar))))))
|}.

Definition v___func____6 := {|
  gvar_info := (tarray tschar 20);
  gvar_init := (Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 86) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_KV_GetCharArraySize := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr (Tstruct _KVKey noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_7 (tarray tschar 9)) ::
       (Evar ___stringlit_1 (tarray tschar 13)) ::
       (Econst_int (Int.repr 240) tint) ::
       (Evar ___func____6 (tarray tschar 20)) :: nil)))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _key (tptr (Tstruct _KVKey noattr)))
          (Tstruct _KVKey noattr)) _len tuint))
    (Sreturn (Some (Etempvar _t'1 tuint)))))
|}.

Definition f_KV_KeyEqual := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_key1, (tptr (Tstruct _KVKey noattr))) ::
                (_key2, (tptr (Tstruct _KVKey noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'5, tuint) :: (_t'4, (tptr tschar)) ::
               (_t'3, tuint) :: (_t'2, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _key1 (tptr (Tstruct _KVKey noattr)))
          (Tstruct _KVKey noattr)) _str (tptr tschar)))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _key1 (tptr (Tstruct _KVKey noattr)))
            (Tstruct _KVKey noattr)) _len tuint))
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _key2 (tptr (Tstruct _KVKey noattr)))
              (Tstruct _KVKey noattr)) _str (tptr tschar)))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _key2 (tptr (Tstruct _KVKey noattr)))
                (Tstruct _KVKey noattr)) _len tuint))
          (Scall (Some _t'1)
            (Evar _UTIL_StrEqual (Tfunction
                                   (Tcons (tptr tschar)
                                     (Tcons tuint
                                       (Tcons (tptr tschar)
                                         (Tcons tuint Tnil)))) tint
                                   cc_default))
            ((Etempvar _t'2 (tptr tschar)) :: (Etempvar _t'3 tuint) ::
             (Etempvar _t'4 (tptr tschar)) :: (Etempvar _t'5 tuint) :: nil))))))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition v___func____7 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 86) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 75) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_KV_FreeKey := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr (Tstruct _KVKey noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_7 (tarray tschar 9)) ::
       (Evar ___stringlit_1 (tarray tschar 13)) ::
       (Econst_int (Int.repr 249) tint) ::
       (Evar ___func____7 (tarray tschar 11)) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _key (tptr (Tstruct _KVKey noattr)))
            (Tstruct _KVKey noattr)) _str (tptr tschar)))
      (Scall None
        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Ecast (Etempvar _t'1 (tptr tschar)) (tptr tvoid)) :: nil)))
    (Scall None
      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _key (tptr (Tstruct _KVKey noattr))) :: nil))))
|}.

Definition f_KV_NewKVStore := {|
  fn_return := (tptr (Tstruct _KVStore noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_store, (tptr (Tstruct _KVStore noattr))) ::
               (_root, (tptr (Tstruct _KVNode noattr))) ::
               (_t'2, (tptr (Tstruct _KVNode noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _KVStore noattr) tuint) :: nil))
    (Sset _store
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _KVStore noattr)))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _store (tptr (Tstruct _KVStore noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _newKVNode (Tfunction Tnil (tptr (Tstruct _KVNode noattr))
                             {|cc_vararg:=false; cc_unproto:=true; cc_structret:=false|}))
          nil)
        (Sset _root (Etempvar _t'2 (tptr (Tstruct _KVNode noattr)))))
      (Ssequence
        (Sifthenelse (Ebinop Oeq
                       (Etempvar _root (tptr (Tstruct _KVNode noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Ssequence
            (Scall None
              (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default))
              ((Etempvar _store (tptr (Tstruct _KVStore noattr))) :: nil))
            (Sreturn (Some (Econst_int (Int.repr 0) tint))))
          Sskip)
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _store (tptr (Tstruct _KVStore noattr)))
                (Tstruct _KVStore noattr)) _rootNode
              (tptr (Tstruct _KVNode noattr)))
            (Etempvar _root (tptr (Tstruct _KVNode noattr))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _store (tptr (Tstruct _KVStore noattr)))
                  (Tstruct _KVStore noattr)) _numKeys tuint)
              (Econst_int (Int.repr 0) tint))
            (Sreturn (Some (Etempvar _store (tptr (Tstruct _KVStore noattr)))))))))))
|}.

Definition f_newKVNode := {|
  fn_return := (tptr (Tstruct _KVNode noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_root, (tptr (Tstruct _KVNode noattr))) ::
               (_tree, (tptr (Tstruct _Relation noattr))) ::
               (_cursor, (tptr (Tstruct _Cursor noattr))) ::
               (_t'3, (tptr (Tstruct _Cursor noattr))) ::
               (_t'2, (tptr (Tstruct _Relation noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _KVNode noattr) tuint) :: nil))
    (Sset _root
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _KVNode noattr)))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _root (tptr (Tstruct _KVNode noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _RL_NewRelation (Tfunction Tnil
                                  (tptr (Tstruct _Relation noattr))
                                  cc_default)) nil)
        (Sset _tree (Etempvar _t'2 (tptr (Tstruct _Relation noattr)))))
      (Ssequence
        (Sifthenelse (Ebinop Oeq
                       (Etempvar _tree (tptr (Tstruct _Relation noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Ssequence
            (Scall None
              (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default))
              ((Etempvar _root (tptr (Tstruct _KVNode noattr))) :: nil))
            (Sreturn (Some (Econst_int (Int.repr 0) tint))))
          Sskip)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _RL_NewCursor (Tfunction
                                    (Tcons (tptr (Tstruct _Relation noattr))
                                      Tnil) (tptr (Tstruct _Cursor noattr))
                                    cc_default))
              ((Etempvar _tree (tptr (Tstruct _Relation noattr))) :: nil))
            (Sset _cursor (Etempvar _t'3 (tptr (Tstruct _Cursor noattr)))))
          (Ssequence
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Ssequence
                (Scall None
                  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                cc_default))
                  ((Etempvar _root (tptr (Tstruct _KVNode noattr))) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _RL_DeleteRelation (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _Relation noattr))
                                                 (Tcons
                                                   (tptr (Tfunction
                                                           (Tcons
                                                             (tptr tvoid)
                                                             Tnil) tvoid
                                                           cc_default)) Tnil))
                                               tvoid cc_default))
                    ((Etempvar _tree (tptr (Tstruct _Relation noattr))) ::
                     (Econst_int (Int.repr 0) tint) :: nil))
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
              Sskip)
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _root (tptr (Tstruct _KVNode noattr)))
                    (Tstruct _KVNode noattr)) _cursor
                  (tptr (Tstruct _Cursor noattr)))
                (Etempvar _cursor (tptr (Tstruct _Cursor noattr))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _root (tptr (Tstruct _KVNode noattr)))
                      (Tstruct _KVNode noattr)) _tree
                    (tptr (Tstruct _Relation noattr)))
                  (Etempvar _tree (tptr (Tstruct _Relation noattr))))
                (Sreturn (Some (Etempvar _root (tptr (Tstruct _KVNode noattr)))))))))))))
|}.

Definition f_getNodeCursor := {|
  fn_return := (tptr (Tstruct _Cursor noattr));
  fn_callconv := cc_default;
  fn_params := ((_node, (tptr (Tstruct _KVNode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _node (tptr (Tstruct _KVNode noattr)))
        (Tstruct _KVNode noattr)) _cursor (tptr (Tstruct _Cursor noattr))))
  (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _Cursor noattr))))))
|}.

Definition v___func____8 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 86) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_KV_Put := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_kvStore, (tptr (Tstruct _KVStore noattr))) ::
                (_key, (tptr (Tstruct _KVKey noattr))) ::
                (_value, (tptr tvoid)) :: nil);
  fn_vars := ((_sndKey, (tptr (Tstruct _KVKey noattr))) :: nil);
  fn_temps := ((_putCompleted, tint) ::
               (_currNode, (tptr (Tstruct _KVNode noattr))) ::
               (_btreeStatus, tint) ::
               (_btreeCursor, (tptr (Tstruct _Cursor noattr))) ::
               (_btree, (tptr (Tstruct _Relation noattr))) ::
               (_borderNode, (tptr (Tstruct _BorderNode noattr))) ::
               (_nextKeySlice, tuint) ::
               (_link, (tptr (Tstruct _KVNode noattr))) ::
               (_sndValue, (tptr tvoid)) :: (_sndKeySlice, tuint) ::
               (_t'22, tint) :: (_t'21, (tptr tvoid)) ::
               (_t'20, (tptr tvoid)) :: (_t'19, tint) ::
               (_t'18, (tptr (Tstruct _KVNode noattr))) ::
               (_t'17, (tptr tvoid)) :: (_t'16, (tptr tvoid)) ::
               (_t'15, (tptr tvoid)) ::
               (_t'14, (tptr (Tstruct _BorderNode noattr))) ::
               (_t'13, tint) ::
               (_t'12, (tptr (Tstruct _BorderNode noattr))) ::
               (_t'11, (tptr (Tstruct _BorderNode noattr))) ::
               (_t'10, tint) ::
               (_t'9, (tptr (Tstruct _BorderNode noattr))) ::
               (_t'8, (tptr (Tstruct _KVNode noattr))) ::
               (_t'7, (tptr (Tstruct _BorderNode noattr))) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, (tptr (Tstruct _Cursor noattr))) ::
               (_t'1, tint) :: (_t'59, tuint) :: (_t'58, (tptr tschar)) ::
               (_t'57, tuint) :: (_t'56, (tptr tschar)) :: (_t'55, tuint) ::
               (_t'54, (tptr (Tstruct _KVKey noattr))) ::
               (_t'53, (tptr tschar)) ::
               (_t'52, (tptr (Tstruct _KVKey noattr))) :: (_t'51, tuint) ::
               (_t'50, (tptr (Tstruct _KVKey noattr))) :: (_t'49, tuint) ::
               (_t'48, tuint) :: (_t'47, (tptr tschar)) :: (_t'46, tuint) ::
               (_t'45, tuint) :: (_t'44, (tptr (Tstruct _KVKey noattr))) ::
               (_t'43, (tptr (Tstruct _KVKey noattr))) ::
               (_t'42, (tptr tschar)) ::
               (_t'41, (tptr (Tstruct _KVKey noattr))) ::
               (_t'40, (tptr (Tstruct _KVKey noattr))) ::
               (_t'39, (tptr (Tstruct _KVKey noattr))) :: (_t'38, tuint) ::
               (_t'37, tuint) :: (_t'36, tuint) :: (_t'35, tuint) ::
               (_t'34, tuint) :: (_t'33, tuint) :: (_t'32, (tptr tschar)) ::
               (_t'31, (tptr tschar)) :: (_t'30, tuint) ::
               (_t'29, (tptr tschar)) :: (_t'28, tuint) :: (_t'27, tuint) ::
               (_t'26, (tptr tschar)) :: (_t'25, tuint) :: (_t'24, tuint) ::
               (_t'23, (tptr (Tstruct _KVKey noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _putCompleted (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _btreeStatus (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign (Evar _sndKey (tptr (Tstruct _KVKey noattr)))
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sset _sndValue (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sset _sndKeySlice (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sifthenelse (Ebinop One
                           (Etempvar _kvStore (tptr (Tstruct _KVStore noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              Sskip
              (Scall None
                (Evar ___assert_fail (Tfunction
                                       (Tcons (tptr tschar)
                                         (Tcons (tptr tschar)
                                           (Tcons tuint
                                             (Tcons (tptr tschar) Tnil))))
                                       tvoid cc_default))
                ((Evar ___stringlit_8 (tarray tschar 13)) ::
                 (Evar ___stringlit_1 (tarray tschar 13)) ::
                 (Econst_int (Int.repr 333) tint) ::
                 (Evar ___func____8 (tarray tschar 7)) :: nil)))
            (Ssequence
              (Sifthenelse (Ebinop One
                             (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                Sskip
                (Scall None
                  (Evar ___assert_fail (Tfunction
                                         (Tcons (tptr tschar)
                                           (Tcons (tptr tschar)
                                             (Tcons tuint
                                               (Tcons (tptr tschar) Tnil))))
                                         tvoid cc_default))
                  ((Evar ___stringlit_7 (tarray tschar 9)) ::
                   (Evar ___stringlit_1 (tarray tschar 13)) ::
                   (Econst_int (Int.repr 334) tint) ::
                   (Evar ___func____8 (tarray tschar 7)) :: nil)))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'58
                      (Efield
                        (Ederef
                          (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                          (Tstruct _KVKey noattr)) _str (tptr tschar)))
                    (Sifthenelse (Ebinop One (Etempvar _t'58 (tptr tschar))
                                   (Ecast (Econst_int (Int.repr 0) tint)
                                     (tptr tvoid)) tint)
                      (Sset _t'1 (Econst_int (Int.repr 1) tint))
                      (Ssequence
                        (Sset _t'59
                          (Efield
                            (Ederef
                              (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                              (Tstruct _KVKey noattr)) _len tuint))
                        (Sset _t'1
                          (Ecast
                            (Ebinop Oeq (Etempvar _t'59 tuint)
                              (Econst_int (Int.repr 0) tint) tint) tbool)))))
                  (Sifthenelse (Etempvar _t'1 tint)
                    Sskip
                    (Scall None
                      (Evar ___assert_fail (Tfunction
                                             (Tcons (tptr tschar)
                                               (Tcons (tptr tschar)
                                                 (Tcons tuint
                                                   (Tcons (tptr tschar) Tnil))))
                                             tvoid cc_default))
                      ((Evar ___stringlit_9 (tarray tschar 31)) ::
                       (Evar ___stringlit_1 (tarray tschar 13)) ::
                       (Econst_int (Int.repr 336) tint) ::
                       (Evar ___func____8 (tarray tschar 7)) :: nil))))
                (Ssequence
                  (Sifthenelse (Ebinop One (Etempvar _value (tptr tvoid))
                                 (Ecast (Econst_int (Int.repr 0) tint)
                                   (tptr tvoid)) tint)
                    Sskip
                    (Scall None
                      (Evar ___assert_fail (Tfunction
                                             (Tcons (tptr tschar)
                                               (Tcons (tptr tschar)
                                                 (Tcons tuint
                                                   (Tcons (tptr tschar) Tnil))))
                                             tvoid cc_default))
                      ((Evar ___stringlit_10 (tarray tschar 11)) ::
                       (Evar ___stringlit_1 (tarray tschar 13)) ::
                       (Econst_int (Int.repr 338) tint) ::
                       (Evar ___func____8 (tarray tschar 7)) :: nil)))
                  (Ssequence
                    (Sset _currNode
                      (Efield
                        (Ederef
                          (Etempvar _kvStore (tptr (Tstruct _KVStore noattr)))
                          (Tstruct _KVStore noattr)) _rootNode
                        (tptr (Tstruct _KVNode noattr))))
                    (Ssequence
                      (Swhile
                        (Ebinop Oeq (Etempvar _putCompleted tint)
                          (Econst_int (Int.repr 0) tint) tint)
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'2)
                              (Evar _getNodeCursor (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _KVNode noattr))
                                                       Tnil)
                                                     (tptr (Tstruct _Cursor noattr))
                                                     cc_default))
                              ((Etempvar _currNode (tptr (Tstruct _KVNode noattr))) ::
                               nil))
                            (Sset _btreeCursor
                              (Etempvar _t'2 (tptr (Tstruct _Cursor noattr)))))
                          (Ssequence
                            (Sset _btree
                              (Efield
                                (Ederef
                                  (Etempvar _currNode (tptr (Tstruct _KVNode noattr)))
                                  (Tstruct _KVNode noattr)) _tree
                                (tptr (Tstruct _Relation noattr))))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'57
                                      (Efield
                                        (Ederef
                                          (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                          (Tstruct _KVKey noattr)) _len
                                        tuint))
                                    (Scall (Some _t'3)
                                      (Evar _UTIL_Min (Tfunction
                                                        (Tcons tuint
                                                          (Tcons tuint Tnil))
                                                        tuint cc_default))
                                      ((Econst_int (Int.repr 4) tint) ::
                                       (Etempvar _t'57 tuint) :: nil)))
                                  (Ssequence
                                    (Sset _t'56
                                      (Efield
                                        (Ederef
                                          (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                          (Tstruct _KVKey noattr)) _str
                                        (tptr tschar)))
                                    (Scall (Some _t'4)
                                      (Evar _UTIL_GetNextKeySlice (Tfunction
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tuint
                                                                    cc_default))
                                      ((Etempvar _t'56 (tptr tschar)) ::
                                       (Etempvar _t'3 tuint) :: nil))))
                                (Sset _nextKeySlice (Etempvar _t'4 tuint)))
                              (Ssequence
                                (Sset _t'23
                                  (Evar _sndKey (tptr (Tstruct _KVKey noattr))))
                                (Sifthenelse (Ebinop One
                                               (Etempvar _t'23 (tptr (Tstruct _KVKey noattr)))
                                               (Ecast
                                                 (Econst_int (Int.repr 0) tint)
                                                 (tptr tvoid)) tint)
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'54
                                            (Evar _sndKey (tptr (Tstruct _KVKey noattr))))
                                          (Ssequence
                                            (Sset _t'55
                                              (Efield
                                                (Ederef
                                                  (Etempvar _t'54 (tptr (Tstruct _KVKey noattr)))
                                                  (Tstruct _KVKey noattr))
                                                _len tuint))
                                            (Scall (Some _t'5)
                                              (Evar _UTIL_Min (Tfunction
                                                                (Tcons tuint
                                                                  (Tcons
                                                                    tuint
                                                                    Tnil))
                                                                tuint
                                                                cc_default))
                                              ((Econst_int (Int.repr 4) tint) ::
                                               (Etempvar _t'55 tuint) :: nil))))
                                        (Ssequence
                                          (Sset _t'52
                                            (Evar _sndKey (tptr (Tstruct _KVKey noattr))))
                                          (Ssequence
                                            (Sset _t'53
                                              (Efield
                                                (Ederef
                                                  (Etempvar _t'52 (tptr (Tstruct _KVKey noattr)))
                                                  (Tstruct _KVKey noattr))
                                                _str (tptr tschar)))
                                            (Scall (Some _t'6)
                                              (Evar _UTIL_GetNextKeySlice 
                                              (Tfunction
                                                (Tcons (tptr tschar)
                                                  (Tcons tint Tnil)) tuint
                                                cc_default))
                                              ((Etempvar _t'53 (tptr tschar)) ::
                                               (Etempvar _t'5 tuint) :: nil)))))
                                      (Sset _sndKeySlice
                                        (Etempvar _t'6 tuint)))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _nextKeySlice tuint)
                                                   (Etempvar _sndKeySlice tuint)
                                                   tint)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'49
                                            (Efield
                                              (Ederef
                                                (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                (Tstruct _KVKey noattr)) _len
                                              tuint))
                                          (Sifthenelse (Ebinop Ole
                                                         (Etempvar _t'49 tuint)
                                                         (Econst_int (Int.repr 4) tint)
                                                         tint)
                                            (Sset _t'10
                                              (Econst_int (Int.repr 1) tint))
                                            (Ssequence
                                              (Sset _t'50
                                                (Evar _sndKey (tptr (Tstruct _KVKey noattr))))
                                              (Ssequence
                                                (Sset _t'51
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _t'50 (tptr (Tstruct _KVKey noattr)))
                                                      (Tstruct _KVKey noattr))
                                                    _len tuint))
                                                (Sset _t'10
                                                  (Ecast
                                                    (Ebinop Ole
                                                      (Etempvar _t'51 tuint)
                                                      (Econst_int (Int.repr 4) tint)
                                                      tint) tbool))))))
                                        (Sifthenelse (Etempvar _t'10 tint)
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'7)
                                                (Evar _BN_NewBorderNode 
                                                (Tfunction Tnil
                                                  (tptr (Tstruct _BorderNode noattr))
                                                  cc_default)) nil)
                                              (Sset _borderNode
                                                (Etempvar _t'7 (tptr (Tstruct _BorderNode noattr)))))
                                            (Ssequence
                                              (Scall None
                                                (Evar _BN_SetValue (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _BorderNode noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct _KVKey noattr))
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                 (Etempvar _key (tptr (Tstruct _KVKey noattr))) ::
                                                 (Etempvar _value (tptr tvoid)) ::
                                                 nil))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _BN_SetValue 
                                                  (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _BorderNode noattr))
                                                      (Tcons
                                                        (tptr (Tstruct _KVKey noattr))
                                                        (Tcons (tptr tvoid)
                                                          Tnil))) tvoid
                                                    cc_default))
                                                  ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                   (Etempvar _key (tptr (Tstruct _KVKey noattr))) ::
                                                   (Etempvar _sndValue (tptr tvoid)) ::
                                                   nil))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _RL_PutRecord 
                                                    (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _Cursor noattr))
                                                        (Tcons tuint
                                                          (Tcons (tptr tvoid)
                                                            Tnil))) tvoid
                                                      cc_default))
                                                    ((Etempvar _btreeCursor (tptr (Tstruct _Cursor noattr))) ::
                                                     (Etempvar _nextKeySlice tuint) ::
                                                     (Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                     nil))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'48
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _kvStore (tptr (Tstruct _KVStore noattr)))
                                                            (Tstruct _KVStore noattr))
                                                          _numKeys tuint))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _kvStore (tptr (Tstruct _KVStore noattr)))
                                                            (Tstruct _KVStore noattr))
                                                          _numKeys tuint)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'48 tuint)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tuint)))
                                                    (Sset _putCompleted
                                                      (Econst_int (Int.repr 1) tint)))))))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'8)
                                                (Evar _newKVNode (Tfunction
                                                                   Tnil
                                                                   (tptr (Tstruct _KVNode noattr))
                                                                   cc_default))
                                                nil)
                                              (Sset _link
                                                (Etempvar _t'8 (tptr (Tstruct _KVNode noattr)))))
                                            (Ssequence
                                              (Sifthenelse (Ebinop One
                                                             (Etempvar _link (tptr (Tstruct _KVNode noattr)))
                                                             (Ecast
                                                               (Econst_int (Int.repr 0) tint)
                                                               (tptr tvoid))
                                                             tint)
                                                Sskip
                                                (Scall None
                                                  (Evar ___assert_fail 
                                                  (Tfunction
                                                    (Tcons (tptr tschar)
                                                      (Tcons (tptr tschar)
                                                        (Tcons tuint
                                                          (Tcons
                                                            (tptr tschar)
                                                            Tnil)))) tvoid
                                                    cc_default))
                                                  ((Evar ___stringlit_11 (tarray tschar 10)) ::
                                                   (Evar ___stringlit_1 (tarray tschar 13)) ::
                                                   (Econst_int (Int.repr 373) tint) ::
                                                   (Evar ___func____8 (tarray tschar 7)) ::
                                                   nil)))
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'9)
                                                    (Evar _BN_NewBorderNode 
                                                    (Tfunction Tnil
                                                      (tptr (Tstruct _BorderNode noattr))
                                                      cc_default)) nil)
                                                  (Sset _borderNode
                                                    (Etempvar _t'9 (tptr (Tstruct _BorderNode noattr)))))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _BN_SetLink 
                                                    (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _BorderNode noattr))
                                                        (Tcons (tptr tvoid)
                                                          Tnil)) tvoid
                                                      cc_default))
                                                    ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                     (Etempvar _link (tptr (Tstruct _KVNode noattr))) ::
                                                     nil))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _RL_PutRecord 
                                                      (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _Cursor noattr))
                                                          (Tcons tuint
                                                            (Tcons
                                                              (tptr tvoid)
                                                              Tnil))) tvoid
                                                        cc_default))
                                                      ((Etempvar _btreeCursor (tptr (Tstruct _Cursor noattr))) ::
                                                       (Etempvar _nextKeySlice tuint) ::
                                                       (Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                       nil))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'47
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                              (Tstruct _KVKey noattr))
                                                            _str
                                                            (tptr tschar)))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                              (Tstruct _KVKey noattr))
                                                            _str
                                                            (tptr tschar))
                                                          (Ebinop Oadd
                                                            (Etempvar _t'47 (tptr tschar))
                                                            (Econst_int (Int.repr 4) tint)
                                                            (tptr tschar))))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'46
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                                (Tstruct _KVKey noattr))
                                                              _len tuint))
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                                (Tstruct _KVKey noattr))
                                                              _len tuint)
                                                            (Ebinop Osub
                                                              (Etempvar _t'46 tuint)
                                                              (Econst_int (Int.repr 4) tint)
                                                              tuint)))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'43
                                                              (Evar _sndKey (tptr (Tstruct _KVKey noattr))))
                                                            (Ssequence
                                                              (Sset _t'44
                                                                (Evar _sndKey (tptr (Tstruct _KVKey noattr))))
                                                              (Ssequence
                                                                (Sset _t'45
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'44 (tptr (Tstruct _KVKey noattr)))
                                                                    (Tstruct _KVKey noattr))
                                                                    _len
                                                                    tuint))
                                                                (Sassign
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'43 (tptr (Tstruct _KVKey noattr)))
                                                                    (Tstruct _KVKey noattr))
                                                                    _len
                                                                    tuint)
                                                                  (Ebinop Osub
                                                                    (Etempvar _t'45 tuint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tuint)))))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'40
                                                                (Evar _sndKey (tptr (Tstruct _KVKey noattr))))
                                                              (Ssequence
                                                                (Sset _t'41
                                                                  (Evar _sndKey (tptr (Tstruct _KVKey noattr))))
                                                                (Ssequence
                                                                  (Sset _t'42
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'41 (tptr (Tstruct _KVKey noattr)))
                                                                    (Tstruct _KVKey noattr))
                                                                    _str
                                                                    (tptr tschar)))
                                                                  (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'40 (tptr (Tstruct _KVKey noattr)))
                                                                    (Tstruct _KVKey noattr))
                                                                    _str
                                                                    (tptr tschar))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'42 (tptr tschar))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tschar))))))
                                                            (Sset _currNode
                                                              (Etempvar _link (tptr (Tstruct _KVNode noattr)))))))))))))))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'11)
                                            (Evar _BN_NewBorderNode (Tfunction
                                                                    Tnil
                                                                    (tptr (Tstruct _BorderNode noattr))
                                                                    cc_default))
                                            nil)
                                          (Sset _borderNode
                                            (Etempvar _t'11 (tptr (Tstruct _BorderNode noattr)))))
                                        (Ssequence
                                          (Scall None
                                            (Evar _BN_SetValue (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _BorderNode noattr))
                                                                   (Tcons
                                                                    (tptr (Tstruct _KVKey noattr))
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)))
                                                                 tvoid
                                                                 cc_default))
                                            ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                             (Etempvar _key (tptr (Tstruct _KVKey noattr))) ::
                                             (Etempvar _value (tptr tvoid)) ::
                                             nil))
                                          (Ssequence
                                            (Scall None
                                              (Evar _RL_PutRecord (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _Cursor noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                              ((Etempvar _btreeCursor (tptr (Tstruct _Cursor noattr))) ::
                                               (Etempvar _nextKeySlice tuint) ::
                                               (Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                               nil))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'12)
                                                  (Evar _BN_NewBorderNode 
                                                  (Tfunction Tnil
                                                    (tptr (Tstruct _BorderNode noattr))
                                                    cc_default)) nil)
                                                (Sset _borderNode
                                                  (Etempvar _t'12 (tptr (Tstruct _BorderNode noattr)))))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'39
                                                    (Evar _sndKey (tptr (Tstruct _KVKey noattr))))
                                                  (Scall None
                                                    (Evar _BN_SetValue 
                                                    (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _BorderNode noattr))
                                                        (Tcons
                                                          (tptr (Tstruct _KVKey noattr))
                                                          (Tcons (tptr tvoid)
                                                            Tnil))) tvoid
                                                      cc_default))
                                                    ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                     (Etempvar _t'39 (tptr (Tstruct _KVKey noattr))) ::
                                                     (Etempvar _sndValue (tptr tvoid)) ::
                                                     nil)))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _RL_PutRecord 
                                                    (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _Cursor noattr))
                                                        (Tcons tuint
                                                          (Tcons (tptr tvoid)
                                                            Tnil))) tvoid
                                                      cc_default))
                                                    ((Etempvar _btreeCursor (tptr (Tstruct _Cursor noattr))) ::
                                                     (Etempvar _sndKeySlice tuint) ::
                                                     (Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                     nil))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'38
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _kvStore (tptr (Tstruct _KVStore noattr)))
                                                            (Tstruct _KVStore noattr))
                                                          _numKeys tuint))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _kvStore (tptr (Tstruct _KVStore noattr)))
                                                            (Tstruct _KVStore noattr))
                                                          _numKeys tuint)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'38 tuint)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tuint)))
                                                    (Sset _putCompleted
                                                      (Econst_int (Int.repr 1) tint)))))))))))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'13)
                                        (Evar _RL_MoveToKey (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _Cursor noattr))
                                                                (Tcons tuint
                                                                  Tnil)) tint
                                                              cc_default))
                                        ((Etempvar _btreeCursor (tptr (Tstruct _Cursor noattr))) ::
                                         (Etempvar _nextKeySlice tuint) ::
                                         nil))
                                      (Sset _btreeStatus
                                        (Etempvar _t'13 tint)))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _btreeStatus tint)
                                                   (Econst_int (Int.repr 0) tint)
                                                   tint)
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'14)
                                            (Evar _BN_NewBorderNode (Tfunction
                                                                    Tnil
                                                                    (tptr (Tstruct _BorderNode noattr))
                                                                    cc_default))
                                            nil)
                                          (Sset _borderNode
                                            (Etempvar _t'14 (tptr (Tstruct _BorderNode noattr)))))
                                        (Ssequence
                                          (Scall None
                                            (Evar _BN_SetValue (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _BorderNode noattr))
                                                                   (Tcons
                                                                    (tptr (Tstruct _KVKey noattr))
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)))
                                                                 tvoid
                                                                 cc_default))
                                            ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                             (Etempvar _key (tptr (Tstruct _KVKey noattr))) ::
                                             (Etempvar _value (tptr tvoid)) ::
                                             nil))
                                          (Ssequence
                                            (Scall None
                                              (Evar _RL_PutRecord (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _Cursor noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                              ((Etempvar _btreeCursor (tptr (Tstruct _Cursor noattr))) ::
                                               (Etempvar _nextKeySlice tuint) ::
                                               (Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                               nil))
                                            (Ssequence
                                              (Sset _t'37
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _kvStore (tptr (Tstruct _KVStore noattr)))
                                                    (Tstruct _KVStore noattr))
                                                  _numKeys tuint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _kvStore (tptr (Tstruct _KVStore noattr)))
                                                    (Tstruct _KVStore noattr))
                                                  _numKeys tuint)
                                                (Ebinop Oadd
                                                  (Etempvar _t'37 tuint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tuint))))))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'15)
                                            (Evar _RL_GetRecord (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct _Cursor noattr))
                                                                    Tnil)
                                                                  (tptr tvoid)
                                                                  cc_default))
                                            ((Etempvar _btreeCursor (tptr (Tstruct _Cursor noattr))) ::
                                             nil))
                                          (Sset _borderNode
                                            (Ecast
                                              (Etempvar _t'15 (tptr tvoid))
                                              (tptr (Tstruct _BorderNode noattr)))))
                                        (Ssequence
                                          (Sset _t'24
                                            (Efield
                                              (Ederef
                                                (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                (Tstruct _KVKey noattr)) _len
                                              tuint))
                                          (Sifthenelse (Ebinop Ole
                                                         (Etempvar _t'24 tuint)
                                                         (Econst_int (Int.repr 4) tint)
                                                         tint)
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'36
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                        (Tstruct _KVKey noattr))
                                                      _len tuint))
                                                  (Scall (Some _t'16)
                                                    (Evar _BN_GetPrefixValue 
                                                    (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _BorderNode noattr))
                                                        (Tcons tint Tnil))
                                                      (tptr tvoid)
                                                      cc_default))
                                                    ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                     (Etempvar _t'36 tuint) ::
                                                     nil)))
                                                (Sifthenelse (Ebinop Oeq
                                                               (Etempvar _t'16 (tptr tvoid))
                                                               (Ecast
                                                                 (Econst_int (Int.repr 0) tint)
                                                                 (tptr tvoid))
                                                               tint)
                                                  (Ssequence
                                                    (Sset _t'35
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _kvStore (tptr (Tstruct _KVStore noattr)))
                                                          (Tstruct _KVStore noattr))
                                                        _numKeys tuint))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _kvStore (tptr (Tstruct _KVStore noattr)))
                                                          (Tstruct _KVStore noattr))
                                                        _numKeys tuint)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'35 tuint)
                                                        (Econst_int (Int.repr 1) tint)
                                                        tuint)))
                                                  Sskip))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'34
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                        (Tstruct _KVKey noattr))
                                                      _len tuint))
                                                  (Scall None
                                                    (Evar _BN_SetPrefixValue 
                                                    (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _BorderNode noattr))
                                                        (Tcons tint
                                                          (Tcons (tptr tvoid)
                                                            Tnil))) tvoid
                                                      cc_default))
                                                    ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                     (Etempvar _t'34 tuint) ::
                                                     (Etempvar _value (tptr tvoid)) ::
                                                     nil)))
                                                (Sset _putCompleted
                                                  (Econst_int (Int.repr 1) tint))))
                                            (Ssequence
                                              (Scall (Some _t'22)
                                                (Evar _BN_HasSuffix (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _BorderNode noattr))
                                                                    Tnil)
                                                                    tint
                                                                    cc_default))
                                                ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                 nil))
                                              (Sifthenelse (Etempvar _t'22 tint)
                                                (Ssequence
                                                  (Scall (Some _t'19)
                                                    (Evar _BN_TestSuffix 
                                                    (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _BorderNode noattr))
                                                        (Tcons
                                                          (tptr (Tstruct _KVKey noattr))
                                                          Tnil)) tint
                                                      cc_default))
                                                    ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                     (Etempvar _key (tptr (Tstruct _KVKey noattr))) ::
                                                     nil))
                                                  (Sifthenelse (Etempvar _t'19 tint)
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'32
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                              (Tstruct _KVKey noattr))
                                                            _str
                                                            (tptr tschar)))
                                                        (Ssequence
                                                          (Sset _t'33
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                                (Tstruct _KVKey noattr))
                                                              _len tuint))
                                                          (Scall None
                                                            (Evar _BN_SetSuffixValue 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _BorderNode noattr))
                                                                (Tcons
                                                                  (tptr tschar)
                                                                  (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil))))
                                                              tvoid
                                                              cc_default))
                                                            ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                             (Ebinop Oadd
                                                               (Etempvar _t'32 (tptr tschar))
                                                               (Econst_int (Int.repr 4) tint)
                                                               (tptr tschar)) ::
                                                             (Ebinop Osub
                                                               (Etempvar _t'33 tuint)
                                                               (Econst_int (Int.repr 4) tint)
                                                               tuint) ::
                                                             (Etempvar _value (tptr tvoid)) ::
                                                             nil))))
                                                      (Sset _putCompleted
                                                        (Econst_int (Int.repr 1) tint)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Scall (Some _t'17)
                                                          (Evar _BN_ExportSuffixValue 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _BorderNode noattr))
                                                              (Tcons
                                                                (tptr (tptr (Tstruct _KVKey noattr)))
                                                                Tnil))
                                                            (tptr tvoid)
                                                            cc_default))
                                                          ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                           (Eaddrof
                                                             (Evar _sndKey (tptr (Tstruct _KVKey noattr)))
                                                             (tptr (tptr (Tstruct _KVKey noattr)))) ::
                                                           nil))
                                                        (Sset _sndValue
                                                          (Etempvar _t'17 (tptr tvoid))))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Scall (Some _t'18)
                                                            (Evar _newKVNode 
                                                            (Tfunction Tnil
                                                              (tptr (Tstruct _KVNode noattr))
                                                              cc_default))
                                                            nil)
                                                          (Sset _link
                                                            (Etempvar _t'18 (tptr (Tstruct _KVNode noattr)))))
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _BN_SetLink 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _BorderNode noattr))
                                                                (Tcons
                                                                  (tptr tvoid)
                                                                  Tnil))
                                                              tvoid
                                                              cc_default))
                                                            ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                             (Etempvar _link (tptr (Tstruct _KVNode noattr))) ::
                                                             nil))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'31
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                                    (Tstruct _KVKey noattr))
                                                                  _str
                                                                  (tptr tschar)))
                                                              (Sassign
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                                    (Tstruct _KVKey noattr))
                                                                  _str
                                                                  (tptr tschar))
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'31 (tptr tschar))
                                                                  (Econst_int (Int.repr 4) tint)
                                                                  (tptr tschar))))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'30
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                                    (Tstruct _KVKey noattr))
                                                                    _len
                                                                    tuint))
                                                                (Sassign
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                                    (Tstruct _KVKey noattr))
                                                                    _len
                                                                    tuint)
                                                                  (Ebinop Osub
                                                                    (Etempvar _t'30 tuint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tuint)))
                                                              (Sset _currNode
                                                                (Etempvar _link (tptr (Tstruct _KVNode noattr)))))))))))
                                                (Ssequence
                                                  (Scall (Some _t'21)
                                                    (Evar _BN_GetLink 
                                                    (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _BorderNode noattr))
                                                        Tnil) (tptr tvoid)
                                                      cc_default))
                                                    ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                     nil))
                                                  (Sifthenelse (Ebinop One
                                                                 (Etempvar _t'21 (tptr tvoid))
                                                                 (Ecast
                                                                   (Econst_int (Int.repr 0) tint)
                                                                   (tptr tvoid))
                                                                 tint)
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'29
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                              (Tstruct _KVKey noattr))
                                                            _str
                                                            (tptr tschar)))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                              (Tstruct _KVKey noattr))
                                                            _str
                                                            (tptr tschar))
                                                          (Ebinop Oadd
                                                            (Etempvar _t'29 (tptr tschar))
                                                            (Econst_int (Int.repr 4) tint)
                                                            (tptr tschar))))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'28
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                                (Tstruct _KVKey noattr))
                                                              _len tuint))
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                                (Tstruct _KVKey noattr))
                                                              _len tuint)
                                                            (Ebinop Osub
                                                              (Etempvar _t'28 tuint)
                                                              (Econst_int (Int.repr 4) tint)
                                                              tuint)))
                                                        (Ssequence
                                                          (Scall (Some _t'20)
                                                            (Evar _BN_GetLink 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _BorderNode noattr))
                                                                Tnil)
                                                              (tptr tvoid)
                                                              cc_default))
                                                            ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                             nil))
                                                          (Sset _currNode
                                                            (Etempvar _t'20 (tptr tvoid))))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'26
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                              (Tstruct _KVKey noattr))
                                                            _str
                                                            (tptr tschar)))
                                                        (Ssequence
                                                          (Sset _t'27
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                                                                (Tstruct _KVKey noattr))
                                                              _len tuint))
                                                          (Scall None
                                                            (Evar _BN_SetSuffixValue 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _BorderNode noattr))
                                                                (Tcons
                                                                  (tptr tschar)
                                                                  (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil))))
                                                              tvoid
                                                              cc_default))
                                                            ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                                                             (Ebinop Oadd
                                                               (Etempvar _t'26 (tptr tschar))
                                                               (Econst_int (Int.repr 4) tint)
                                                               (tptr tschar)) ::
                                                             (Ebinop Osub
                                                               (Etempvar _t'27 tuint)
                                                               (Econst_int (Int.repr 4) tint)
                                                               tuint) ::
                                                             (Etempvar _value (tptr tvoid)) ::
                                                             nil))))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'25
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _kvStore (tptr (Tstruct _KVStore noattr)))
                                                                (Tstruct _KVStore noattr))
                                                              _numKeys tuint))
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _kvStore (tptr (Tstruct _KVStore noattr)))
                                                                (Tstruct _KVStore noattr))
                                                              _numKeys tuint)
                                                            (Ebinop Oadd
                                                              (Etempvar _t'25 tuint)
                                                              (Econst_int (Int.repr 1) tint)
                                                              tuint)))
                                                        (Sset _putCompleted
                                                          (Econst_int (Int.repr 1) tint)))))))))))))))))))
                      (Sreturn (Some (Econst_int (Int.repr 1) tint))))))))))))))
|}.

Definition v___func____9 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 86) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_KV_Get := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_kvStore, (tptr (Tstruct _KVStore noattr))) ::
                (_key, (tptr (Tstruct _KVKey noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_totalKey, (tptr tschar)) :: (_totalKeyLength, tuint) ::
               (_t'1, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _KVNode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One
                 (Etempvar _kvStore (tptr (Tstruct _KVStore noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_8 (tarray tschar 13)) ::
       (Evar ___stringlit_1 (tarray tschar 13)) ::
       (Econst_int (Int.repr 511) tint) ::
       (Evar ___func____9 (tarray tschar 7)) :: nil)))
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar _key (tptr (Tstruct _KVKey noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      Sskip
      (Scall None
        (Evar ___assert_fail (Tfunction
                               (Tcons (tptr tschar)
                                 (Tcons (tptr tschar)
                                   (Tcons tuint (Tcons (tptr tschar) Tnil))))
                               tvoid cc_default))
        ((Evar ___stringlit_7 (tarray tschar 9)) ::
         (Evar ___stringlit_1 (tarray tschar 13)) ::
         (Econst_int (Int.repr 512) tint) ::
         (Evar ___func____9 (tarray tschar 7)) :: nil)))
    (Ssequence
      (Sset _totalKey
        (Efield
          (Ederef (Etempvar _key (tptr (Tstruct _KVKey noattr)))
            (Tstruct _KVKey noattr)) _str (tptr tschar)))
      (Ssequence
        (Sset _totalKeyLength
          (Efield
            (Ederef (Etempvar _key (tptr (Tstruct _KVKey noattr)))
              (Tstruct _KVKey noattr)) _len tuint))
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _kvStore (tptr (Tstruct _KVStore noattr)))
                  (Tstruct _KVStore noattr)) _rootNode
                (tptr (Tstruct _KVNode noattr))))
            (Scall (Some _t'1)
              (Evar _getValueOfPartialKey (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _KVNode noattr))
                                              (Tcons (tptr tschar)
                                                (Tcons tuint Tnil)))
                                            (tptr tvoid) cc_default))
              ((Etempvar _t'2 (tptr (Tstruct _KVNode noattr))) ::
               (Etempvar _totalKey (tptr tschar)) ::
               (Etempvar _totalKeyLength tuint) :: nil)))
          (Sreturn (Some (Etempvar _t'1 (tptr tvoid)))))))))
|}.

Definition v___func____10 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 86) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_KV_NumKeys := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_kvStore, (tptr (Tstruct _KVStore noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One
                 (Etempvar _kvStore (tptr (Tstruct _KVStore noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_8 (tarray tschar 13)) ::
       (Evar ___stringlit_1 (tarray tschar 13)) ::
       (Econst_int (Int.repr 531) tint) ::
       (Evar ___func____10 (tarray tschar 11)) :: nil)))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _kvStore (tptr (Tstruct _KVStore noattr)))
          (Tstruct _KVStore noattr)) _numKeys tuint))
    (Sreturn (Some (Etempvar _t'1 tuint)))))
|}.

Definition f_getValueOfPartialKey := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_node, (tptr (Tstruct _KVNode noattr))) ::
                (_partialKey, (tptr tschar)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_cursor, (tptr (Tstruct _Cursor noattr))) ::
               (_btree, (tptr (Tstruct _Relation noattr))) ::
               (_borderNode, (tptr (Tstruct _BorderNode noattr))) ::
               (_keySlice, tuint) :: (_btreeStatus, tint) :: (_t'11, tint) ::
               (_t'10, (tptr tvoid)) :: (_t'9, (tptr tvoid)) ::
               (_t'8, (tptr tvoid)) :: (_t'7, (tptr tvoid)) ::
               (_t'6, (tptr tvoid)) :: (_t'5, (tptr tvoid)) ::
               (_t'4, tint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _getNodeCursor (Tfunction
                             (Tcons (tptr (Tstruct _KVNode noattr)) Tnil)
                             (tptr (Tstruct _Cursor noattr)) cc_default))
      ((Etempvar _node (tptr (Tstruct _KVNode noattr))) :: nil))
    (Sset _cursor (Etempvar _t'1 (tptr (Tstruct _Cursor noattr)))))
  (Ssequence
    (Sset _btree
      (Efield
        (Ederef (Etempvar _node (tptr (Tstruct _KVNode noattr)))
          (Tstruct _KVNode noattr)) _tree (tptr (Tstruct _Relation noattr))))
    (Ssequence
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _UTIL_Min (Tfunction (Tcons tuint (Tcons tuint Tnil)) tuint
                              cc_default))
            ((Econst_int (Int.repr 4) tint) :: (Etempvar _len tuint) :: nil))
          (Scall (Some _t'3)
            (Evar _UTIL_GetNextKeySlice (Tfunction
                                          (Tcons (tptr tschar)
                                            (Tcons tint Tnil)) tuint
                                          cc_default))
            ((Etempvar _partialKey (tptr tschar)) ::
             (Ecast (Etempvar _t'2 tuint) tint) :: nil)))
        (Sset _keySlice (Etempvar _t'3 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _RL_MoveToKey (Tfunction
                                  (Tcons (tptr (Tstruct _Cursor noattr))
                                    (Tcons tuint Tnil)) tint cc_default))
            ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
             (Etempvar _keySlice tuint) :: nil))
          (Sset _btreeStatus (Etempvar _t'4 tint)))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _btreeStatus tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip)
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _RL_GetRecord (Tfunction
                                      (Tcons (tptr (Tstruct _Cursor noattr))
                                        Tnil) (tptr tvoid) cc_default))
                ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
              (Sset _borderNode
                (Ecast (Etempvar _t'5 (tptr tvoid))
                  (tptr (Tstruct _BorderNode noattr)))))
            (Sifthenelse (Ebinop Ole (Etempvar _len tuint)
                           (Econst_int (Int.repr 4) tint) tint)
              (Ssequence
                (Scall (Some _t'6)
                  (Evar _BN_GetPrefixValue (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _BorderNode noattr))
                                               (Tcons tint Tnil))
                                             (tptr tvoid) cc_default))
                  ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                   (Etempvar _len tuint) :: nil))
                (Sreturn (Some (Etempvar _t'6 (tptr tvoid)))))
              (Ssequence
                (Scall (Some _t'11)
                  (Evar _BN_HasSuffix (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _BorderNode noattr))
                                          Tnil) tint cc_default))
                  ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                   nil))
                (Sifthenelse (Etempvar _t'11 tint)
                  (Ssequence
                    (Scall (Some _t'7)
                      (Evar _BN_GetSuffixValue (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _BorderNode noattr))
                                                   (Tcons (tptr tschar)
                                                     (Tcons tuint Tnil)))
                                                 (tptr tvoid) cc_default))
                      ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                       (Ebinop Oadd (Etempvar _partialKey (tptr tschar))
                         (Econst_int (Int.repr 4) tint) (tptr tschar)) ::
                       (Ebinop Osub (Etempvar _len tuint)
                         (Econst_int (Int.repr 4) tint) tuint) :: nil))
                    (Sreturn (Some (Etempvar _t'7 (tptr tvoid)))))
                  (Ssequence
                    (Scall (Some _t'10)
                      (Evar _BN_GetLink (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _BorderNode noattr))
                                            Tnil) (tptr tvoid) cc_default))
                      ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                       nil))
                    (Sifthenelse (Ebinop One (Etempvar _t'10 (tptr tvoid))
                                   (Ecast (Econst_int (Int.repr 0) tint)
                                     (tptr tvoid)) tint)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'8)
                            (Evar _BN_GetLink (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _BorderNode noattr))
                                                  Tnil) (tptr tvoid)
                                                cc_default))
                            ((Etempvar _borderNode (tptr (Tstruct _BorderNode noattr))) ::
                             nil))
                          (Scall (Some _t'9)
                            (Evar _getValueOfPartialKey (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _KVNode noattr))
                                                            (Tcons
                                                              (tptr tschar)
                                                              (Tcons tuint
                                                                Tnil)))
                                                          (tptr tvoid)
                                                          cc_default))
                            ((Etempvar _t'8 (tptr tvoid)) ::
                             (Ebinop Oadd
                               (Etempvar _partialKey (tptr tschar))
                               (Econst_int (Int.repr 4) tint) (tptr tschar)) ::
                             (Ebinop Osub (Etempvar _len tuint)
                               (Econst_int (Int.repr 4) tint) tuint) :: nil)))
                        (Sreturn (Some (Etempvar _t'9 (tptr tvoid)))))
                      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))
|}.

Definition composites : list composite_definition :=
(Composite _KVKey Struct
   ((_str, (tptr tschar)) :: (_len, tuint) :: nil)
   noattr ::
 Composite _KVStore Struct
   ((_rootNode, (tptr (Tstruct _KVNode noattr))) :: (_numKeys, tuint) :: nil)
   noattr ::
 Composite _KVNode Struct
   ((_tree, (tptr (Tstruct _Relation noattr))) ::
    (_cursor, (tptr (Tstruct _Cursor noattr))) :: nil)
   noattr ::
 Composite _BorderNode Struct
   ((_prefixLinks, (tarray (tptr tvoid) 4)) :: (_suffixLink, (tptr tvoid)) ::
    (_keySuffix, (tptr tschar)) :: (_keySuffixLength, tuint) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_11, Gvar v___stringlit_11) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_9, Gvar v___stringlit_9) ::
 (___stringlit_8, Gvar v___stringlit_8) ::
 (___stringlit_10, Gvar v___stringlit_10) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___assert_fail,
   Gfun(External (EF_external "__assert_fail"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tschar)
       (Tcons (tptr tschar) (Tcons tuint (Tcons (tptr tschar) Tnil)))) tvoid
     cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_UTIL_Min,
   Gfun(External (EF_external "UTIL_Min"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tuint (Tcons tuint Tnil)) tuint
     cc_default)) ::
 (_RL_NewRelation,
   Gfun(External (EF_external "RL_NewRelation"
                   (mksignature nil (Some AST.Tint) cc_default)) Tnil
     (tptr (Tstruct _Relation noattr)) cc_default)) ::
 (_RL_DeleteRelation,
   Gfun(External (EF_external "RL_DeleteRelation"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr (Tstruct _Relation noattr))
       (Tcons (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
         Tnil)) tvoid cc_default)) ::
 (_RL_NewCursor,
   Gfun(External (EF_external "RL_NewCursor"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _Relation noattr)) Tnil)
     (tptr (Tstruct _Cursor noattr)) cc_default)) ::
 (_RL_PutRecord,
   Gfun(External (EF_external "RL_PutRecord"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr (Tstruct _Cursor noattr))
       (Tcons tuint (Tcons (tptr tvoid) Tnil))) tvoid cc_default)) ::
 (_RL_MoveToKey,
   Gfun(External (EF_external "RL_MoveToKey"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr (Tstruct _Cursor noattr)) (Tcons tuint Tnil)) tint
     cc_default)) ::
 (_RL_GetRecord,
   Gfun(External (EF_external "RL_GetRecord"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) (tptr tvoid) cc_default)) ::
 (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_UTIL_StrEqual, Gfun(Internal f_UTIL_StrEqual)) ::
 (___func__, Gvar v___func__) ::
 (_UTIL_GetNextKeySlice, Gfun(Internal f_UTIL_GetNextKeySlice)) ::
 (_BN_NewBorderNode, Gfun(Internal f_BN_NewBorderNode)) ::
 (_BN_FreeBorderNode, Gfun(Internal f_BN_FreeBorderNode)) ::
 (___func____1, Gvar v___func____1) ::
 (_BN_SetPrefixValue, Gfun(Internal f_BN_SetPrefixValue)) ::
 (___func____2, Gvar v___func____2) ::
 (_BN_GetPrefixValue, Gfun(Internal f_BN_GetPrefixValue)) ::
 (_BN_SetSuffixValue, Gfun(Internal f_BN_SetSuffixValue)) ::
 (_BN_TestSuffix, Gfun(Internal f_BN_TestSuffix)) ::
 (_BN_GetSuffixValue, Gfun(Internal f_BN_GetSuffixValue)) ::
 (_BN_ExportSuffixValue, Gfun(Internal f_BN_ExportSuffixValue)) ::
 (_BN_SetLink, Gfun(Internal f_BN_SetLink)) ::
 (_BN_GetLink, Gfun(Internal f_BN_GetLink)) ::
 (_BN_HasSuffix, Gfun(Internal f_BN_HasSuffix)) ::
 (_BN_SetValue, Gfun(Internal f_BN_SetValue)) ::
 (___func____3, Gvar v___func____3) ::
 (_KV_NewKey, Gfun(Internal f_KV_NewKey)) ::
 (___func____4, Gvar v___func____4) ::
 (_KV_MoveKey, Gfun(Internal f_KV_MoveKey)) ::
 (___func____5, Gvar v___func____5) ::
 (_KV_GetCharArray, Gfun(Internal f_KV_GetCharArray)) ::
 (___func____6, Gvar v___func____6) ::
 (_KV_GetCharArraySize, Gfun(Internal f_KV_GetCharArraySize)) ::
 (_KV_KeyEqual, Gfun(Internal f_KV_KeyEqual)) ::
 (___func____7, Gvar v___func____7) ::
 (_KV_FreeKey, Gfun(Internal f_KV_FreeKey)) ::
 (_KV_NewKVStore, Gfun(Internal f_KV_NewKVStore)) ::
 (_newKVNode, Gfun(Internal f_newKVNode)) ::
 (_getNodeCursor, Gfun(Internal f_getNodeCursor)) ::
 (___func____8, Gvar v___func____8) :: (_KV_Put, Gfun(Internal f_KV_Put)) ::
 (___func____9, Gvar v___func____9) :: (_KV_Get, Gfun(Internal f_KV_Get)) ::
 (___func____10, Gvar v___func____10) ::
 (_KV_NumKeys, Gfun(Internal f_KV_NumKeys)) ::
 (_getValueOfPartialKey, Gfun(Internal f_getValueOfPartialKey)) :: nil).

Definition public_idents : list ident :=
(_getValueOfPartialKey :: _KV_NumKeys :: _KV_Get :: _KV_Put ::
 _getNodeCursor :: _newKVNode :: _KV_NewKVStore :: _KV_FreeKey ::
 _KV_KeyEqual :: _KV_GetCharArraySize :: _KV_GetCharArray :: _KV_MoveKey ::
 _KV_NewKey :: _BN_SetValue :: _BN_HasSuffix :: _BN_GetLink :: _BN_SetLink ::
 _BN_ExportSuffixValue :: _BN_GetSuffixValue :: _BN_TestSuffix ::
 _BN_SetSuffixValue :: _BN_GetPrefixValue :: _BN_SetPrefixValue ::
 _BN_FreeBorderNode :: _BN_NewBorderNode :: _UTIL_GetNextKeySlice ::
 _UTIL_StrEqual :: _surely_malloc :: _RL_GetRecord :: _RL_MoveToKey ::
 _RL_PutRecord :: _RL_NewCursor :: _RL_DeleteRelation :: _RL_NewRelation ::
 _UTIL_Min :: _exit :: _free :: _malloc :: ___assert_fail ::
 ___builtin_debug :: ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


