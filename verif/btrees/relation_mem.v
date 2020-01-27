From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.5"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "64"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "relation_mem.c"%string.
  Definition normalized := true.
End Info.

Definition _AscendToParent : ident := 155%positive.
Definition _BtNode : ident := 35%positive.
Definition _Child_or_Record : ident := 42%positive.
Definition _Cursor : ident := 56%positive.
Definition _Entry : ident := 45%positive.
Definition _First : ident := 47%positive.
Definition _Last : ident := 48%positive.
Definition _RL_CursorIsValid : ident := 142%positive.
Definition _RL_DeleteRecord : ident := 166%positive.
Definition _RL_DeleteRelation : ident := 133%positive.
Definition _RL_FreeCursor : ident := 139%positive.
Definition _RL_GetKey : ident := 162%positive.
Definition _RL_GetRecord : ident := 159%positive.
Definition _RL_IsEmpty : ident := 178%positive.
Definition _RL_MoveToFirst : ident := 169%positive.
Definition _RL_MoveToKey : ident := 165%positive.
Definition _RL_MoveToNext : ident := 147%positive.
Definition _RL_MoveToNextValid : ident := 175%positive.
Definition _RL_MoveToPrevious : ident := 174%positive.
Definition _RL_MoveToPreviousNotFirst : ident := 176%positive.
Definition _RL_NewCursor : ident := 137%positive.
Definition _RL_NewRelation : ident := 127%positive.
Definition _RL_NumRecords : ident := 180%positive.
Definition _RL_PrintCursor : ident := 187%positive.
Definition _RL_PrintTree : ident := 184%positive.
Definition _RL_PutRecord : ident := 148%positive.
Definition _Relation : ident := 39%positive.
Definition __IO_FILE : ident := 3%positive.
Definition __IO_backup_base : ident := 16%positive.
Definition __IO_buf_base : ident := 13%positive.
Definition __IO_buf_end : ident := 14%positive.
Definition __IO_marker : ident := 1%positive.
Definition __IO_read_base : ident := 9%positive.
Definition __IO_read_end : ident := 8%positive.
Definition __IO_read_ptr : ident := 7%positive.
Definition __IO_save_base : ident := 15%positive.
Definition __IO_save_end : ident := 17%positive.
Definition __IO_write_base : ident := 10%positive.
Definition __IO_write_end : ident := 12%positive.
Definition __IO_write_ptr : ident := 11%positive.
Definition ___assert_fail : ident := 109%positive.
Definition ___builtin_ais_annot : ident := 57%positive.
Definition ___builtin_annot : ident := 64%positive.
Definition ___builtin_annot_intval : ident := 65%positive.
Definition ___builtin_bswap : ident := 58%positive.
Definition ___builtin_bswap16 : ident := 60%positive.
Definition ___builtin_bswap32 : ident := 59%positive.
Definition ___builtin_bswap64 : ident := 90%positive.
Definition ___builtin_clz : ident := 91%positive.
Definition ___builtin_clzl : ident := 92%positive.
Definition ___builtin_clzll : ident := 93%positive.
Definition ___builtin_ctz : ident := 94%positive.
Definition ___builtin_ctzl : ident := 95%positive.
Definition ___builtin_ctzll : ident := 96%positive.
Definition ___builtin_debug : ident := 108%positive.
Definition ___builtin_fabs : ident := 61%positive.
Definition ___builtin_fmadd : ident := 99%positive.
Definition ___builtin_fmax : ident := 97%positive.
Definition ___builtin_fmin : ident := 98%positive.
Definition ___builtin_fmsub : ident := 100%positive.
Definition ___builtin_fnmadd : ident := 101%positive.
Definition ___builtin_fnmsub : ident := 102%positive.
Definition ___builtin_fsqrt : ident := 62%positive.
Definition ___builtin_membar : ident := 66%positive.
Definition ___builtin_memcpy_aligned : ident := 63%positive.
Definition ___builtin_nop : ident := 107%positive.
Definition ___builtin_read16_reversed : ident := 103%positive.
Definition ___builtin_read32_reversed : ident := 104%positive.
Definition ___builtin_va_arg : ident := 68%positive.
Definition ___builtin_va_copy : ident := 69%positive.
Definition ___builtin_va_end : ident := 70%positive.
Definition ___builtin_va_start : ident := 67%positive.
Definition ___builtin_write16_reversed : ident := 105%positive.
Definition ___builtin_write32_reversed : ident := 106%positive.
Definition ___compcert_i64_dtos : ident := 75%positive.
Definition ___compcert_i64_dtou : ident := 76%positive.
Definition ___compcert_i64_sar : ident := 87%positive.
Definition ___compcert_i64_sdiv : ident := 81%positive.
Definition ___compcert_i64_shl : ident := 85%positive.
Definition ___compcert_i64_shr : ident := 86%positive.
Definition ___compcert_i64_smod : ident := 83%positive.
Definition ___compcert_i64_smulh : ident := 88%positive.
Definition ___compcert_i64_stod : ident := 77%positive.
Definition ___compcert_i64_stof : ident := 79%positive.
Definition ___compcert_i64_udiv : ident := 82%positive.
Definition ___compcert_i64_umod : ident := 84%positive.
Definition ___compcert_i64_umulh : ident := 89%positive.
Definition ___compcert_i64_utod : ident := 78%positive.
Definition ___compcert_i64_utof : ident := 80%positive.
Definition ___compcert_va_composite : ident := 74%positive.
Definition ___compcert_va_float64 : ident := 73%positive.
Definition ___compcert_va_int32 : ident := 71%positive.
Definition ___compcert_va_int64 : ident := 72%positive.
Definition ___func__ : ident := 128%positive.
Definition ___func____1 : ident := 134%positive.
Definition ___func____10 : ident := 181%positive.
Definition ___func____11 : ident := 185%positive.
Definition ___func____12 : ident := 189%positive.
Definition ___func____13 : ident := 196%positive.
Definition ___func____14 : ident := 201%positive.
Definition ___func____15 : ident := 203%positive.
Definition ___func____16 : ident := 206%positive.
Definition ___func____17 : ident := 209%positive.
Definition ___func____2 : ident := 140%positive.
Definition ___func____3 : ident := 143%positive.
Definition ___func____4 : ident := 156%positive.
Definition ___func____5 : ident := 160%positive.
Definition ___func____6 : ident := 163%positive.
Definition ___func____7 : ident := 167%positive.
Definition ___func____8 : ident := 177%positive.
Definition ___func____9 : ident := 179%positive.
Definition ___pad1 : ident := 28%positive.
Definition ___pad2 : ident := 29%positive.
Definition ___pad3 : ident := 30%positive.
Definition ___pad4 : ident := 31%positive.
Definition ___pad5 : ident := 32%positive.
Definition ___stringlit_1 : ident := 130%positive.
Definition ___stringlit_10 : ident := 202%positive.
Definition ___stringlit_11 : ident := 204%positive.
Definition ___stringlit_12 : ident := 207%positive.
Definition ___stringlit_13 : ident := 208%positive.
Definition ___stringlit_14 : ident := 210%positive.
Definition ___stringlit_15 : ident := 211%positive.
Definition ___stringlit_16 : ident := 212%positive.
Definition ___stringlit_17 : ident := 213%positive.
Definition ___stringlit_18 : ident := 214%positive.
Definition ___stringlit_19 : ident := 215%positive.
Definition ___stringlit_2 : ident := 131%positive.
Definition ___stringlit_20 : ident := 216%positive.
Definition ___stringlit_21 : ident := 217%positive.
Definition ___stringlit_3 : ident := 141%positive.
Definition ___stringlit_4 : ident := 157%positive.
Definition ___stringlit_5 : ident := 161%positive.
Definition ___stringlit_6 : ident := 168%positive.
Definition ___stringlit_7 : ident := 182%positive.
Definition ___stringlit_8 : ident := 194%positive.
Definition ___stringlit_9 : ident := 200%positive.
Definition __chain : ident := 19%positive.
Definition __cur_column : ident := 23%positive.
Definition __fileno : ident := 20%positive.
Definition __flags : ident := 6%positive.
Definition __flags2 : ident := 21%positive.
Definition __lock : ident := 26%positive.
Definition __markers : ident := 18%positive.
Definition __mode : ident := 33%positive.
Definition __next : ident := 2%positive.
Definition __offset : ident := 27%positive.
Definition __old_offset : ident := 22%positive.
Definition __pos : ident := 5%positive.
Definition __sbuf : ident := 4%positive.
Definition __shortbuf : ident := 25%positive.
Definition __unused2 : ident := 34%positive.
Definition __vtable_offset : ident := 24%positive.
Definition _allEntries : ident := 191%positive.
Definition _ancestors : ident := 55%positive.
Definition _ancestorsIdx : ident := 54%positive.
Definition _btCursor : ident := 138%positive.
Definition _child : ident := 40%positive.
Definition _createNewNode : ident := 126%positive.
Definition _currNode : ident := 121%positive.
Definition _currNode__1 : ident := 197%positive.
Definition _cursor : ident := 119%positive.
Definition _depth : ident := 38%positive.
Definition _e : ident := 205%positive.
Definition _entries : ident := 51%positive.
Definition _entry : ident := 190%positive.
Definition _entryIndex : ident := 120%positive.
Definition _exit : ident := 115%positive.
Definition _findChildIndex : ident := 153%positive.
Definition _findRecordIndex : ident := 193%positive.
Definition _firstpointer : ident := 171%positive.
Definition _fprintf : ident := 111%positive.
Definition _free : ident := 113%positive.
Definition _freeRecord : ident := 129%positive.
Definition _goToKey : ident := 145%positive.
Definition _handleDeleteBtree : ident := 132%positive.
Definition _highest : ident := 152%positive.
Definition _i : ident := 135%positive.
Definition _i__1 : ident := 199%positive.
Definition _idx : ident := 150%positive.
Definition _isFirst : ident := 123%positive.
Definition _isLeaf : ident := 46%positive.
Definition _isNodeParent : ident := 154%positive.
Definition _isValid : ident := 122%positive.
Definition _key : ident := 43%positive.
Definition _lastpointer : ident := 170%positive.
Definition _level : ident := 53%positive.
Definition _lowest : ident := 151%positive.
Definition _main : ident := 218%positive.
Definition _malloc : ident := 114%positive.
Definition _moveToFirst : ident := 136%positive.
Definition _moveToKey : ident := 164%positive.
Definition _moveToLast : ident := 172%positive.
Definition _moveToNext : ident := 158%positive.
Definition _moveToPrev : ident := 173%positive.
Definition _n : ident := 116%positive.
Definition _newEntry : ident := 144%positive.
Definition _newNode : ident := 188%positive.
Definition _node : ident := 149%positive.
Definition _numKeys : ident := 49%positive.
Definition _numRecords : ident := 37%positive.
Definition _p : ident := 117%positive.
Definition _pNewRelation : ident := 125%positive.
Definition _pRootNode : ident := 124%positive.
Definition _printCursor : ident := 186%positive.
Definition _printTree : ident := 183%positive.
Definition _printf : ident := 112%positive.
Definition _ptr : ident := 44%positive.
Definition _ptr0 : ident := 50%positive.
Definition _putEntry : ident := 146%positive.
Definition _record : ident := 41%positive.
Definition _relation : ident := 52%positive.
Definition _root : ident := 36%positive.
Definition _splitnode : ident := 195%positive.
Definition _stderr : ident := 110%positive.
Definition _surely_malloc : ident := 118%positive.
Definition _tgtIdx : ident := 192%positive.
Definition _tgtIdx__1 : ident := 198%positive.
Definition _t'1 : ident := 219%positive.
Definition _t'10 : ident := 228%positive.
Definition _t'11 : ident := 229%positive.
Definition _t'12 : ident := 230%positive.
Definition _t'13 : ident := 231%positive.
Definition _t'14 : ident := 232%positive.
Definition _t'15 : ident := 233%positive.
Definition _t'16 : ident := 234%positive.
Definition _t'17 : ident := 235%positive.
Definition _t'18 : ident := 236%positive.
Definition _t'19 : ident := 237%positive.
Definition _t'2 : ident := 220%positive.
Definition _t'20 : ident := 238%positive.
Definition _t'21 : ident := 239%positive.
Definition _t'22 : ident := 240%positive.
Definition _t'23 : ident := 241%positive.
Definition _t'24 : ident := 242%positive.
Definition _t'25 : ident := 243%positive.
Definition _t'26 : ident := 244%positive.
Definition _t'27 : ident := 245%positive.
Definition _t'28 : ident := 246%positive.
Definition _t'29 : ident := 247%positive.
Definition _t'3 : ident := 221%positive.
Definition _t'30 : ident := 248%positive.
Definition _t'31 : ident := 249%positive.
Definition _t'32 : ident := 250%positive.
Definition _t'33 : ident := 251%positive.
Definition _t'34 : ident := 252%positive.
Definition _t'35 : ident := 253%positive.
Definition _t'36 : ident := 254%positive.
Definition _t'37 : ident := 255%positive.
Definition _t'38 : ident := 256%positive.
Definition _t'39 : ident := 257%positive.
Definition _t'4 : ident := 222%positive.
Definition _t'40 : ident := 258%positive.
Definition _t'41 : ident := 259%positive.
Definition _t'42 : ident := 260%positive.
Definition _t'43 : ident := 261%positive.
Definition _t'44 : ident := 262%positive.
Definition _t'45 : ident := 263%positive.
Definition _t'46 : ident := 264%positive.
Definition _t'47 : ident := 265%positive.
Definition _t'48 : ident := 266%positive.
Definition _t'49 : ident := 267%positive.
Definition _t'5 : ident := 223%positive.
Definition _t'50 : ident := 268%positive.
Definition _t'51 : ident := 269%positive.
Definition _t'52 : ident := 270%positive.
Definition _t'53 : ident := 271%positive.
Definition _t'54 : ident := 272%positive.
Definition _t'55 : ident := 273%positive.
Definition _t'56 : ident := 274%positive.
Definition _t'57 : ident := 275%positive.
Definition _t'58 : ident := 276%positive.
Definition _t'59 : ident := 277%positive.
Definition _t'6 : ident := 224%positive.
Definition _t'60 : ident := 278%positive.
Definition _t'61 : ident := 279%positive.
Definition _t'62 : ident := 280%positive.
Definition _t'63 : ident := 281%positive.
Definition _t'64 : ident := 282%positive.
Definition _t'65 : ident := 283%positive.
Definition _t'66 : ident := 284%positive.
Definition _t'67 : ident := 285%positive.
Definition _t'68 : ident := 286%positive.
Definition _t'69 : ident := 287%positive.
Definition _t'7 : ident := 225%positive.
Definition _t'70 : ident := 288%positive.
Definition _t'8 : ident := 226%positive.
Definition _t'9 : ident := 227%positive.

Definition v___stringlit_12 := {|
  gvar_info := (tarray tschar 20);
  gvar_init := (Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 33) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 42) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_13 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 24);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 86) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 22);
  gvar_init := (Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 33) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 42) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_14 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_17 := {|
  gvar_info := (tarray tschar 5);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_9 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_11 := {|
  gvar_info := (tarray tschar 19);
  gvar_init := (Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 75) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_20 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_15 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_16 := {|
  gvar_info := (tarray tschar 17);
  gvar_init := (Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 22);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 86) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_18 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 24);
  gvar_init := (Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 33) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 42) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_10 := {|
  gvar_info := (tarray tschar 18);
  gvar_init := (Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 75) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_21 := {|
  gvar_info := (tarray tschar 4);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 15);
  gvar_init := (Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_7 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 33) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 42) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_8 := {|
  gvar_info := (tarray tschar 8);
  gvar_init := (Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_19 := {|
  gvar_info := (tarray tschar 19);
  gvar_init := (Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_stderr := {|
  gvar_info := (tptr (Tstruct __IO_FILE noattr));
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_surely_malloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Etempvar _n tulong) :: nil))
    (Sset _p (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr tvoid)) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Sreturn (Some (Etempvar _p (tptr tvoid))))))
|}.

Definition f_entryIndex := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
        (Tstruct _Cursor noattr)) _level tint))
  (Ssequence
    (Sset _t'2
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
              (Tstruct _Cursor noattr)) _ancestorsIdx (tarray tint 20))
          (Etempvar _t'1 tint) (tptr tint)) tint))
    (Sreturn (Some (Etempvar _t'2 tint)))))
|}.

Definition f_currNode := {|
  fn_return := (tptr (Tstruct _BtNode noattr));
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _BtNode noattr))) :: (_t'1, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
        (Tstruct _Cursor noattr)) _level tint))
  (Ssequence
    (Sset _t'2
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
              (Tstruct _Cursor noattr)) _ancestors
            (tarray (tptr (Tstruct _BtNode noattr)) 20)) (Etempvar _t'1 tint)
          (tptr (tptr (Tstruct _BtNode noattr))))
        (tptr (Tstruct _BtNode noattr))))
    (Sreturn (Some (Etempvar _t'2 (tptr (Tstruct _BtNode noattr)))))))
|}.

Definition f_isValid := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, (tptr (Tstruct _BtNode noattr))) :: (_t'3, tint) ::
               (_t'2, (tptr (Tstruct _BtNode noattr))) :: (_t'1, tint) ::
               (_t'6, tint) :: (_t'5, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _entryIndex (Tfunction
                            (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tint
                            cc_default))
        ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
      (Scall (Some _t'2)
        (Evar _currNode (Tfunction
                          (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                          (tptr (Tstruct _BtNode noattr)) cc_default))
        ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil)))
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _t'2 (tptr (Tstruct _BtNode noattr)))
            (Tstruct _BtNode noattr)) _numKeys tint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint) (Etempvar _t'5 tint)
                     tint)
        (Ssequence
          (Scall (Some _t'4)
            (Evar _currNode (Tfunction
                              (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                              (tptr (Tstruct _BtNode noattr)) cc_default))
            ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _t'4 (tptr (Tstruct _BtNode noattr)))
                  (Tstruct _BtNode noattr)) _Last tint))
            (Sset _t'3
              (Ecast
                (Ebinop Oeq (Etempvar _t'6 tint)
                  (Econst_int (Int.repr 1) tint) tint) tbool))))
        (Sset _t'3 (Econst_int (Int.repr 0) tint)))))
  (Sifthenelse (Etempvar _t'3 tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
|}.

Definition f_isFirst := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, (tptr (Tstruct _BtNode noattr))) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'4, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _entryIndex (Tfunction
                          (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tint
                          cc_default))
      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Scall (Some _t'3)
          (Evar _currNode (Tfunction
                            (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                            (tptr (Tstruct _BtNode noattr)) cc_default))
          ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _t'3 (tptr (Tstruct _BtNode noattr)))
                (Tstruct _BtNode noattr)) _First tint))
          (Sset _t'2
            (Ecast
              (Ebinop Oeq (Etempvar _t'4 tint) (Econst_int (Int.repr 1) tint)
                tint) tbool))))
      (Sset _t'2 (Econst_int (Int.repr 0) tint))))
  (Sifthenelse (Etempvar _t'2 tint)
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_RL_NewRelation := {|
  fn_return := (tptr (Tstruct _Relation noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_pRootNode, (tptr (Tstruct _BtNode noattr))) ::
               (_pNewRelation, (tptr (Tstruct _Relation noattr))) ::
               (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr (Tstruct _BtNode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _createNewNode (Tfunction
                             (Tcons tint (Tcons tint (Tcons tint Tnil)))
                             (tptr (Tstruct _BtNode noattr)) cc_default))
      ((Econst_int (Int.repr 1) tint) :: (Econst_int (Int.repr 1) tint) ::
       (Econst_int (Int.repr 1) tint) :: nil))
    (Sset _pRootNode (Etempvar _t'1 (tptr (Tstruct _BtNode noattr)))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _pRootNode (tptr (Tstruct _BtNode noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                                 cc_default))
          ((Esizeof (Tstruct _Relation noattr) tulong) :: nil))
        (Sset _pNewRelation
          (Ecast (Etempvar _t'2 (tptr tvoid))
            (tptr (Tstruct _Relation noattr)))))
      (Ssequence
        (Sifthenelse (Ebinop Oeq
                       (Etempvar _pNewRelation (tptr (Tstruct _Relation noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Ssequence
            (Scall None
              (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default))
              ((Etempvar _pRootNode (tptr (Tstruct _BtNode noattr))) :: nil))
            (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)))))
          Sskip)
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Etempvar _pNewRelation (tptr (Tstruct _Relation noattr)))
                (Tstruct _Relation noattr)) _root
              (tptr (Tstruct _BtNode noattr)))
            (Etempvar _pRootNode (tptr (Tstruct _BtNode noattr))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _pNewRelation (tptr (Tstruct _Relation noattr)))
                  (Tstruct _Relation noattr)) _numRecords tulong)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _pNewRelation (tptr (Tstruct _Relation noattr)))
                    (Tstruct _Relation noattr)) _depth tint)
                (Econst_int (Int.repr 0) tint))
              (Sreturn (Some (Etempvar _pNewRelation (tptr (Tstruct _Relation noattr))))))))))))
|}.

Definition v___func__ := {|
  gvar_info := (tarray tschar 18);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 68) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_RL_DeleteRelation := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_relation, (tptr (Tstruct _Relation noattr))) ::
                (_freeRecord,
                 (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _BtNode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One
                 (Etempvar _relation (tptr (Tstruct _Relation noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_2 (tarray tschar 24)) ::
       (Evar ___stringlit_1 (tarray tschar 15)) ::
       (Econst_int (Int.repr 202) tint) ::
       (Evar ___func__ (tarray tschar 18)) :: nil)))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _relation (tptr (Tstruct _Relation noattr)))
          (Tstruct _Relation noattr)) _root (tptr (Tstruct _BtNode noattr))))
    (Scall None
      (Evar _handleDeleteBtree (Tfunction
                                 (Tcons (tptr (Tstruct _BtNode noattr))
                                   (Tcons
                                     (tptr (Tfunction
                                             (Tcons (tptr tvoid) Tnil) tvoid
                                             cc_default)) Tnil)) tvoid
                                 cc_default))
      ((Etempvar _t'1 (tptr (Tstruct _BtNode noattr))) ::
       (Etempvar _freeRecord (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                     cc_default))) :: nil))))
|}.

Definition v___func____1 := {|
  gvar_info := (tarray tschar 13);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_RL_NewCursor := {|
  fn_return := (tptr (Tstruct _Cursor noattr));
  fn_callconv := cc_default;
  fn_params := ((_relation, (tptr (Tstruct _Relation noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: (_i, tulong) ::
               (_t'1, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _BtNode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One
                 (Etempvar _relation (tptr (Tstruct _Relation noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_2 (tarray tschar 24)) ::
       (Evar ___stringlit_1 (tarray tschar 15)) ::
       (Econst_int (Int.repr 210) tint) ::
       (Evar ___func____1 (tarray tschar 13)) :: nil)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                               cc_default))
        ((Esizeof (Tstruct _Cursor noattr) tulong) :: nil))
      (Sset _cursor
        (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _Cursor noattr)))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
        Sskip)
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
              (Tstruct _Cursor noattr)) _relation
            (tptr (Tstruct _Relation noattr)))
          (Etempvar _relation (tptr (Tstruct _Relation noattr))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                (Tstruct _Cursor noattr)) _level tint)
            (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef
                    (Etempvar _relation (tptr (Tstruct _Relation noattr)))
                    (Tstruct _Relation noattr)) _root
                  (tptr (Tstruct _BtNode noattr))))
              (Scall None
                (Evar _moveToFirst (Tfunction
                                     (Tcons (tptr (Tstruct _BtNode noattr))
                                       (Tcons (tptr (Tstruct _Cursor noattr))
                                         (Tcons tint Tnil))) tvoid
                                     cc_default))
                ((Etempvar _t'2 (tptr (Tstruct _BtNode noattr))) ::
                 (Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                 (Econst_int (Int.repr 0) tint) :: nil)))
            (Sreturn (Some (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))))))))))
|}.

Definition f_RL_FreeCursor := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_btCursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
  ((Etempvar _btCursor (tptr (Tstruct _Cursor noattr))) :: nil))
|}.

Definition v___func____2 := {|
  gvar_info := (tarray tschar 17);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 86) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_RL_CursorIsValid := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_3 (tarray tschar 22)) ::
       (Evar ___stringlit_1 (tarray tschar 15)) ::
       (Econst_int (Int.repr 229) tint) ::
       (Evar ___func____2 (tarray tschar 17)) :: nil)))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _isValid (Tfunction (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                       tint cc_default))
      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition v___func____3 := {|
  gvar_info := (tarray tschar 13);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_RL_PutRecord := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) ::
                (_key, tulong) :: (_record, (tptr tvoid)) :: nil);
  fn_vars := ((_newEntry, (Tstruct _Entry noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_3 (tarray tschar 22)) ::
       (Evar ___stringlit_1 (tarray tschar 15)) ::
       (Econst_int (Int.repr 235) tint) ::
       (Evar ___func____3 (tarray tschar 13)) :: nil)))
  (Ssequence
    (Sassign
      (Efield
        (Efield (Evar _newEntry (Tstruct _Entry noattr)) _ptr
          (Tunion _Child_or_Record noattr)) _record (tptr tvoid))
      (Etempvar _record (tptr tvoid)))
    (Ssequence
      (Sassign (Efield (Evar _newEntry (Tstruct _Entry noattr)) _key tulong)
        (Etempvar _key tulong))
      (Ssequence
        (Scall None
          (Evar _goToKey (Tfunction
                           (Tcons (tptr (Tstruct _Cursor noattr))
                             (Tcons tulong Tnil)) tvoid cc_default))
          ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
           (Etempvar _key tulong) :: nil))
        (Ssequence
          (Scall None
            (Evar _putEntry (Tfunction
                              (Tcons (tptr (Tstruct _Cursor noattr))
                                (Tcons (tptr (Tstruct _Entry noattr))
                                  (Tcons tulong Tnil))) tvoid cc_default))
            ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
             (Eaddrof (Evar _newEntry (Tstruct _Entry noattr))
               (tptr (Tstruct _Entry noattr))) :: (Etempvar _key tulong) ::
             nil))
          (Ssequence
            (Scall None
              (Evar _RL_MoveToNext (Tfunction
                                     (Tcons (tptr (Tstruct _Cursor noattr))
                                       Tnil) tvoid cc_default))
              ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
            (Sreturn None)))))))
|}.

Definition f_isNodeParent := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_node, (tptr (Tstruct _BtNode noattr))) :: (_key, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_idx, tint) :: (_lowest, tulong) :: (_highest, tulong) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'10, tint) :: (_t'9, tint) ::
               (_t'8, tint) :: (_t'7, tint) :: (_t'6, tint) ::
               (_t'5, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'5
    (Efield
      (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
        (Tstruct _BtNode noattr)) _isLeaf tint))
  (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tint)
                 (Econst_int (Int.repr 1) tint) tint)
    (Ssequence
      (Ssequence
        (Sset _t'10
          (Efield
            (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
              (Tstruct _BtNode noattr)) _numKeys tint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'10 tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sreturn (Some (Econst_int (Int.repr 1) tint)))
          Sskip))
      (Ssequence
        (Sset _lowest
          (Efield
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                    (Tstruct _BtNode noattr)) _entries
                  (tarray (Tstruct _Entry noattr) 15))
                (Econst_int (Int.repr 0) tint)
                (tptr (Tstruct _Entry noattr))) (Tstruct _Entry noattr)) _key
            tulong))
        (Ssequence
          (Ssequence
            (Sset _t'9
              (Efield
                (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                  (Tstruct _BtNode noattr)) _numKeys tint))
            (Sset _highest
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                        (Tstruct _BtNode noattr)) _entries
                      (tarray (Tstruct _Entry noattr) 15))
                    (Ebinop Osub (Etempvar _t'9 tint)
                      (Econst_int (Int.repr 1) tint) tint)
                    (tptr (Tstruct _Entry noattr))) (Tstruct _Entry noattr))
                _key tulong)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sifthenelse (Ebinop Oge (Etempvar _key tulong)
                               (Etempvar _lowest tulong) tint)
                  (Sset _t'1 (Econst_int (Int.repr 1) tint))
                  (Ssequence
                    (Sset _t'8
                      (Efield
                        (Ederef
                          (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                          (Tstruct _BtNode noattr)) _First tint))
                    (Sset _t'1
                      (Ecast
                        (Ebinop Oeq (Etempvar _t'8 tint)
                          (Econst_int (Int.repr 1) tint) tint) tbool))))
                (Sifthenelse (Etempvar _t'1 tint)
                  (Sifthenelse (Ebinop Ole (Etempvar _key tulong)
                                 (Etempvar _highest tulong) tint)
                    (Sset _t'2 (Ecast (Econst_int (Int.repr 1) tint) tbool))
                    (Ssequence
                      (Ssequence
                        (Sset _t'7
                          (Efield
                            (Ederef
                              (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                              (Tstruct _BtNode noattr)) _Last tint))
                        (Sset _t'2
                          (Ecast
                            (Ebinop Oeq (Etempvar _t'7 tint)
                              (Econst_int (Int.repr 1) tint) tint) tbool)))
                      (Sset _t'2 (Ecast (Etempvar _t'2 tint) tbool))))
                  (Sset _t'2 (Econst_int (Int.repr 0) tint))))
              (Sifthenelse (Etempvar _t'2 tint)
                (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                Sskip))
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _findChildIndex (Tfunction
                                  (Tcons (tptr (Tstruct _BtNode noattr))
                                    (Tcons tulong Tnil)) tint cc_default))
          ((Etempvar _node (tptr (Tstruct _BtNode noattr))) ::
           (Etempvar _key tulong) :: nil))
        (Sset _idx (Etempvar _t'3 tint)))
      (Ssequence
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _idx tint)
                         (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                         tint)
            (Sset _t'4 (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                    (Tstruct _BtNode noattr)) _numKeys tint))
              (Sset _t'4
                (Ecast
                  (Ebinop Oeq (Etempvar _idx tint)
                    (Ebinop Osub (Etempvar _t'6 tint)
                      (Econst_int (Int.repr 1) tint) tint) tint) tbool))))
          (Sifthenelse (Etempvar _t'4 tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip))
        (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))
|}.

Definition f_AscendToParent := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) ::
                (_key, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, (tptr (Tstruct _BtNode noattr))) ::
               (_t'4, tint) :: (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'4
      (Efield
        (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
          (Tstruct _Cursor noattr)) _level tint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sreturn None)
      Sskip))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _currNode (Tfunction
                          (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                          (tptr (Tstruct _BtNode noattr)) cc_default))
        ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
      (Scall (Some _t'2)
        (Evar _isNodeParent (Tfunction
                              (Tcons (tptr (Tstruct _BtNode noattr))
                                (Tcons tulong Tnil)) tint cc_default))
        ((Etempvar _t'1 (tptr (Tstruct _BtNode noattr))) ::
         (Etempvar _key tulong) :: nil)))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                   (Econst_int (Int.repr 1) tint) tint)
      (Sreturn None)
      (Ssequence
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                (Tstruct _Cursor noattr)) _level tint))
          (Sassign
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                (Tstruct _Cursor noattr)) _level tint)
            (Ebinop Osub (Etempvar _t'3 tint) (Econst_int (Int.repr 1) tint)
              tint)))
        (Scall None
          (Evar _AscendToParent (Tfunction
                                  (Tcons (tptr (Tstruct _Cursor noattr))
                                    (Tcons tulong Tnil)) tvoid cc_default))
          ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
           (Etempvar _key tulong) :: nil))))))
|}.

Definition v___func____4 := {|
  gvar_info := (tarray tschar 13);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_RL_GetRecord := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tint) :: (_t'4, (tptr (Tstruct _BtNode noattr))) ::
               (_t'3, (tptr (Tstruct _BtNode noattr))) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'7, tint) :: (_t'6, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _isValid (Tfunction (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                       tint cc_default))
      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                   (Econst_int (Int.repr 1) tint) tint)
      Sskip
      (Scall None
        (Evar ___assert_fail (Tfunction
                               (Tcons (tptr tschar)
                                 (Tcons (tptr tschar)
                                   (Tcons tuint (Tcons (tptr tschar) Tnil))))
                               tvoid cc_default))
        ((Evar ___stringlit_4 (tarray tschar 24)) ::
         (Evar ___stringlit_1 (tarray tschar 15)) ::
         (Econst_int (Int.repr 295) tint) ::
         (Evar ___func____4 (tarray tschar 13)) :: nil))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _entryIndex (Tfunction
                              (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                              tint cc_default))
          ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
        (Scall (Some _t'3)
          (Evar _currNode (Tfunction
                            (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                            (tptr (Tstruct _BtNode noattr)) cc_default))
          ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil)))
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _t'3 (tptr (Tstruct _BtNode noattr)))
              (Tstruct _BtNode noattr)) _numKeys tint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint) (Etempvar _t'7 tint)
                       tint)
          (Scall None
            (Evar _moveToNext (Tfunction
                                (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                                tvoid cc_default))
            ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
          Sskip)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'4)
          (Evar _currNode (Tfunction
                            (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                            (tptr (Tstruct _BtNode noattr)) cc_default))
          ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
        (Scall (Some _t'5)
          (Evar _entryIndex (Tfunction
                              (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                              tint cc_default))
          ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil)))
      (Ssequence
        (Sset _t'6
          (Efield
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _t'4 (tptr (Tstruct _BtNode noattr)))
                      (Tstruct _BtNode noattr)) _entries
                    (tarray (Tstruct _Entry noattr) 15)) (Etempvar _t'5 tint)
                  (tptr (Tstruct _Entry noattr))) (Tstruct _Entry noattr))
              _ptr (Tunion _Child_or_Record noattr)) _record (tptr tvoid)))
        (Sreturn (Some (Etempvar _t'6 (tptr tvoid))))))))
|}.

Definition v___func____5 := {|
  gvar_info := (tarray tschar 10);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_RL_GetKey := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tint) :: (_t'4, (tptr (Tstruct _BtNode noattr))) ::
               (_t'3, (tptr (Tstruct _BtNode noattr))) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'7, tint) :: (_t'6, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _isValid (Tfunction (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                       tint cc_default))
      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                   (Econst_int (Int.repr 1) tint) tint)
      Sskip
      (Scall None
        (Evar ___assert_fail (Tfunction
                               (Tcons (tptr tschar)
                                 (Tcons (tptr tschar)
                                   (Tcons tuint (Tcons (tptr tschar) Tnil))))
                               tvoid cc_default))
        ((Evar ___stringlit_5 (tarray tschar 22)) ::
         (Evar ___stringlit_1 (tarray tschar 15)) ::
         (Econst_int (Int.repr 306) tint) ::
         (Evar ___func____5 (tarray tschar 10)) :: nil))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _entryIndex (Tfunction
                              (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                              tint cc_default))
          ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
        (Scall (Some _t'3)
          (Evar _currNode (Tfunction
                            (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                            (tptr (Tstruct _BtNode noattr)) cc_default))
          ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil)))
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _t'3 (tptr (Tstruct _BtNode noattr)))
              (Tstruct _BtNode noattr)) _numKeys tint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint) (Etempvar _t'7 tint)
                       tint)
          (Scall None
            (Evar _moveToNext (Tfunction
                                (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                                tvoid cc_default))
            ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
          Sskip)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'4)
          (Evar _currNode (Tfunction
                            (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                            (tptr (Tstruct _BtNode noattr)) cc_default))
          ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
        (Scall (Some _t'5)
          (Evar _entryIndex (Tfunction
                              (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                              tint cc_default))
          ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil)))
      (Ssequence
        (Sset _t'6
          (Efield
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _t'4 (tptr (Tstruct _BtNode noattr)))
                    (Tstruct _BtNode noattr)) _entries
                  (tarray (Tstruct _Entry noattr) 15)) (Etempvar _t'5 tint)
                (tptr (Tstruct _Entry noattr))) (Tstruct _Entry noattr)) _key
            tulong))
        (Sreturn (Some (Etempvar _t'6 tulong)))))))
|}.

Definition v___func____6 := {|
  gvar_info := (tarray tschar 8);
  gvar_init := (Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_goToKey := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) ::
                (_key, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _BtNode noattr))) :: (_t'2, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_3 (tarray tschar 22)) ::
       (Evar ___stringlit_1 (tarray tschar 15)) ::
       (Econst_int (Int.repr 317) tint) ::
       (Evar ___func____6 (tarray tschar 8)) :: nil)))
  (Ssequence
    (Scall None
      (Evar _AscendToParent (Tfunction
                              (Tcons (tptr (Tstruct _Cursor noattr))
                                (Tcons tulong Tnil)) tvoid cc_default))
      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
       (Etempvar _key tulong) :: nil))
    (Ssequence
      (Scall (Some _t'1)
        (Evar _currNode (Tfunction
                          (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                          (tptr (Tstruct _BtNode noattr)) cc_default))
        ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
              (Tstruct _Cursor noattr)) _level tint))
        (Scall None
          (Evar _moveToKey (Tfunction
                             (Tcons (tptr (Tstruct _BtNode noattr))
                               (Tcons tulong
                                 (Tcons (tptr (Tstruct _Cursor noattr))
                                   (Tcons tint Tnil)))) tvoid cc_default))
          ((Etempvar _t'1 (tptr (Tstruct _BtNode noattr))) ::
           (Etempvar _key tulong) ::
           (Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
           (Etempvar _t'2 tint) :: nil))))))
|}.

Definition f_RL_MoveToKey := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) ::
                (_key, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tulong) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _goToKey (Tfunction
                     (Tcons (tptr (Tstruct _Cursor noattr))
                       (Tcons tulong Tnil)) tvoid cc_default))
    ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
     (Etempvar _key tulong) :: nil))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _isValid (Tfunction
                         (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tint
                         cc_default))
        ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip))
    (Ssequence
      (Scall (Some _t'2)
        (Evar _RL_GetKey (Tfunction
                           (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                           tulong cc_default))
        ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tulong) (Etempvar _key tulong)
                     tint)
        (Sreturn (Some (Econst_int (Int.repr 1) tint)))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_RL_DeleteRecord := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) ::
                (_key, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 0) tint)))
|}.

Definition v___func____7 := {|
  gvar_info := (tarray tschar 15);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_RL_MoveToFirst := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'3, (tptr (Tstruct _BtNode noattr))) ::
               (_t'2, (tptr (Tstruct _Relation noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_6 (tarray tschar 7)) ::
       (Evar ___stringlit_1 (tarray tschar 15)) ::
       (Econst_int (Int.repr 357) tint) ::
       (Evar ___func____7 (tarray tschar 15)) :: nil)))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
          (Tstruct _Cursor noattr)) _level tint)
      (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
              (Tstruct _Cursor noattr)) _relation
            (tptr (Tstruct _Relation noattr))))
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _t'2 (tptr (Tstruct _Relation noattr)))
                (Tstruct _Relation noattr)) _root
              (tptr (Tstruct _BtNode noattr))))
          (Scall None
            (Evar _moveToFirst (Tfunction
                                 (Tcons (tptr (Tstruct _BtNode noattr))
                                   (Tcons (tptr (Tstruct _Cursor noattr))
                                     (Tcons tint Tnil))) tvoid cc_default))
            ((Etempvar _t'3 (tptr (Tstruct _BtNode noattr))) ::
             (Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
             (Econst_int (Int.repr 0) tint) :: nil))))
      (Ssequence
        (Scall (Some _t'1)
          (Evar _isValid (Tfunction
                           (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tint
                           cc_default))
          ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
        (Sreturn (Some (Etempvar _t'1 tint)))))))
|}.

Definition f_lastpointer := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_node, (tptr (Tstruct _BtNode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
        (Tstruct _BtNode noattr)) _isLeaf tint))
  (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                 (Econst_int (Int.repr 1) tint) tint)
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
            (Tstruct _BtNode noattr)) _numKeys tint))
      (Sreturn (Some (Etempvar _t'3 tint))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
            (Tstruct _BtNode noattr)) _numKeys tint))
      (Sreturn (Some (Ebinop Osub (Etempvar _t'2 tint)
                       (Econst_int (Int.repr 1) tint) tint))))))
|}.

Definition f_firstpointer := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_node, (tptr (Tstruct _BtNode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
        (Tstruct _BtNode noattr)) _isLeaf tint))
  (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                 (Econst_int (Int.repr 1) tint) tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))))
|}.

Definition f_moveToNext := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'8, tint) :: (_t'7, (tptr (Tstruct _BtNode noattr))) ::
               (_t'6, (tptr (Tstruct _BtNode noattr))) :: (_t'5, tint) ::
               (_t'4, (tptr (Tstruct _BtNode noattr))) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: (_t'16, tint) ::
               (_t'15, tint) :: (_t'14, tint) :: (_t'13, tint) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, (tptr (Tstruct _BtNode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _isValid (Tfunction (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                       tint cc_default))
      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sreturn None)
      Sskip))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'16
              (Efield
                (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                  (Tstruct _Cursor noattr)) _level tint))
            (Sifthenelse (Ebinop Ogt (Etempvar _t'16 tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _entryIndex (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _Cursor noattr))
                                            Tnil) tint cc_default))
                      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                       nil))
                    (Scall (Some _t'4)
                      (Evar _currNode (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _Cursor noattr))
                                          Tnil)
                                        (tptr (Tstruct _BtNode noattr))
                                        cc_default))
                      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                       nil)))
                  (Scall (Some _t'5)
                    (Evar _lastpointer (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _BtNode noattr))
                                           Tnil) tint cc_default))
                    ((Etempvar _t'4 (tptr (Tstruct _BtNode noattr))) :: nil)))
                (Sset _t'2
                  (Ecast
                    (Ebinop Oeq (Etempvar _t'3 tint) (Etempvar _t'5 tint)
                      tint) tbool)))
              (Sset _t'2 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _t'2 tint) Sskip Sbreak))
        (Ssequence
          (Sset _t'15
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                (Tstruct _Cursor noattr)) _level tint))
          (Sassign
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                (Tstruct _Cursor noattr)) _level tint)
            (Ebinop Osub (Etempvar _t'15 tint) (Econst_int (Int.repr 1) tint)
              tint))))
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _t'12
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
              (Tstruct _Cursor noattr)) _level tint))
        (Ssequence
          (Sset _t'13
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                (Tstruct _Cursor noattr)) _level tint))
          (Ssequence
            (Sset _t'14
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                      (Tstruct _Cursor noattr)) _ancestorsIdx
                    (tarray tint 20)) (Etempvar _t'13 tint) (tptr tint))
                tint))
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                      (Tstruct _Cursor noattr)) _ancestorsIdx
                    (tarray tint 20)) (Etempvar _t'12 tint) (tptr tint))
                tint)
              (Ebinop Oadd (Etempvar _t'14 tint)
                (Econst_int (Int.repr 1) tint) tint)))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'6)
            (Evar _currNode (Tfunction
                              (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                              (tptr (Tstruct _BtNode noattr)) cc_default))
            ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
          (Ssequence
            (Sset _t'11
              (Efield
                (Ederef (Etempvar _t'6 (tptr (Tstruct _BtNode noattr)))
                  (Tstruct _BtNode noattr)) _isLeaf tint))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'11 tint)
                           (Econst_int (Int.repr 1) tint) tint)
              (Sreturn None)
              Sskip)))
        (Ssequence
          (Ssequence
            (Ssequence
              (Scall (Some _t'7)
                (Evar _currNode (Tfunction
                                  (Tcons (tptr (Tstruct _Cursor noattr))
                                    Tnil) (tptr (Tstruct _BtNode noattr))
                                  cc_default))
                ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
              (Scall (Some _t'8)
                (Evar _entryIndex (Tfunction
                                    (Tcons (tptr (Tstruct _Cursor noattr))
                                      Tnil) tint cc_default))
                ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil)))
            (Ssequence
              (Sset _t'9
                (Efield
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _t'7 (tptr (Tstruct _BtNode noattr)))
                            (Tstruct _BtNode noattr)) _entries
                          (tarray (Tstruct _Entry noattr) 15))
                        (Etempvar _t'8 tint) (tptr (Tstruct _Entry noattr)))
                      (Tstruct _Entry noattr)) _ptr
                    (Tunion _Child_or_Record noattr)) _child
                  (tptr (Tstruct _BtNode noattr))))
              (Ssequence
                (Sset _t'10
                  (Efield
                    (Ederef
                      (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                      (Tstruct _Cursor noattr)) _level tint))
                (Scall None
                  (Evar _moveToFirst (Tfunction
                                       (Tcons (tptr (Tstruct _BtNode noattr))
                                         (Tcons
                                           (tptr (Tstruct _Cursor noattr))
                                           (Tcons tint Tnil))) tvoid
                                       cc_default))
                  ((Etempvar _t'9 (tptr (Tstruct _BtNode noattr))) ::
                   (Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                   (Ebinop Oadd (Etempvar _t'10 tint)
                     (Econst_int (Int.repr 1) tint) tint) :: nil)))))
          (Sreturn None))))))
|}.

Definition f_moveToPrev := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'8, tint) :: (_t'7, (tptr (Tstruct _BtNode noattr))) ::
               (_t'6, (tptr (Tstruct _BtNode noattr))) :: (_t'5, tint) ::
               (_t'4, (tptr (Tstruct _BtNode noattr))) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: (_t'16, tint) ::
               (_t'15, tint) :: (_t'14, tint) :: (_t'13, tint) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, (tptr (Tstruct _BtNode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _isFirst (Tfunction (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                       tint cc_default))
      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                   (Econst_int (Int.repr 1) tint) tint)
      (Sreturn None)
      Sskip))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'16
              (Efield
                (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                  (Tstruct _Cursor noattr)) _level tint))
            (Sifthenelse (Ebinop Ogt (Etempvar _t'16 tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _entryIndex (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _Cursor noattr))
                                            Tnil) tint cc_default))
                      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                       nil))
                    (Scall (Some _t'4)
                      (Evar _currNode (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _Cursor noattr))
                                          Tnil)
                                        (tptr (Tstruct _BtNode noattr))
                                        cc_default))
                      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                       nil)))
                  (Scall (Some _t'5)
                    (Evar _firstpointer (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _BtNode noattr))
                                            Tnil) tint cc_default))
                    ((Etempvar _t'4 (tptr (Tstruct _BtNode noattr))) :: nil)))
                (Sset _t'2
                  (Ecast
                    (Ebinop Oeq (Etempvar _t'3 tint) (Etempvar _t'5 tint)
                      tint) tbool)))
              (Sset _t'2 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _t'2 tint) Sskip Sbreak))
        (Ssequence
          (Sset _t'15
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                (Tstruct _Cursor noattr)) _level tint))
          (Sassign
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                (Tstruct _Cursor noattr)) _level tint)
            (Ebinop Osub (Etempvar _t'15 tint) (Econst_int (Int.repr 1) tint)
              tint))))
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _t'12
          (Efield
            (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
              (Tstruct _Cursor noattr)) _level tint))
        (Ssequence
          (Sset _t'13
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                (Tstruct _Cursor noattr)) _level tint))
          (Ssequence
            (Sset _t'14
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                      (Tstruct _Cursor noattr)) _ancestorsIdx
                    (tarray tint 20)) (Etempvar _t'13 tint) (tptr tint))
                tint))
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                      (Tstruct _Cursor noattr)) _ancestorsIdx
                    (tarray tint 20)) (Etempvar _t'12 tint) (tptr tint))
                tint)
              (Ebinop Osub (Etempvar _t'14 tint)
                (Econst_int (Int.repr 1) tint) tint)))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'6)
            (Evar _currNode (Tfunction
                              (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                              (tptr (Tstruct _BtNode noattr)) cc_default))
            ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
          (Ssequence
            (Sset _t'11
              (Efield
                (Ederef (Etempvar _t'6 (tptr (Tstruct _BtNode noattr)))
                  (Tstruct _BtNode noattr)) _isLeaf tint))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'11 tint)
                           (Econst_int (Int.repr 1) tint) tint)
              (Sreturn None)
              Sskip)))
        (Ssequence
          (Ssequence
            (Ssequence
              (Scall (Some _t'7)
                (Evar _currNode (Tfunction
                                  (Tcons (tptr (Tstruct _Cursor noattr))
                                    Tnil) (tptr (Tstruct _BtNode noattr))
                                  cc_default))
                ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
              (Scall (Some _t'8)
                (Evar _entryIndex (Tfunction
                                    (Tcons (tptr (Tstruct _Cursor noattr))
                                      Tnil) tint cc_default))
                ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil)))
            (Ssequence
              (Sset _t'9
                (Efield
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _t'7 (tptr (Tstruct _BtNode noattr)))
                            (Tstruct _BtNode noattr)) _entries
                          (tarray (Tstruct _Entry noattr) 15))
                        (Etempvar _t'8 tint) (tptr (Tstruct _Entry noattr)))
                      (Tstruct _Entry noattr)) _ptr
                    (Tunion _Child_or_Record noattr)) _child
                  (tptr (Tstruct _BtNode noattr))))
              (Ssequence
                (Sset _t'10
                  (Efield
                    (Ederef
                      (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                      (Tstruct _Cursor noattr)) _level tint))
                (Scall None
                  (Evar _moveToLast (Tfunction
                                      (Tcons (tptr (Tstruct _BtNode noattr))
                                        (Tcons
                                          (tptr (Tstruct _Cursor noattr))
                                          (Tcons tint Tnil))) tvoid
                                      cc_default))
                  ((Etempvar _t'9 (tptr (Tstruct _BtNode noattr))) ::
                   (Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                   (Ebinop Oadd (Etempvar _t'10 tint)
                     (Econst_int (Int.repr 1) tint) tint) :: nil)))))
          (Sreturn None))))))
|}.

Definition f_RL_MoveToNext := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _BtNode noattr))) :: (_t'1, tint) ::
               (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _entryIndex (Tfunction
                            (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tint
                            cc_default))
        ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
      (Scall (Some _t'2)
        (Evar _currNode (Tfunction
                          (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                          (tptr (Tstruct _BtNode noattr)) cc_default))
        ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil)))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _t'2 (tptr (Tstruct _BtNode noattr)))
            (Tstruct _BtNode noattr)) _numKeys tint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint) (Etempvar _t'3 tint)
                     tint)
        (Scall None
          (Evar _moveToNext (Tfunction
                              (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                              tvoid cc_default))
          ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
        Sskip)))
  (Ssequence
    (Scall None
      (Evar _moveToNext (Tfunction
                          (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tvoid
                          cc_default))
      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
    (Sreturn None)))
|}.

Definition f_RL_MoveToPrevious := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _entryIndex (Tfunction
                          (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tint
                          cc_default))
      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Scall None
        (Evar _moveToPrev (Tfunction
                            (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                            tvoid cc_default))
        ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
      Sskip))
  (Ssequence
    (Scall None
      (Evar _moveToPrev (Tfunction
                          (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tvoid
                          cc_default))
      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
    (Sreturn None)))
|}.

Definition f_RL_MoveToNextValid := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _RL_MoveToNext (Tfunction
                           (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tvoid
                           cc_default))
    ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _RL_CursorIsValid (Tfunction
                                (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                                tint cc_default))
      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_RL_MoveToPreviousNotFirst := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _RL_MoveToPrevious (Tfunction
                               (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                               tvoid cc_default))
    ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _isFirst (Tfunction (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                       tint cc_default))
      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                   (Econst_int (Int.repr 1) tint) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      (Sreturn (Some (Econst_int (Int.repr 1) tint))))))
|}.

Definition v___func____8 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_RL_IsEmpty := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tint) :: (_t'2, (tptr (Tstruct _BtNode noattr))) ::
               (_t'1, (tptr (Tstruct _Relation noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_3 (tarray tschar 22)) ::
       (Evar ___stringlit_1 (tarray tschar 15)) ::
       (Econst_int (Int.repr 459) tint) ::
       (Evar ___func____8 (tarray tschar 11)) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
            (Tstruct _Cursor noattr)) _relation
          (tptr (Tstruct _Relation noattr))))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _t'1 (tptr (Tstruct _Relation noattr)))
              (Tstruct _Relation noattr)) _root
            (tptr (Tstruct _BtNode noattr))))
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _t'2 (tptr (Tstruct _BtNode noattr)))
                (Tstruct _BtNode noattr)) _numKeys tint))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sreturn (Some (Econst_int (Int.repr 1) tint)))
            Sskip))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition v___func____9 := {|
  gvar_info := (tarray tschar 14);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_RL_NumRecords := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tulong) :: (_t'1, (tptr (Tstruct _Relation noattr))) ::
               nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_3 (tarray tschar 22)) ::
       (Evar ___stringlit_1 (tarray tschar 15)) ::
       (Econst_int (Int.repr 468) tint) ::
       (Evar ___func____9 (tarray tschar 14)) :: nil)))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
          (Tstruct _Cursor noattr)) _relation
        (tptr (Tstruct _Relation noattr))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _t'1 (tptr (Tstruct _Relation noattr)))
            (Tstruct _Relation noattr)) _numRecords tulong))
      (Sreturn (Some (Etempvar _t'2 tulong))))))
|}.

Definition v___func____10 := {|
  gvar_info := (tarray tschar 13);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_RL_PrintTree := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_relation, (tptr (Tstruct _Relation noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _BtNode noattr))) ::
               (_t'1, (tptr (Tstruct _BtNode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One
                 (Etempvar _relation (tptr (Tstruct _Relation noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_2 (tarray tschar 24)) ::
       (Evar ___stringlit_1 (tarray tschar 15)) ::
       (Econst_int (Int.repr 476) tint) ::
       (Evar ___func____10 (tarray tschar 13)) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _relation (tptr (Tstruct _Relation noattr)))
            (Tstruct _Relation noattr)) _root
          (tptr (Tstruct _BtNode noattr))))
      (Sifthenelse (Ebinop One
                     (Etempvar _t'2 (tptr (Tstruct _BtNode noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        Sskip
        (Scall None
          (Evar ___assert_fail (Tfunction
                                 (Tcons (tptr tschar)
                                   (Tcons (tptr tschar)
                                     (Tcons tuint (Tcons (tptr tschar) Tnil))))
                                 tvoid cc_default))
          ((Evar ___stringlit_7 (tarray tschar 30)) ::
           (Evar ___stringlit_1 (tarray tschar 15)) ::
           (Econst_int (Int.repr 477) tint) ::
           (Evar ___func____10 (tarray tschar 13)) :: nil))))
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _relation (tptr (Tstruct _Relation noattr)))
            (Tstruct _Relation noattr)) _root
          (tptr (Tstruct _BtNode noattr))))
      (Scall None
        (Evar _printTree (Tfunction
                           (Tcons (tptr (Tstruct _BtNode noattr))
                             (Tcons tint Tnil)) tvoid cc_default))
        ((Etempvar _t'1 (tptr (Tstruct _BtNode noattr))) ::
         (Econst_int (Int.repr 0) tint) :: nil)))))
|}.

Definition v___func____11 := {|
  gvar_info := (tarray tschar 15);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_RL_PrintCursor := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_3 (tarray tschar 22)) ::
       (Evar ___stringlit_1 (tarray tschar 15)) ::
       (Econst_int (Int.repr 485) tint) ::
       (Evar ___func____11 (tarray tschar 15)) :: nil)))
  (Scall None
    (Evar _printCursor (Tfunction
                         (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tvoid
                         cc_default))
    ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil)))
|}.

Definition f_createNewNode := {|
  fn_return := (tptr (Tstruct _BtNode noattr));
  fn_callconv := cc_default;
  fn_params := ((_isLeaf, tint) :: (_First, tint) :: (_Last, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_newNode, (tptr (Tstruct _BtNode noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _BtNode noattr) tulong) :: nil))
    (Sset _newNode
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _BtNode noattr)))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _newNode (tptr (Tstruct _BtNode noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _newNode (tptr (Tstruct _BtNode noattr)))
            (Tstruct _BtNode noattr)) _numKeys tint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _newNode (tptr (Tstruct _BtNode noattr)))
              (Tstruct _BtNode noattr)) _isLeaf tint)
          (Etempvar _isLeaf tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _newNode (tptr (Tstruct _BtNode noattr)))
                (Tstruct _BtNode noattr)) _First tint)
            (Etempvar _First tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _newNode (tptr (Tstruct _BtNode noattr)))
                  (Tstruct _BtNode noattr)) _Last tint)
              (Etempvar _Last tint))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _newNode (tptr (Tstruct _BtNode noattr)))
                    (Tstruct _BtNode noattr)) _ptr0
                  (tptr (Tstruct _BtNode noattr)))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
              (Sreturn (Some (Etempvar _newNode (tptr (Tstruct _BtNode noattr))))))))))))
|}.

Definition v___func____12 := {|
  gvar_info := (tarray tschar 10);
  gvar_init := (Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_splitnode := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_node, (tptr (Tstruct _BtNode noattr))) ::
                (_entry, (tptr (Tstruct _Entry noattr))) ::
                (_isLeaf, tint) :: nil);
  fn_vars := ((_allEntries, (tarray (Tstruct _Entry noattr) 16)) :: nil);
  fn_temps := ((_newNode, (tptr (Tstruct _BtNode noattr))) :: (_i, tint) ::
               (_tgtIdx, tint) :: (_t'2, (tptr (Tstruct _BtNode noattr))) ::
               (_t'1, tint) :: (_t'28, tulong) :: (_t'27, tint) ::
               (_t'26, tulong) :: (_t'25, (tptr tvoid)) :: (_t'24, tulong) ::
               (_t'23, (tptr tvoid)) :: (_t'22, tulong) ::
               (_t'21, (tptr tvoid)) :: (_t'20, tulong) ::
               (_t'19, (tptr tvoid)) :: (_t'18, tulong) ::
               (_t'17, (tptr tvoid)) :: (_t'16, tulong) :: (_t'15, tulong) ::
               (_t'14, (tptr (Tstruct _BtNode noattr))) :: (_t'13, tulong) ::
               (_t'12, (tptr (Tstruct _BtNode noattr))) :: (_t'11, tulong) ::
               (_t'10, (tptr (Tstruct _BtNode noattr))) :: (_t'9, tulong) ::
               (_t'8, (tptr (Tstruct _BtNode noattr))) :: (_t'7, tulong) ::
               (_t'6, (tptr (Tstruct _BtNode noattr))) ::
               (_t'5, (tptr (Tstruct _BtNode noattr))) :: (_t'4, tulong) ::
               (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'28
        (Efield
          (Ederef (Etempvar _entry (tptr (Tstruct _Entry noattr)))
            (Tstruct _Entry noattr)) _key tulong))
      (Scall (Some _t'1)
        (Evar _findRecordIndex (Tfunction
                                 (Tcons (tptr (Tstruct _BtNode noattr))
                                   (Tcons tulong Tnil)) tint cc_default))
        ((Etempvar _node (tptr (Tstruct _BtNode noattr))) ::
         (Etempvar _t'28 tulong) :: nil)))
    (Sset _tgtIdx (Etempvar _t'1 tint)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'27
          (Efield
            (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
              (Tstruct _BtNode noattr)) _Last tint))
        (Scall (Some _t'2)
          (Evar _createNewNode (Tfunction
                                 (Tcons tint (Tcons tint (Tcons tint Tnil)))
                                 (tptr (Tstruct _BtNode noattr)) cc_default))
          ((Etempvar _isLeaf tint) :: (Econst_int (Int.repr 0) tint) ::
           (Etempvar _t'27 tint) :: nil)))
      (Sset _newNode (Etempvar _t'2 (tptr (Tstruct _BtNode noattr)))))
    (Ssequence
      (Sifthenelse (Etempvar _newNode (tptr (Tstruct _BtNode noattr)))
        Sskip
        (Scall None
          (Evar ___assert_fail (Tfunction
                                 (Tcons (tptr tschar)
                                   (Tcons (tptr tschar)
                                     (Tcons tuint (Tcons (tptr tschar) Tnil))))
                                 tvoid cc_default))
          ((Evar ___stringlit_8 (tarray tschar 8)) ::
           (Evar ___stringlit_1 (tarray tschar 15)) ::
           (Econst_int (Int.repr 524) tint) ::
           (Evar ___func____12 (tarray tschar 10)) :: nil)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
              (Tstruct _BtNode noattr)) _Last tint)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                (Tstruct _BtNode noattr)) _isLeaf tint))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tint)
                         (Econst_int (Int.repr 1) tint) tint)
            (Ssequence
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                   (Etempvar _tgtIdx tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Ssequence
                        (Sset _t'26
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                                    (Tstruct _BtNode noattr)) _entries
                                  (tarray (Tstruct _Entry noattr) 15))
                                (Etempvar _i tint)
                                (tptr (Tstruct _Entry noattr)))
                              (Tstruct _Entry noattr)) _key tulong))
                        (Sassign
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                (Etempvar _i tint)
                                (tptr (Tstruct _Entry noattr)))
                              (Tstruct _Entry noattr)) _key tulong)
                          (Etempvar _t'26 tulong)))
                      (Ssequence
                        (Sset _t'25
                          (Efield
                            (Efield
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                                      (Tstruct _BtNode noattr)) _entries
                                    (tarray (Tstruct _Entry noattr) 15))
                                  (Etempvar _i tint)
                                  (tptr (Tstruct _Entry noattr)))
                                (Tstruct _Entry noattr)) _ptr
                              (Tunion _Child_or_Record noattr)) _record
                            (tptr tvoid)))
                        (Sassign
                          (Efield
                            (Efield
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                  (Etempvar _i tint)
                                  (tptr (Tstruct _Entry noattr)))
                                (Tstruct _Entry noattr)) _ptr
                              (Tunion _Child_or_Record noattr)) _record
                            (tptr tvoid)) (Etempvar _t'25 (tptr tvoid))))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Ssequence
                (Ssequence
                  (Sset _t'24
                    (Efield
                      (Ederef
                        (Etempvar _entry (tptr (Tstruct _Entry noattr)))
                        (Tstruct _Entry noattr)) _key tulong))
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                          (Etempvar _tgtIdx tint)
                          (tptr (Tstruct _Entry noattr)))
                        (Tstruct _Entry noattr)) _key tulong)
                    (Etempvar _t'24 tulong)))
                (Ssequence
                  (Ssequence
                    (Sset _t'23
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _entry (tptr (Tstruct _Entry noattr)))
                            (Tstruct _Entry noattr)) _ptr
                          (Tunion _Child_or_Record noattr)) _record
                        (tptr tvoid)))
                    (Sassign
                      (Efield
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                              (Etempvar _tgtIdx tint)
                              (tptr (Tstruct _Entry noattr)))
                            (Tstruct _Entry noattr)) _ptr
                          (Tunion _Child_or_Record noattr)) _record
                        (tptr tvoid)) (Etempvar _t'23 (tptr tvoid))))
                  (Ssequence
                    (Ssequence
                      (Sset _i (Etempvar _tgtIdx tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                         (Econst_int (Int.repr 15) tint)
                                         tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Ssequence
                              (Sset _t'22
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                                          (Tstruct _BtNode noattr)) _entries
                                        (tarray (Tstruct _Entry noattr) 15))
                                      (Etempvar _i tint)
                                      (tptr (Tstruct _Entry noattr)))
                                    (Tstruct _Entry noattr)) _key tulong))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                      (Ebinop Oadd (Etempvar _i tint)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      (tptr (Tstruct _Entry noattr)))
                                    (Tstruct _Entry noattr)) _key tulong)
                                (Etempvar _t'22 tulong)))
                            (Ssequence
                              (Sset _t'21
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                                            (Tstruct _BtNode noattr))
                                          _entries
                                          (tarray (Tstruct _Entry noattr) 15))
                                        (Etempvar _i tint)
                                        (tptr (Tstruct _Entry noattr)))
                                      (Tstruct _Entry noattr)) _ptr
                                    (Tunion _Child_or_Record noattr)) _record
                                  (tptr tvoid)))
                              (Sassign
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                        (Ebinop Oadd (Etempvar _i tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint)
                                        (tptr (Tstruct _Entry noattr)))
                                      (Tstruct _Entry noattr)) _ptr
                                    (Tunion _Child_or_Record noattr)) _record
                                  (tptr tvoid))
                                (Etempvar _t'21 (tptr tvoid))))))
                        (Sset _i
                          (Ebinop Oadd (Etempvar _i tint)
                            (Econst_int (Int.repr 1) tint) tint))))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                            (Tstruct _BtNode noattr)) _numKeys tint)
                        (Econst_int (Int.repr 8) tint))
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _tgtIdx tint)
                                       (Econst_int (Int.repr 8) tint) tint)
                          (Ssequence
                            (Sset _i (Etempvar _tgtIdx tint))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                               (Econst_int (Int.repr 8) tint)
                                               tint)
                                  Sskip
                                  Sbreak)
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'20
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                            (Etempvar _i tint)
                                            (tptr (Tstruct _Entry noattr)))
                                          (Tstruct _Entry noattr)) _key
                                        tulong))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                                                (Tstruct _BtNode noattr))
                                              _entries
                                              (tarray (Tstruct _Entry noattr) 15))
                                            (Etempvar _i tint)
                                            (tptr (Tstruct _Entry noattr)))
                                          (Tstruct _Entry noattr)) _key
                                        tulong) (Etempvar _t'20 tulong)))
                                  (Ssequence
                                    (Sset _t'19
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                              (Etempvar _i tint)
                                              (tptr (Tstruct _Entry noattr)))
                                            (Tstruct _Entry noattr)) _ptr
                                          (Tunion _Child_or_Record noattr))
                                        _record (tptr tvoid)))
                                    (Sassign
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                                                  (Tstruct _BtNode noattr))
                                                _entries
                                                (tarray (Tstruct _Entry noattr) 15))
                                              (Etempvar _i tint)
                                              (tptr (Tstruct _Entry noattr)))
                                            (Tstruct _Entry noattr)) _ptr
                                          (Tunion _Child_or_Record noattr))
                                        _record (tptr tvoid))
                                      (Etempvar _t'19 (tptr tvoid))))))
                              (Sset _i
                                (Ebinop Oadd (Etempvar _i tint)
                                  (Econst_int (Int.repr 1) tint) tint))))
                          Sskip)
                        (Ssequence
                          (Ssequence
                            (Sset _i (Econst_int (Int.repr 8) tint))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                               (Ebinop Oadd
                                                 (Econst_int (Int.repr 15) tint)
                                                 (Econst_int (Int.repr 1) tint)
                                                 tint) tint)
                                  Sskip
                                  Sbreak)
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'18
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                            (Etempvar _i tint)
                                            (tptr (Tstruct _Entry noattr)))
                                          (Tstruct _Entry noattr)) _key
                                        tulong))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _newNode (tptr (Tstruct _BtNode noattr)))
                                                (Tstruct _BtNode noattr))
                                              _entries
                                              (tarray (Tstruct _Entry noattr) 15))
                                            (Ebinop Osub (Etempvar _i tint)
                                              (Econst_int (Int.repr 8) tint)
                                              tint)
                                            (tptr (Tstruct _Entry noattr)))
                                          (Tstruct _Entry noattr)) _key
                                        tulong) (Etempvar _t'18 tulong)))
                                  (Ssequence
                                    (Sset _t'17
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                              (Etempvar _i tint)
                                              (tptr (Tstruct _Entry noattr)))
                                            (Tstruct _Entry noattr)) _ptr
                                          (Tunion _Child_or_Record noattr))
                                        _record (tptr tvoid)))
                                    (Sassign
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _newNode (tptr (Tstruct _BtNode noattr)))
                                                  (Tstruct _BtNode noattr))
                                                _entries
                                                (tarray (Tstruct _Entry noattr) 15))
                                              (Ebinop Osub (Etempvar _i tint)
                                                (Econst_int (Int.repr 8) tint)
                                                tint)
                                              (tptr (Tstruct _Entry noattr)))
                                            (Tstruct _Entry noattr)) _ptr
                                          (Tunion _Child_or_Record noattr))
                                        _record (tptr tvoid))
                                      (Etempvar _t'17 (tptr tvoid))))))
                              (Sset _i
                                (Ebinop Oadd (Etempvar _i tint)
                                  (Econst_int (Int.repr 1) tint) tint))))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _newNode (tptr (Tstruct _BtNode noattr)))
                                  (Tstruct _BtNode noattr)) _numKeys tint)
                              (Ebinop Osub
                                (Ebinop Oadd (Econst_int (Int.repr 15) tint)
                                  (Econst_int (Int.repr 1) tint) tint)
                                (Econst_int (Int.repr 8) tint) tint))
                            (Ssequence
                              (Ssequence
                                (Sset _t'16
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                        (Econst_int (Int.repr 8) tint)
                                        (tptr (Tstruct _Entry noattr)))
                                      (Tstruct _Entry noattr)) _key tulong))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _entry (tptr (Tstruct _Entry noattr)))
                                      (Tstruct _Entry noattr)) _key tulong)
                                  (Etempvar _t'16 tulong)))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Efield
                                      (Ederef
                                        (Etempvar _entry (tptr (Tstruct _Entry noattr)))
                                        (Tstruct _Entry noattr)) _ptr
                                      (Tunion _Child_or_Record noattr))
                                    _child (tptr (Tstruct _BtNode noattr)))
                                  (Etempvar _newNode (tptr (Tstruct _BtNode noattr))))
                                (Sreturn None)))))))))))
            (Ssequence
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                   (Etempvar _tgtIdx tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Ssequence
                        (Sset _t'15
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                                    (Tstruct _BtNode noattr)) _entries
                                  (tarray (Tstruct _Entry noattr) 15))
                                (Etempvar _i tint)
                                (tptr (Tstruct _Entry noattr)))
                              (Tstruct _Entry noattr)) _key tulong))
                        (Sassign
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                (Etempvar _i tint)
                                (tptr (Tstruct _Entry noattr)))
                              (Tstruct _Entry noattr)) _key tulong)
                          (Etempvar _t'15 tulong)))
                      (Ssequence
                        (Sset _t'14
                          (Efield
                            (Efield
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                                      (Tstruct _BtNode noattr)) _entries
                                    (tarray (Tstruct _Entry noattr) 15))
                                  (Etempvar _i tint)
                                  (tptr (Tstruct _Entry noattr)))
                                (Tstruct _Entry noattr)) _ptr
                              (Tunion _Child_or_Record noattr)) _child
                            (tptr (Tstruct _BtNode noattr))))
                        (Sassign
                          (Efield
                            (Efield
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                  (Etempvar _i tint)
                                  (tptr (Tstruct _Entry noattr)))
                                (Tstruct _Entry noattr)) _ptr
                              (Tunion _Child_or_Record noattr)) _child
                            (tptr (Tstruct _BtNode noattr)))
                          (Etempvar _t'14 (tptr (Tstruct _BtNode noattr)))))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Ssequence
                (Ssequence
                  (Sset _t'13
                    (Efield
                      (Ederef
                        (Etempvar _entry (tptr (Tstruct _Entry noattr)))
                        (Tstruct _Entry noattr)) _key tulong))
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                          (Etempvar _tgtIdx tint)
                          (tptr (Tstruct _Entry noattr)))
                        (Tstruct _Entry noattr)) _key tulong)
                    (Etempvar _t'13 tulong)))
                (Ssequence
                  (Ssequence
                    (Sset _t'12
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _entry (tptr (Tstruct _Entry noattr)))
                            (Tstruct _Entry noattr)) _ptr
                          (Tunion _Child_or_Record noattr)) _child
                        (tptr (Tstruct _BtNode noattr))))
                    (Sassign
                      (Efield
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                              (Etempvar _tgtIdx tint)
                              (tptr (Tstruct _Entry noattr)))
                            (Tstruct _Entry noattr)) _ptr
                          (Tunion _Child_or_Record noattr)) _child
                        (tptr (Tstruct _BtNode noattr)))
                      (Etempvar _t'12 (tptr (Tstruct _BtNode noattr)))))
                  (Ssequence
                    (Ssequence
                      (Sset _i (Etempvar _tgtIdx tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                         (Econst_int (Int.repr 15) tint)
                                         tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Ssequence
                              (Sset _t'11
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                                          (Tstruct _BtNode noattr)) _entries
                                        (tarray (Tstruct _Entry noattr) 15))
                                      (Etempvar _i tint)
                                      (tptr (Tstruct _Entry noattr)))
                                    (Tstruct _Entry noattr)) _key tulong))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                      (Ebinop Oadd (Etempvar _i tint)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      (tptr (Tstruct _Entry noattr)))
                                    (Tstruct _Entry noattr)) _key tulong)
                                (Etempvar _t'11 tulong)))
                            (Ssequence
                              (Sset _t'10
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                                            (Tstruct _BtNode noattr))
                                          _entries
                                          (tarray (Tstruct _Entry noattr) 15))
                                        (Etempvar _i tint)
                                        (tptr (Tstruct _Entry noattr)))
                                      (Tstruct _Entry noattr)) _ptr
                                    (Tunion _Child_or_Record noattr)) _child
                                  (tptr (Tstruct _BtNode noattr))))
                              (Sassign
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                        (Ebinop Oadd (Etempvar _i tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint)
                                        (tptr (Tstruct _Entry noattr)))
                                      (Tstruct _Entry noattr)) _ptr
                                    (Tunion _Child_or_Record noattr)) _child
                                  (tptr (Tstruct _BtNode noattr)))
                                (Etempvar _t'10 (tptr (Tstruct _BtNode noattr)))))))
                        (Sset _i
                          (Ebinop Oadd (Etempvar _i tint)
                            (Econst_int (Int.repr 1) tint) tint))))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                            (Tstruct _BtNode noattr)) _numKeys tint)
                        (Econst_int (Int.repr 8) tint))
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _tgtIdx tint)
                                       (Econst_int (Int.repr 8) tint) tint)
                          (Ssequence
                            (Sset _i (Etempvar _tgtIdx tint))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                               (Econst_int (Int.repr 8) tint)
                                               tint)
                                  Sskip
                                  Sbreak)
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'9
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                            (Etempvar _i tint)
                                            (tptr (Tstruct _Entry noattr)))
                                          (Tstruct _Entry noattr)) _key
                                        tulong))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                                                (Tstruct _BtNode noattr))
                                              _entries
                                              (tarray (Tstruct _Entry noattr) 15))
                                            (Etempvar _i tint)
                                            (tptr (Tstruct _Entry noattr)))
                                          (Tstruct _Entry noattr)) _key
                                        tulong) (Etempvar _t'9 tulong)))
                                  (Ssequence
                                    (Sset _t'8
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                              (Etempvar _i tint)
                                              (tptr (Tstruct _Entry noattr)))
                                            (Tstruct _Entry noattr)) _ptr
                                          (Tunion _Child_or_Record noattr))
                                        _child
                                        (tptr (Tstruct _BtNode noattr))))
                                    (Sassign
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                                                  (Tstruct _BtNode noattr))
                                                _entries
                                                (tarray (Tstruct _Entry noattr) 15))
                                              (Etempvar _i tint)
                                              (tptr (Tstruct _Entry noattr)))
                                            (Tstruct _Entry noattr)) _ptr
                                          (Tunion _Child_or_Record noattr))
                                        _child
                                        (tptr (Tstruct _BtNode noattr)))
                                      (Etempvar _t'8 (tptr (Tstruct _BtNode noattr)))))))
                              (Sset _i
                                (Ebinop Oadd (Etempvar _i tint)
                                  (Econst_int (Int.repr 1) tint) tint))))
                          Sskip)
                        (Ssequence
                          (Ssequence
                            (Sset _i
                              (Ebinop Oadd (Econst_int (Int.repr 8) tint)
                                (Econst_int (Int.repr 1) tint) tint))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                               (Ebinop Oadd
                                                 (Econst_int (Int.repr 15) tint)
                                                 (Econst_int (Int.repr 1) tint)
                                                 tint) tint)
                                  Sskip
                                  Sbreak)
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'7
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                            (Etempvar _i tint)
                                            (tptr (Tstruct _Entry noattr)))
                                          (Tstruct _Entry noattr)) _key
                                        tulong))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _newNode (tptr (Tstruct _BtNode noattr)))
                                                (Tstruct _BtNode noattr))
                                              _entries
                                              (tarray (Tstruct _Entry noattr) 15))
                                            (Ebinop Osub (Etempvar _i tint)
                                              (Ebinop Oadd
                                                (Econst_int (Int.repr 8) tint)
                                                (Econst_int (Int.repr 1) tint)
                                                tint) tint)
                                            (tptr (Tstruct _Entry noattr)))
                                          (Tstruct _Entry noattr)) _key
                                        tulong) (Etempvar _t'7 tulong)))
                                  (Ssequence
                                    (Sset _t'6
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                              (Etempvar _i tint)
                                              (tptr (Tstruct _Entry noattr)))
                                            (Tstruct _Entry noattr)) _ptr
                                          (Tunion _Child_or_Record noattr))
                                        _child
                                        (tptr (Tstruct _BtNode noattr))))
                                    (Sassign
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _newNode (tptr (Tstruct _BtNode noattr)))
                                                  (Tstruct _BtNode noattr))
                                                _entries
                                                (tarray (Tstruct _Entry noattr) 15))
                                              (Ebinop Osub (Etempvar _i tint)
                                                (Ebinop Oadd
                                                  (Econst_int (Int.repr 8) tint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tint) tint)
                                              (tptr (Tstruct _Entry noattr)))
                                            (Tstruct _Entry noattr)) _ptr
                                          (Tunion _Child_or_Record noattr))
                                        _child
                                        (tptr (Tstruct _BtNode noattr)))
                                      (Etempvar _t'6 (tptr (Tstruct _BtNode noattr)))))))
                              (Sset _i
                                (Ebinop Oadd (Etempvar _i tint)
                                  (Econst_int (Int.repr 1) tint) tint))))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _newNode (tptr (Tstruct _BtNode noattr)))
                                  (Tstruct _BtNode noattr)) _numKeys tint)
                              (Ebinop Osub (Econst_int (Int.repr 15) tint)
                                (Econst_int (Int.repr 8) tint) tint))
                            (Ssequence
                              (Ssequence
                                (Sset _t'5
                                  (Efield
                                    (Efield
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                          (Econst_int (Int.repr 8) tint)
                                          (tptr (Tstruct _Entry noattr)))
                                        (Tstruct _Entry noattr)) _ptr
                                      (Tunion _Child_or_Record noattr))
                                    _child (tptr (Tstruct _BtNode noattr))))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _newNode (tptr (Tstruct _BtNode noattr)))
                                      (Tstruct _BtNode noattr)) _ptr0
                                    (tptr (Tstruct _BtNode noattr)))
                                  (Etempvar _t'5 (tptr (Tstruct _BtNode noattr)))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'4
                                    (Efield
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _allEntries (tarray (Tstruct _Entry noattr) 16))
                                          (Econst_int (Int.repr 8) tint)
                                          (tptr (Tstruct _Entry noattr)))
                                        (Tstruct _Entry noattr)) _key tulong))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _entry (tptr (Tstruct _Entry noattr)))
                                        (Tstruct _Entry noattr)) _key tulong)
                                    (Etempvar _t'4 tulong)))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Efield
                                        (Ederef
                                          (Etempvar _entry (tptr (Tstruct _Entry noattr)))
                                          (Tstruct _Entry noattr)) _ptr
                                        (Tunion _Child_or_Record noattr))
                                      _child (tptr (Tstruct _BtNode noattr)))
                                    (Etempvar _newNode (tptr (Tstruct _BtNode noattr))))
                                  (Sreturn None))))))))))))))))))
|}.

Definition v___func____13 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_putEntry := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) ::
                (_newEntry, (tptr (Tstruct _Entry noattr))) ::
                (_key, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_currNode__1, (tptr (Tstruct _BtNode noattr))) ::
               (_tgtIdx, tint) :: (_i, tint) :: (_tgtIdx__1, tint) ::
               (_i__1, tint) :: (_t'32, (tptr (Tstruct _BtNode noattr))) ::
               (_t'31, (tptr (Tstruct _BtNode noattr))) ::
               (_t'30, (tptr (Tstruct _BtNode noattr))) ::
               (_t'29, (tptr (Tstruct _BtNode noattr))) ::
               (_t'28, (tptr (Tstruct _BtNode noattr))) ::
               (_t'27, (tptr (Tstruct _BtNode noattr))) ::
               (_t'26, (tptr (Tstruct _BtNode noattr))) ::
               (_t'25, (tptr (Tstruct _BtNode noattr))) ::
               (_t'24, (tptr (Tstruct _BtNode noattr))) ::
               (_t'23, (tptr (Tstruct _BtNode noattr))) ::
               (_t'22, (tptr (Tstruct _BtNode noattr))) ::
               (_t'21, (tptr (Tstruct _BtNode noattr))) :: (_t'20, tint) ::
               (_t'19, tint) :: (_t'18, (tptr (Tstruct _BtNode noattr))) ::
               (_t'17, tint) :: (_t'16, (tptr (Tstruct _BtNode noattr))) ::
               (_t'15, tint) :: (_t'14, (tptr (Tstruct _BtNode noattr))) ::
               (_t'13, (tptr (Tstruct _BtNode noattr))) ::
               (_t'12, (tptr (Tstruct _BtNode noattr))) ::
               (_t'11, (tptr (Tstruct _BtNode noattr))) ::
               (_t'10, (tptr (Tstruct _BtNode noattr))) ::
               (_t'9, (tptr (Tstruct _BtNode noattr))) ::
               (_t'8, (tptr (Tstruct _BtNode noattr))) ::
               (_t'7, (tptr (Tstruct _BtNode noattr))) ::
               (_t'6, (tptr (Tstruct _BtNode noattr))) ::
               (_t'5, (tptr (Tstruct _BtNode noattr))) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, (tptr (Tstruct _BtNode noattr))) ::
               (_t'1, (tptr (Tstruct _BtNode noattr))) ::
               (_t'70, (tptr (Tstruct _BtNode noattr))) ::
               (_t'69, (tptr (Tstruct _Relation noattr))) ::
               (_t'68, tulong) :: (_t'67, (tptr (Tstruct _BtNode noattr))) ::
               (_t'66, (tptr (Tstruct _Relation noattr))) :: (_t'65, tint) ::
               (_t'64, (tptr (Tstruct _Relation noattr))) ::
               (_t'63, (tptr (Tstruct _Relation noattr))) ::
               (_t'62, tulong) ::
               (_t'61, (tptr (Tstruct _Relation noattr))) ::
               (_t'60, (tptr (Tstruct _Relation noattr))) :: (_t'59, tint) ::
               (_t'58, tulong) :: (_t'57, tulong) :: (_t'56, tint) ::
               (_t'55, (tptr tvoid)) :: (_t'54, tulong) ::
               (_t'53, (tptr tvoid)) :: (_t'52, tulong) ::
               (_t'51, (tptr tvoid)) :: (_t'50, tint) :: (_t'49, tulong) ::
               (_t'48, (tptr (Tstruct _Relation noattr))) ::
               (_t'47, (tptr (Tstruct _Relation noattr))) :: (_t'46, tint) ::
               (_t'45, tint) :: (_t'44, tulong) ::
               (_t'43, (tptr (Tstruct _BtNode noattr))) :: (_t'42, tulong) ::
               (_t'41, (tptr (Tstruct _BtNode noattr))) :: (_t'40, tint) ::
               (_t'39, tulong) ::
               (_t'38, (tptr (Tstruct _Relation noattr))) ::
               (_t'37, (tptr (Tstruct _Relation noattr))) :: (_t'36, tint) ::
               (_t'35, tint) :: (_t'34, tint) :: (_t'33, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'59
      (Efield
        (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
          (Tstruct _Cursor noattr)) _level tint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'59 tint)
                   (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _createNewNode (Tfunction
                                   (Tcons tint
                                     (Tcons tint (Tcons tint Tnil)))
                                   (tptr (Tstruct _BtNode noattr))
                                   cc_default))
            ((Econst_int (Int.repr 0) tint) ::
             (Econst_int (Int.repr 1) tint) ::
             (Econst_int (Int.repr 1) tint) :: nil))
          (Sset _currNode__1 (Etempvar _t'1 (tptr (Tstruct _BtNode noattr)))))
        (Ssequence
          (Sifthenelse (Etempvar _currNode__1 (tptr (Tstruct _BtNode noattr)))
            Sskip
            (Scall None
              (Evar ___assert_fail (Tfunction
                                     (Tcons (tptr tschar)
                                       (Tcons (tptr tschar)
                                         (Tcons tuint
                                           (Tcons (tptr tschar) Tnil))))
                                     tvoid cc_default))
              ((Evar ___stringlit_9 (tarray tschar 9)) ::
               (Evar ___stringlit_1 (tarray tschar 15)) ::
               (Econst_int (Int.repr 686) tint) ::
               (Evar ___func____13 (tarray tschar 9)) :: nil)))
          (Ssequence
            (Ssequence
              (Sset _t'69
                (Efield
                  (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                    (Tstruct _Cursor noattr)) _relation
                  (tptr (Tstruct _Relation noattr))))
              (Ssequence
                (Sset _t'70
                  (Efield
                    (Ederef
                      (Etempvar _t'69 (tptr (Tstruct _Relation noattr)))
                      (Tstruct _Relation noattr)) _root
                    (tptr (Tstruct _BtNode noattr))))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _currNode__1 (tptr (Tstruct _BtNode noattr)))
                      (Tstruct _BtNode noattr)) _ptr0
                    (tptr (Tstruct _BtNode noattr)))
                  (Etempvar _t'70 (tptr (Tstruct _BtNode noattr))))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _currNode__1 (tptr (Tstruct _BtNode noattr)))
                    (Tstruct _BtNode noattr)) _numKeys tint)
                (Econst_int (Int.repr 1) tint))
              (Ssequence
                (Ssequence
                  (Sset _t'68
                    (Efield
                      (Ederef
                        (Etempvar _newEntry (tptr (Tstruct _Entry noattr)))
                        (Tstruct _Entry noattr)) _key tulong))
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _currNode__1 (tptr (Tstruct _BtNode noattr)))
                              (Tstruct _BtNode noattr)) _entries
                            (tarray (Tstruct _Entry noattr) 15))
                          (Econst_int (Int.repr 0) tint)
                          (tptr (Tstruct _Entry noattr)))
                        (Tstruct _Entry noattr)) _key tulong)
                    (Etempvar _t'68 tulong)))
                (Ssequence
                  (Ssequence
                    (Sset _t'67
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _newEntry (tptr (Tstruct _Entry noattr)))
                            (Tstruct _Entry noattr)) _ptr
                          (Tunion _Child_or_Record noattr)) _child
                        (tptr (Tstruct _BtNode noattr))))
                    (Sassign
                      (Efield
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _currNode__1 (tptr (Tstruct _BtNode noattr)))
                                  (Tstruct _BtNode noattr)) _entries
                                (tarray (Tstruct _Entry noattr) 15))
                              (Econst_int (Int.repr 0) tint)
                              (tptr (Tstruct _Entry noattr)))
                            (Tstruct _Entry noattr)) _ptr
                          (Tunion _Child_or_Record noattr)) _child
                        (tptr (Tstruct _BtNode noattr)))
                      (Etempvar _t'67 (tptr (Tstruct _BtNode noattr)))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'66
                        (Efield
                          (Ederef
                            (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                            (Tstruct _Cursor noattr)) _relation
                          (tptr (Tstruct _Relation noattr))))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _t'66 (tptr (Tstruct _Relation noattr)))
                            (Tstruct _Relation noattr)) _root
                          (tptr (Tstruct _BtNode noattr)))
                        (Etempvar _currNode__1 (tptr (Tstruct _BtNode noattr)))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'63
                          (Efield
                            (Ederef
                              (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                              (Tstruct _Cursor noattr)) _relation
                            (tptr (Tstruct _Relation noattr))))
                        (Ssequence
                          (Sset _t'64
                            (Efield
                              (Ederef
                                (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                                (Tstruct _Cursor noattr)) _relation
                              (tptr (Tstruct _Relation noattr))))
                          (Ssequence
                            (Sset _t'65
                              (Efield
                                (Ederef
                                  (Etempvar _t'64 (tptr (Tstruct _Relation noattr)))
                                  (Tstruct _Relation noattr)) _depth tint))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _t'63 (tptr (Tstruct _Relation noattr)))
                                  (Tstruct _Relation noattr)) _depth tint)
                              (Ebinop Oadd (Etempvar _t'65 tint)
                                (Econst_int (Int.repr 1) tint) tint)))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'60
                            (Efield
                              (Ederef
                                (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                                (Tstruct _Cursor noattr)) _relation
                              (tptr (Tstruct _Relation noattr))))
                          (Ssequence
                            (Sset _t'61
                              (Efield
                                (Ederef
                                  (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                                  (Tstruct _Cursor noattr)) _relation
                                (tptr (Tstruct _Relation noattr))))
                            (Ssequence
                              (Sset _t'62
                                (Efield
                                  (Ederef
                                    (Etempvar _t'61 (tptr (Tstruct _Relation noattr)))
                                    (Tstruct _Relation noattr)) _numRecords
                                  tulong))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _t'60 (tptr (Tstruct _Relation noattr)))
                                    (Tstruct _Relation noattr)) _numRecords
                                  tulong)
                                (Ebinop Oadd (Etempvar _t'62 tulong)
                                  (Econst_int (Int.repr 1) tint) tulong)))))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                                    (Tstruct _Cursor noattr)) _ancestors
                                  (tarray (tptr (Tstruct _BtNode noattr)) 20))
                                (Econst_int (Int.repr 0) tint)
                                (tptr (tptr (Tstruct _BtNode noattr))))
                              (tptr (Tstruct _BtNode noattr)))
                            (Etempvar _currNode__1 (tptr (Tstruct _BtNode noattr))))
                          (Ssequence
                            (Scall None
                              (Evar _moveToKey (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _BtNode noattr))
                                                   (Tcons tulong
                                                     (Tcons
                                                       (tptr (Tstruct _Cursor noattr))
                                                       (Tcons tint Tnil))))
                                                 tvoid cc_default))
                              ((Etempvar _currNode__1 (tptr (Tstruct _BtNode noattr))) ::
                               (Etempvar _key tulong) ::
                               (Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                               (Econst_int (Int.repr 0) tint) :: nil))
                            (Sreturn None))))))))))))
      Sskip))
  (Ssequence
    (Scall (Some _t'32)
      (Evar _currNode (Tfunction (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                        (tptr (Tstruct _BtNode noattr)) cc_default))
      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
    (Ssequence
      (Sset _t'33
        (Efield
          (Ederef (Etempvar _t'32 (tptr (Tstruct _BtNode noattr)))
            (Tstruct _BtNode noattr)) _isLeaf tint))
      (Sifthenelse (Etempvar _t'33 tint)
        (Ssequence
          (Ssequence
            (Ssequence
              (Scall (Some _t'15)
                (Evar _entryIndex (Tfunction
                                    (Tcons (tptr (Tstruct _Cursor noattr))
                                      Tnil) tint cc_default))
                ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
              (Scall (Some _t'16)
                (Evar _currNode (Tfunction
                                  (Tcons (tptr (Tstruct _Cursor noattr))
                                    Tnil) (tptr (Tstruct _BtNode noattr))
                                  cc_default))
                ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil)))
            (Ssequence
              (Sset _t'56
                (Efield
                  (Ederef (Etempvar _t'16 (tptr (Tstruct _BtNode noattr)))
                    (Tstruct _BtNode noattr)) _numKeys tint))
              (Sifthenelse (Ebinop Olt (Etempvar _t'15 tint)
                             (Etempvar _t'56 tint) tint)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'18)
                      (Evar _currNode (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _Cursor noattr))
                                          Tnil)
                                        (tptr (Tstruct _BtNode noattr))
                                        cc_default))
                      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                       nil))
                    (Scall (Some _t'19)
                      (Evar _entryIndex (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _Cursor noattr))
                                            Tnil) tint cc_default))
                      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                       nil)))
                  (Ssequence
                    (Sset _t'57
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _t'18 (tptr (Tstruct _BtNode noattr)))
                                (Tstruct _BtNode noattr)) _entries
                              (tarray (Tstruct _Entry noattr) 15))
                            (Etempvar _t'19 tint)
                            (tptr (Tstruct _Entry noattr)))
                          (Tstruct _Entry noattr)) _key tulong))
                    (Ssequence
                      (Sset _t'58
                        (Efield
                          (Ederef
                            (Etempvar _newEntry (tptr (Tstruct _Entry noattr)))
                            (Tstruct _Entry noattr)) _key tulong))
                      (Sset _t'17
                        (Ecast
                          (Ebinop Oeq (Etempvar _t'57 tulong)
                            (Etempvar _t'58 tulong) tint) tbool)))))
                (Sset _t'17 (Econst_int (Int.repr 0) tint)))))
          (Sifthenelse (Etempvar _t'17 tint)
            (Ssequence
              (Ssequence
                (Ssequence
                  (Scall (Some _t'2)
                    (Evar _currNode (Tfunction
                                      (Tcons (tptr (Tstruct _Cursor noattr))
                                        Tnil) (tptr (Tstruct _BtNode noattr))
                                      cc_default))
                    ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                     nil))
                  (Scall (Some _t'3)
                    (Evar _entryIndex (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _Cursor noattr))
                                          Tnil) tint cc_default))
                    ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                     nil)))
                (Ssequence
                  (Sset _t'55
                    (Efield
                      (Efield
                        (Ederef
                          (Etempvar _newEntry (tptr (Tstruct _Entry noattr)))
                          (Tstruct _Entry noattr)) _ptr
                        (Tunion _Child_or_Record noattr)) _record
                      (tptr tvoid)))
                  (Sassign
                    (Efield
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _t'2 (tptr (Tstruct _BtNode noattr)))
                                (Tstruct _BtNode noattr)) _entries
                              (tarray (Tstruct _Entry noattr) 15))
                            (Etempvar _t'3 tint)
                            (tptr (Tstruct _Entry noattr)))
                          (Tstruct _Entry noattr)) _ptr
                        (Tunion _Child_or_Record noattr)) _record
                      (tptr tvoid)) (Etempvar _t'55 (tptr tvoid)))))
              (Sreturn None))
            (Ssequence
              (Scall (Some _t'14)
                (Evar _currNode (Tfunction
                                  (Tcons (tptr (Tstruct _Cursor noattr))
                                    Tnil) (tptr (Tstruct _BtNode noattr))
                                  cc_default))
                ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
              (Ssequence
                (Sset _t'45
                  (Efield
                    (Ederef (Etempvar _t'14 (tptr (Tstruct _BtNode noattr)))
                      (Tstruct _BtNode noattr)) _numKeys tint))
                (Sifthenelse (Ebinop Olt (Etempvar _t'45 tint)
                               (Econst_int (Int.repr 15) tint) tint)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _entryIndex (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _Cursor noattr))
                                              Tnil) tint cc_default))
                        ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                         nil))
                      (Sset _tgtIdx (Etempvar _t'4 tint)))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'5)
                            (Evar _currNode (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _Cursor noattr))
                                                Tnil)
                                              (tptr (Tstruct _BtNode noattr))
                                              cc_default))
                            ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                             nil))
                          (Sset _i
                            (Efield
                              (Ederef
                                (Etempvar _t'5 (tptr (Tstruct _BtNode noattr)))
                                (Tstruct _BtNode noattr)) _numKeys tint)))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Ogt (Etempvar _i tint)
                                           (Etempvar _tgtIdx tint) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'6)
                                    (Evar _currNode (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _Cursor noattr))
                                                        Tnil)
                                                      (tptr (Tstruct _BtNode noattr))
                                                      cc_default))
                                    ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                                     nil))
                                  (Scall (Some _t'7)
                                    (Evar _currNode (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _Cursor noattr))
                                                        Tnil)
                                                      (tptr (Tstruct _BtNode noattr))
                                                      cc_default))
                                    ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                                     nil)))
                                (Ssequence
                                  (Sset _t'54
                                    (Efield
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _t'7 (tptr (Tstruct _BtNode noattr)))
                                              (Tstruct _BtNode noattr))
                                            _entries
                                            (tarray (Tstruct _Entry noattr) 15))
                                          (Ebinop Osub (Etempvar _i tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint)
                                          (tptr (Tstruct _Entry noattr)))
                                        (Tstruct _Entry noattr)) _key tulong))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _t'6 (tptr (Tstruct _BtNode noattr)))
                                              (Tstruct _BtNode noattr))
                                            _entries
                                            (tarray (Tstruct _Entry noattr) 15))
                                          (Etempvar _i tint)
                                          (tptr (Tstruct _Entry noattr)))
                                        (Tstruct _Entry noattr)) _key tulong)
                                    (Etempvar _t'54 tulong))))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'8)
                                    (Evar _currNode (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _Cursor noattr))
                                                        Tnil)
                                                      (tptr (Tstruct _BtNode noattr))
                                                      cc_default))
                                    ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                                     nil))
                                  (Scall (Some _t'9)
                                    (Evar _currNode (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _Cursor noattr))
                                                        Tnil)
                                                      (tptr (Tstruct _BtNode noattr))
                                                      cc_default))
                                    ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                                     nil)))
                                (Ssequence
                                  (Sset _t'53
                                    (Efield
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _t'9 (tptr (Tstruct _BtNode noattr)))
                                                (Tstruct _BtNode noattr))
                                              _entries
                                              (tarray (Tstruct _Entry noattr) 15))
                                            (Ebinop Osub (Etempvar _i tint)
                                              (Econst_int (Int.repr 1) tint)
                                              tint)
                                            (tptr (Tstruct _Entry noattr)))
                                          (Tstruct _Entry noattr)) _ptr
                                        (Tunion _Child_or_Record noattr))
                                      _record (tptr tvoid)))
                                  (Sassign
                                    (Efield
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _t'8 (tptr (Tstruct _BtNode noattr)))
                                                (Tstruct _BtNode noattr))
                                              _entries
                                              (tarray (Tstruct _Entry noattr) 15))
                                            (Etempvar _i tint)
                                            (tptr (Tstruct _Entry noattr)))
                                          (Tstruct _Entry noattr)) _ptr
                                        (Tunion _Child_or_Record noattr))
                                      _record (tptr tvoid))
                                    (Etempvar _t'53 (tptr tvoid)))))))
                          (Sset _i
                            (Ebinop Osub (Etempvar _i tint)
                              (Econst_int (Int.repr 1) tint) tint))))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'10)
                            (Evar _currNode (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _Cursor noattr))
                                                Tnil)
                                              (tptr (Tstruct _BtNode noattr))
                                              cc_default))
                            ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                             nil))
                          (Ssequence
                            (Sset _t'52
                              (Efield
                                (Ederef
                                  (Etempvar _newEntry (tptr (Tstruct _Entry noattr)))
                                  (Tstruct _Entry noattr)) _key tulong))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'10 (tptr (Tstruct _BtNode noattr)))
                                        (Tstruct _BtNode noattr)) _entries
                                      (tarray (Tstruct _Entry noattr) 15))
                                    (Etempvar _tgtIdx tint)
                                    (tptr (Tstruct _Entry noattr)))
                                  (Tstruct _Entry noattr)) _key tulong)
                              (Etempvar _t'52 tulong))))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'11)
                              (Evar _currNode (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _Cursor noattr))
                                                  Tnil)
                                                (tptr (Tstruct _BtNode noattr))
                                                cc_default))
                              ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                               nil))
                            (Ssequence
                              (Sset _t'51
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Etempvar _newEntry (tptr (Tstruct _Entry noattr)))
                                      (Tstruct _Entry noattr)) _ptr
                                    (Tunion _Child_or_Record noattr)) _record
                                  (tptr tvoid)))
                              (Sassign
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _t'11 (tptr (Tstruct _BtNode noattr)))
                                            (Tstruct _BtNode noattr))
                                          _entries
                                          (tarray (Tstruct _Entry noattr) 15))
                                        (Etempvar _tgtIdx tint)
                                        (tptr (Tstruct _Entry noattr)))
                                      (Tstruct _Entry noattr)) _ptr
                                    (Tunion _Child_or_Record noattr)) _record
                                  (tptr tvoid))
                                (Etempvar _t'51 (tptr tvoid)))))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'12)
                                (Evar _currNode (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _Cursor noattr))
                                                    Tnil)
                                                  (tptr (Tstruct _BtNode noattr))
                                                  cc_default))
                                ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                                 nil))
                              (Ssequence
                                (Sset _t'50
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'12 (tptr (Tstruct _BtNode noattr)))
                                      (Tstruct _BtNode noattr)) _numKeys
                                    tint))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'12 (tptr (Tstruct _BtNode noattr)))
                                      (Tstruct _BtNode noattr)) _numKeys
                                    tint)
                                  (Ebinop Oadd (Etempvar _t'50 tint)
                                    (Econst_int (Int.repr 1) tint) tint))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'47
                                  (Efield
                                    (Ederef
                                      (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                                      (Tstruct _Cursor noattr)) _relation
                                    (tptr (Tstruct _Relation noattr))))
                                (Ssequence
                                  (Sset _t'48
                                    (Efield
                                      (Ederef
                                        (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                                        (Tstruct _Cursor noattr)) _relation
                                      (tptr (Tstruct _Relation noattr))))
                                  (Ssequence
                                    (Sset _t'49
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'48 (tptr (Tstruct _Relation noattr)))
                                          (Tstruct _Relation noattr))
                                        _numRecords tulong))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'47 (tptr (Tstruct _Relation noattr)))
                                          (Tstruct _Relation noattr))
                                        _numRecords tulong)
                                      (Ebinop Oadd (Etempvar _t'49 tulong)
                                        (Econst_int (Int.repr 1) tint)
                                        tulong)))))
                              (Sreturn None)))))))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'13)
                        (Evar _currNode (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _Cursor noattr))
                                            Tnil)
                                          (tptr (Tstruct _BtNode noattr))
                                          cc_default))
                        ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                         nil))
                      (Scall None
                        (Evar _splitnode (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _BtNode noattr))
                                             (Tcons
                                               (tptr (Tstruct _Entry noattr))
                                               (Tcons tint Tnil))) tvoid
                                           cc_default))
                        ((Etempvar _t'13 (tptr (Tstruct _BtNode noattr))) ::
                         (Etempvar _newEntry (tptr (Tstruct _Entry noattr))) ::
                         (Econst_int (Int.repr 1) tint) :: nil)))
                    (Ssequence
                      (Ssequence
                        (Sset _t'46
                          (Efield
                            (Ederef
                              (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                              (Tstruct _Cursor noattr)) _level tint))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                              (Tstruct _Cursor noattr)) _level tint)
                          (Ebinop Osub (Etempvar _t'46 tint)
                            (Econst_int (Int.repr 1) tint) tint)))
                      (Ssequence
                        (Scall None
                          (Evar _putEntry (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _Cursor noattr))
                                              (Tcons
                                                (tptr (Tstruct _Entry noattr))
                                                (Tcons tulong Tnil))) tvoid
                                            cc_default))
                          ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                           (Etempvar _newEntry (tptr (Tstruct _Entry noattr))) ::
                           (Etempvar _key tulong) :: nil))
                        (Sreturn None)))))))))
        (Ssequence
          (Scall (Some _t'31)
            (Evar _currNode (Tfunction
                              (Tcons (tptr (Tstruct _Cursor noattr)) Tnil)
                              (tptr (Tstruct _BtNode noattr)) cc_default))
            ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
          (Ssequence
            (Sset _t'34
              (Efield
                (Ederef (Etempvar _t'31 (tptr (Tstruct _BtNode noattr)))
                  (Tstruct _BtNode noattr)) _numKeys tint))
            (Sifthenelse (Ebinop Olt (Etempvar _t'34 tint)
                           (Econst_int (Int.repr 15) tint) tint)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'20)
                    (Evar _entryIndex (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _Cursor noattr))
                                          Tnil) tint cc_default))
                    ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                     nil))
                  (Sset _tgtIdx__1
                    (Ebinop Oadd (Etempvar _t'20 tint)
                      (Econst_int (Int.repr 1) tint) tint)))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'21)
                        (Evar _currNode (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _Cursor noattr))
                                            Tnil)
                                          (tptr (Tstruct _BtNode noattr))
                                          cc_default))
                        ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                         nil))
                      (Sset _i__1
                        (Efield
                          (Ederef
                            (Etempvar _t'21 (tptr (Tstruct _BtNode noattr)))
                            (Tstruct _BtNode noattr)) _numKeys tint)))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Ogt (Etempvar _i__1 tint)
                                       (Etempvar _tgtIdx__1 tint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'22)
                                (Evar _currNode (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _Cursor noattr))
                                                    Tnil)
                                                  (tptr (Tstruct _BtNode noattr))
                                                  cc_default))
                                ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                                 nil))
                              (Scall (Some _t'23)
                                (Evar _currNode (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _Cursor noattr))
                                                    Tnil)
                                                  (tptr (Tstruct _BtNode noattr))
                                                  cc_default))
                                ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                                 nil)))
                            (Ssequence
                              (Sset _t'44
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'23 (tptr (Tstruct _BtNode noattr)))
                                          (Tstruct _BtNode noattr)) _entries
                                        (tarray (Tstruct _Entry noattr) 15))
                                      (Ebinop Osub (Etempvar _i__1 tint)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      (tptr (Tstruct _Entry noattr)))
                                    (Tstruct _Entry noattr)) _key tulong))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'22 (tptr (Tstruct _BtNode noattr)))
                                          (Tstruct _BtNode noattr)) _entries
                                        (tarray (Tstruct _Entry noattr) 15))
                                      (Etempvar _i__1 tint)
                                      (tptr (Tstruct _Entry noattr)))
                                    (Tstruct _Entry noattr)) _key tulong)
                                (Etempvar _t'44 tulong))))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'24)
                                (Evar _currNode (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _Cursor noattr))
                                                    Tnil)
                                                  (tptr (Tstruct _BtNode noattr))
                                                  cc_default))
                                ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                                 nil))
                              (Scall (Some _t'25)
                                (Evar _currNode (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _Cursor noattr))
                                                    Tnil)
                                                  (tptr (Tstruct _BtNode noattr))
                                                  cc_default))
                                ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                                 nil)))
                            (Ssequence
                              (Sset _t'43
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _t'25 (tptr (Tstruct _BtNode noattr)))
                                            (Tstruct _BtNode noattr))
                                          _entries
                                          (tarray (Tstruct _Entry noattr) 15))
                                        (Ebinop Osub (Etempvar _i__1 tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint)
                                        (tptr (Tstruct _Entry noattr)))
                                      (Tstruct _Entry noattr)) _ptr
                                    (Tunion _Child_or_Record noattr)) _child
                                  (tptr (Tstruct _BtNode noattr))))
                              (Sassign
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _t'24 (tptr (Tstruct _BtNode noattr)))
                                            (Tstruct _BtNode noattr))
                                          _entries
                                          (tarray (Tstruct _Entry noattr) 15))
                                        (Etempvar _i__1 tint)
                                        (tptr (Tstruct _Entry noattr)))
                                      (Tstruct _Entry noattr)) _ptr
                                    (Tunion _Child_or_Record noattr)) _child
                                  (tptr (Tstruct _BtNode noattr)))
                                (Etempvar _t'43 (tptr (Tstruct _BtNode noattr))))))))
                      (Sset _i__1
                        (Ebinop Osub (Etempvar _i__1 tint)
                          (Econst_int (Int.repr 1) tint) tint))))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'26)
                        (Evar _currNode (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _Cursor noattr))
                                            Tnil)
                                          (tptr (Tstruct _BtNode noattr))
                                          cc_default))
                        ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                         nil))
                      (Ssequence
                        (Sset _t'42
                          (Efield
                            (Ederef
                              (Etempvar _newEntry (tptr (Tstruct _Entry noattr)))
                              (Tstruct _Entry noattr)) _key tulong))
                        (Sassign
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _t'26 (tptr (Tstruct _BtNode noattr)))
                                    (Tstruct _BtNode noattr)) _entries
                                  (tarray (Tstruct _Entry noattr) 15))
                                (Etempvar _tgtIdx__1 tint)
                                (tptr (Tstruct _Entry noattr)))
                              (Tstruct _Entry noattr)) _key tulong)
                          (Etempvar _t'42 tulong))))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'27)
                          (Evar _currNode (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _Cursor noattr))
                                              Tnil)
                                            (tptr (Tstruct _BtNode noattr))
                                            cc_default))
                          ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                           nil))
                        (Ssequence
                          (Sset _t'41
                            (Efield
                              (Efield
                                (Ederef
                                  (Etempvar _newEntry (tptr (Tstruct _Entry noattr)))
                                  (Tstruct _Entry noattr)) _ptr
                                (Tunion _Child_or_Record noattr)) _child
                              (tptr (Tstruct _BtNode noattr))))
                          (Sassign
                            (Efield
                              (Efield
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'27 (tptr (Tstruct _BtNode noattr)))
                                        (Tstruct _BtNode noattr)) _entries
                                      (tarray (Tstruct _Entry noattr) 15))
                                    (Etempvar _tgtIdx__1 tint)
                                    (tptr (Tstruct _Entry noattr)))
                                  (Tstruct _Entry noattr)) _ptr
                                (Tunion _Child_or_Record noattr)) _child
                              (tptr (Tstruct _BtNode noattr)))
                            (Etempvar _t'41 (tptr (Tstruct _BtNode noattr))))))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'28)
                            (Evar _currNode (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _Cursor noattr))
                                                Tnil)
                                              (tptr (Tstruct _BtNode noattr))
                                              cc_default))
                            ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                             nil))
                          (Ssequence
                            (Sset _t'40
                              (Efield
                                (Ederef
                                  (Etempvar _t'28 (tptr (Tstruct _BtNode noattr)))
                                  (Tstruct _BtNode noattr)) _numKeys tint))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _t'28 (tptr (Tstruct _BtNode noattr)))
                                  (Tstruct _BtNode noattr)) _numKeys tint)
                              (Ebinop Oadd (Etempvar _t'40 tint)
                                (Econst_int (Int.repr 1) tint) tint))))
                        (Ssequence
                          (Ssequence
                            (Sset _t'37
                              (Efield
                                (Ederef
                                  (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                                  (Tstruct _Cursor noattr)) _relation
                                (tptr (Tstruct _Relation noattr))))
                            (Ssequence
                              (Sset _t'38
                                (Efield
                                  (Ederef
                                    (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                                    (Tstruct _Cursor noattr)) _relation
                                  (tptr (Tstruct _Relation noattr))))
                              (Ssequence
                                (Sset _t'39
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'38 (tptr (Tstruct _Relation noattr)))
                                      (Tstruct _Relation noattr)) _numRecords
                                    tulong))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'37 (tptr (Tstruct _Relation noattr)))
                                      (Tstruct _Relation noattr)) _numRecords
                                    tulong)
                                  (Ebinop Oadd (Etempvar _t'39 tulong)
                                    (Econst_int (Int.repr 1) tint) tulong)))))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'29)
                                (Evar _currNode (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _Cursor noattr))
                                                    Tnil)
                                                  (tptr (Tstruct _BtNode noattr))
                                                  cc_default))
                                ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                                 nil))
                              (Ssequence
                                (Sset _t'36
                                  (Efield
                                    (Ederef
                                      (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                                      (Tstruct _Cursor noattr)) _level tint))
                                (Scall None
                                  (Evar _moveToKey (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _BtNode noattr))
                                                       (Tcons tulong
                                                         (Tcons
                                                           (tptr (Tstruct _Cursor noattr))
                                                           (Tcons tint Tnil))))
                                                     tvoid cc_default))
                                  ((Etempvar _t'29 (tptr (Tstruct _BtNode noattr))) ::
                                   (Etempvar _key tulong) ::
                                   (Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                                   (Etempvar _t'36 tint) :: nil))))
                            (Sreturn None))))))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'30)
                    (Evar _currNode (Tfunction
                                      (Tcons (tptr (Tstruct _Cursor noattr))
                                        Tnil) (tptr (Tstruct _BtNode noattr))
                                      cc_default))
                    ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                     nil))
                  (Scall None
                    (Evar _splitnode (Tfunction
                                       (Tcons (tptr (Tstruct _BtNode noattr))
                                         (Tcons
                                           (tptr (Tstruct _Entry noattr))
                                           (Tcons tint Tnil))) tvoid
                                       cc_default))
                    ((Etempvar _t'30 (tptr (Tstruct _BtNode noattr))) ::
                     (Etempvar _newEntry (tptr (Tstruct _Entry noattr))) ::
                     (Econst_int (Int.repr 0) tint) :: nil)))
                (Ssequence
                  (Ssequence
                    (Sset _t'35
                      (Efield
                        (Ederef
                          (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                          (Tstruct _Cursor noattr)) _level tint))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                          (Tstruct _Cursor noattr)) _level tint)
                      (Ebinop Osub (Etempvar _t'35 tint)
                        (Econst_int (Int.repr 1) tint) tint)))
                  (Ssequence
                    (Scall None
                      (Evar _putEntry (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _Cursor noattr))
                                          (Tcons
                                            (tptr (Tstruct _Entry noattr))
                                            (Tcons tulong Tnil))) tvoid
                                        cc_default))
                      ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                       (Etempvar _newEntry (tptr (Tstruct _Entry noattr))) ::
                       (Etempvar _key tulong) :: nil))
                    (Sreturn None)))))))))))
|}.

Definition v___func____14 := {|
  gvar_info := (tarray tschar 15);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_findChildIndex := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_node, (tptr (Tstruct _BtNode noattr))) :: (_key, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tulong) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
            (Tstruct _BtNode noattr)) _numKeys tint))
      (Sifthenelse (Ebinop Ogt (Etempvar _t'4 tint)
                     (Econst_int (Int.repr 0) tint) tint)
        Sskip
        (Scall None
          (Evar ___assert_fail (Tfunction
                                 (Tcons (tptr tschar)
                                   (Tcons (tptr tschar)
                                     (Tcons tuint (Tcons (tptr tschar) Tnil))))
                                 tvoid cc_default))
          ((Evar ___stringlit_10 (tarray tschar 18)) ::
           (Evar ___stringlit_1 (tarray tschar 15)) ::
           (Econst_int (Int.repr 1152) tint) ::
           (Evar ___func____14 (tarray tschar 15)) :: nil))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                    (Tstruct _BtNode noattr)) _numKeys tint))
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Etempvar _t'3 tint) tint)
                Sskip
                Sbreak))
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                          (Tstruct _BtNode noattr)) _entries
                        (tarray (Tstruct _Entry noattr) 15))
                      (Etempvar _i tint) (tptr (Tstruct _Entry noattr)))
                    (Tstruct _Entry noattr)) _key tulong))
              (Sifthenelse (Ebinop Olt (Etempvar _key tulong)
                             (Etempvar _t'2 tulong) tint)
                (Sreturn (Some (Ebinop Osub (Etempvar _i tint)
                                 (Econst_int (Int.repr 1) tint) tint)))
                Sskip)))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
              (Tstruct _BtNode noattr)) _numKeys tint))
        (Sreturn (Some (Ebinop Osub (Etempvar _t'1 tint)
                         (Econst_int (Int.repr 1) tint) tint)))))))
|}.

Definition v___func____15 := {|
  gvar_info := (tarray tschar 16);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_findRecordIndex := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_node, (tptr (Tstruct _BtNode noattr))) :: (_key, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tulong) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
            (Tstruct _BtNode noattr)) _numKeys tint))
      (Sifthenelse (Ebinop Oge (Etempvar _t'5 tint)
                     (Econst_int (Int.repr 0) tint) tint)
        Sskip
        (Scall None
          (Evar ___assert_fail (Tfunction
                                 (Tcons (tptr tschar)
                                   (Tcons (tptr tschar)
                                     (Tcons tuint (Tcons (tptr tschar) Tnil))))
                                 tvoid cc_default))
          ((Evar ___stringlit_11 (tarray tschar 19)) ::
           (Evar ___stringlit_1 (tarray tschar 15)) ::
           (Econst_int (Int.repr 1168) tint) ::
           (Evar ___func____15 (tarray tschar 16)) :: nil))))
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
              (Tstruct _BtNode noattr)) _numKeys tint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          Sskip))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                      (Tstruct _BtNode noattr)) _numKeys tint))
                (Sifthenelse (Ebinop Ole (Etempvar _i tint)
                               (Ebinop Osub (Etempvar _t'3 tint)
                                 (Econst_int (Int.repr 1) tint) tint) tint)
                  Sskip
                  Sbreak))
              (Ssequence
                (Sset _t'2
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                            (Tstruct _BtNode noattr)) _entries
                          (tarray (Tstruct _Entry noattr) 15))
                        (Etempvar _i tint) (tptr (Tstruct _Entry noattr)))
                      (Tstruct _Entry noattr)) _key tulong))
                (Sifthenelse (Ebinop Ole (Etempvar _key tulong)
                               (Etempvar _t'2 tulong) tint)
                  (Sreturn (Some (Etempvar _i tint)))
                  Sskip)))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                (Tstruct _BtNode noattr)) _numKeys tint))
          (Sreturn (Some (Etempvar _t'1 tint))))))))
|}.

Definition f_moveToKey := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_node, (tptr (Tstruct _BtNode noattr))) :: (_key, tulong) ::
                (_cursor, (tptr (Tstruct _Cursor noattr))) ::
                (_level, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_child, (tptr (Tstruct _BtNode noattr))) ::
               (_e, (tptr (Tstruct _Entry noattr))) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
            (Tstruct _Cursor noattr)) _ancestors
          (tarray (tptr (Tstruct _BtNode noattr)) 20)) (Etempvar _level tint)
        (tptr (tptr (Tstruct _BtNode noattr))))
      (tptr (Tstruct _BtNode noattr)))
    (Etempvar _node (tptr (Tstruct _BtNode noattr))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
          (Tstruct _Cursor noattr)) _level tint) (Etempvar _level tint))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
            (Tstruct _BtNode noattr)) _isLeaf tint))
      (Sifthenelse (Etempvar _t'3 tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _findRecordIndex (Tfunction
                                       (Tcons (tptr (Tstruct _BtNode noattr))
                                         (Tcons tulong Tnil)) tint
                                       cc_default))
              ((Etempvar _node (tptr (Tstruct _BtNode noattr))) ::
               (Etempvar _key tulong) :: nil))
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                      (Tstruct _Cursor noattr)) _ancestorsIdx
                    (tarray tint 20)) (Etempvar _level tint) (tptr tint))
                tint) (Etempvar _t'1 tint)))
          (Sreturn None))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _findChildIndex (Tfunction
                                      (Tcons (tptr (Tstruct _BtNode noattr))
                                        (Tcons tulong Tnil)) tint cc_default))
              ((Etempvar _node (tptr (Tstruct _BtNode noattr))) ::
               (Etempvar _key tulong) :: nil))
            (Sset _i (Etempvar _t'2 tint)))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                      (Tstruct _Cursor noattr)) _ancestorsIdx
                    (tarray tint 20)) (Etempvar _level tint) (tptr tint))
                tint) (Etempvar _i tint))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _i tint)
                             (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                             tint)
                (Sset _child
                  (Efield
                    (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                      (Tstruct _BtNode noattr)) _ptr0
                    (tptr (Tstruct _BtNode noattr))))
                (Sset _child
                  (Efield
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                              (Tstruct _BtNode noattr)) _entries
                            (tarray (Tstruct _Entry noattr) 15))
                          (Etempvar _i tint) (tptr (Tstruct _Entry noattr)))
                        (Tstruct _Entry noattr)) _ptr
                      (Tunion _Child_or_Record noattr)) _child
                    (tptr (Tstruct _BtNode noattr)))))
              (Ssequence
                (Scall None
                  (Evar _moveToKey (Tfunction
                                     (Tcons (tptr (Tstruct _BtNode noattr))
                                       (Tcons tulong
                                         (Tcons
                                           (tptr (Tstruct _Cursor noattr))
                                           (Tcons tint Tnil)))) tvoid
                                     cc_default))
                  ((Etempvar _child (tptr (Tstruct _BtNode noattr))) ::
                   (Etempvar _key tulong) ::
                   (Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                   (Ebinop Oadd (Etempvar _level tint)
                     (Econst_int (Int.repr 1) tint) tint) :: nil))
                (Sreturn None)))))))))
|}.

Definition v___func____16 := {|
  gvar_info := (tarray tschar 12);
  gvar_init := (Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_moveToFirst := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_node, (tptr (Tstruct _BtNode noattr))) ::
                (_cursor, (tptr (Tstruct _Cursor noattr))) ::
                (_level, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, (tptr (Tstruct _BtNode noattr))) ::
               nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_12 (tarray tschar 20)) ::
       (Evar ___stringlit_1 (tarray tschar 15)) ::
       (Econst_int (Int.repr 1217) tint) ::
       (Evar ___func____16 (tarray tschar 12)) :: nil)))
  (Ssequence
    (Sifthenelse (Ebinop One
                   (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      Sskip
      (Scall None
        (Evar ___assert_fail (Tfunction
                               (Tcons (tptr tschar)
                                 (Tcons (tptr tschar)
                                   (Tcons tuint (Tcons (tptr tschar) Tnil))))
                               tvoid cc_default))
        ((Evar ___stringlit_3 (tarray tschar 22)) ::
         (Evar ___stringlit_1 (tarray tschar 15)) ::
         (Econst_int (Int.repr 1218) tint) ::
         (Evar ___func____16 (tarray tschar 12)) :: nil)))
    (Ssequence
      (Sifthenelse (Ebinop Oge (Etempvar _level tint)
                     (Econst_int (Int.repr 0) tint) tint)
        Sskip
        (Scall None
          (Evar ___assert_fail (Tfunction
                                 (Tcons (tptr tschar)
                                   (Tcons (tptr tschar)
                                     (Tcons tuint (Tcons (tptr tschar) Tnil))))
                                 tvoid cc_default))
          ((Evar ___stringlit_13 (tarray tschar 11)) ::
           (Evar ___stringlit_1 (tarray tschar 15)) ::
           (Econst_int (Int.repr 1219) tint) ::
           (Evar ___func____16 (tarray tschar 12)) :: nil)))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                  (Tstruct _Cursor noattr)) _ancestors
                (tarray (tptr (Tstruct _BtNode noattr)) 20))
              (Etempvar _level tint) (tptr (tptr (Tstruct _BtNode noattr))))
            (tptr (Tstruct _BtNode noattr)))
          (Etempvar _node (tptr (Tstruct _BtNode noattr))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                (Tstruct _Cursor noattr)) _level tint)
            (Etempvar _level tint))
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                    (Tstruct _BtNode noattr)) _isLeaf tint))
              (Sifthenelse (Etempvar _t'2 tint)
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                            (Tstruct _Cursor noattr)) _ancestorsIdx
                          (tarray tint 20)) (Etempvar _level tint)
                        (tptr tint)) tint) (Econst_int (Int.repr 0) tint))
                  (Sreturn None))
                Sskip))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                        (Tstruct _Cursor noattr)) _ancestorsIdx
                      (tarray tint 20)) (Etempvar _level tint) (tptr tint))
                  tint) (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
              (Ssequence
                (Sset _t'1
                  (Efield
                    (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                      (Tstruct _BtNode noattr)) _ptr0
                    (tptr (Tstruct _BtNode noattr))))
                (Scall None
                  (Evar _moveToFirst (Tfunction
                                       (Tcons (tptr (Tstruct _BtNode noattr))
                                         (Tcons
                                           (tptr (Tstruct _Cursor noattr))
                                           (Tcons tint Tnil))) tvoid
                                       cc_default))
                  ((Etempvar _t'1 (tptr (Tstruct _BtNode noattr))) ::
                   (Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                   (Ebinop Oadd (Etempvar _level tint)
                     (Econst_int (Int.repr 1) tint) tint) :: nil))))))))))
|}.

Definition v___func____17 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_moveToLast := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_node, (tptr (Tstruct _BtNode noattr))) ::
                (_cursor, (tptr (Tstruct _Cursor noattr))) ::
                (_level, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, (tptr (Tstruct _BtNode noattr))) :: (_t'1, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    Sskip
    (Scall None
      (Evar ___assert_fail (Tfunction
                             (Tcons (tptr tschar)
                               (Tcons (tptr tschar)
                                 (Tcons tuint (Tcons (tptr tschar) Tnil))))
                             tvoid cc_default))
      ((Evar ___stringlit_12 (tarray tschar 20)) ::
       (Evar ___stringlit_1 (tarray tschar 15)) ::
       (Econst_int (Int.repr 1236) tint) ::
       (Evar ___func____17 (tarray tschar 11)) :: nil)))
  (Ssequence
    (Sifthenelse (Ebinop One
                   (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      Sskip
      (Scall None
        (Evar ___assert_fail (Tfunction
                               (Tcons (tptr tschar)
                                 (Tcons (tptr tschar)
                                   (Tcons tuint (Tcons (tptr tschar) Tnil))))
                               tvoid cc_default))
        ((Evar ___stringlit_3 (tarray tschar 22)) ::
         (Evar ___stringlit_1 (tarray tschar 15)) ::
         (Econst_int (Int.repr 1237) tint) ::
         (Evar ___func____17 (tarray tschar 11)) :: nil)))
    (Ssequence
      (Sifthenelse (Ebinop Oge (Etempvar _level tint)
                     (Econst_int (Int.repr 0) tint) tint)
        Sskip
        (Scall None
          (Evar ___assert_fail (Tfunction
                                 (Tcons (tptr tschar)
                                   (Tcons (tptr tschar)
                                     (Tcons tuint (Tcons (tptr tschar) Tnil))))
                                 tvoid cc_default))
          ((Evar ___stringlit_13 (tarray tschar 11)) ::
           (Evar ___stringlit_1 (tarray tschar 15)) ::
           (Econst_int (Int.repr 1238) tint) ::
           (Evar ___func____17 (tarray tschar 11)) :: nil)))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                  (Tstruct _Cursor noattr)) _ancestors
                (tarray (tptr (Tstruct _BtNode noattr)) 20))
              (Etempvar _level tint) (tptr (tptr (Tstruct _BtNode noattr))))
            (tptr (Tstruct _BtNode noattr)))
          (Etempvar _node (tptr (Tstruct _BtNode noattr))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                (Tstruct _Cursor noattr)) _level tint)
            (Etempvar _level tint))
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                    (Tstruct _BtNode noattr)) _isLeaf tint))
              (Sifthenelse (Etempvar _t'4 tint)
                (Ssequence
                  (Ssequence
                    (Sset _t'5
                      (Efield
                        (Ederef
                          (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                          (Tstruct _BtNode noattr)) _numKeys tint))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                              (Tstruct _Cursor noattr)) _ancestorsIdx
                            (tarray tint 20)) (Etempvar _level tint)
                          (tptr tint)) tint) (Etempvar _t'5 tint)))
                  (Sreturn None))
                Sskip))
            (Ssequence
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                      (Tstruct _BtNode noattr)) _numKeys tint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                          (Tstruct _Cursor noattr)) _ancestorsIdx
                        (tarray tint 20)) (Etempvar _level tint) (tptr tint))
                    tint)
                  (Ebinop Osub (Etempvar _t'3 tint)
                    (Econst_int (Int.repr 1) tint) tint)))
              (Ssequence
                (Ssequence
                  (Sset _t'1
                    (Efield
                      (Ederef
                        (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                        (Tstruct _BtNode noattr)) _numKeys tint))
                  (Ssequence
                    (Sset _t'2
                      (Efield
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                                  (Tstruct _BtNode noattr)) _entries
                                (tarray (Tstruct _Entry noattr) 15))
                              (Ebinop Osub (Etempvar _t'1 tint)
                                (Econst_int (Int.repr 1) tint) tint)
                              (tptr (Tstruct _Entry noattr)))
                            (Tstruct _Entry noattr)) _ptr
                          (Tunion _Child_or_Record noattr)) _child
                        (tptr (Tstruct _BtNode noattr))))
                    (Scall None
                      (Evar _moveToLast (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _BtNode noattr))
                                            (Tcons
                                              (tptr (Tstruct _Cursor noattr))
                                              (Tcons tint Tnil))) tvoid
                                          cc_default))
                      ((Etempvar _t'2 (tptr (Tstruct _BtNode noattr))) ::
                       (Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                       (Ebinop Oadd (Etempvar _level tint)
                         (Econst_int (Int.repr 1) tint) tint) :: nil))))
                (Sreturn None)))))))))
|}.

Definition f_handleDeleteBtree := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_node, (tptr (Tstruct _BtNode noattr))) ::
                (_freeRecord,
                 (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn None)
|}.

Definition f_printTree := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_node, (tptr (Tstruct _BtNode noattr))) :: (_level, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'18, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'17, tint) :: (_t'16, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'15, tint) :: (_t'14, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'13, tint) :: (_t'12, tulong) ::
               (_t'11, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'10, (tptr (Tstruct __IO_FILE noattr))) :: (_t'9, tint) ::
               (_t'8, (tptr (Tstruct __IO_FILE noattr))) :: (_t'7, tint) ::
               (_t'6, tulong) :: (_t'5, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'4, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'3, (tptr (Tstruct _BtNode noattr))) :: (_t'2, tint) ::
               (_t'1, (tptr (Tstruct _BtNode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'17
      (Efield
        (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
          (Tstruct _BtNode noattr)) _First tint))
    (Sifthenelse (Etempvar _t'17 tint)
      (Ssequence
        (Sset _t'18 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
        (Scall None
          (Evar _fprintf (Tfunction
                           (Tcons (tptr (Tstruct __IO_FILE noattr))
                             (Tcons (tptr tschar) Tnil)) tint
                           {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
          ((Etempvar _t'18 (tptr (Tstruct __IO_FILE noattr))) ::
           (Evar ___stringlit_14 (tarray tschar 7)) :: nil)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'15
        (Efield
          (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
            (Tstruct _BtNode noattr)) _Last tint))
      (Sifthenelse (Etempvar _t'15 tint)
        (Ssequence
          (Sset _t'16 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
          (Scall None
            (Evar _fprintf (Tfunction
                             (Tcons (tptr (Tstruct __IO_FILE noattr))
                               (Tcons (tptr tschar) Tnil)) tint
                             {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
            ((Etempvar _t'16 (tptr (Tstruct __IO_FILE noattr))) ::
             (Evar ___stringlit_15 (tarray tschar 6)) :: nil)))
        Sskip))
    (Ssequence
      (Ssequence
        (Sset _t'9
          (Efield
            (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
              (Tstruct _BtNode noattr)) _isLeaf tint))
        (Sifthenelse (Etempvar _t'9 tint)
          (Ssequence
            (Ssequence
              (Sset _t'14 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
              (Scall None
                (Evar _fprintf (Tfunction
                                 (Tcons (tptr (Tstruct __IO_FILE noattr))
                                   (Tcons (tptr tschar) Tnil)) tint
                                 {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                ((Etempvar _t'14 (tptr (Tstruct __IO_FILE noattr))) ::
                 (Evar ___stringlit_16 (tarray tschar 17)) ::
                 (Etempvar _level tint) :: nil)))
            (Ssequence
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Sset _t'13
                        (Efield
                          (Ederef
                            (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                            (Tstruct _BtNode noattr)) _numKeys tint))
                      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                     (Etempvar _t'13 tint) tint)
                        Sskip
                        Sbreak))
                    (Ssequence
                      (Sset _t'11
                        (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                      (Ssequence
                        (Sset _t'12
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                                    (Tstruct _BtNode noattr)) _entries
                                  (tarray (Tstruct _Entry noattr) 15))
                                (Etempvar _i tint)
                                (tptr (Tstruct _Entry noattr)))
                              (Tstruct _Entry noattr)) _key tulong))
                        (Scall None
                          (Evar _fprintf (Tfunction
                                           (Tcons
                                             (tptr (Tstruct __IO_FILE noattr))
                                             (Tcons (tptr tschar) Tnil)) tint
                                           {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                          ((Etempvar _t'11 (tptr (Tstruct __IO_FILE noattr))) ::
                           (Evar ___stringlit_17 (tarray tschar 5)) ::
                           (Etempvar _t'12 tulong) :: nil)))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Ssequence
                (Ssequence
                  (Sset _t'10
                    (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                  (Scall None
                    (Evar _fprintf (Tfunction
                                     (Tcons (tptr (Tstruct __IO_FILE noattr))
                                       (Tcons (tptr tschar) Tnil)) tint
                                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                    ((Etempvar _t'10 (tptr (Tstruct __IO_FILE noattr))) ::
                     (Evar ___stringlit_18 (tarray tschar 2)) :: nil)))
                (Sreturn None))))
          Sskip))
      (Ssequence
        (Ssequence
          (Sset _t'8 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
          (Scall None
            (Evar _fprintf (Tfunction
                             (Tcons (tptr (Tstruct __IO_FILE noattr))
                               (Tcons (tptr tschar) Tnil)) tint
                             {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
            ((Etempvar _t'8 (tptr (Tstruct __IO_FILE noattr))) ::
             (Evar ___stringlit_19 (tarray tschar 19)) ::
             (Etempvar _level tint) :: nil)))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Ssequence
                  (Sset _t'7
                    (Efield
                      (Ederef
                        (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                        (Tstruct _BtNode noattr)) _numKeys tint))
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Etempvar _t'7 tint) tint)
                    Sskip
                    Sbreak))
                (Ssequence
                  (Sset _t'5
                    (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                  (Ssequence
                    (Sset _t'6
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                                (Tstruct _BtNode noattr)) _entries
                              (tarray (Tstruct _Entry noattr) 15))
                            (Etempvar _i tint)
                            (tptr (Tstruct _Entry noattr)))
                          (Tstruct _Entry noattr)) _key tulong))
                    (Scall None
                      (Evar _fprintf (Tfunction
                                       (Tcons
                                         (tptr (Tstruct __IO_FILE noattr))
                                         (Tcons (tptr tschar) Tnil)) tint
                                       {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                      ((Etempvar _t'5 (tptr (Tstruct __IO_FILE noattr))) ::
                       (Evar ___stringlit_17 (tarray tschar 5)) ::
                       (Etempvar _t'6 tulong) :: nil)))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Ssequence
              (Sset _t'4 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
              (Scall None
                (Evar _fprintf (Tfunction
                                 (Tcons (tptr (Tstruct __IO_FILE noattr))
                                   (Tcons (tptr tschar) Tnil)) tint
                                 {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                ((Etempvar _t'4 (tptr (Tstruct __IO_FILE noattr))) ::
                 (Evar ___stringlit_18 (tarray tschar 2)) :: nil)))
            (Ssequence
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                      (Tstruct _BtNode noattr)) _ptr0
                    (tptr (Tstruct _BtNode noattr))))
                (Scall None
                  (Evar _printTree (Tfunction
                                     (Tcons (tptr (Tstruct _BtNode noattr))
                                       (Tcons tint Tnil)) tvoid cc_default))
                  ((Etempvar _t'3 (tptr (Tstruct _BtNode noattr))) ::
                   (Ebinop Oadd (Etempvar _level tint)
                     (Econst_int (Int.repr 1) tint) tint) :: nil)))
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Sset _t'2
                        (Efield
                          (Ederef
                            (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                            (Tstruct _BtNode noattr)) _numKeys tint))
                      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                     (Etempvar _t'2 tint) tint)
                        Sskip
                        Sbreak))
                    (Ssequence
                      (Sset _t'1
                        (Efield
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _node (tptr (Tstruct _BtNode noattr)))
                                    (Tstruct _BtNode noattr)) _entries
                                  (tarray (Tstruct _Entry noattr) 15))
                                (Etempvar _i tint)
                                (tptr (Tstruct _Entry noattr)))
                              (Tstruct _Entry noattr)) _ptr
                            (Tunion _Child_or_Record noattr)) _child
                          (tptr (Tstruct _BtNode noattr))))
                      (Scall None
                        (Evar _printTree (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _BtNode noattr))
                                             (Tcons tint Tnil)) tvoid
                                           cc_default))
                        ((Etempvar _t'1 (tptr (Tstruct _BtNode noattr))) ::
                         (Ebinop Oadd (Etempvar _level tint)
                           (Econst_int (Int.repr 1) tint) tint) :: nil))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint)))))))))))
|}.

Definition f_printCursor := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cursor, (tptr (Tstruct _Cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                    {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
    ((Evar ___stringlit_20 (tarray tschar 9)) :: nil))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                  (Tstruct _Cursor noattr)) _level tint))
            (Sifthenelse (Ebinop Ole (Etempvar _i tint) (Etempvar _t'2 tint)
                           tint)
              Sskip
              Sbreak))
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _cursor (tptr (Tstruct _Cursor noattr)))
                      (Tstruct _Cursor noattr)) _ancestorsIdx
                    (tarray tint 20)) (Etempvar _i tint) (tptr tint)) tint))
            (Scall None
              (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                              {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
              ((Evar ___stringlit_21 (tarray tschar 4)) ::
               (Etempvar _t'1 tint) :: nil))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Scall None
      (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                      {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
      ((Evar ___stringlit_18 (tarray tschar 2)) :: nil))))
|}.

Definition composites : list composite_definition :=
(Composite __IO_marker Struct
   ((__next, (tptr (Tstruct __IO_marker noattr))) ::
    (__sbuf, (tptr (Tstruct __IO_FILE noattr))) :: (__pos, tint) :: nil)
   noattr ::
 Composite __IO_FILE Struct
   ((__flags, tint) :: (__IO_read_ptr, (tptr tschar)) ::
    (__IO_read_end, (tptr tschar)) :: (__IO_read_base, (tptr tschar)) ::
    (__IO_write_base, (tptr tschar)) :: (__IO_write_ptr, (tptr tschar)) ::
    (__IO_write_end, (tptr tschar)) :: (__IO_buf_base, (tptr tschar)) ::
    (__IO_buf_end, (tptr tschar)) :: (__IO_save_base, (tptr tschar)) ::
    (__IO_backup_base, (tptr tschar)) :: (__IO_save_end, (tptr tschar)) ::
    (__markers, (tptr (Tstruct __IO_marker noattr))) ::
    (__chain, (tptr (Tstruct __IO_FILE noattr))) :: (__fileno, tint) ::
    (__flags2, tint) :: (__old_offset, tlong) :: (__cur_column, tushort) ::
    (__vtable_offset, tschar) :: (__shortbuf, (tarray tschar 1)) ::
    (__lock, (tptr tvoid)) :: (__offset, tlong) :: (___pad1, (tptr tvoid)) ::
    (___pad2, (tptr tvoid)) :: (___pad3, (tptr tvoid)) ::
    (___pad4, (tptr tvoid)) :: (___pad5, tulong) :: (__mode, tint) ::
    (__unused2, (tarray tschar 20)) :: nil)
   noattr ::
 Composite _Relation Struct
   ((_root, (tptr (Tstruct _BtNode noattr))) :: (_numRecords, tulong) ::
    (_depth, tint) :: nil)
   noattr ::
 Composite _Child_or_Record Union
   ((_child, (tptr (Tstruct _BtNode noattr))) :: (_record, (tptr tvoid)) ::
    nil)
   noattr ::
 Composite _Entry Struct
   ((_key, tulong) :: (_ptr, (Tunion _Child_or_Record noattr)) :: nil)
   noattr ::
 Composite _BtNode Struct
   ((_isLeaf, tint) :: (_First, tint) :: (_Last, tint) :: (_numKeys, tint) ::
    (_ptr0, (tptr (Tstruct _BtNode noattr))) ::
    (_entries, (tarray (Tstruct _Entry noattr) 15)) :: nil)
   noattr ::
 Composite _Cursor Struct
   ((_relation, (tptr (Tstruct _Relation noattr))) :: (_level, tint) ::
    (_ancestorsIdx, (tarray tint 20)) ::
    (_ancestors, (tarray (tptr (Tstruct _BtNode noattr)) 20)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_12, Gvar v___stringlit_12) ::
 (___stringlit_13, Gvar v___stringlit_13) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_14, Gvar v___stringlit_14) ::
 (___stringlit_17, Gvar v___stringlit_17) ::
 (___stringlit_9, Gvar v___stringlit_9) ::
 (___stringlit_11, Gvar v___stringlit_11) ::
 (___stringlit_20, Gvar v___stringlit_20) ::
 (___stringlit_15, Gvar v___stringlit_15) ::
 (___stringlit_16, Gvar v___stringlit_16) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_18, Gvar v___stringlit_18) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_10, Gvar v___stringlit_10) ::
 (___stringlit_21, Gvar v___stringlit_21) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_8, Gvar v___stringlit_8) ::
 (___stringlit_19, Gvar v___stringlit_19) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tlong :: nil) None
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
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tschar) (Tcons tint Tnil)) tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tuint
     cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons (tptr tvoid) (Tcons tulong Tnil)) (tptr tvoid) cc_default)) ::
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
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
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
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
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
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tuint) Tnil) tuint
     cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) None
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
                     (AST.Tlong :: AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     None cc_default))
     (Tcons (tptr tschar)
       (Tcons (tptr tschar) (Tcons tuint (Tcons (tptr tschar) Tnil)))) tvoid
     cc_default)) :: (_stderr, Gvar v_stderr) ::
 (_fprintf,
   Gfun(External (EF_external "fprintf"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr (Tstruct __IO_FILE noattr)) (Tcons (tptr tschar) Tnil))
     tint {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_entryIndex, Gfun(Internal f_entryIndex)) ::
 (_currNode, Gfun(Internal f_currNode)) ::
 (_isValid, Gfun(Internal f_isValid)) ::
 (_isFirst, Gfun(Internal f_isFirst)) ::
 (_RL_NewRelation, Gfun(Internal f_RL_NewRelation)) ::
 (___func__, Gvar v___func__) ::
 (_RL_DeleteRelation, Gfun(Internal f_RL_DeleteRelation)) ::
 (___func____1, Gvar v___func____1) ::
 (_RL_NewCursor, Gfun(Internal f_RL_NewCursor)) ::
 (_RL_FreeCursor, Gfun(Internal f_RL_FreeCursor)) ::
 (___func____2, Gvar v___func____2) ::
 (_RL_CursorIsValid, Gfun(Internal f_RL_CursorIsValid)) ::
 (___func____3, Gvar v___func____3) ::
 (_RL_PutRecord, Gfun(Internal f_RL_PutRecord)) ::
 (_isNodeParent, Gfun(Internal f_isNodeParent)) ::
 (_AscendToParent, Gfun(Internal f_AscendToParent)) ::
 (___func____4, Gvar v___func____4) ::
 (_RL_GetRecord, Gfun(Internal f_RL_GetRecord)) ::
 (___func____5, Gvar v___func____5) ::
 (_RL_GetKey, Gfun(Internal f_RL_GetKey)) ::
 (___func____6, Gvar v___func____6) ::
 (_goToKey, Gfun(Internal f_goToKey)) ::
 (_RL_MoveToKey, Gfun(Internal f_RL_MoveToKey)) ::
 (_RL_DeleteRecord, Gfun(Internal f_RL_DeleteRecord)) ::
 (___func____7, Gvar v___func____7) ::
 (_RL_MoveToFirst, Gfun(Internal f_RL_MoveToFirst)) ::
 (_lastpointer, Gfun(Internal f_lastpointer)) ::
 (_firstpointer, Gfun(Internal f_firstpointer)) ::
 (_moveToNext, Gfun(Internal f_moveToNext)) ::
 (_moveToPrev, Gfun(Internal f_moveToPrev)) ::
 (_RL_MoveToNext, Gfun(Internal f_RL_MoveToNext)) ::
 (_RL_MoveToPrevious, Gfun(Internal f_RL_MoveToPrevious)) ::
 (_RL_MoveToNextValid, Gfun(Internal f_RL_MoveToNextValid)) ::
 (_RL_MoveToPreviousNotFirst, Gfun(Internal f_RL_MoveToPreviousNotFirst)) ::
 (___func____8, Gvar v___func____8) ::
 (_RL_IsEmpty, Gfun(Internal f_RL_IsEmpty)) ::
 (___func____9, Gvar v___func____9) ::
 (_RL_NumRecords, Gfun(Internal f_RL_NumRecords)) ::
 (___func____10, Gvar v___func____10) ::
 (_RL_PrintTree, Gfun(Internal f_RL_PrintTree)) ::
 (___func____11, Gvar v___func____11) ::
 (_RL_PrintCursor, Gfun(Internal f_RL_PrintCursor)) ::
 (_createNewNode, Gfun(Internal f_createNewNode)) ::
 (___func____12, Gvar v___func____12) ::
 (_splitnode, Gfun(Internal f_splitnode)) ::
 (___func____13, Gvar v___func____13) ::
 (_putEntry, Gfun(Internal f_putEntry)) ::
 (___func____14, Gvar v___func____14) ::
 (_findChildIndex, Gfun(Internal f_findChildIndex)) ::
 (___func____15, Gvar v___func____15) ::
 (_findRecordIndex, Gfun(Internal f_findRecordIndex)) ::
 (_moveToKey, Gfun(Internal f_moveToKey)) ::
 (___func____16, Gvar v___func____16) ::
 (_moveToFirst, Gfun(Internal f_moveToFirst)) ::
 (___func____17, Gvar v___func____17) ::
 (_moveToLast, Gfun(Internal f_moveToLast)) ::
 (_handleDeleteBtree, Gfun(Internal f_handleDeleteBtree)) ::
 (_printTree, Gfun(Internal f_printTree)) ::
 (_printCursor, Gfun(Internal f_printCursor)) :: nil).

Definition public_idents : list ident :=
(_RL_PrintCursor :: _RL_PrintTree :: _RL_NumRecords :: _RL_IsEmpty ::
 _RL_MoveToPreviousNotFirst :: _RL_MoveToNextValid :: _RL_MoveToPrevious ::
 _RL_MoveToNext :: _firstpointer :: _lastpointer :: _RL_MoveToFirst ::
 _RL_DeleteRecord :: _RL_MoveToKey :: _RL_GetKey :: _RL_GetRecord ::
 _AscendToParent :: _RL_PutRecord :: _RL_CursorIsValid :: _RL_FreeCursor ::
 _RL_NewCursor :: _RL_DeleteRelation :: _RL_NewRelation :: _isFirst ::
 _isValid :: _currNode :: _entryIndex :: _surely_malloc :: _exit ::
 _malloc :: _free :: _printf :: _fprintf :: _stderr :: ___assert_fail ::
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


