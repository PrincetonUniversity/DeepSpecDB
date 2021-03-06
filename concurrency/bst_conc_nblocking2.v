From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.5"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "bst_conc_nblocking2.c"%string.
  Definition normalized := true.
End Info.

Definition _GET_FLAG : ident := 104%positive.
Definition _IS_NULL : ident := 108%positive.
Definition _SET_FLAG : ident := 102%positive.
Definition _SET_NULL : ident := 106%positive.
Definition _UNFLAG : ident := 105%positive.
Definition ___builtin_annot : ident := 35%positive.
Definition ___builtin_annot_intval : ident := 36%positive.
Definition ___builtin_bswap : ident := 29%positive.
Definition ___builtin_bswap16 : ident := 31%positive.
Definition ___builtin_bswap32 : ident := 30%positive.
Definition ___builtin_bswap64 : ident := 61%positive.
Definition ___builtin_clz : ident := 62%positive.
Definition ___builtin_clzl : ident := 63%positive.
Definition ___builtin_clzll : ident := 64%positive.
Definition ___builtin_ctz : ident := 65%positive.
Definition ___builtin_ctzl : ident := 66%positive.
Definition ___builtin_ctzll : ident := 67%positive.
Definition ___builtin_debug : ident := 79%positive.
Definition ___builtin_fabs : ident := 32%positive.
Definition ___builtin_fmadd : ident := 70%positive.
Definition ___builtin_fmax : ident := 68%positive.
Definition ___builtin_fmin : ident := 69%positive.
Definition ___builtin_fmsub : ident := 71%positive.
Definition ___builtin_fnmadd : ident := 72%positive.
Definition ___builtin_fnmsub : ident := 73%positive.
Definition ___builtin_fsqrt : ident := 33%positive.
Definition ___builtin_membar : ident := 37%positive.
Definition ___builtin_memcpy_aligned : ident := 34%positive.
Definition ___builtin_nop : ident := 78%positive.
Definition ___builtin_read16_reversed : ident := 74%positive.
Definition ___builtin_read32_reversed : ident := 75%positive.
Definition ___builtin_va_arg : ident := 39%positive.
Definition ___builtin_va_copy : ident := 40%positive.
Definition ___builtin_va_end : ident := 41%positive.
Definition ___builtin_va_start : ident := 38%positive.
Definition ___builtin_write16_reversed : ident := 76%positive.
Definition ___builtin_write32_reversed : ident := 77%positive.
Definition ___compcert_i64_dtos : ident := 46%positive.
Definition ___compcert_i64_dtou : ident := 47%positive.
Definition ___compcert_i64_sar : ident := 58%positive.
Definition ___compcert_i64_sdiv : ident := 52%positive.
Definition ___compcert_i64_shl : ident := 56%positive.
Definition ___compcert_i64_shr : ident := 57%positive.
Definition ___compcert_i64_smod : ident := 54%positive.
Definition ___compcert_i64_smulh : ident := 59%positive.
Definition ___compcert_i64_stod : ident := 48%positive.
Definition ___compcert_i64_stof : ident := 50%positive.
Definition ___compcert_i64_udiv : ident := 53%positive.
Definition ___compcert_i64_umod : ident := 55%positive.
Definition ___compcert_i64_umulh : ident := 60%positive.
Definition ___compcert_i64_utod : ident := 49%positive.
Definition ___compcert_i64_utof : ident := 51%positive.
Definition ___compcert_va_composite : ident := 45%positive.
Definition ___compcert_va_float64 : ident := 44%positive.
Definition ___compcert_va_int32 : ident := 42%positive.
Definition ___compcert_va_int64 : ident := 43%positive.
Definition ___dummy : ident := 1%positive.
Definition ___pthread_cond_t : ident := 3%positive.
Definition ___pthread_mutex_t : ident := 2%positive.
Definition ___stringlit_1 : ident := 145%positive.
Definition ___stringlit_10 : ident := 165%positive.
Definition ___stringlit_11 : ident := 166%positive.
Definition ___stringlit_12 : ident := 167%positive.
Definition ___stringlit_13 : ident := 168%positive.
Definition ___stringlit_14 : ident := 169%positive.
Definition ___stringlit_15 : ident := 171%positive.
Definition ___stringlit_16 : ident := 172%positive.
Definition ___stringlit_17 : ident := 173%positive.
Definition ___stringlit_18 : ident := 180%positive.
Definition ___stringlit_19 : ident := 181%positive.
Definition ___stringlit_2 : ident := 146%positive.
Definition ___stringlit_20 : ident := 182%positive.
Definition ___stringlit_21 : ident := 183%positive.
Definition ___stringlit_22 : ident := 184%positive.
Definition ___stringlit_23 : ident := 185%positive.
Definition ___stringlit_3 : ident := 147%positive.
Definition ___stringlit_4 : ident := 158%positive.
Definition ___stringlit_5 : ident := 159%positive.
Definition ___stringlit_6 : ident := 160%positive.
Definition ___stringlit_7 : ident := 161%positive.
Definition ___stringlit_8 : ident := 162%positive.
Definition ___stringlit_9 : ident := 164%positive.
Definition _acquire : ident := 85%positive.
Definition _add : ident := 148%positive.
Definition _add_to_hp_list : ident := 112%positive.
Definition _address : ident := 113%positive.
Definition _arg_struct : ident := 28%positive.
Definition _args : ident := 156%positive.
Definition _arguments : ident := 157%positive.
Definition _atom_CAS : ident := 92%positive.
Definition _atom_int : ident := 18%positive.
Definition _atom_load : ident := 91%positive.
Definition _atom_ptr : ident := 8%positive.
Definition _atomic_CAS_ptr : ident := 95%positive.
Definition _atomic_load_ptr : ident := 93%positive.
Definition _atomic_store_ptr : ident := 94%positive.
Definition _auxRoot : ident := 133%positive.
Definition _base_root : ident := 100%positive.
Definition _cas_op : ident := 121%positive.
Definition _child_cas_operation : ident := 17%positive.
Definition _cond : ident := 97%positive.
Definition _curr : ident := 119%positive.
Definition _curr_key : ident := 135%positive.
Definition _curr_op : ident := 131%positive.
Definition _curr_real : ident := 153%positive.
Definition _delete : ident := 155%positive.
Definition _dest : ident := 20%positive.
Definition _dest_op : ident := 21%positive.
Definition _expected : ident := 15%positive.
Definition _find : ident := 140%positive.
Definition _flag : ident := 103%positive.
Definition _free : ident := 81%positive.
Definition _freelock2 : ident := 86%positive.
Definition _help : ident := 132%positive.
Definition _helpChildCAS : ident := 116%positive.
Definition _helpMarked : ident := 122%positive.
Definition _helpRelocate : ident := 130%positive.
Definition _hp : ident := 98%positive.
Definition _hp_off : ident := 99%positive.
Definition _i : ident := 127%positive.
Definition _i__1 : ident := 128%positive.
Definition _i__2 : ident := 176%positive.
Definition _i__3 : ident := 177%positive.
Definition _i__4 : ident := 178%positive.
Definition _i__5 : ident := 179%positive.
Definition _is_left : ident := 14%positive.
Definition _key : ident := 7%positive.
Definition _l : ident := 26%positive.
Definition _last_right : ident := 137%positive.
Definition _last_right_op : ident := 138%positive.
Definition _left : ident := 11%positive.
Definition _left_child : ident := 142%positive.
Definition _list : ident := 5%positive.
Definition _main : ident := 186%positive.
Definition _make_atomic : ident := 89%positive.
Definition _make_atomic_ptr : ident := 90%positive.
Definition _makelock : ident := 84%positive.
Definition _newNode : ident := 141%positive.
Definition _new_ref : ident := 120%positive.
Definition _next : ident := 136%positive.
Definition _node : ident := 111%positive.
Definition _old : ident := 144%positive.
Definition _old_op : ident := 125%positive.
Definition _op : ident := 10%positive.
Definition _op_cast : ident := 115%positive.
Definition _pred : ident := 117%positive.
Definition _pred_op : ident := 118%positive.
Definition _pred_real : ident := 154%positive.
Definition _printf : ident := 80%positive.
Definition _pthread_cond_broadcast : ident := 82%positive.
Definition _pthread_cond_wait : ident := 83%positive.
Definition _ptr : ident := 4%positive.
Definition _real_dest : ident := 124%positive.
Definition _release2 : ident := 87%positive.
Definition _reloc_op : ident := 151%positive.
Definition _relocate_operation : ident := 25%positive.
Definition _remove_key : ident := 22%positive.
Definition _replace : ident := 150%positive.
Definition _replace_key : ident := 23%positive.
Definition _replace_op : ident := 149%positive.
Definition _replace_real : ident := 152%positive.
Definition _replace_value : ident := 24%positive.
Definition _result : ident := 129%positive.
Definition _right : ident := 12%positive.
Definition _right_child : ident := 143%positive.
Definition _root : ident := 175%positive.
Definition _rp : ident := 101%positive.
Definition _seen_state : ident := 123%positive.
Definition _spawn : ident := 88%positive.
Definition _state : ident := 19%positive.
Definition _success : ident := 126%positive.
Definition _surely_malloc : ident := 96%positive.
Definition _tail : ident := 6%positive.
Definition _tb : ident := 109%positive.
Definition _thread_func_add : ident := 163%positive.
Definition _thread_func_find : ident := 170%positive.
Definition _thread_func_remove : ident := 174%positive.
Definition _thread_lock : ident := 110%positive.
Definition _thread_num : ident := 27%positive.
Definition _tp : ident := 114%positive.
Definition _tp_next : ident := 139%positive.
Definition _tree : ident := 13%positive.
Definition _update : ident := 16%positive.
Definition _v : ident := 134%positive.
Definition _val : ident := 107%positive.
Definition _value : ident := 9%positive.
Definition _t'1 : ident := 187%positive.
Definition _t'10 : ident := 196%positive.
Definition _t'11 : ident := 197%positive.
Definition _t'12 : ident := 198%positive.
Definition _t'13 : ident := 199%positive.
Definition _t'14 : ident := 200%positive.
Definition _t'15 : ident := 201%positive.
Definition _t'16 : ident := 202%positive.
Definition _t'17 : ident := 203%positive.
Definition _t'18 : ident := 204%positive.
Definition _t'19 : ident := 205%positive.
Definition _t'2 : ident := 188%positive.
Definition _t'20 : ident := 206%positive.
Definition _t'21 : ident := 207%positive.
Definition _t'22 : ident := 208%positive.
Definition _t'23 : ident := 209%positive.
Definition _t'24 : ident := 210%positive.
Definition _t'25 : ident := 211%positive.
Definition _t'26 : ident := 212%positive.
Definition _t'27 : ident := 213%positive.
Definition _t'28 : ident := 214%positive.
Definition _t'29 : ident := 215%positive.
Definition _t'3 : ident := 189%positive.
Definition _t'30 : ident := 216%positive.
Definition _t'31 : ident := 217%positive.
Definition _t'32 : ident := 218%positive.
Definition _t'33 : ident := 219%positive.
Definition _t'34 : ident := 220%positive.
Definition _t'35 : ident := 221%positive.
Definition _t'36 : ident := 222%positive.
Definition _t'37 : ident := 223%positive.
Definition _t'38 : ident := 224%positive.
Definition _t'39 : ident := 225%positive.
Definition _t'4 : ident := 190%positive.
Definition _t'40 : ident := 226%positive.
Definition _t'41 : ident := 227%positive.
Definition _t'42 : ident := 228%positive.
Definition _t'43 : ident := 229%positive.
Definition _t'5 : ident := 191%positive.
Definition _t'6 : ident := 192%positive.
Definition _t'7 : ident := 193%positive.
Definition _t'8 : ident := 194%positive.
Definition _t'9 : ident := 195%positive.

Definition v___stringlit_8 := {|
  gvar_info := (tarray tschar 40);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 123) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 125) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_20 := {|
  gvar_info := (tarray tschar 27);
  gvar_init := (Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 123) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 125) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 123) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 125) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_10 := {|
  gvar_info := (tarray tschar 37);
  gvar_init := (Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 123) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 125) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 123) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 125) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_18 := {|
  gvar_info := (tarray tschar 17);
  gvar_init := (Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_17 := {|
  gvar_info := (tarray tschar 32);
  gvar_init := (Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 123) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 125) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_16 := {|
  gvar_info := (tarray tschar 57);
  gvar_init := (Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 123) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 125) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 123) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 125) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 17);
  gvar_init := (Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_22 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 86) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_12 := {|
  gvar_info := (tarray tschar 17);
  gvar_init := (Init_int8 (Int.repr 86) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_21 := {|
  gvar_info := (tarray tschar 26);
  gvar_init := (Init_int8 (Int.repr 123) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 125) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 123) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 125) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 37);
  gvar_init := (Init_int8 (Int.repr 86) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_13 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 123) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 125) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_11 := {|
  gvar_info := (tarray tschar 46);
  gvar_init := (Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 123) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 125) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 123) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 125) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 33);
  gvar_init := (Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 123) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 125) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 123) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 125) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_14 := {|
  gvar_info := (tarray tschar 40);
  gvar_init := (Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 123) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 125) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_7 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 123) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 125) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_23 := {|
  gvar_info := (tarray tschar 23);
  gvar_init := (Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_15 := {|
  gvar_info := (tarray tschar 29);
  gvar_init := (Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 123) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 125) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 18);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 123) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 125) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_9 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 123) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 125) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_19 := {|
  gvar_info := (tarray tschar 23);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_cond := {|
  gvar_info := (tptr (Tstruct ___pthread_cond_t noattr));
  gvar_init := (Init_int32 (Int.repr 21) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_hp := {|
  gvar_info := (tarray (tptr (Tstruct _atom_ptr noattr)) 150);
  gvar_init := (Init_space 600 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_hp_off := {|
  gvar_info := (tarray tint 15);
  gvar_init := (Init_space 60 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_base_root := {|
  gvar_info := (tptr (Tstruct _atom_ptr noattr));
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_rp := {|
  gvar_info := (tarray (tptr (Tstruct _list noattr)) 15);
  gvar_init := (Init_int32 (Int.repr 0) :: Init_space 56 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_SET_FLAG := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_ptr, (tptr tvoid)) :: (_state, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sset _ptr
    (Ecast
      (Ebinop Oor (Ecast (Etempvar _ptr (tptr tvoid)) tuint)
        (Ecast (Etempvar _state tint) tuint) tuint) (tptr tvoid)))
  (Sreturn (Some (Etempvar _ptr (tptr tvoid)))))
|}.

Definition f_GET_FLAG := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ptr, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_flag, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _flag
    (Ebinop Oand (Ecast (Etempvar _ptr (tptr tvoid)) tuint)
      (Ecast (Econst_int (Int.repr 3) tint) tuint) tuint))
  (Sreturn (Some (Etempvar _flag tint))))
|}.

Definition f_UNFLAG := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_ptr, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sset _ptr
    (Ecast
      (Ebinop Oand (Ecast (Etempvar _ptr (tptr tvoid)) tuint)
        (Eunop Onotint (Ecast (Econst_int (Int.repr 3) tint) tuint) tuint)
        tuint) (tptr tvoid)))
  (Sreturn (Some (Etempvar _ptr (tptr tvoid)))))
|}.

Definition f_SET_NULL := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_ptr, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sset _ptr
    (Ecast
      (Ebinop Oor (Ecast (Etempvar _ptr (tptr tvoid)) tuint)
        (Ecast (Econst_int (Int.repr 1) tint) tuint) tuint) (tptr tvoid)))
  (Sreturn (Some (Etempvar _ptr (tptr tvoid)))))
|}.

Definition f_IS_NULL := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ptr, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_val, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _val
    (Ebinop Oand (Ecast (Etempvar _ptr (tptr tvoid)) tuint)
      (Ecast (Econst_int (Int.repr 1) tint) tuint) tuint))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _val tint)
                   (Econst_int (Int.repr 1) tint) tint)
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))
      Sskip)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition v_tb := {|
  gvar_info := (tptr (Tstruct _atom_ptr noattr));
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_thread_lock := {|
  gvar_info := (tarray (tarray (tptr tvoid) 2) 15);
  gvar_init := (Init_space 120 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_add_to_hp_list := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_thread_num, tint) ::
                (_node, (tptr (Tstruct _tree noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, (tptr (Tstruct _atom_ptr noattr))) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Ederef
        (Ebinop Oadd (Evar _hp_off (tarray tint 15))
          (Etempvar _thread_num tint) (tptr tint)) tint))
    (Ssequence
      (Sset _t'4
        (Ederef
          (Ebinop Oadd
            (Evar _hp (tarray (tptr (Tstruct _atom_ptr noattr)) 150))
            (Etempvar _t'3 tint) (tptr (tptr (Tstruct _atom_ptr noattr))))
          (tptr (Tstruct _atom_ptr noattr))))
      (Scall None
        (Evar _atomic_store_ptr (Tfunction
                                  (Tcons (tptr (Tstruct _atom_ptr noattr))
                                    (Tcons (tptr tvoid) Tnil)) tvoid
                                  cc_default))
        ((Etempvar _t'4 (tptr (Tstruct _atom_ptr noattr))) ::
         (Etempvar _node (tptr (Tstruct _tree noattr))) :: nil))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Evar _hp_off (tarray tint 15))
            (Etempvar _thread_num tint) (tptr tint)) tint))
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _hp_off (tarray tint 15))
            (Etempvar _thread_num tint) (tptr tint)) tint)
        (Ebinop Oadd (Etempvar _t'2 tint) (Econst_int (Int.repr 1) tint)
          tint)))
    (Ssequence
      (Sset _t'1
        (Ederef
          (Ebinop Oadd (Evar _hp_off (tarray tint 15))
            (Etempvar _thread_num tint) (tptr tint)) tint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                     (Ebinop Oadd
                       (Ebinop Omul (Etempvar _thread_num tint)
                         (Econst_int (Int.repr 10) tint) tint)
                       (Econst_int (Int.repr 10) tint) tint) tint)
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _hp_off (tarray tint 15))
              (Etempvar _thread_num tint) (tptr tint)) tint)
          (Ebinop Omul (Etempvar _thread_num tint)
            (Econst_int (Int.repr 10) tint) tint))
        Sskip))))
|}.

Definition f_helpChildCAS := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_op, (tptr (Tstruct _child_cas_operation noattr))) ::
                (_dest, (tptr (Tstruct _tree noattr))) ::
                (_thread_num, tint) :: nil);
  fn_vars := ((_tp, (tptr tvoid)) :: (_op_cast, (tptr tvoid)) :: nil);
  fn_temps := ((_address, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr tvoid)) ::
               (_t'2, tint) :: (_t'1, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'10, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'9, (tptr (Tstruct _atom_ptr noattr))) :: (_t'8, tint) ::
               (_t'7, (tptr (Tstruct _tree noattr))) ::
               (_t'6, (tptr (Tstruct _tree noattr))) ::
               (_t'5, (tptr (Tstruct _atom_ptr noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'8
        (Efield
          (Ederef (Etempvar _op (tptr (Tstruct _child_cas_operation noattr)))
            (Tstruct _child_cas_operation noattr)) _is_left tint))
      (Sifthenelse (Etempvar _t'8 tint)
        (Ssequence
          (Sset _t'10
            (Efield
              (Ederef (Etempvar _dest (tptr (Tstruct _tree noattr)))
                (Tstruct _tree noattr)) _left
              (tptr (Tstruct _atom_ptr noattr))))
          (Sset _t'1
            (Ecast (Etempvar _t'10 (tptr (Tstruct _atom_ptr noattr)))
              (tptr (Tstruct _atom_ptr noattr)))))
        (Ssequence
          (Sset _t'9
            (Efield
              (Ederef (Etempvar _dest (tptr (Tstruct _tree noattr)))
                (Tstruct _tree noattr)) _right
              (tptr (Tstruct _atom_ptr noattr))))
          (Sset _t'1
            (Ecast (Etempvar _t'9 (tptr (Tstruct _atom_ptr noattr)))
              (tptr (Tstruct _atom_ptr noattr)))))))
    (Sset _address (Etempvar _t'1 (tptr (Tstruct _atom_ptr noattr)))))
  (Ssequence
    (Ssequence
      (Sset _t'7
        (Efield
          (Ederef (Etempvar _op (tptr (Tstruct _child_cas_operation noattr)))
            (Tstruct _child_cas_operation noattr)) _expected
          (tptr (Tstruct _tree noattr))))
      (Sassign (Evar _tp (tptr tvoid))
        (Etempvar _t'7 (tptr (Tstruct _tree noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'6
          (Efield
            (Ederef
              (Etempvar _op (tptr (Tstruct _child_cas_operation noattr)))
              (Tstruct _child_cas_operation noattr)) _update
            (tptr (Tstruct _tree noattr))))
        (Scall (Some _t'2)
          (Evar _atomic_CAS_ptr (Tfunction
                                  (Tcons (tptr (Tstruct _atom_ptr noattr))
                                    (Tcons (tptr (tptr tvoid))
                                      (Tcons (tptr tvoid) Tnil))) tint
                                  cc_default))
          ((Etempvar _address (tptr (Tstruct _atom_ptr noattr))) ::
           (Eaddrof (Evar _tp (tptr tvoid)) (tptr (tptr tvoid))) ::
           (Etempvar _t'6 (tptr (Tstruct _tree noattr))) :: nil)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _SET_FLAG (Tfunction (Tcons (tptr tvoid) (Tcons tint Tnil))
                              (tptr tvoid) cc_default))
            ((Etempvar _op (tptr (Tstruct _child_cas_operation noattr))) ::
             (Econst_int (Int.repr 2) tint) :: nil))
          (Sassign (Evar _op_cast (tptr tvoid)) (Etempvar _t'3 (tptr tvoid))))
        (Ssequence
          (Scall (Some _t'4)
            (Evar _SET_FLAG (Tfunction (Tcons (tptr tvoid) (Tcons tint Tnil))
                              (tptr tvoid) cc_default))
            ((Etempvar _op (tptr (Tstruct _child_cas_operation noattr))) ::
             (Econst_int (Int.repr 0) tint) :: nil))
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _dest (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _op
                (tptr (Tstruct _atom_ptr noattr))))
            (Scall None
              (Evar _atomic_CAS_ptr (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _atom_ptr noattr))
                                        (Tcons (tptr (tptr tvoid))
                                          (Tcons (tptr tvoid) Tnil))) tint
                                      cc_default))
              ((Etempvar _t'5 (tptr (Tstruct _atom_ptr noattr))) ::
               (Eaddrof (Evar _op_cast (tptr tvoid)) (tptr (tptr tvoid))) ::
               (Etempvar _t'4 (tptr tvoid)) :: nil))))))))
|}.

Definition f_helpMarked := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pred, (tptr (Tstruct _tree noattr))) ::
                (_pred_op, (tptr tvoid)) ::
                (_curr, (tptr (Tstruct _tree noattr))) ::
                (_thread_num, tint) :: nil);
  fn_vars := ((_pred_op, (tptr tvoid)) :: nil);
  fn_temps := ((_new_ref, (tptr (Tstruct _tree noattr))) ::
               (_cas_op, (tptr (Tstruct _child_cas_operation noattr))) ::
               (_t'9, tint) :: (_t'8, (tptr tvoid)) ::
               (_t'7, (tptr tvoid)) :: (_t'6, (tptr tvoid)) ::
               (_t'5, tint) :: (_t'4, (tptr tvoid)) :: (_t'3, tint) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'15, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'14, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'13, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'12, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'11, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'10, (tptr (Tstruct _atom_ptr noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _pred_op (tptr tvoid)) (Etempvar _pred_op (tptr tvoid)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'15
          (Efield
            (Ederef (Etempvar _curr (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _left
            (tptr (Tstruct _atom_ptr noattr))))
        (Scall (Some _t'5)
          (Evar _IS_NULL (Tfunction (Tcons (tptr tvoid) Tnil) tint
                           cc_default))
          ((Etempvar _t'15 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
      (Sifthenelse (Etempvar _t'5 tint)
        (Ssequence
          (Ssequence
            (Sset _t'14
              (Efield
                (Ederef (Etempvar _curr (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _right
                (tptr (Tstruct _atom_ptr noattr))))
            (Scall (Some _t'3)
              (Evar _IS_NULL (Tfunction (Tcons (tptr tvoid) Tnil) tint
                               cc_default))
              ((Etempvar _t'14 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
          (Sifthenelse (Etempvar _t'3 tint)
            (Ssequence
              (Scall (Some _t'1)
                (Evar _SET_NULL (Tfunction (Tcons (tptr tvoid) Tnil)
                                  (tptr tvoid) cc_default))
                ((Ecast (Etempvar _curr (tptr (Tstruct _tree noattr)))
                   (tptr tvoid)) :: nil))
              (Sset _new_ref
                (Ecast (Etempvar _t'1 (tptr tvoid))
                  (tptr (Tstruct _tree noattr)))))
            (Ssequence
              (Ssequence
                (Sset _t'13
                  (Efield
                    (Ederef (Etempvar _curr (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _right
                    (tptr (Tstruct _atom_ptr noattr))))
                (Scall (Some _t'2)
                  (Evar _atomic_load_ptr (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _atom_ptr noattr))
                                             Tnil) (tptr tvoid) cc_default))
                  ((Etempvar _t'13 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
              (Sset _new_ref (Etempvar _t'2 (tptr tvoid))))))
        (Ssequence
          (Ssequence
            (Sset _t'12
              (Efield
                (Ederef (Etempvar _curr (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _left
                (tptr (Tstruct _atom_ptr noattr))))
            (Scall (Some _t'4)
              (Evar _atomic_load_ptr (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _atom_ptr noattr))
                                         Tnil) (tptr tvoid) cc_default))
              ((Etempvar _t'12 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
          (Sset _new_ref (Etempvar _t'4 (tptr tvoid))))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'6)
          (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                 cc_default))
          ((Esizeof (Tstruct _child_cas_operation noattr) tuint) :: nil))
        (Sset _cas_op
          (Ecast (Etempvar _t'6 (tptr tvoid))
            (tptr (Tstruct _child_cas_operation noattr)))))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'11
              (Efield
                (Ederef (Etempvar _pred (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _left
                (tptr (Tstruct _atom_ptr noattr))))
            (Scall (Some _t'7)
              (Evar _atomic_load_ptr (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _atom_ptr noattr))
                                         Tnil) (tptr tvoid) cc_default))
              ((Etempvar _t'11 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
          (Sassign
            (Efield
              (Ederef
                (Etempvar _cas_op (tptr (Tstruct _child_cas_operation noattr)))
                (Tstruct _child_cas_operation noattr)) _is_left tint)
            (Ebinop Oeq (Etempvar _curr (tptr (Tstruct _tree noattr)))
              (Etempvar _t'7 (tptr tvoid)) tint)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Etempvar _cas_op (tptr (Tstruct _child_cas_operation noattr)))
                (Tstruct _child_cas_operation noattr)) _expected
              (tptr (Tstruct _tree noattr)))
            (Etempvar _curr (tptr (Tstruct _tree noattr))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _cas_op (tptr (Tstruct _child_cas_operation noattr)))
                  (Tstruct _child_cas_operation noattr)) _update
                (tptr (Tstruct _tree noattr)))
              (Etempvar _new_ref (tptr (Tstruct _tree noattr))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'8)
                  (Evar _SET_FLAG (Tfunction
                                    (Tcons (tptr tvoid) (Tcons tint Tnil))
                                    (tptr tvoid) cc_default))
                  ((Ecast
                     (Etempvar _cas_op (tptr (Tstruct _child_cas_operation noattr)))
                     (tptr tvoid)) :: (Econst_int (Int.repr 2) tint) :: nil))
                (Ssequence
                  (Sset _t'10
                    (Efield
                      (Ederef (Etempvar _pred (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _op
                      (tptr (Tstruct _atom_ptr noattr))))
                  (Scall (Some _t'9)
                    (Evar _atomic_CAS_ptr (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _atom_ptr noattr))
                                              (Tcons (tptr (tptr tvoid))
                                                (Tcons (tptr tvoid) Tnil)))
                                            tint cc_default))
                    ((Etempvar _t'10 (tptr (Tstruct _atom_ptr noattr))) ::
                     (Eaddrof (Evar _pred_op (tptr tvoid))
                       (tptr (tptr tvoid))) ::
                     (Etempvar _t'8 (tptr tvoid)) :: nil))))
              (Sifthenelse (Etempvar _t'9 tint)
                (Scall None
                  (Evar _helpChildCAS (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _child_cas_operation noattr))
                                          (Tcons
                                            (tptr (Tstruct _tree noattr))
                                            (Tcons tint Tnil))) tvoid
                                        cc_default))
                  ((Etempvar _cas_op (tptr (Tstruct _child_cas_operation noattr))) ::
                   (Etempvar _pred (tptr (Tstruct _tree noattr))) ::
                   (Etempvar _thread_num tint) :: nil))
                (Scall None
                  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                cc_default))
                  ((Etempvar _cas_op (tptr (Tstruct _child_cas_operation noattr))) ::
                   nil))))))))))
|}.

Definition f_helpRelocate := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_op, (tptr (Tstruct _relocate_operation noattr))) ::
                (_pred, (tptr (Tstruct _tree noattr))) ::
                (_pred_op, (tptr tvoid)) ::
                (_curr, (tptr (Tstruct _tree noattr))) ::
                (_thread_num, tint) :: nil);
  fn_vars := ((_i, tint) :: (_i__1, tint) :: (_op_cast, (tptr tvoid)) :: nil);
  fn_temps := ((_seen_state, tint) ::
               (_real_dest, (tptr (Tstruct _tree noattr))) ::
               (_old_op, (tptr tvoid)) :: (_success, tint) ::
               (_result, tint) :: (_t'13, (tptr tvoid)) ::
               (_t'12, (tptr tvoid)) :: (_t'11, tint) ::
               (_t'10, (tptr tvoid)) :: (_t'9, (tptr tvoid)) ::
               (_t'8, (tptr tvoid)) :: (_t'7, tint) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, (tptr tvoid)) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, tint) :: (_t'25, (tptr (Tstruct _atom_int noattr))) ::
               (_t'24, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'23, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'22, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'21, (tptr (Tstruct _atom_int noattr))) ::
               (_t'20, (tptr (Tstruct _atom_int noattr))) ::
               (_t'19, (tptr (Tstruct _atom_int noattr))) :: (_t'18, tint) ::
               (_t'17, (tptr tvoid)) ::
               (_t'16, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'15, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'14, (tptr (Tstruct _atom_ptr noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'25
        (Efield
          (Ederef (Etempvar _op (tptr (Tstruct _relocate_operation noattr)))
            (Tstruct _relocate_operation noattr)) _state
          (tptr (Tstruct _atom_int noattr))))
      (Scall (Some _t'1)
        (Evar _atom_load (Tfunction
                           (Tcons (tptr (Tstruct _atom_int noattr)) Tnil)
                           tint cc_default))
        ((Etempvar _t'25 (tptr (Tstruct _atom_int noattr))) :: nil)))
    (Sset _seen_state (Etempvar _t'1 tint)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'24
          (Efield
            (Ederef
              (Etempvar _op (tptr (Tstruct _relocate_operation noattr)))
              (Tstruct _relocate_operation noattr)) _dest
            (tptr (Tstruct _atom_ptr noattr))))
        (Scall (Some _t'2)
          (Evar _atomic_load_ptr (Tfunction
                                   (Tcons (tptr (Tstruct _atom_ptr noattr))
                                     Tnil) (tptr tvoid) cc_default))
          ((Etempvar _t'24 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
      (Sset _real_dest (Etempvar _t'2 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _seen_state tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'23
                (Efield
                  (Ederef (Etempvar _real_dest (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _op
                  (tptr (Tstruct _atom_ptr noattr))))
              (Scall (Some _t'3)
                (Evar _atomic_load_ptr (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _atom_ptr noattr))
                                           Tnil) (tptr tvoid) cc_default))
                ((Etempvar _t'23 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
            (Sset _old_op (Etempvar _t'3 (tptr tvoid))))
          (Ssequence
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _SET_FLAG (Tfunction
                                    (Tcons (tptr tvoid) (Tcons tint Tnil))
                                    (tptr tvoid) cc_default))
                  ((Ecast
                     (Etempvar _op (tptr (Tstruct _relocate_operation noattr)))
                     (tptr tvoid)) :: (Econst_int (Int.repr 3) tint) :: nil))
                (Ssequence
                  (Sset _t'22
                    (Efield
                      (Ederef
                        (Etempvar _real_dest (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _op
                      (tptr (Tstruct _atom_ptr noattr))))
                  (Scall (Some _t'5)
                    (Evar _atomic_CAS_ptr (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _atom_ptr noattr))
                                              (Tcons (tptr (tptr tvoid))
                                                (Tcons (tptr tvoid) Tnil)))
                                            tint cc_default))
                    ((Etempvar _t'22 (tptr (Tstruct _atom_ptr noattr))) ::
                     (Eaddrof
                       (Efield
                         (Ederef
                           (Etempvar _op (tptr (Tstruct _relocate_operation noattr)))
                           (Tstruct _relocate_operation noattr)) _dest_op
                         (tptr tvoid)) (tptr (tptr tvoid))) ::
                     (Etempvar _t'4 (tptr tvoid)) :: nil))))
              (Sset _success (Etempvar _t'5 tint)))
            (Ssequence
              (Sifthenelse (Etempvar _success tint)
                (Sset _t'7 (Econst_int (Int.repr 1) tint))
                (Ssequence
                  (Scall (Some _t'8)
                    (Evar _SET_FLAG (Tfunction
                                      (Tcons (tptr tvoid) (Tcons tint Tnil))
                                      (tptr tvoid) cc_default))
                    ((Ecast
                       (Etempvar _op (tptr (Tstruct _relocate_operation noattr)))
                       (tptr tvoid)) :: (Econst_int (Int.repr 3) tint) ::
                     nil))
                  (Sset _t'7
                    (Ecast
                      (Ebinop Oeq (Etempvar _old_op (tptr tvoid))
                        (Etempvar _t'8 (tptr tvoid)) tint) tbool))))
              (Sifthenelse (Etempvar _t'7 tint)
                (Ssequence
                  (Sassign (Evar _i tint) (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Ssequence
                      (Sset _t'21
                        (Efield
                          (Ederef
                            (Etempvar _op (tptr (Tstruct _relocate_operation noattr)))
                            (Tstruct _relocate_operation noattr)) _state
                          (tptr (Tstruct _atom_int noattr))))
                      (Scall None
                        (Evar _atom_CAS (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _atom_int noattr))
                                            (Tcons (tptr tint)
                                              (Tcons tint Tnil))) tint
                                          cc_default))
                        ((Etempvar _t'21 (tptr (Tstruct _atom_int noattr))) ::
                         (Eaddrof (Evar _i tint) (tptr tint)) ::
                         (Econst_int (Int.repr 1) tint) :: nil)))
                    (Sset _seen_state (Econst_int (Int.repr 1) tint))))
                (Ssequence
                  (Sassign (Evar _i__1 tint) (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'20
                          (Efield
                            (Ederef
                              (Etempvar _op (tptr (Tstruct _relocate_operation noattr)))
                              (Tstruct _relocate_operation noattr)) _state
                            (tptr (Tstruct _atom_int noattr))))
                        (Scall (Some _t'6)
                          (Evar _atom_load (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _atom_int noattr))
                                               Tnil) tint cc_default))
                          ((Etempvar _t'20 (tptr (Tstruct _atom_int noattr))) ::
                           nil)))
                      (Sset _seen_state (Etempvar _t'6 tint)))
                    (Ssequence
                      (Sset _t'19
                        (Efield
                          (Ederef
                            (Etempvar _op (tptr (Tstruct _relocate_operation noattr)))
                            (Tstruct _relocate_operation noattr)) _state
                          (tptr (Tstruct _atom_int noattr))))
                      (Scall None
                        (Evar _atom_CAS (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _atom_int noattr))
                                            (Tcons (tptr tint)
                                              (Tcons tint Tnil))) tint
                                          cc_default))
                        ((Etempvar _t'19 (tptr (Tstruct _atom_int noattr))) ::
                         (Eaddrof (Evar _i__1 tint) (tptr tint)) ::
                         (Econst_int (Int.repr 2) tint) :: nil)))))))))
        Sskip)
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _seen_state tint)
                       (Econst_int (Int.repr 1) tint) tint)
          (Ssequence
            (Ssequence
              (Sset _t'18
                (Efield
                  (Ederef
                    (Etempvar _op (tptr (Tstruct _relocate_operation noattr)))
                    (Tstruct _relocate_operation noattr)) _replace_key tint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _real_dest (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _key tint) (Etempvar _t'18 tint)))
            (Ssequence
              (Ssequence
                (Sset _t'16
                  (Efield
                    (Ederef
                      (Etempvar _real_dest (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _value
                    (tptr (Tstruct _atom_ptr noattr))))
                (Ssequence
                  (Sset _t'17
                    (Efield
                      (Ederef
                        (Etempvar _op (tptr (Tstruct _relocate_operation noattr)))
                        (Tstruct _relocate_operation noattr)) _replace_value
                      (tptr tvoid)))
                  (Scall None
                    (Evar _atomic_store_ptr (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _atom_ptr noattr))
                                                (Tcons (tptr tvoid) Tnil))
                                              tvoid cc_default))
                    ((Etempvar _t'16 (tptr (Tstruct _atom_ptr noattr))) ::
                     (Etempvar _t'17 (tptr tvoid)) :: nil))))
              (Ssequence
                (Scall (Some _t'9)
                  (Evar _SET_FLAG (Tfunction
                                    (Tcons (tptr tvoid) (Tcons tint Tnil))
                                    (tptr tvoid) cc_default))
                  ((Ecast
                     (Etempvar _op (tptr (Tstruct _relocate_operation noattr)))
                     (tptr tvoid)) :: (Econst_int (Int.repr 0) tint) :: nil))
                (Ssequence
                  (Sset _t'15
                    (Efield
                      (Ederef
                        (Etempvar _real_dest (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _op
                      (tptr (Tstruct _atom_ptr noattr))))
                  (Scall None
                    (Evar _atomic_store_ptr (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _atom_ptr noattr))
                                                (Tcons (tptr tvoid) Tnil))
                                              tvoid cc_default))
                    ((Etempvar _t'15 (tptr (Tstruct _atom_ptr noattr))) ::
                     (Etempvar _t'9 (tptr tvoid)) :: nil))))))
          Sskip)
        (Ssequence
          (Sset _result
            (Ebinop Oeq (Etempvar _seen_state tint)
              (Econst_int (Int.repr 1) tint) tint))
          (Ssequence
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _real_dest (tptr (Tstruct _tree noattr)))
                           (Etempvar _curr (tptr (Tstruct _tree noattr)))
                           tint)
              (Sreturn (Some (Etempvar _result tint)))
              Sskip)
            (Ssequence
              (Ssequence
                (Scall (Some _t'10)
                  (Evar _SET_FLAG (Tfunction
                                    (Tcons (tptr tvoid) (Tcons tint Tnil))
                                    (tptr tvoid) cc_default))
                  ((Ecast
                     (Etempvar _op (tptr (Tstruct _relocate_operation noattr)))
                     (tptr tvoid)) :: (Econst_int (Int.repr 3) tint) :: nil))
                (Sassign (Evar _op_cast (tptr tvoid))
                  (Etempvar _t'10 (tptr tvoid))))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sifthenelse (Etempvar _result tint)
                      (Sset _t'11
                        (Ecast (Econst_int (Int.repr 1) tint) tint))
                      (Sset _t'11
                        (Ecast (Econst_int (Int.repr 0) tint) tint)))
                    (Scall (Some _t'12)
                      (Evar _SET_FLAG (Tfunction
                                        (Tcons (tptr tvoid)
                                          (Tcons tint Tnil)) (tptr tvoid)
                                        cc_default))
                      ((Ecast
                         (Etempvar _op (tptr (Tstruct _relocate_operation noattr)))
                         (tptr tvoid)) :: (Etempvar _t'11 tint) :: nil)))
                  (Ssequence
                    (Sset _t'14
                      (Efield
                        (Ederef
                          (Etempvar _curr (tptr (Tstruct _tree noattr)))
                          (Tstruct _tree noattr)) _op
                        (tptr (Tstruct _atom_ptr noattr))))
                    (Scall None
                      (Evar _atomic_CAS_ptr (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _atom_ptr noattr))
                                                (Tcons (tptr (tptr tvoid))
                                                  (Tcons (tptr tvoid) Tnil)))
                                              tint cc_default))
                      ((Etempvar _t'14 (tptr (Tstruct _atom_ptr noattr))) ::
                       (Eaddrof (Evar _op_cast (tptr tvoid))
                         (tptr (tptr tvoid))) ::
                       (Etempvar _t'12 (tptr tvoid)) :: nil))))
                (Ssequence
                  (Sifthenelse (Etempvar _result tint)
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq
                                     (Etempvar _real_dest (tptr (Tstruct _tree noattr)))
                                     (Etempvar _pred (tptr (Tstruct _tree noattr)))
                                     tint)
                        (Ssequence
                          (Scall (Some _t'13)
                            (Evar _SET_FLAG (Tfunction
                                              (Tcons (tptr tvoid)
                                                (Tcons tint Tnil))
                                              (tptr tvoid) cc_default))
                            ((Ecast
                               (Etempvar _op (tptr (Tstruct _relocate_operation noattr)))
                               (tptr tvoid)) ::
                             (Econst_int (Int.repr 0) tint) :: nil))
                          (Sset _pred_op (Etempvar _t'13 (tptr tvoid))))
                        Sskip)
                      (Scall None
                        (Evar _helpMarked (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _tree noattr))
                                              (Tcons (tptr tvoid)
                                                (Tcons
                                                  (tptr (Tstruct _tree noattr))
                                                  (Tcons tint Tnil)))) tvoid
                                            cc_default))
                        ((Etempvar _pred (tptr (Tstruct _tree noattr))) ::
                         (Etempvar _pred_op (tptr tvoid)) ::
                         (Etempvar _curr (tptr (Tstruct _tree noattr))) ::
                         (Etempvar _thread_num tint) :: nil)))
                    Sskip)
                  (Sreturn (Some (Etempvar _result tint))))))))))))
|}.

Definition f_help := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pred, (tptr (Tstruct _tree noattr))) ::
                (_pred_op, (tptr tvoid)) ::
                (_curr, (tptr (Tstruct _tree noattr))) ::
                (_curr_op, (tptr tvoid)) :: (_thread_num, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'5)
    (Evar _GET_FLAG (Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default))
    ((Etempvar _curr_op (tptr tvoid)) :: nil))
  (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tint)
                 (Econst_int (Int.repr 2) tint) tint)
    (Ssequence
      (Scall (Some _t'1)
        (Evar _UNFLAG (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid)
                        cc_default))
        ((Etempvar _curr_op (tptr tvoid)) :: nil))
      (Scall None
        (Evar _helpChildCAS (Tfunction
                              (Tcons
                                (tptr (Tstruct _child_cas_operation noattr))
                                (Tcons (tptr (Tstruct _tree noattr))
                                  (Tcons tint Tnil))) tvoid cc_default))
        ((Ecast (Etempvar _t'1 (tptr tvoid))
           (tptr (Tstruct _child_cas_operation noattr))) ::
         (Etempvar _curr (tptr (Tstruct _tree noattr))) ::
         (Etempvar _thread_num tint) :: nil)))
    (Ssequence
      (Scall (Some _t'4)
        (Evar _GET_FLAG (Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default))
        ((Etempvar _curr_op (tptr tvoid)) :: nil))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tint)
                     (Econst_int (Int.repr 3) tint) tint)
        (Ssequence
          (Scall (Some _t'2)
            (Evar _UNFLAG (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid)
                            cc_default))
            ((Etempvar _curr_op (tptr tvoid)) :: nil))
          (Scall None
            (Evar _helpRelocate (Tfunction
                                  (Tcons
                                    (tptr (Tstruct _relocate_operation noattr))
                                    (Tcons (tptr (Tstruct _tree noattr))
                                      (Tcons (tptr tvoid)
                                        (Tcons (tptr (Tstruct _tree noattr))
                                          (Tcons tint Tnil))))) tint
                                  cc_default))
            ((Ecast (Etempvar _t'2 (tptr tvoid))
               (tptr (Tstruct _relocate_operation noattr))) ::
             (Etempvar _pred (tptr (Tstruct _tree noattr))) ::
             (Etempvar _pred_op (tptr tvoid)) ::
             (Etempvar _curr (tptr (Tstruct _tree noattr))) ::
             (Etempvar _thread_num tint) :: nil)))
        (Ssequence
          (Scall (Some _t'3)
            (Evar _GET_FLAG (Tfunction (Tcons (tptr tvoid) Tnil) tint
                              cc_default))
            ((Etempvar _curr_op (tptr tvoid)) :: nil))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tint)
                         (Econst_int (Int.repr 1) tint) tint)
            (Scall None
              (Evar _helpMarked (Tfunction
                                  (Tcons (tptr (Tstruct _tree noattr))
                                    (Tcons (tptr tvoid)
                                      (Tcons (tptr (Tstruct _tree noattr))
                                        (Tcons tint Tnil)))) tvoid
                                  cc_default))
              ((Etempvar _pred (tptr (Tstruct _tree noattr))) ::
               (Etempvar _pred_op (tptr tvoid)) ::
               (Etempvar _curr (tptr (Tstruct _tree noattr))) ::
               (Etempvar _thread_num tint) :: nil))
            Sskip))))))
|}.

Definition f_find := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_key, tint) ::
                (_pred, (tptr (tptr (Tstruct _atom_ptr noattr)))) ::
                (_pred_op, (tptr (tptr tvoid))) ::
                (_curr, (tptr (tptr (Tstruct _atom_ptr noattr)))) ::
                (_curr_op, (tptr (tptr tvoid))) ::
                (_auxRoot, (tptr (Tstruct _atom_ptr noattr))) ::
                (_thread_num, tint) :: (_v, (tptr (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, tint) :: (_curr_key, tint) ::
               (_next, (tptr (Tstruct _atom_ptr noattr))) ::
               (_last_right, (tptr (Tstruct _atom_ptr noattr))) ::
               (_last_right_op, (tptr tvoid)) ::
               (_tp, (tptr (Tstruct _tree noattr))) ::
               (_tp_next, (tptr (Tstruct _tree noattr))) ::
               (_t'14, (tptr tvoid)) :: (_t'13, (tptr tvoid)) ::
               (_t'12, (tptr tvoid)) :: (_t'11, tint) ::
               (_t'10, (tptr tvoid)) :: (_t'9, (tptr tvoid)) ::
               (_t'8, (tptr tvoid)) :: (_t'7, tint) :: (_t'6, tint) ::
               (_t'5, (tptr tvoid)) :: (_t'4, tint) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) ::
               (_t'28, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'27, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'26, (tptr tvoid)) :: (_t'25, (tptr tvoid)) ::
               (_t'24, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'23, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'22, (tptr tvoid)) ::
               (_t'21, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'20, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'19, (tptr tvoid)) ::
               (_t'18, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'17, (tptr tvoid)) :: (_t'16, (tptr tvoid)) ::
               (_t'15, (tptr (Tstruct _atom_ptr noattr))) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Ssequence
      (Sset _result (Econst_int (Int.repr 2) tint))
      (Ssequence
        (Sassign
          (Ederef (Etempvar _curr (tptr (tptr (Tstruct _atom_ptr noattr))))
            (tptr (Tstruct _atom_ptr noattr)))
          (Etempvar _auxRoot (tptr (Tstruct _atom_ptr noattr))))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'28
                (Ederef
                  (Etempvar _curr (tptr (tptr (Tstruct _atom_ptr noattr))))
                  (tptr (Tstruct _atom_ptr noattr))))
              (Scall (Some _t'1)
                (Evar _atomic_load_ptr (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _atom_ptr noattr))
                                           Tnil) (tptr tvoid) cc_default))
                ((Etempvar _t'28 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
            (Sset _tp (Etempvar _t'1 (tptr tvoid))))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'27
                  (Efield
                    (Ederef (Etempvar _tp (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _op
                    (tptr (Tstruct _atom_ptr noattr))))
                (Scall (Some _t'2)
                  (Evar _atomic_load_ptr (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _atom_ptr noattr))
                                             Tnil) (tptr tvoid) cc_default))
                  ((Etempvar _t'27 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
              (Sassign
                (Ederef (Etempvar _curr_op (tptr (tptr tvoid))) (tptr tvoid))
                (Etempvar _t'2 (tptr tvoid))))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'26
                    (Ederef (Etempvar _curr_op (tptr (tptr tvoid)))
                      (tptr tvoid)))
                  (Scall (Some _t'4)
                    (Evar _GET_FLAG (Tfunction (Tcons (tptr tvoid) Tnil) tint
                                      cc_default))
                    ((Etempvar _t'26 (tptr tvoid)) :: nil)))
                (Sifthenelse (Ebinop One (Etempvar _t'4 tint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Ssequence
                    (Sset _t'24
                      (Evar _base_root (tptr (Tstruct _atom_ptr noattr))))
                    (Sifthenelse (Ebinop Oeq
                                   (Etempvar _auxRoot (tptr (Tstruct _atom_ptr noattr)))
                                   (Etempvar _t'24 (tptr (Tstruct _atom_ptr noattr)))
                                   tint)
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'25
                              (Ederef (Etempvar _curr_op (tptr (tptr tvoid)))
                                (tptr tvoid)))
                            (Scall (Some _t'3)
                              (Evar _UNFLAG (Tfunction
                                              (Tcons (tptr tvoid) Tnil)
                                              (tptr tvoid) cc_default))
                              ((Etempvar _t'25 (tptr tvoid)) :: nil)))
                          (Scall None
                            (Evar _helpChildCAS (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _child_cas_operation noattr))
                                                    (Tcons
                                                      (tptr (Tstruct _tree noattr))
                                                      (Tcons tint Tnil)))
                                                  tvoid cc_default))
                            ((Ecast (Etempvar _t'3 (tptr tvoid))
                               (tptr (Tstruct _child_cas_operation noattr))) ::
                             (Etempvar _tp (tptr (Tstruct _tree noattr))) ::
                             (Etempvar _thread_num tint) :: nil)))
                        Scontinue)
                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
                  Sskip))
              (Ssequence
                (Sset _next
                  (Efield
                    (Ederef (Etempvar _tp (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _right
                    (tptr (Tstruct _atom_ptr noattr))))
                (Ssequence
                  (Sset _last_right
                    (Ederef
                      (Etempvar _curr (tptr (tptr (Tstruct _atom_ptr noattr))))
                      (tptr (Tstruct _atom_ptr noattr))))
                  (Ssequence
                    (Sset _last_right_op
                      (Ederef (Etempvar _curr_op (tptr (tptr tvoid)))
                        (tptr tvoid)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'5)
                          (Evar _atomic_load_ptr (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _atom_ptr noattr))
                                                     Tnil) (tptr tvoid)
                                                   cc_default))
                          ((Etempvar _next (tptr (Tstruct _atom_ptr noattr))) ::
                           nil))
                        (Sset _tp_next (Etempvar _t'5 (tptr tvoid))))
                      (Ssequence
                        (Sloop
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'6)
                                  (Evar _IS_NULL (Tfunction
                                                   (Tcons (tptr tvoid) Tnil)
                                                   tint cc_default))
                                  ((Etempvar _tp_next (tptr (Tstruct _tree noattr))) ::
                                   nil))
                                (Sifthenelse (Eunop Onotbool
                                               (Etempvar _t'6 tint) tint)
                                  (Sset _t'7
                                    (Ecast
                                      (Ebinop One
                                        (Etempvar _tp_next (tptr (Tstruct _tree noattr)))
                                        (Ecast (Econst_int (Int.repr 0) tint)
                                          (tptr tvoid)) tint) tbool))
                                  (Sset _t'7 (Econst_int (Int.repr 0) tint))))
                              (Sifthenelse (Etempvar _t'7 tint) Sskip Sbreak))
                            (Ssequence
                              (Ssequence
                                (Sset _t'23
                                  (Ederef
                                    (Etempvar _curr (tptr (tptr (Tstruct _atom_ptr noattr))))
                                    (tptr (Tstruct _atom_ptr noattr))))
                                (Sassign
                                  (Ederef
                                    (Etempvar _pred (tptr (tptr (Tstruct _atom_ptr noattr))))
                                    (tptr (Tstruct _atom_ptr noattr)))
                                  (Etempvar _t'23 (tptr (Tstruct _atom_ptr noattr)))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'22
                                    (Ederef
                                      (Etempvar _curr_op (tptr (tptr tvoid)))
                                      (tptr tvoid)))
                                  (Sassign
                                    (Ederef
                                      (Etempvar _pred_op (tptr (tptr tvoid)))
                                      (tptr tvoid))
                                    (Etempvar _t'22 (tptr tvoid))))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Etempvar _curr (tptr (tptr (Tstruct _atom_ptr noattr))))
                                      (tptr (Tstruct _atom_ptr noattr)))
                                    (Etempvar _next (tptr (Tstruct _atom_ptr noattr))))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'21
                                          (Ederef
                                            (Etempvar _curr (tptr (tptr (Tstruct _atom_ptr noattr))))
                                            (tptr (Tstruct _atom_ptr noattr))))
                                        (Scall (Some _t'8)
                                          (Evar _atomic_load_ptr (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _atom_ptr noattr))
                                                                    Tnil)
                                                                   (tptr tvoid)
                                                                   cc_default))
                                          ((Etempvar _t'21 (tptr (Tstruct _atom_ptr noattr))) ::
                                           nil)))
                                      (Sset _tp (Etempvar _t'8 (tptr tvoid))))
                                    (Ssequence
                                      (Scall None
                                        (Evar _add_to_hp_list (Tfunction
                                                                (Tcons tint
                                                                  (Tcons
                                                                    (tptr (Tstruct _tree noattr))
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                                        ((Etempvar _thread_num tint) ::
                                         (Etempvar _tp (tptr (Tstruct _tree noattr))) ::
                                         nil))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'20
                                              (Efield
                                                (Ederef
                                                  (Etempvar _tp (tptr (Tstruct _tree noattr)))
                                                  (Tstruct _tree noattr)) _op
                                                (tptr (Tstruct _atom_ptr noattr))))
                                            (Scall (Some _t'9)
                                              (Evar _atomic_load_ptr 
                                              (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _atom_ptr noattr))
                                                  Tnil) (tptr tvoid)
                                                cc_default))
                                              ((Etempvar _t'20 (tptr (Tstruct _atom_ptr noattr))) ::
                                               nil)))
                                          (Sassign
                                            (Ederef
                                              (Etempvar _curr_op (tptr (tptr tvoid)))
                                              (tptr tvoid))
                                            (Etempvar _t'9 (tptr tvoid))))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'19
                                                (Ederef
                                                  (Etempvar _curr_op (tptr (tptr tvoid)))
                                                  (tptr tvoid)))
                                              (Scall (Some _t'11)
                                                (Evar _GET_FLAG (Tfunction
                                                                  (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                  tint
                                                                  cc_default))
                                                ((Etempvar _t'19 (tptr tvoid)) ::
                                                 nil)))
                                            (Sifthenelse (Ebinop One
                                                           (Etempvar _t'11 tint)
                                                           (Econst_int (Int.repr 0) tint)
                                                           tint)
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'18
                                                      (Ederef
                                                        (Etempvar _pred (tptr (tptr (Tstruct _atom_ptr noattr))))
                                                        (tptr (Tstruct _atom_ptr noattr))))
                                                    (Scall (Some _t'10)
                                                      (Evar _atomic_load_ptr 
                                                      (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _atom_ptr noattr))
                                                          Tnil) (tptr tvoid)
                                                        cc_default))
                                                      ((Etempvar _t'18 (tptr (Tstruct _atom_ptr noattr))) ::
                                                       nil)))
                                                  (Ssequence
                                                    (Sset _t'16
                                                      (Ederef
                                                        (Etempvar _pred_op (tptr (tptr tvoid)))
                                                        (tptr tvoid)))
                                                    (Ssequence
                                                      (Sset _t'17
                                                        (Ederef
                                                          (Etempvar _curr_op (tptr (tptr tvoid)))
                                                          (tptr tvoid)))
                                                      (Scall None
                                                        (Evar _help (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _tree noattr))
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    (tptr (Tstruct _tree noattr))
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    tint
                                                                    Tnil)))))
                                                                    tvoid
                                                                    cc_default))
                                                        ((Etempvar _t'10 (tptr tvoid)) ::
                                                         (Etempvar _t'16 (tptr tvoid)) ::
                                                         (Etempvar _tp (tptr (Tstruct _tree noattr))) ::
                                                         (Etempvar _t'17 (tptr tvoid)) ::
                                                         (Etempvar _thread_num tint) ::
                                                         nil)))))
                                                Sbreak)
                                              Sskip))
                                          (Ssequence
                                            (Sset _curr_key
                                              (Efield
                                                (Ederef
                                                  (Etempvar _tp (tptr (Tstruct _tree noattr)))
                                                  (Tstruct _tree noattr))
                                                _key tint))
                                            (Sifthenelse (Ebinop Olt
                                                           (Etempvar _key tint)
                                                           (Etempvar _curr_key tint)
                                                           tint)
                                              (Ssequence
                                                (Sset _result
                                                  (Econst_int (Int.repr 1) tint))
                                                (Ssequence
                                                  (Sset _next
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _tp (tptr (Tstruct _tree noattr)))
                                                        (Tstruct _tree noattr))
                                                      _left
                                                      (tptr (Tstruct _atom_ptr noattr))))
                                                  (Ssequence
                                                    (Scall (Some _t'12)
                                                      (Evar _atomic_load_ptr 
                                                      (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _atom_ptr noattr))
                                                          Tnil) (tptr tvoid)
                                                        cc_default))
                                                      ((Etempvar _next (tptr (Tstruct _atom_ptr noattr))) ::
                                                       nil))
                                                    (Sset _tp_next
                                                      (Etempvar _t'12 (tptr tvoid))))))
                                              (Sifthenelse (Ebinop Ogt
                                                             (Etempvar _key tint)
                                                             (Etempvar _curr_key tint)
                                                             tint)
                                                (Ssequence
                                                  (Sset _result
                                                    (Econst_int (Int.repr 2) tint))
                                                  (Ssequence
                                                    (Sset _next
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _tp (tptr (Tstruct _tree noattr)))
                                                          (Tstruct _tree noattr))
                                                        _right
                                                        (tptr (Tstruct _atom_ptr noattr))))
                                                    (Ssequence
                                                      (Sset _last_right
                                                        (Ederef
                                                          (Etempvar _curr (tptr (tptr (Tstruct _atom_ptr noattr))))
                                                          (tptr (Tstruct _atom_ptr noattr))))
                                                      (Ssequence
                                                        (Sset _last_right_op
                                                          (Ederef
                                                            (Etempvar _curr_op (tptr (tptr tvoid)))
                                                            (tptr tvoid)))
                                                        (Ssequence
                                                          (Scall (Some _t'13)
                                                            (Evar _atomic_load_ptr 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _atom_ptr noattr))
                                                                Tnil)
                                                              (tptr tvoid)
                                                              cc_default))
                                                            ((Etempvar _next (tptr (Tstruct _atom_ptr noattr))) ::
                                                             nil))
                                                          (Sset _tp_next
                                                            (Etempvar _t'13 (tptr tvoid))))))))
                                                (Ssequence
                                                  (Sset _result
                                                    (Econst_int (Int.repr 3) tint))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'15
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _tp (tptr (Tstruct _tree noattr)))
                                                              (Tstruct _tree noattr))
                                                            _value
                                                            (tptr (Tstruct _atom_ptr noattr))))
                                                        (Scall (Some _t'14)
                                                          (Evar _atomic_load_ptr 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _atom_ptr noattr))
                                                              Tnil)
                                                            (tptr tvoid)
                                                            cc_default))
                                                          ((Etempvar _t'15 (tptr (Tstruct _atom_ptr noattr))) ::
                                                           nil)))
                                                      (Sassign
                                                        (Ederef
                                                          (Etempvar _v (tptr (tptr tvoid)))
                                                          (tptr tvoid))
                                                        (Etempvar _t'14 (tptr tvoid))))
                                                    Sbreak)))))))))))))
                          Sskip)
                        (Sreturn (Some (Etempvar _result tint))))))))))))))
  Sskip)
|}.

Definition f_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_key, tint) :: (_value, (tptr tvoid)) ::
                (_thread_num, tint) :: nil);
  fn_vars := ((_curr, (tptr (Tstruct _atom_ptr noattr))) ::
              (_pred, (tptr (Tstruct _atom_ptr noattr))) ::
              (_curr_op, (tptr tvoid)) :: (_pred_op, (tptr tvoid)) ::
              (_v, (tptr tvoid)) :: nil);
  fn_temps := ((_newNode, (tptr (Tstruct _tree noattr))) ::
               (_tp, (tptr (Tstruct _tree noattr))) ::
               (_left_child, (tptr (Tstruct _tree noattr))) ::
               (_right_child, (tptr (Tstruct _tree noattr))) ::
               (_cas_op, (tptr (Tstruct _child_cas_operation noattr))) ::
               (_result, tint) ::
               (_val, (tptr (Tstruct _atom_ptr noattr))) ::
               (_left, (tptr (Tstruct _atom_ptr noattr))) ::
               (_right, (tptr (Tstruct _atom_ptr noattr))) ::
               (_op, (tptr (Tstruct _atom_ptr noattr))) ::
               (_is_left, tint) :: (_old, (tptr (Tstruct _tree noattr))) ::
               (_t'18, tint) :: (_t'17, (tptr tvoid)) ::
               (_t'16, (tptr tvoid)) ::
               (_t'15, (tptr (Tstruct _tree noattr))) ::
               (_t'14, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'13, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'12, (tptr tvoid)) ::
               (_t'11, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'10, (tptr tvoid)) ::
               (_t'9, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'8, (tptr tvoid)) :: (_t'7, (tptr tvoid)) ::
               (_t'6, (tptr tvoid)) :: (_t'5, tint) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, tint) ::
               (_t'28, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'27, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'26, (tptr tvoid)) ::
               (_t'25, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'24, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'23, (tptr tvoid)) ::
               (_t'22, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'21, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'20, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'19, (tptr (Tstruct _atom_ptr noattr))) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'28 (Evar _base_root (tptr (Tstruct _atom_ptr noattr))))
          (Scall (Some _t'1)
            (Evar _find (Tfunction
                          (Tcons tint
                            (Tcons (tptr (tptr (Tstruct _atom_ptr noattr)))
                              (Tcons (tptr (tptr tvoid))
                                (Tcons
                                  (tptr (tptr (Tstruct _atom_ptr noattr)))
                                  (Tcons (tptr (tptr tvoid))
                                    (Tcons (tptr (Tstruct _atom_ptr noattr))
                                      (Tcons tint
                                        (Tcons (tptr (tptr tvoid)) Tnil))))))))
                          tint cc_default))
            ((Etempvar _key tint) ::
             (Eaddrof (Evar _pred (tptr (Tstruct _atom_ptr noattr)))
               (tptr (tptr (Tstruct _atom_ptr noattr)))) ::
             (Eaddrof (Evar _pred_op (tptr tvoid)) (tptr (tptr tvoid))) ::
             (Eaddrof (Evar _curr (tptr (Tstruct _atom_ptr noattr)))
               (tptr (tptr (Tstruct _atom_ptr noattr)))) ::
             (Eaddrof (Evar _curr_op (tptr tvoid)) (tptr (tptr tvoid))) ::
             (Etempvar _t'28 (tptr (Tstruct _atom_ptr noattr))) ::
             (Etempvar _thread_num tint) ::
             (Eaddrof (Evar _v (tptr tvoid)) (tptr (tptr tvoid))) :: nil)))
        (Sset _result (Etempvar _t'1 tint)))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'27 (Evar _curr (tptr (Tstruct _atom_ptr noattr))))
            (Scall (Some _t'2)
              (Evar _atomic_load_ptr (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _atom_ptr noattr))
                                         Tnil) (tptr tvoid) cc_default))
              ((Etempvar _t'27 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
          (Sset _tp (Etempvar _t'2 (tptr tvoid))))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _result tint)
                         (Econst_int (Int.repr 3) tint) tint)
            (Ssequence
              (Scall None
                (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                ((Evar ___stringlit_1 (tarray tschar 37)) ::
                 (Etempvar _key tint) :: nil))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'26 (Evar _curr_op (tptr tvoid)))
                    (Scall (Some _t'4)
                      (Evar _SET_FLAG (Tfunction
                                        (Tcons (tptr tvoid)
                                          (Tcons tint Tnil)) (tptr tvoid)
                                        cc_default))
                      ((Ecast (Etempvar _t'26 (tptr tvoid)) (tptr tvoid)) ::
                       (Econst_int (Int.repr 4) tint) :: nil)))
                  (Ssequence
                    (Sset _t'25
                      (Efield
                        (Ederef (Etempvar _tp (tptr (Tstruct _tree noattr)))
                          (Tstruct _tree noattr)) _op
                        (tptr (Tstruct _atom_ptr noattr))))
                    (Scall (Some _t'5)
                      (Evar _atomic_CAS_ptr (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _atom_ptr noattr))
                                                (Tcons (tptr (tptr tvoid))
                                                  (Tcons (tptr tvoid) Tnil)))
                                              tint cc_default))
                      ((Etempvar _t'25 (tptr (Tstruct _atom_ptr noattr))) ::
                       (Eaddrof (Evar _curr_op (tptr tvoid))
                         (tptr (tptr tvoid))) ::
                       (Etempvar _t'4 (tptr tvoid)) :: nil))))
                (Sifthenelse (Etempvar _t'5 tint)
                  (Ssequence
                    (Ssequence
                      (Sset _t'24
                        (Efield
                          (Ederef
                            (Etempvar _tp (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _value
                          (tptr (Tstruct _atom_ptr noattr))))
                      (Scall None
                        (Evar _atomic_store_ptr (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _atom_ptr noattr))
                                                    (Tcons (tptr tvoid) Tnil))
                                                  tvoid cc_default))
                        ((Etempvar _t'24 (tptr (Tstruct _atom_ptr noattr))) ::
                         (Etempvar _value (tptr tvoid)) :: nil)))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'23 (Evar _curr_op (tptr tvoid)))
                          (Scall (Some _t'3)
                            (Evar _SET_FLAG (Tfunction
                                              (Tcons (tptr tvoid)
                                                (Tcons tint Tnil))
                                              (tptr tvoid) cc_default))
                            ((Ecast (Etempvar _t'23 (tptr tvoid))
                               (tptr tvoid)) ::
                             (Econst_int (Int.repr 0) tint) :: nil)))
                        (Ssequence
                          (Sset _t'22
                            (Efield
                              (Ederef
                                (Etempvar _tp (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _op
                              (tptr (Tstruct _atom_ptr noattr))))
                          (Scall None
                            (Evar _atomic_store_ptr (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _atom_ptr noattr))
                                                        (Tcons (tptr tvoid)
                                                          Tnil)) tvoid
                                                      cc_default))
                            ((Etempvar _t'22 (tptr (Tstruct _atom_ptr noattr))) ::
                             (Etempvar _t'3 (tptr tvoid)) :: nil))))
                      (Sreturn None)))
                  Scontinue)))
            Sskip)
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'21
                  (Efield
                    (Ederef (Etempvar _tp (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _left
                    (tptr (Tstruct _atom_ptr noattr))))
                (Scall (Some _t'6)
                  (Evar _atomic_load_ptr (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _atom_ptr noattr))
                                             Tnil) (tptr tvoid) cc_default))
                  ((Etempvar _t'21 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
              (Sset _left_child (Etempvar _t'6 (tptr tvoid))))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'20
                    (Efield
                      (Ederef (Etempvar _tp (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _right
                      (tptr (Tstruct _atom_ptr noattr))))
                  (Scall (Some _t'7)
                    (Evar _atomic_load_ptr (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _atom_ptr noattr))
                                               Tnil) (tptr tvoid) cc_default))
                    ((Etempvar _t'20 (tptr (Tstruct _atom_ptr noattr))) ::
                     nil)))
                (Sset _right_child (Etempvar _t'7 (tptr tvoid))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'8)
                    (Evar _surely_malloc (Tfunction (Tcons tuint Tnil)
                                           (tptr tvoid) cc_default))
                    ((Esizeof (Tstruct _tree noattr) tuint) :: nil))
                  (Sset _newNode
                    (Ecast (Etempvar _t'8 (tptr tvoid))
                      (tptr (Tstruct _tree noattr)))))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _newNode (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _key tint)
                    (Etempvar _key tint))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'9)
                        (Evar _make_atomic_ptr (Tfunction
                                                 (Tcons (tptr tvoid) Tnil)
                                                 (tptr (Tstruct _atom_ptr noattr))
                                                 cc_default))
                        ((Etempvar _value (tptr tvoid)) :: nil))
                      (Sset _val
                        (Etempvar _t'9 (tptr (Tstruct _atom_ptr noattr)))))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _newNode (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _value
                          (tptr (Tstruct _atom_ptr noattr)))
                        (Etempvar _val (tptr (Tstruct _atom_ptr noattr))))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'10)
                              (Evar _SET_NULL (Tfunction
                                                (Tcons (tptr tvoid) Tnil)
                                                (tptr tvoid) cc_default))
                              ((Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) :: nil))
                            (Scall (Some _t'11)
                              (Evar _make_atomic_ptr (Tfunction
                                                       (Tcons (tptr tvoid)
                                                         Tnil)
                                                       (tptr (Tstruct _atom_ptr noattr))
                                                       cc_default))
                              ((Etempvar _t'10 (tptr tvoid)) :: nil)))
                          (Sset _left
                            (Etempvar _t'11 (tptr (Tstruct _atom_ptr noattr)))))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _newNode (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _left
                              (tptr (Tstruct _atom_ptr noattr)))
                            (Etempvar _left (tptr (Tstruct _atom_ptr noattr))))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'12)
                                  (Evar _SET_NULL (Tfunction
                                                    (Tcons (tptr tvoid) Tnil)
                                                    (tptr tvoid) cc_default))
                                  ((Ecast (Econst_int (Int.repr 0) tint)
                                     (tptr tvoid)) :: nil))
                                (Scall (Some _t'13)
                                  (Evar _make_atomic_ptr (Tfunction
                                                           (Tcons
                                                             (tptr tvoid)
                                                             Tnil)
                                                           (tptr (Tstruct _atom_ptr noattr))
                                                           cc_default))
                                  ((Etempvar _t'12 (tptr tvoid)) :: nil)))
                              (Sset _right
                                (Etempvar _t'13 (tptr (Tstruct _atom_ptr noattr)))))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _newNode (tptr (Tstruct _tree noattr)))
                                    (Tstruct _tree noattr)) _right
                                  (tptr (Tstruct _atom_ptr noattr)))
                                (Etempvar _right (tptr (Tstruct _atom_ptr noattr))))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'14)
                                    (Evar _make_atomic_ptr (Tfunction
                                                             (Tcons
                                                               (tptr tvoid)
                                                               Tnil)
                                                             (tptr (Tstruct _atom_ptr noattr))
                                                             cc_default))
                                    ((Econst_int (Int.repr 0) tint) :: nil))
                                  (Sset _op
                                    (Etempvar _t'14 (tptr (Tstruct _atom_ptr noattr)))))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _newNode (tptr (Tstruct _tree noattr)))
                                        (Tstruct _tree noattr)) _op
                                      (tptr (Tstruct _atom_ptr noattr)))
                                    (Etempvar _op (tptr (Tstruct _atom_ptr noattr))))
                                  (Ssequence
                                    (Sset _is_left
                                      (Ebinop Oeq (Etempvar _result tint)
                                        (Econst_int (Int.repr 1) tint) tint))
                                    (Ssequence
                                      (Ssequence
                                        (Sifthenelse (Etempvar _is_left tint)
                                          (Sset _t'15
                                            (Ecast
                                              (Etempvar _left_child (tptr (Tstruct _tree noattr)))
                                              (tptr (Tstruct _tree noattr))))
                                          (Sset _t'15
                                            (Ecast
                                              (Etempvar _right_child (tptr (Tstruct _tree noattr)))
                                              (tptr (Tstruct _tree noattr)))))
                                        (Sset _old
                                          (Etempvar _t'15 (tptr (Tstruct _tree noattr)))))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'16)
                                            (Evar _surely_malloc (Tfunction
                                                                   (Tcons
                                                                    tuint
                                                                    Tnil)
                                                                   (tptr tvoid)
                                                                   cc_default))
                                            ((Esizeof (Tstruct _child_cas_operation noattr) tuint) ::
                                             nil))
                                          (Sset _cas_op
                                            (Ecast
                                              (Etempvar _t'16 (tptr tvoid))
                                              (tptr (Tstruct _child_cas_operation noattr)))))
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _cas_op (tptr (Tstruct _child_cas_operation noattr)))
                                                (Tstruct _child_cas_operation noattr))
                                              _is_left tint)
                                            (Etempvar _is_left tint))
                                          (Ssequence
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _cas_op (tptr (Tstruct _child_cas_operation noattr)))
                                                  (Tstruct _child_cas_operation noattr))
                                                _expected
                                                (tptr (Tstruct _tree noattr)))
                                              (Etempvar _old (tptr (Tstruct _tree noattr))))
                                            (Ssequence
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _cas_op (tptr (Tstruct _child_cas_operation noattr)))
                                                    (Tstruct _child_cas_operation noattr))
                                                  _update
                                                  (tptr (Tstruct _tree noattr)))
                                                (Etempvar _newNode (tptr (Tstruct _tree noattr))))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _printf (Tfunction
                                                                  (Tcons
                                                                    (tptr tschar)
                                                                    Tnil)
                                                                  tint
                                                                  {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                                  ((Evar ___stringlit_2 (tarray tschar 17)) ::
                                                   nil))
                                                (Ssequence
                                                  (Ssequence
                                                    (Scall (Some _t'17)
                                                      (Evar _SET_FLAG 
                                                      (Tfunction
                                                        (Tcons (tptr tvoid)
                                                          (Tcons tint Tnil))
                                                        (tptr tvoid)
                                                        cc_default))
                                                      ((Ecast
                                                         (Etempvar _cas_op (tptr (Tstruct _child_cas_operation noattr)))
                                                         (tptr tvoid)) ::
                                                       (Econst_int (Int.repr 2) tint) ::
                                                       nil))
                                                    (Ssequence
                                                      (Sset _t'19
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _tp (tptr (Tstruct _tree noattr)))
                                                            (Tstruct _tree noattr))
                                                          _op
                                                          (tptr (Tstruct _atom_ptr noattr))))
                                                      (Scall (Some _t'18)
                                                        (Evar _atomic_CAS_ptr 
                                                        (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _atom_ptr noattr))
                                                            (Tcons
                                                              (tptr (tptr tvoid))
                                                              (Tcons
                                                                (tptr tvoid)
                                                                Tnil))) tint
                                                          cc_default))
                                                        ((Etempvar _t'19 (tptr (Tstruct _atom_ptr noattr))) ::
                                                         (Eaddrof
                                                           (Evar _curr_op (tptr tvoid))
                                                           (tptr (tptr tvoid))) ::
                                                         (Etempvar _t'17 (tptr tvoid)) ::
                                                         nil))))
                                                  (Sifthenelse (Etempvar _t'18 tint)
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _printf 
                                                        (Tfunction
                                                          (Tcons
                                                            (tptr tschar)
                                                            Tnil) tint
                                                          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                                        ((Evar ___stringlit_3 (tarray tschar 18)) ::
                                                         (Etempvar _key tint) ::
                                                         nil))
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _helpChildCAS 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _child_cas_operation noattr))
                                                              (Tcons
                                                                (tptr (Tstruct _tree noattr))
                                                                (Tcons tint
                                                                  Tnil)))
                                                            tvoid cc_default))
                                                          ((Etempvar _cas_op (tptr (Tstruct _child_cas_operation noattr))) ::
                                                           (Etempvar _tp (tptr (Tstruct _tree noattr))) ::
                                                           (Etempvar _thread_num tint) ::
                                                           nil))
                                                        (Sreturn None)))
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _free (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                                        ((Etempvar _newNode (tptr (Tstruct _tree noattr))) ::
                                                         nil))
                                                      (Scall None
                                                        (Evar _free (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                                        ((Etempvar _cas_op (tptr (Tstruct _child_cas_operation noattr))) ::
                                                         nil))))))))))))))))))))))))))))
  Sskip)
|}.

Definition f_delete := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_key, tint) :: (_thread_num, tint) :: nil);
  fn_vars := ((_pred_op, (tptr tvoid)) :: (_curr_op, (tptr tvoid)) ::
              (_replace_op, (tptr tvoid)) ::
              (_pred, (tptr (Tstruct _atom_ptr noattr))) ::
              (_curr, (tptr (Tstruct _atom_ptr noattr))) ::
              (_replace, (tptr (Tstruct _atom_ptr noattr))) ::
              (_v, (tptr tvoid)) :: nil);
  fn_temps := ((_tp, (tptr (Tstruct _tree noattr))) ::
               (_left, (tptr (Tstruct _tree noattr))) ::
               (_right, (tptr (Tstruct _tree noattr))) ::
               (_reloc_op, (tptr (Tstruct _relocate_operation noattr))) ::
               (_replace_real, (tptr (Tstruct _tree noattr))) ::
               (_curr_real, (tptr (Tstruct _tree noattr))) ::
               (_pred_real, (tptr (Tstruct _tree noattr))) ::
               (_t'22, tint) :: (_t'21, tint) :: (_t'20, tint) ::
               (_t'19, tint) :: (_t'18, (tptr tvoid)) :: (_t'17, tint) ::
               (_t'16, (tptr tvoid)) ::
               (_t'15, (tptr (Tstruct _atom_int noattr))) ::
               (_t'14, (tptr tvoid)) :: (_t'13, (tptr tvoid)) ::
               (_t'12, (tptr tvoid)) :: (_t'11, (tptr tvoid)) ::
               (_t'10, (tptr tvoid)) :: (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, (tptr tvoid)) ::
               (_t'5, (tptr tvoid)) :: (_t'4, (tptr tvoid)) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, tint) :: (_t'43, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'42, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'41, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'40, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'39, (tptr tvoid)) ::
               (_t'38, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'37, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'36, (tptr tvoid)) :: (_t'35, (tptr tvoid)) ::
               (_t'34, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'33, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'32, (tptr tvoid)) ::
               (_t'31, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'30, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'29, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'28, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'27, (tptr tvoid)) :: (_t'26, tint) ::
               (_t'25, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'24, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'23, (tptr tvoid)) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'43 (Evar _base_root (tptr (Tstruct _atom_ptr noattr))))
          (Scall (Some _t'1)
            (Evar _find (Tfunction
                          (Tcons tint
                            (Tcons (tptr (tptr (Tstruct _atom_ptr noattr)))
                              (Tcons (tptr (tptr tvoid))
                                (Tcons
                                  (tptr (tptr (Tstruct _atom_ptr noattr)))
                                  (Tcons (tptr (tptr tvoid))
                                    (Tcons (tptr (Tstruct _atom_ptr noattr))
                                      (Tcons tint
                                        (Tcons (tptr (tptr tvoid)) Tnil))))))))
                          tint cc_default))
            ((Etempvar _key tint) ::
             (Eaddrof (Evar _pred (tptr (Tstruct _atom_ptr noattr)))
               (tptr (tptr (Tstruct _atom_ptr noattr)))) ::
             (Eaddrof (Evar _pred_op (tptr tvoid)) (tptr (tptr tvoid))) ::
             (Eaddrof (Evar _curr (tptr (Tstruct _atom_ptr noattr)))
               (tptr (tptr (Tstruct _atom_ptr noattr)))) ::
             (Eaddrof (Evar _curr_op (tptr tvoid)) (tptr (tptr tvoid))) ::
             (Etempvar _t'43 (tptr (Tstruct _atom_ptr noattr))) ::
             (Etempvar _thread_num tint) ::
             (Eaddrof (Evar _v (tptr tvoid)) (tptr (tptr tvoid))) :: nil)))
        (Sifthenelse (Ebinop One (Etempvar _t'1 tint)
                       (Econst_int (Int.repr 3) tint) tint)
          (Sreturn None)
          Sskip))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'42 (Evar _curr (tptr (Tstruct _atom_ptr noattr))))
            (Scall (Some _t'2)
              (Evar _atomic_load_ptr (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _atom_ptr noattr))
                                         Tnil) (tptr tvoid) cc_default))
              ((Etempvar _t'42 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
          (Sset _tp (Etempvar _t'2 (tptr tvoid))))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'41
                (Efield
                  (Ederef (Etempvar _tp (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _left
                  (tptr (Tstruct _atom_ptr noattr))))
              (Scall (Some _t'3)
                (Evar _atomic_load_ptr (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _atom_ptr noattr))
                                           Tnil) (tptr tvoid) cc_default))
                ((Etempvar _t'41 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
            (Sset _left (Etempvar _t'3 (tptr tvoid))))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'40
                  (Efield
                    (Ederef (Etempvar _tp (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _right
                    (tptr (Tstruct _atom_ptr noattr))))
                (Scall (Some _t'4)
                  (Evar _atomic_load_ptr (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _atom_ptr noattr))
                                             Tnil) (tptr tvoid) cc_default))
                  ((Etempvar _t'40 (tptr (Tstruct _atom_ptr noattr))) :: nil)))
              (Sset _right (Etempvar _t'4 (tptr tvoid))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'20)
                  (Evar _IS_NULL (Tfunction (Tcons (tptr tvoid) Tnil) tint
                                   cc_default))
                  ((Etempvar _right (tptr (Tstruct _tree noattr))) :: nil))
                (Sifthenelse (Etempvar _t'20 tint)
                  (Sset _t'21 (Econst_int (Int.repr 1) tint))
                  (Ssequence
                    (Scall (Some _t'22)
                      (Evar _IS_NULL (Tfunction (Tcons (tptr tvoid) Tnil)
                                       tint cc_default))
                      ((Etempvar _left (tptr (Tstruct _tree noattr))) :: nil))
                    (Sset _t'21 (Ecast (Etempvar _t'22 tint) tbool)))))
              (Sifthenelse (Etempvar _t'21 tint)
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'39 (Evar _curr_op (tptr tvoid)))
                      (Scall (Some _t'6)
                        (Evar _SET_FLAG (Tfunction
                                          (Tcons (tptr tvoid)
                                            (Tcons tint Tnil)) (tptr tvoid)
                                          cc_default))
                        ((Etempvar _t'39 (tptr tvoid)) ::
                         (Econst_int (Int.repr 1) tint) :: nil)))
                    (Ssequence
                      (Sset _t'38
                        (Efield
                          (Ederef
                            (Etempvar _tp (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _op
                          (tptr (Tstruct _atom_ptr noattr))))
                      (Scall (Some _t'7)
                        (Evar _atomic_CAS_ptr (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _atom_ptr noattr))
                                                  (Tcons (tptr (tptr tvoid))
                                                    (Tcons (tptr tvoid) Tnil)))
                                                tint cc_default))
                        ((Etempvar _t'38 (tptr (Tstruct _atom_ptr noattr))) ::
                         (Eaddrof (Evar _curr_op (tptr tvoid))
                           (tptr (tptr tvoid))) ::
                         (Etempvar _t'6 (tptr tvoid)) :: nil))))
                  (Sifthenelse (Etempvar _t'7 tint)
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'37
                            (Evar _pred (tptr (Tstruct _atom_ptr noattr))))
                          (Scall (Some _t'5)
                            (Evar _atomic_load_ptr (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _atom_ptr noattr))
                                                       Tnil) (tptr tvoid)
                                                     cc_default))
                            ((Etempvar _t'37 (tptr (Tstruct _atom_ptr noattr))) ::
                             nil)))
                        (Ssequence
                          (Sset _t'36 (Evar _pred_op (tptr tvoid)))
                          (Scall None
                            (Evar _helpMarked (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _tree noattr))
                                                  (Tcons (tptr tvoid)
                                                    (Tcons
                                                      (tptr (Tstruct _tree noattr))
                                                      (Tcons tint Tnil))))
                                                tvoid cc_default))
                            ((Etempvar _t'5 (tptr tvoid)) ::
                             (Etempvar _t'36 (tptr tvoid)) ::
                             (Etempvar _tp (tptr (Tstruct _tree noattr))) ::
                             (Etempvar _thread_num tint) :: nil))))
                      (Sreturn None))
                    Sskip))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'34
                          (Evar _curr (tptr (Tstruct _atom_ptr noattr))))
                        (Ssequence
                          (Sset _t'35 (Evar _v (tptr tvoid)))
                          (Scall (Some _t'8)
                            (Evar _find (Tfunction
                                          (Tcons tint
                                            (Tcons
                                              (tptr (tptr (Tstruct _atom_ptr noattr)))
                                              (Tcons (tptr (tptr tvoid))
                                                (Tcons
                                                  (tptr (tptr (Tstruct _atom_ptr noattr)))
                                                  (Tcons (tptr (tptr tvoid))
                                                    (Tcons
                                                      (tptr (Tstruct _atom_ptr noattr))
                                                      (Tcons tint
                                                        (Tcons
                                                          (tptr (tptr tvoid))
                                                          Tnil)))))))) tint
                                          cc_default))
                            ((Etempvar _key tint) ::
                             (Eaddrof
                               (Evar _pred (tptr (Tstruct _atom_ptr noattr)))
                               (tptr (tptr (Tstruct _atom_ptr noattr)))) ::
                             (Eaddrof (Evar _pred_op (tptr tvoid))
                               (tptr (tptr tvoid))) ::
                             (Eaddrof
                               (Evar _replace (tptr (Tstruct _atom_ptr noattr)))
                               (tptr (tptr (Tstruct _atom_ptr noattr)))) ::
                             (Eaddrof (Evar _replace_op (tptr tvoid))
                               (tptr (tptr tvoid))) ::
                             (Etempvar _t'34 (tptr (Tstruct _atom_ptr noattr))) ::
                             (Etempvar _thread_num tint) ::
                             (Etempvar _t'35 (tptr tvoid)) :: nil))))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'8 tint)
                                     (Econst_int (Int.repr 0) tint) tint)
                        (Sset _t'9 (Econst_int (Int.repr 1) tint))
                        (Ssequence
                          (Ssequence
                            (Sset _t'33
                              (Efield
                                (Ederef
                                  (Etempvar _tp (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _op
                                (tptr (Tstruct _atom_ptr noattr))))
                            (Scall (Some _t'10)
                              (Evar _atomic_load_ptr (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct _atom_ptr noattr))
                                                         Tnil) (tptr tvoid)
                                                       cc_default))
                              ((Etempvar _t'33 (tptr (Tstruct _atom_ptr noattr))) ::
                               nil)))
                          (Ssequence
                            (Sset _t'32 (Evar _curr_op (tptr tvoid)))
                            (Sset _t'9
                              (Ecast
                                (Ebinop One (Etempvar _t'10 (tptr tvoid))
                                  (Etempvar _t'32 (tptr tvoid)) tint) tbool))))))
                    (Sifthenelse (Etempvar _t'9 tint) Scontinue Sskip))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'31
                          (Evar _replace (tptr (Tstruct _atom_ptr noattr))))
                        (Scall (Some _t'11)
                          (Evar _atomic_load_ptr (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _atom_ptr noattr))
                                                     Tnil) (tptr tvoid)
                                                   cc_default))
                          ((Etempvar _t'31 (tptr (Tstruct _atom_ptr noattr))) ::
                           nil)))
                      (Sset _replace_real (Etempvar _t'11 (tptr tvoid))))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'30
                            (Evar _curr (tptr (Tstruct _atom_ptr noattr))))
                          (Scall (Some _t'12)
                            (Evar _atomic_load_ptr (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _atom_ptr noattr))
                                                       Tnil) (tptr tvoid)
                                                     cc_default))
                            ((Etempvar _t'30 (tptr (Tstruct _atom_ptr noattr))) ::
                             nil)))
                        (Sset _curr_real (Etempvar _t'12 (tptr tvoid))))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'29
                              (Evar _pred (tptr (Tstruct _atom_ptr noattr))))
                            (Scall (Some _t'13)
                              (Evar _atomic_load_ptr (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct _atom_ptr noattr))
                                                         Tnil) (tptr tvoid)
                                                       cc_default))
                              ((Etempvar _t'29 (tptr (Tstruct _atom_ptr noattr))) ::
                               nil)))
                          (Sset _pred_real (Etempvar _t'13 (tptr tvoid))))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'14)
                              (Evar _surely_malloc (Tfunction
                                                     (Tcons tuint Tnil)
                                                     (tptr tvoid) cc_default))
                              ((Esizeof (Tstruct _relocate_operation noattr) tuint) ::
                               nil))
                            (Sset _reloc_op
                              (Ecast (Etempvar _t'14 (tptr tvoid))
                                (tptr (Tstruct _relocate_operation noattr)))))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'15)
                                (Evar _make_atomic (Tfunction
                                                     (Tcons tint Tnil)
                                                     (tptr (Tstruct _atom_int noattr))
                                                     cc_default))
                                ((Econst_int (Int.repr 0) tint) :: nil))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _reloc_op (tptr (Tstruct _relocate_operation noattr)))
                                    (Tstruct _relocate_operation noattr))
                                  _state (tptr (Tstruct _atom_int noattr)))
                                (Etempvar _t'15 (tptr (Tstruct _atom_int noattr)))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'28
                                  (Evar _curr (tptr (Tstruct _atom_ptr noattr))))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _reloc_op (tptr (Tstruct _relocate_operation noattr)))
                                      (Tstruct _relocate_operation noattr))
                                    _dest (tptr (Tstruct _atom_ptr noattr)))
                                  (Etempvar _t'28 (tptr (Tstruct _atom_ptr noattr)))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'27 (Evar _curr_op (tptr tvoid)))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _reloc_op (tptr (Tstruct _relocate_operation noattr)))
                                        (Tstruct _relocate_operation noattr))
                                      _dest_op (tptr tvoid))
                                    (Etempvar _t'27 (tptr tvoid))))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _reloc_op (tptr (Tstruct _relocate_operation noattr)))
                                        (Tstruct _relocate_operation noattr))
                                      _remove_key tint) (Etempvar _key tint))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'26
                                        (Efield
                                          (Ederef
                                            (Etempvar _replace_real (tptr (Tstruct _tree noattr)))
                                            (Tstruct _tree noattr)) _key
                                          tint))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _reloc_op (tptr (Tstruct _relocate_operation noattr)))
                                            (Tstruct _relocate_operation noattr))
                                          _replace_key tint)
                                        (Etempvar _t'26 tint)))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'25
                                            (Efield
                                              (Ederef
                                                (Etempvar _replace_real (tptr (Tstruct _tree noattr)))
                                                (Tstruct _tree noattr))
                                              _value
                                              (tptr (Tstruct _atom_ptr noattr))))
                                          (Scall (Some _t'16)
                                            (Evar _atomic_load_ptr (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _atom_ptr noattr))
                                                                    Tnil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                            ((Etempvar _t'25 (tptr (Tstruct _atom_ptr noattr))) ::
                                             nil)))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _reloc_op (tptr (Tstruct _relocate_operation noattr)))
                                              (Tstruct _relocate_operation noattr))
                                            _replace_value (tptr tvoid))
                                          (Etempvar _t'16 (tptr tvoid))))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'18)
                                            (Evar _SET_FLAG (Tfunction
                                                              (Tcons
                                                                (tptr tvoid)
                                                                (Tcons tint
                                                                  Tnil))
                                                              (tptr tvoid)
                                                              cc_default))
                                            ((Ecast
                                               (Etempvar _reloc_op (tptr (Tstruct _relocate_operation noattr)))
                                               (tptr tvoid)) ::
                                             (Econst_int (Int.repr 3) tint) ::
                                             nil))
                                          (Ssequence
                                            (Sset _t'24
                                              (Efield
                                                (Ederef
                                                  (Etempvar _replace_real (tptr (Tstruct _tree noattr)))
                                                  (Tstruct _tree noattr)) _op
                                                (tptr (Tstruct _atom_ptr noattr))))
                                            (Scall (Some _t'19)
                                              (Evar _atomic_CAS_ptr (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _atom_ptr noattr))
                                                                    (Tcons
                                                                    (tptr (tptr tvoid))
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)))
                                                                    tint
                                                                    cc_default))
                                              ((Etempvar _t'24 (tptr (Tstruct _atom_ptr noattr))) ::
                                               (Eaddrof
                                                 (Evar _replace_op (tptr tvoid))
                                                 (tptr (tptr tvoid))) ::
                                               (Etempvar _t'18 (tptr tvoid)) ::
                                               nil))))
                                        (Sifthenelse (Etempvar _t'19 tint)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'23
                                                (Evar _pred_op (tptr tvoid)))
                                              (Scall (Some _t'17)
                                                (Evar _helpRelocate (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _relocate_operation noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct _tree noattr))
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    (tptr (Tstruct _tree noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil)))))
                                                                    tint
                                                                    cc_default))
                                                ((Etempvar _reloc_op (tptr (Tstruct _relocate_operation noattr))) ::
                                                 (Etempvar _pred_real (tptr (Tstruct _tree noattr))) ::
                                                 (Etempvar _t'23 (tptr tvoid)) ::
                                                 (Etempvar _replace_real (tptr (Tstruct _tree noattr))) ::
                                                 (Etempvar _thread_num tint) ::
                                                 nil)))
                                            (Sifthenelse (Etempvar _t'17 tint)
                                              (Sreturn None)
                                              (Scall None
                                                (Evar _free (Tfunction
                                                              (Tcons
                                                                (tptr tvoid)
                                                                Tnil) tvoid
                                                              cc_default))
                                                ((Etempvar _reloc_op (tptr (Tstruct _relocate_operation noattr))) ::
                                                 nil))))
                                          (Scall None
                                            (Evar _free (Tfunction
                                                          (Tcons (tptr tvoid)
                                                            Tnil) tvoid
                                                          cc_default))
                                            ((Etempvar _reloc_op (tptr (Tstruct _relocate_operation noattr))) ::
                                             nil))))))))))))))))))))))
  Sskip)
|}.

Definition f_thread_func_add := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_args, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_arguments, (tptr (Tstruct _arg_struct noattr))) ::
               (_i, tint) :: (_t'7, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'6, tint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'1, (tptr (tarray (tptr tvoid) 2))) :: nil);
  fn_body :=
(Ssequence
  (Sset _arguments (Etempvar _args (tptr tvoid)))
  (Ssequence
    (Ssequence
      (Sset _t'7
        (Efield
          (Ederef (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
            (Tstruct _arg_struct noattr)) _l (tptr (tarray (tptr tvoid) 2))))
      (Scall None
        (Evar _pthread_cond_wait (Tfunction
                                   (Tcons
                                     (tptr (tptr (Tstruct ___pthread_cond_t noattr)))
                                     (Tcons
                                       (tptr (tptr (Tstruct ___pthread_mutex_t noattr)))
                                       Tnil)) tint cc_default))
        ((Eaddrof (Evar _cond (tptr (Tstruct ___pthread_cond_t noattr)))
           (tptr (tptr (Tstruct ___pthread_cond_t noattr)))) ::
         (Ecast (Etempvar _t'7 (tptr (tarray (tptr tvoid) 2))) (tptr tvoid)) ::
         nil)))
    (Ssequence
      (Ssequence
        (Sset _t'6
          (Efield
            (Ederef (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
              (Tstruct _arg_struct noattr)) _thread_num tint))
        (Scall None
          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
          ((Evar ___stringlit_4 (tarray tschar 30)) ::
           (Etempvar _t'6 tint) :: nil)))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 1) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Ole (Etempvar _i tint)
                             (Econst_int (Int.repr 10) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Sset _t'5
                    (Efield
                      (Ederef
                        (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
                        (Tstruct _arg_struct noattr)) _thread_num tint))
                  (Scall None
                    (Evar _add (Tfunction
                                 (Tcons tint
                                   (Tcons (tptr tvoid) (Tcons tint Tnil)))
                                 tvoid cc_default))
                    ((Etempvar _i tint) ::
                     (Evar ___stringlit_5 (tarray tschar 6)) ::
                     (Etempvar _t'5 tint) :: nil)))
                (Ssequence
                  (Sset _t'4
                    (Efield
                      (Ederef
                        (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
                        (Tstruct _arg_struct noattr)) _thread_num tint))
                  (Scall None
                    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                    {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                    ((Evar ___stringlit_6 (tarray tschar 33)) ::
                     (Etempvar _i tint) :: (Etempvar _t'4 tint) :: nil)))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef
                  (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
                  (Tstruct _arg_struct noattr)) _thread_num tint))
            (Scall None
              (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                              {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
              ((Evar ___stringlit_7 (tarray tschar 30)) ::
               (Etempvar _t'3 tint) :: nil)))
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef
                    (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
                    (Tstruct _arg_struct noattr)) _l
                  (tptr (tarray (tptr tvoid) 2))))
              (Scall None
                (Evar _release2 (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                ((Ecast (Etempvar _t'2 (tptr (tarray (tptr tvoid) 2)))
                   (tptr tvoid)) :: nil)))
            (Ssequence
              (Ssequence
                (Sset _t'1
                  (Efield
                    (Ederef
                      (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
                      (Tstruct _arg_struct noattr)) _l
                    (tptr (tarray (tptr tvoid) 2))))
                (Scall None
                  (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                  {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                  ((Evar ___stringlit_8 (tarray tschar 40)) ::
                   (Etempvar _t'1 (tptr (tarray (tptr tvoid) 2))) :: nil)))
              (Sreturn (Some (Ecast
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) (tptr tvoid)))))))))))
|}.

Definition f_thread_func_find := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_args, (tptr tvoid)) :: nil);
  fn_vars := ((_pred, (tptr (Tstruct _atom_ptr noattr))) ::
              (_curr, (tptr (Tstruct _atom_ptr noattr))) ::
              (_pred_op, (tptr tvoid)) :: (_curr_op, (tptr tvoid)) ::
              (_v, (tptr tvoid)) :: nil);
  fn_temps := ((_arguments, (tptr (Tstruct _arg_struct noattr))) ::
               (_i, tint) :: (_result, tint) :: (_t'1, tint) ::
               (_t'11, (tptr (tarray (tptr tvoid) 2))) :: (_t'10, tint) ::
               (_t'9, tint) :: (_t'8, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'7, tint) :: (_t'6, (tptr tvoid)) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'2, (tptr (tarray (tptr tvoid) 2))) :: nil);
  fn_body :=
(Ssequence
  (Sset _arguments (Etempvar _args (tptr tvoid)))
  (Ssequence
    (Ssequence
      (Sset _t'11
        (Efield
          (Ederef (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
            (Tstruct _arg_struct noattr)) _l (tptr (tarray (tptr tvoid) 2))))
      (Scall None
        (Evar _pthread_cond_wait (Tfunction
                                   (Tcons
                                     (tptr (tptr (Tstruct ___pthread_cond_t noattr)))
                                     (Tcons
                                       (tptr (tptr (Tstruct ___pthread_mutex_t noattr)))
                                       Tnil)) tint cc_default))
        ((Eaddrof (Evar _cond (tptr (Tstruct ___pthread_cond_t noattr)))
           (tptr (tptr (Tstruct ___pthread_cond_t noattr)))) ::
         (Ecast (Etempvar _t'11 (tptr (tarray (tptr tvoid) 2))) (tptr tvoid)) ::
         nil)))
    (Ssequence
      (Ssequence
        (Sset _t'10
          (Efield
            (Ederef (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
              (Tstruct _arg_struct noattr)) _thread_num tint))
        (Scall None
          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
          ((Evar ___stringlit_9 (tarray tschar 30)) ::
           (Etempvar _t'10 tint) :: nil)))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 10) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                             (Econst_int (Int.repr 1) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'8
                      (Evar _base_root (tptr (Tstruct _atom_ptr noattr))))
                    (Ssequence
                      (Sset _t'9
                        (Efield
                          (Ederef
                            (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
                            (Tstruct _arg_struct noattr)) _thread_num tint))
                      (Scall (Some _t'1)
                        (Evar _find (Tfunction
                                      (Tcons tint
                                        (Tcons
                                          (tptr (tptr (Tstruct _atom_ptr noattr)))
                                          (Tcons (tptr (tptr tvoid))
                                            (Tcons
                                              (tptr (tptr (Tstruct _atom_ptr noattr)))
                                              (Tcons (tptr (tptr tvoid))
                                                (Tcons
                                                  (tptr (Tstruct _atom_ptr noattr))
                                                  (Tcons tint
                                                    (Tcons
                                                      (tptr (tptr tvoid))
                                                      Tnil)))))))) tint
                                      cc_default))
                        ((Etempvar _i tint) ::
                         (Eaddrof
                           (Evar _pred (tptr (Tstruct _atom_ptr noattr)))
                           (tptr (tptr (Tstruct _atom_ptr noattr)))) ::
                         (Eaddrof (Evar _pred_op (tptr tvoid))
                           (tptr (tptr tvoid))) ::
                         (Eaddrof
                           (Evar _curr (tptr (Tstruct _atom_ptr noattr)))
                           (tptr (tptr (Tstruct _atom_ptr noattr)))) ::
                         (Eaddrof (Evar _curr_op (tptr tvoid))
                           (tptr (tptr tvoid))) ::
                         (Etempvar _t'8 (tptr (Tstruct _atom_ptr noattr))) ::
                         (Etempvar _t'9 tint) ::
                         (Eaddrof (Evar _v (tptr tvoid)) (tptr (tptr tvoid))) ::
                         nil))))
                  (Sset _result (Etempvar _t'1 tint)))
                (Sifthenelse (Ebinop Oeq (Etempvar _result tint)
                               (Econst_int (Int.repr 3) tint) tint)
                  (Ssequence
                    (Ssequence
                      (Sset _t'7
                        (Efield
                          (Ederef
                            (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
                            (Tstruct _arg_struct noattr)) _thread_num tint))
                      (Scall None
                        (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                        tint
                                        {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                        ((Evar ___stringlit_11 (tarray tschar 46)) ::
                         (Etempvar _i tint) :: (Etempvar _t'7 tint) :: nil)))
                    (Ssequence
                      (Sset _t'6 (Evar _v (tptr tvoid)))
                      (Scall None
                        (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                        tint
                                        {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                        ((Evar ___stringlit_12 (tarray tschar 17)) ::
                         (Etempvar _t'6 (tptr tvoid)) :: nil))))
                  (Ssequence
                    (Sset _t'5
                      (Efield
                        (Ederef
                          (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
                          (Tstruct _arg_struct noattr)) _thread_num tint))
                    (Scall None
                      (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                      tint
                                      {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                      ((Evar ___stringlit_10 (tarray tschar 37)) ::
                       (Etempvar _i tint) :: (Etempvar _t'5 tint) :: nil))))))
            (Sset _i
              (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef
                  (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
                  (Tstruct _arg_struct noattr)) _thread_num tint))
            (Scall None
              (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                              {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
              ((Evar ___stringlit_13 (tarray tschar 30)) ::
               (Etempvar _t'4 tint) :: nil)))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef
                    (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
                    (Tstruct _arg_struct noattr)) _l
                  (tptr (tarray (tptr tvoid) 2))))
              (Scall None
                (Evar _release2 (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                ((Ecast (Etempvar _t'3 (tptr (tarray (tptr tvoid) 2)))
                   (tptr tvoid)) :: nil)))
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Efield
                    (Ederef
                      (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
                      (Tstruct _arg_struct noattr)) _l
                    (tptr (tarray (tptr tvoid) 2))))
                (Scall None
                  (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                  {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                  ((Evar ___stringlit_14 (tarray tschar 40)) ::
                   (Etempvar _t'2 (tptr (tarray (tptr tvoid) 2))) :: nil)))
              (Sreturn (Some (Ecast
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) (tptr tvoid)))))))))))
|}.

Definition f_thread_func_remove := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_args, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_arguments, (tptr (Tstruct _arg_struct noattr))) ::
               (_i, tint) :: (_t'6, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, (tptr (tarray (tptr tvoid) 2))) :: nil);
  fn_body :=
(Ssequence
  (Sset _arguments (Etempvar _args (tptr tvoid)))
  (Ssequence
    (Ssequence
      (Sset _t'6
        (Efield
          (Ederef (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
            (Tstruct _arg_struct noattr)) _l (tptr (tarray (tptr tvoid) 2))))
      (Scall None
        (Evar _pthread_cond_wait (Tfunction
                                   (Tcons
                                     (tptr (tptr (Tstruct ___pthread_cond_t noattr)))
                                     (Tcons
                                       (tptr (tptr (Tstruct ___pthread_mutex_t noattr)))
                                       Tnil)) tint cc_default))
        ((Eaddrof (Evar _cond (tptr (Tstruct ___pthread_cond_t noattr)))
           (tptr (tptr (Tstruct ___pthread_cond_t noattr)))) ::
         (Ecast (Etempvar _t'6 (tptr (tarray (tptr tvoid) 2))) (tptr tvoid)) ::
         nil)))
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
              (Tstruct _arg_struct noattr)) _thread_num tint))
        (Scall None
          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
          ((Evar ___stringlit_15 (tarray tschar 29)) ::
           (Etempvar _t'5 tint) :: nil)))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 10) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                             (Econst_int (Int.repr 1) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Sset _t'4
                    (Efield
                      (Ederef
                        (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
                        (Tstruct _arg_struct noattr)) _thread_num tint))
                  (Scall None
                    (Evar _delete (Tfunction (Tcons tint (Tcons tint Tnil))
                                    tvoid cc_default))
                    ((Etempvar _i tint) :: (Etempvar _t'4 tint) :: nil)))
                (Ssequence
                  (Sset _t'3
                    (Efield
                      (Ederef
                        (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
                        (Tstruct _arg_struct noattr)) _thread_num tint))
                  (Scall None
                    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                    {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                    ((Evar ___stringlit_16 (tarray tschar 57)) ::
                     (Etempvar _i tint) :: (Etempvar _t'3 tint) :: nil)))))
            (Sset _i
              (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef
                  (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
                  (Tstruct _arg_struct noattr)) _thread_num tint))
            (Scall None
              (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                              {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
              ((Evar ___stringlit_17 (tarray tschar 32)) ::
               (Etempvar _t'2 tint) :: nil)))
          (Ssequence
            (Ssequence
              (Sset _t'1
                (Efield
                  (Ederef
                    (Etempvar _arguments (tptr (Tstruct _arg_struct noattr)))
                    (Tstruct _arg_struct noattr)) _l
                  (tptr (tarray (tptr tvoid) 2))))
              (Scall None
                (Evar _release2 (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                ((Ecast (Etempvar _t'1 (tptr (tarray (tptr tvoid) 2)))
                   (tptr tvoid)) :: nil)))
            (Sreturn (Some (Ecast
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) (tptr tvoid))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_args, (tarray (Tstruct _arg_struct noattr) 15)) ::
              (_pred, (tptr (Tstruct _atom_ptr noattr))) ::
              (_curr, (tptr (Tstruct _atom_ptr noattr))) ::
              (_pred_op, (tptr tvoid)) :: (_curr_op, (tptr tvoid)) ::
              (_v, (tptr tvoid)) :: nil);
  fn_temps := ((_i, tint) :: (_root, (tptr (Tstruct _tree noattr))) ::
               (_val, (tptr (Tstruct _atom_ptr noattr))) ::
               (_left, (tptr (Tstruct _atom_ptr noattr))) ::
               (_right, (tptr (Tstruct _atom_ptr noattr))) ::
               (_op, (tptr (Tstruct _atom_ptr noattr))) :: (_i__1, tint) ::
               (_i__2, tint) :: (_i__3, tint) :: (_i__4, tint) ::
               (_l, (tptr (tarray (tptr tvoid) 2))) :: (_i__5, tint) ::
               (_t'8, tint) :: (_t'7, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'6, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'5, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'4, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'1, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'14, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'13, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'12, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'11, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'10, (tptr (Tstruct _atom_ptr noattr))) ::
               (_t'9, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall None
      (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                      {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
      ((Evar ___stringlit_18 (tarray tschar 17)) :: nil))
    (Ssequence
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Ebinop Omul (Econst_int (Int.repr 15) tint)
                           (Econst_int (Int.repr 10) tint) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Scall (Some _t'1)
              (Evar _make_atomic_ptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                       (tptr (Tstruct _atom_ptr noattr))
                                       cc_default))
              ((Econst_int (Int.repr 0) tint) :: nil))
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Evar _hp (tarray (tptr (Tstruct _atom_ptr noattr)) 150))
                  (Etempvar _i tint)
                  (tptr (tptr (Tstruct _atom_ptr noattr))))
                (tptr (Tstruct _atom_ptr noattr)))
              (Etempvar _t'1 (tptr (Tstruct _atom_ptr noattr))))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _make_atomic_ptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                     (tptr (Tstruct _atom_ptr noattr))
                                     cc_default))
            ((Econst_int (Int.repr 0) tint) :: nil))
          (Sassign (Evar _base_root (tptr (Tstruct _atom_ptr noattr)))
            (Etempvar _t'2 (tptr (Tstruct _atom_ptr noattr)))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                     cc_default))
              ((Esizeof (Tstruct _tree noattr) tuint) :: nil))
            (Sset _root
              (Ecast (Etempvar _t'3 (tptr tvoid))
                (tptr (Tstruct _tree noattr)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _root (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _key tint)
              (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _make_atomic_ptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                           (tptr (Tstruct _atom_ptr noattr))
                                           cc_default))
                  ((Econst_int (Int.repr 0) tint) :: nil))
                (Sset _val (Etempvar _t'4 (tptr (Tstruct _atom_ptr noattr)))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _root (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _value
                    (tptr (Tstruct _atom_ptr noattr)))
                  (Etempvar _val (tptr (Tstruct _atom_ptr noattr))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'5)
                      (Evar _make_atomic_ptr (Tfunction
                                               (Tcons (tptr tvoid) Tnil)
                                               (tptr (Tstruct _atom_ptr noattr))
                                               cc_default))
                      ((Econst_int (Int.repr 0) tint) :: nil))
                    (Sset _left
                      (Etempvar _t'5 (tptr (Tstruct _atom_ptr noattr)))))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _root (tptr (Tstruct _tree noattr)))
                          (Tstruct _tree noattr)) _left
                        (tptr (Tstruct _atom_ptr noattr)))
                      (Etempvar _left (tptr (Tstruct _atom_ptr noattr))))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'6)
                          (Evar _make_atomic_ptr (Tfunction
                                                   (Tcons (tptr tvoid) Tnil)
                                                   (tptr (Tstruct _atom_ptr noattr))
                                                   cc_default))
                          ((Econst_int (Int.repr 0) tint) :: nil))
                        (Sset _right
                          (Etempvar _t'6 (tptr (Tstruct _atom_ptr noattr)))))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _root (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _right
                            (tptr (Tstruct _atom_ptr noattr)))
                          (Etempvar _right (tptr (Tstruct _atom_ptr noattr))))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'7)
                              (Evar _make_atomic_ptr (Tfunction
                                                       (Tcons (tptr tvoid)
                                                         Tnil)
                                                       (tptr (Tstruct _atom_ptr noattr))
                                                       cc_default))
                              ((Econst_int (Int.repr 0) tint) :: nil))
                            (Sset _op
                              (Etempvar _t'7 (tptr (Tstruct _atom_ptr noattr)))))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _root (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _op
                                (tptr (Tstruct _atom_ptr noattr)))
                              (Etempvar _op (tptr (Tstruct _atom_ptr noattr))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'14
                                  (Evar _base_root (tptr (Tstruct _atom_ptr noattr))))
                                (Scall None
                                  (Evar _atomic_store_ptr (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _atom_ptr noattr))
                                                              (Tcons
                                                                (tptr tvoid)
                                                                Tnil)) tvoid
                                                            cc_default))
                                  ((Etempvar _t'14 (tptr (Tstruct _atom_ptr noattr))) ::
                                   (Ecast
                                     (Etempvar _root (tptr (Tstruct _tree noattr)))
                                     (tptr tvoid)) :: nil)))
                              (Ssequence
                                (Ssequence
                                  (Sset _i__1 (Econst_int (Int.repr 5) tint))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _i__1 tint)
                                                     (Econst_int (Int.repr 15) tint)
                                                     tint)
                                        Sskip
                                        Sbreak)
                                      (Ssequence
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _args (tarray (Tstruct _arg_struct noattr) 15))
                                                (Etempvar _i__1 tint)
                                                (tptr (Tstruct _arg_struct noattr)))
                                              (Tstruct _arg_struct noattr))
                                            _l
                                            (tptr (tarray (tptr tvoid) 2)))
                                          (Ebinop Oadd
                                            (Evar _thread_lock (tarray (tarray (tptr tvoid) 2) 15))
                                            (Etempvar _i__1 tint)
                                            (tptr (tarray (tptr tvoid) 2))))
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _args (tarray (Tstruct _arg_struct noattr) 15))
                                                  (Etempvar _i__1 tint)
                                                  (tptr (Tstruct _arg_struct noattr)))
                                                (Tstruct _arg_struct noattr))
                                              _thread_num tint)
                                            (Etempvar _i__1 tint))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'13
                                                (Efield
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _args (tarray (Tstruct _arg_struct noattr) 15))
                                                      (Etempvar _i__1 tint)
                                                      (tptr (Tstruct _arg_struct noattr)))
                                                    (Tstruct _arg_struct noattr))
                                                  _l
                                                  (tptr (tarray (tptr tvoid) 2))))
                                              (Scall None
                                                (Evar _makelock (Tfunction
                                                                  (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                  tvoid
                                                                  cc_default))
                                                ((Ecast
                                                   (Etempvar _t'13 (tptr (tarray (tptr tvoid) 2)))
                                                   (tptr tvoid)) :: nil)))
                                            (Scall None
                                              (Evar _spawn (Tfunction
                                                             (Tcons
                                                               (tptr 
                                                               (Tfunction
                                                                 (Tcons
                                                                   (tptr tvoid)
                                                                   Tnil)
                                                                 (tptr tvoid)
                                                                 cc_default))
                                                               (Tcons
                                                                 (tptr tvoid)
                                                                 Tnil)) tvoid
                                                             cc_default))
                                              ((Ecast
                                                 (Eaddrof
                                                   (Evar _thread_func_add 
                                                   (Tfunction
                                                     (Tcons (tptr tvoid)
                                                       Tnil) (tptr tvoid)
                                                     cc_default))
                                                   (tptr (Tfunction
                                                           (Tcons
                                                             (tptr tvoid)
                                                             Tnil)
                                                           (tptr tvoid)
                                                           cc_default)))
                                                 (tptr tvoid)) ::
                                               (Ecast
                                                 (Ebinop Oadd
                                                   (Evar _args (tarray (Tstruct _arg_struct noattr) 15))
                                                   (Etempvar _i__1 tint)
                                                   (tptr (Tstruct _arg_struct noattr)))
                                                 (tptr tvoid)) :: nil))))))
                                    (Sset _i__1
                                      (Ebinop Oadd (Etempvar _i__1 tint)
                                        (Econst_int (Int.repr 1) tint) tint))))
                                (Ssequence
                                  (Scall None
                                    (Evar _printf (Tfunction
                                                    (Tcons (tptr tschar)
                                                      Tnil) tint
                                                    {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                    ((Evar ___stringlit_19 (tarray tschar 23)) ::
                                     nil))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _i__2
                                        (Econst_int (Int.repr 0) tint))
                                      (Sloop
                                        (Ssequence
                                          (Sifthenelse (Ebinop Olt
                                                         (Etempvar _i__2 tint)
                                                         (Econst_int (Int.repr 5) tint)
                                                         tint)
                                            Sskip
                                            Sbreak)
                                          (Ssequence
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _args (tarray (Tstruct _arg_struct noattr) 15))
                                                    (Etempvar _i__2 tint)
                                                    (tptr (Tstruct _arg_struct noattr)))
                                                  (Tstruct _arg_struct noattr))
                                                _l
                                                (tptr (tarray (tptr tvoid) 2)))
                                              (Ebinop Oadd
                                                (Evar _thread_lock (tarray (tarray (tptr tvoid) 2) 15))
                                                (Etempvar _i__2 tint)
                                                (tptr (tarray (tptr tvoid) 2))))
                                            (Ssequence
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _args (tarray (Tstruct _arg_struct noattr) 15))
                                                      (Etempvar _i__2 tint)
                                                      (tptr (Tstruct _arg_struct noattr)))
                                                    (Tstruct _arg_struct noattr))
                                                  _thread_num tint)
                                                (Etempvar _i__2 tint))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'12
                                                    (Efield
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _args (tarray (Tstruct _arg_struct noattr) 15))
                                                          (Etempvar _i__2 tint)
                                                          (tptr (Tstruct _arg_struct noattr)))
                                                        (Tstruct _arg_struct noattr))
                                                      _l
                                                      (tptr (tarray (tptr tvoid) 2))))
                                                  (Scall None
                                                    (Evar _makelock (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                                    ((Ecast
                                                       (Etempvar _t'12 (tptr (tarray (tptr tvoid) 2)))
                                                       (tptr tvoid)) :: nil)))
                                                (Scall None
                                                  (Evar _spawn (Tfunction
                                                                 (Tcons
                                                                   (tptr 
                                                                   (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                   (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil))
                                                                 tvoid
                                                                 cc_default))
                                                  ((Ecast
                                                     (Eaddrof
                                                       (Evar _thread_func_find 
                                                       (Tfunction
                                                         (Tcons (tptr tvoid)
                                                           Tnil) (tptr tvoid)
                                                         cc_default))
                                                       (tptr (Tfunction
                                                               (Tcons
                                                                 (tptr tvoid)
                                                                 Tnil)
                                                               (tptr tvoid)
                                                               cc_default)))
                                                     (tptr tvoid)) ::
                                                   (Ecast
                                                     (Ebinop Oadd
                                                       (Evar _args (tarray (Tstruct _arg_struct noattr) 15))
                                                       (Etempvar _i__2 tint)
                                                       (tptr (Tstruct _arg_struct noattr)))
                                                     (tptr tvoid)) :: nil))))))
                                        (Sset _i__2
                                          (Ebinop Oadd (Etempvar _i__2 tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _i__3
                                          (Econst_int (Int.repr 10) tint))
                                        (Sloop
                                          (Ssequence
                                            (Sifthenelse (Ebinop Olt
                                                           (Etempvar _i__3 tint)
                                                           (Econst_int (Int.repr 15) tint)
                                                           tint)
                                              Sskip
                                              Sbreak)
                                            (Ssequence
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _args (tarray (Tstruct _arg_struct noattr) 15))
                                                      (Etempvar _i__3 tint)
                                                      (tptr (Tstruct _arg_struct noattr)))
                                                    (Tstruct _arg_struct noattr))
                                                  _l
                                                  (tptr (tarray (tptr tvoid) 2)))
                                                (Ebinop Oadd
                                                  (Evar _thread_lock (tarray (tarray (tptr tvoid) 2) 15))
                                                  (Etempvar _i__3 tint)
                                                  (tptr (tarray (tptr tvoid) 2))))
                                              (Ssequence
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _args (tarray (Tstruct _arg_struct noattr) 15))
                                                        (Etempvar _i__3 tint)
                                                        (tptr (Tstruct _arg_struct noattr)))
                                                      (Tstruct _arg_struct noattr))
                                                    _thread_num tint)
                                                  (Etempvar _i__3 tint))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'11
                                                      (Efield
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _args (tarray (Tstruct _arg_struct noattr) 15))
                                                            (Etempvar _i__3 tint)
                                                            (tptr (Tstruct _arg_struct noattr)))
                                                          (Tstruct _arg_struct noattr))
                                                        _l
                                                        (tptr (tarray (tptr tvoid) 2))))
                                                    (Scall None
                                                      (Evar _makelock 
                                                      (Tfunction
                                                        (Tcons (tptr tvoid)
                                                          Tnil) tvoid
                                                        cc_default))
                                                      ((Ecast
                                                         (Etempvar _t'11 (tptr (tarray (tptr tvoid) 2)))
                                                         (tptr tvoid)) ::
                                                       nil)))
                                                  (Scall None
                                                    (Evar _spawn (Tfunction
                                                                   (Tcons
                                                                    (tptr 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil))
                                                                   tvoid
                                                                   cc_default))
                                                    ((Ecast
                                                       (Eaddrof
                                                         (Evar _thread_func_remove 
                                                         (Tfunction
                                                           (Tcons
                                                             (tptr tvoid)
                                                             Tnil)
                                                           (tptr tvoid)
                                                           cc_default))
                                                         (tptr (Tfunction
                                                                 (Tcons
                                                                   (tptr tvoid)
                                                                   Tnil)
                                                                 (tptr tvoid)
                                                                 cc_default)))
                                                       (tptr tvoid)) ::
                                                     (Ecast
                                                       (Ebinop Oadd
                                                         (Evar _args (tarray (Tstruct _arg_struct noattr) 15))
                                                         (Etempvar _i__3 tint)
                                                         (tptr (Tstruct _arg_struct noattr)))
                                                       (tptr tvoid)) :: nil))))))
                                          (Sset _i__3
                                            (Ebinop Oadd
                                              (Etempvar _i__3 tint)
                                              (Econst_int (Int.repr 1) tint)
                                              tint))))
                                      (Ssequence
                                        (Scall None
                                          (Evar _pthread_cond_broadcast 
                                          (Tfunction
                                            (Tcons
                                              (tptr (tptr (Tstruct ___pthread_cond_t noattr)))
                                              Tnil) tint cc_default))
                                          ((Eaddrof
                                             (Evar _cond (tptr (Tstruct ___pthread_cond_t noattr)))
                                             (tptr (tptr (Tstruct ___pthread_cond_t noattr)))) ::
                                           nil))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _i__4
                                              (Econst_int (Int.repr 0) tint))
                                            (Sloop
                                              (Ssequence
                                                (Sifthenelse (Ebinop Olt
                                                               (Etempvar _i__4 tint)
                                                               (Econst_int (Int.repr 15) tint)
                                                               tint)
                                                  Sskip
                                                  Sbreak)
                                                (Ssequence
                                                  (Sset _l
                                                    (Ebinop Oadd
                                                      (Evar _thread_lock (tarray (tarray (tptr tvoid) 2) 15))
                                                      (Etempvar _i__4 tint)
                                                      (tptr (tarray (tptr tvoid) 2))))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _acquire 
                                                      (Tfunction
                                                        (Tcons (tptr tvoid)
                                                          Tnil) tvoid
                                                        cc_default))
                                                      ((Ecast
                                                         (Etempvar _l (tptr (tarray (tptr tvoid) 2)))
                                                         (tptr tvoid)) ::
                                                       nil))
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _freelock2 
                                                        (Tfunction
                                                          (Tcons (tptr tvoid)
                                                            Tnil) tvoid
                                                          cc_default))
                                                        ((Ecast
                                                           (Etempvar _l (tptr (tarray (tptr tvoid) 2)))
                                                           (tptr tvoid)) ::
                                                         nil))
                                                      (Scall None
                                                        (Evar _printf 
                                                        (Tfunction
                                                          (Tcons
                                                            (tptr tschar)
                                                            Tnil) tint
                                                          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                                        ((Evar ___stringlit_20 (tarray tschar 27)) ::
                                                         (Etempvar _i__4 tint) ::
                                                         nil))))))
                                              (Sset _i__4
                                                (Ebinop Oadd
                                                  (Etempvar _i__4 tint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tint))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _i__5
                                                (Econst_int (Int.repr 1) tint))
                                              (Sloop
                                                (Ssequence
                                                  (Sifthenelse (Ebinop Ole
                                                                 (Etempvar _i__5 tint)
                                                                 (Econst_int (Int.repr 10) tint)
                                                                 tint)
                                                    Sskip
                                                    Sbreak)
                                                  (Ssequence
                                                    (Sassign
                                                      (Evar _v (tptr tvoid))
                                                      (Ecast
                                                        (Econst_int (Int.repr 0) tint)
                                                        (tptr tvoid)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'10
                                                            (Evar _base_root (tptr (Tstruct _atom_ptr noattr))))
                                                          (Scall (Some _t'8)
                                                            (Evar _find 
                                                            (Tfunction
                                                              (Tcons tint
                                                                (Tcons
                                                                  (tptr (tptr (Tstruct _atom_ptr noattr)))
                                                                  (Tcons
                                                                    (tptr (tptr tvoid))
                                                                    (Tcons
                                                                    (tptr (tptr (Tstruct _atom_ptr noattr)))
                                                                    (Tcons
                                                                    (tptr (tptr tvoid))
                                                                    (Tcons
                                                                    (tptr (Tstruct _atom_ptr noattr))
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr (tptr tvoid))
                                                                    Tnil))))))))
                                                              tint
                                                              cc_default))
                                                            ((Etempvar _i__5 tint) ::
                                                             (Eaddrof
                                                               (Evar _pred (tptr (Tstruct _atom_ptr noattr)))
                                                               (tptr (tptr (Tstruct _atom_ptr noattr)))) ::
                                                             (Eaddrof
                                                               (Evar _pred_op (tptr tvoid))
                                                               (tptr (tptr tvoid))) ::
                                                             (Eaddrof
                                                               (Evar _curr (tptr (Tstruct _atom_ptr noattr)))
                                                               (tptr (tptr (Tstruct _atom_ptr noattr)))) ::
                                                             (Eaddrof
                                                               (Evar _curr_op (tptr tvoid))
                                                               (tptr (tptr tvoid))) ::
                                                             (Etempvar _t'10 (tptr (Tstruct _atom_ptr noattr))) ::
                                                             (Econst_int (Int.repr 1) tint) ::
                                                             (Eaddrof
                                                               (Evar _v (tptr tvoid))
                                                               (tptr (tptr tvoid))) ::
                                                             nil)))
                                                        (Scall None
                                                          (Evar _printf 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr tschar)
                                                              Tnil) tint
                                                            {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                                          ((Evar ___stringlit_21 (tarray tschar 26)) ::
                                                           (Etempvar _i__5 tint) ::
                                                           (Ebinop Oeq
                                                             (Etempvar _t'8 tint)
                                                             (Econst_int (Int.repr 3) tint)
                                                             tint) :: nil)))
                                                      (Ssequence
                                                        (Sset _t'9
                                                          (Evar _v (tptr tvoid)))
                                                        (Scall None
                                                          (Evar _printf 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr tschar)
                                                              Tnil) tint
                                                            {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                                          ((Evar ___stringlit_22 (tarray tschar 11)) ::
                                                           (Etempvar _t'9 (tptr tvoid)) ::
                                                           nil))))))
                                                (Sset _i__5
                                                  (Ebinop Oadd
                                                    (Etempvar _i__5 tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint))))
                                            (Ssequence
                                              (Scall None
                                                (Evar _printf (Tfunction
                                                                (Tcons
                                                                  (tptr tschar)
                                                                  Tnil) tint
                                                                {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                                ((Evar ___stringlit_23 (tarray tschar 23)) ::
                                                 nil))
                                              (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite ___pthread_mutex_t Struct ((___dummy, tschar) :: nil) noattr ::
 Composite ___pthread_cond_t Struct ((___dummy, tschar) :: nil) noattr ::
 Composite _list Struct
   ((_ptr, (tptr tvoid)) :: (_tail, (tptr (Tstruct _list noattr))) :: nil)
   noattr ::
 Composite _tree Struct
   ((_key, tint) :: (_value, (tptr (Tstruct _atom_ptr noattr))) ::
    (_op, (tptr (Tstruct _atom_ptr noattr))) ::
    (_left, (tptr (Tstruct _atom_ptr noattr))) ::
    (_right, (tptr (Tstruct _atom_ptr noattr))) :: nil)
   noattr ::
 Composite _child_cas_operation Struct
   ((_is_left, tint) :: (_expected, (tptr (Tstruct _tree noattr))) ::
    (_update, (tptr (Tstruct _tree noattr))) :: nil)
   noattr ::
 Composite _relocate_operation Struct
   ((_state, (tptr (Tstruct _atom_int noattr))) ::
    (_dest, (tptr (Tstruct _atom_ptr noattr))) :: (_dest_op, (tptr tvoid)) ::
    (_remove_key, tint) :: (_replace_key, tint) ::
    (_replace_value, (tptr tvoid)) :: nil)
   noattr ::
 Composite _arg_struct Struct
   ((_l, (tptr (tarray (tptr tvoid) 2))) :: (_thread_num, tint) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_8, Gvar v___stringlit_8) ::
 (___stringlit_20, Gvar v___stringlit_20) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_10, Gvar v___stringlit_10) ::
 (___stringlit_18, Gvar v___stringlit_18) ::
 (___stringlit_17, Gvar v___stringlit_17) ::
 (___stringlit_16, Gvar v___stringlit_16) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_22, Gvar v___stringlit_22) ::
 (___stringlit_12, Gvar v___stringlit_12) ::
 (___stringlit_21, Gvar v___stringlit_21) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_13, Gvar v___stringlit_13) ::
 (___stringlit_11, Gvar v___stringlit_11) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_14, Gvar v___stringlit_14) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_23, Gvar v___stringlit_23) ::
 (___stringlit_15, Gvar v___stringlit_15) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_9, Gvar v___stringlit_9) ::
 (___stringlit_19, Gvar v___stringlit_19) ::
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
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_pthread_cond_broadcast,
   Gfun(External (EF_external "pthread_cond_broadcast"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (tptr (Tstruct ___pthread_cond_t noattr))) Tnil) tint
     cc_default)) ::
 (_pthread_cond_wait,
   Gfun(External (EF_external "pthread_cond_wait"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr (tptr (Tstruct ___pthread_cond_t noattr)))
       (Tcons (tptr (tptr (Tstruct ___pthread_mutex_t noattr))) Tnil)) tint
     cc_default)) ::
 (_makelock,
   Gfun(External (EF_external "makelock"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_acquire,
   Gfun(External (EF_external "acquire"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_freelock2,
   Gfun(External (EF_external "freelock2"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_release2,
   Gfun(External (EF_external "release2"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_spawn,
   Gfun(External (EF_external "spawn"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons
       (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default))
       (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (_make_atomic,
   Gfun(External (EF_external "make_atomic"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tint Tnil) (tptr (Tstruct _atom_int noattr)) cc_default)) ::
 (_make_atomic_ptr,
   Gfun(External (EF_external "make_atomic_ptr"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) (tptr (Tstruct _atom_ptr noattr)) cc_default)) ::
 (_atom_load,
   Gfun(External (EF_external "atom_load"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr)) Tnil) tint cc_default)) ::
 (_atom_CAS,
   Gfun(External (EF_external "atom_CAS"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr))
       (Tcons (tptr tint) (Tcons tint Tnil))) tint cc_default)) ::
 (_atomic_load_ptr,
   Gfun(External (EF_external "atomic_load_ptr"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _atom_ptr noattr)) Tnil) (tptr tvoid) cc_default)) ::
 (_atomic_store_ptr,
   Gfun(External (EF_external "atomic_store_ptr"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr (Tstruct _atom_ptr noattr)) (Tcons (tptr tvoid) Tnil))
     tvoid cc_default)) ::
 (_atomic_CAS_ptr,
   Gfun(External (EF_external "atomic_CAS_ptr"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _atom_ptr noattr))
       (Tcons (tptr (tptr tvoid)) (Tcons (tptr tvoid) Tnil))) tint
     cc_default)) ::
 (_surely_malloc,
   Gfun(External (EF_external "surely_malloc"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) (tptr tvoid) cc_default)) :: (_cond, Gvar v_cond) ::
 (_hp, Gvar v_hp) :: (_hp_off, Gvar v_hp_off) ::
 (_base_root, Gvar v_base_root) :: (_rp, Gvar v_rp) ::
 (_SET_FLAG, Gfun(Internal f_SET_FLAG)) ::
 (_GET_FLAG, Gfun(Internal f_GET_FLAG)) ::
 (_UNFLAG, Gfun(Internal f_UNFLAG)) ::
 (_SET_NULL, Gfun(Internal f_SET_NULL)) ::
 (_IS_NULL, Gfun(Internal f_IS_NULL)) :: (_tb, Gvar v_tb) ::
 (_thread_lock, Gvar v_thread_lock) ::
 (_add_to_hp_list, Gfun(Internal f_add_to_hp_list)) ::
 (_helpChildCAS, Gfun(Internal f_helpChildCAS)) ::
 (_helpMarked, Gfun(Internal f_helpMarked)) ::
 (_helpRelocate, Gfun(Internal f_helpRelocate)) ::
 (_help, Gfun(Internal f_help)) :: (_find, Gfun(Internal f_find)) ::
 (_add, Gfun(Internal f_add)) :: (_delete, Gfun(Internal f_delete)) ::
 (_thread_func_add, Gfun(Internal f_thread_func_add)) ::
 (_thread_func_find, Gfun(Internal f_thread_func_find)) ::
 (_thread_func_remove, Gfun(Internal f_thread_func_remove)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _thread_func_remove :: _thread_func_find :: _thread_func_add ::
 _delete :: _add :: _find :: _help :: _helpRelocate :: _helpMarked ::
 _helpChildCAS :: _add_to_hp_list :: _thread_lock :: _tb :: _IS_NULL ::
 _SET_NULL :: _UNFLAG :: _GET_FLAG :: _SET_FLAG :: _rp :: _base_root ::
 _hp_off :: _hp :: _cond :: _surely_malloc :: _atomic_CAS_ptr ::
 _atomic_store_ptr :: _atomic_load_ptr :: _atom_CAS :: _atom_load ::
 _make_atomic_ptr :: _make_atomic :: _spawn :: _release2 :: _freelock2 ::
 _acquire :: _makelock :: _pthread_cond_wait :: _pthread_cond_broadcast ::
 _free :: _printf :: ___builtin_debug :: ___builtin_nop ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_memcpy_aligned :: ___builtin_fsqrt :: ___builtin_fabs ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


