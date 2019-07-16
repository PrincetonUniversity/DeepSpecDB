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
  Definition source_file := "btrees.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := 18%positive.
Definition ___builtin_annot : ident := 25%positive.
Definition ___builtin_annot_intval : ident := 26%positive.
Definition ___builtin_bswap : ident := 19%positive.
Definition ___builtin_bswap16 : ident := 21%positive.
Definition ___builtin_bswap32 : ident := 20%positive.
Definition ___builtin_bswap64 : ident := 51%positive.
Definition ___builtin_clz : ident := 52%positive.
Definition ___builtin_clzl : ident := 53%positive.
Definition ___builtin_clzll : ident := 54%positive.
Definition ___builtin_ctz : ident := 55%positive.
Definition ___builtin_ctzl : ident := 56%positive.
Definition ___builtin_ctzll : ident := 57%positive.
Definition ___builtin_debug : ident := 69%positive.
Definition ___builtin_fabs : ident := 22%positive.
Definition ___builtin_fmadd : ident := 60%positive.
Definition ___builtin_fmax : ident := 58%positive.
Definition ___builtin_fmin : ident := 59%positive.
Definition ___builtin_fmsub : ident := 61%positive.
Definition ___builtin_fnmadd : ident := 62%positive.
Definition ___builtin_fnmsub : ident := 63%positive.
Definition ___builtin_fsqrt : ident := 23%positive.
Definition ___builtin_membar : ident := 27%positive.
Definition ___builtin_memcpy_aligned : ident := 24%positive.
Definition ___builtin_nop : ident := 68%positive.
Definition ___builtin_read16_reversed : ident := 64%positive.
Definition ___builtin_read32_reversed : ident := 65%positive.
Definition ___builtin_va_arg : ident := 29%positive.
Definition ___builtin_va_copy : ident := 30%positive.
Definition ___builtin_va_end : ident := 31%positive.
Definition ___builtin_va_start : ident := 28%positive.
Definition ___builtin_write16_reversed : ident := 66%positive.
Definition ___builtin_write32_reversed : ident := 67%positive.
Definition ___compcert_i64_dtos : ident := 36%positive.
Definition ___compcert_i64_dtou : ident := 37%positive.
Definition ___compcert_i64_sar : ident := 48%positive.
Definition ___compcert_i64_sdiv : ident := 42%positive.
Definition ___compcert_i64_shl : ident := 46%positive.
Definition ___compcert_i64_shr : ident := 47%positive.
Definition ___compcert_i64_smod : ident := 44%positive.
Definition ___compcert_i64_smulh : ident := 49%positive.
Definition ___compcert_i64_stod : ident := 38%positive.
Definition ___compcert_i64_stof : ident := 40%positive.
Definition ___compcert_i64_udiv : ident := 43%positive.
Definition ___compcert_i64_umod : ident := 45%positive.
Definition ___compcert_i64_umulh : ident := 50%positive.
Definition ___compcert_i64_utod : ident := 39%positive.
Definition ___compcert_i64_utof : ident := 41%positive.
Definition ___compcert_va_composite : ident := 35%positive.
Definition ___compcert_va_float64 : ident := 34%positive.
Definition ___compcert_va_int32 : ident := 32%positive.
Definition ___compcert_va_int64 : ident := 33%positive.
Definition ___stringlit_1 : ident := 103%positive.
Definition _ancestors : ident := 16%positive.
Definition _btree : ident := 5%positive.
Definition _c : ident := 79%positive.
Definition _cursor : ident := 17%positive.
Definition _cursor_entry : ident := 14%positive.
Definition _depth : ident := 4%positive.
Definition _down_to_first : ident := 81%positive.
Definition _down_to_key : ident := 87%positive.
Definition _entries : ident := 12%positive.
Definition _entry : ident := 8%positive.
Definition _exit : ident := 71%positive.
Definition _find_index : ident := 86%positive.
Definition _get : ident := 89%positive.
Definition _i : ident := 77%positive.
Definition _i__1 : ident := 102%positive.
Definition _index : ident := 13%positive.
Definition _init : ident := 90%positive.
Definition _insert : ident := 101%positive.
Definition _insert_aux : ident := 100%positive.
Definition _insert_entry : ident := 93%positive.
Definition _is_leaf : ident := 9%positive.
Definition _j : ident := 96%positive.
Definition _k : ident := 85%positive.
Definition _key : ident := 6%positive.
Definition _last : ident := 80%positive.
Definition _level : ident := 15%positive.
Definition _main : ident := 104%positive.
Definition _malloc : ident := 70%positive.
Definition _memcpy : ident := 72%positive.
Definition _middle_key : ident := 99%positive.
Definition _move_to_first : ident := 82%positive.
Definition _move_to_key : ident := 88%positive.
Definition _move_to_next : ident := 84%positive.
Definition _n : ident := 76%positive.
Definition _new : ident := 97%positive.
Definition _new__1 : ident := 98%positive.
Definition _new_btree : ident := 75%positive.
Definition _new_cursor : ident := 83%positive.
Definition _new_root : ident := 94%positive.
Definition _next : ident := 92%positive.
Definition _node : ident := 1%positive.
Definition _num_keys : ident := 10%positive.
Definition _num_records : ident := 3%positive.
Definition _old_root : ident := 95%positive.
Definition _printf : ident := 73%positive.
Definition _ptr : ident := 7%positive.
Definition _ptr0 : ident := 11%positive.
Definition _ptr_at : ident := 78%positive.
Definition _rec : ident := 91%positive.
Definition _root : ident := 2%positive.
Definition _t : ident := 74%positive.
Definition _t'1 : ident := 105%positive.
Definition _t'10 : ident := 114%positive.
Definition _t'11 : ident := 115%positive.
Definition _t'12 : ident := 116%positive.
Definition _t'13 : ident := 117%positive.
Definition _t'14 : ident := 118%positive.
Definition _t'15 : ident := 119%positive.
Definition _t'16 : ident := 120%positive.
Definition _t'17 : ident := 121%positive.
Definition _t'18 : ident := 122%positive.
Definition _t'19 : ident := 123%positive.
Definition _t'2 : ident := 106%positive.
Definition _t'20 : ident := 124%positive.
Definition _t'21 : ident := 125%positive.
Definition _t'22 : ident := 126%positive.
Definition _t'23 : ident := 127%positive.
Definition _t'24 : ident := 128%positive.
Definition _t'25 : ident := 129%positive.
Definition _t'26 : ident := 130%positive.
Definition _t'27 : ident := 131%positive.
Definition _t'28 : ident := 132%positive.
Definition _t'29 : ident := 133%positive.
Definition _t'3 : ident := 107%positive.
Definition _t'30 : ident := 134%positive.
Definition _t'31 : ident := 135%positive.
Definition _t'32 : ident := 136%positive.
Definition _t'4 : ident := 108%positive.
Definition _t'5 : ident := 109%positive.
Definition _t'6 : ident := 110%positive.
Definition _t'7 : ident := 111%positive.
Definition _t'8 : ident := 112%positive.
Definition _t'9 : ident := 113%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 4);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_new_btree := {|
  fn_return := (tptr (Tstruct _btree noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t, (tptr (Tstruct _btree noattr))) ::
               (_t'4, (tptr (Tstruct _node noattr))) ::
               (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _btree noattr))) ::
               (_t'1, (tptr tvoid)) ::
               (_t'7, (tptr (Tstruct _node noattr))) ::
               (_t'6, (tptr (Tstruct _node noattr))) ::
               (_t'5, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                          cc_default))
          ((Esizeof (Tstruct _btree noattr) tuint) :: nil))
        (Sset _t'2
          (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _btree noattr)))))
      (Sset _t (Etempvar _t'2 (tptr (Tstruct _btree noattr)))))
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _t'2 (tptr (Tstruct _btree noattr))) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip))
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                            cc_default))
            ((Esizeof (Tstruct _node noattr) tuint) :: nil))
          (Sset _t'4
            (Ecast (Etempvar _t'3 (tptr tvoid))
              (tptr (Tstruct _node noattr)))))
        (Sassign
          (Efield
            (Ederef (Etempvar _t (tptr (Tstruct _btree noattr)))
              (Tstruct _btree noattr)) _root (tptr (Tstruct _node noattr)))
          (Etempvar _t'4 (tptr (Tstruct _node noattr)))))
      (Sifthenelse (Eunop Onotbool
                     (Etempvar _t'4 (tptr (Tstruct _node noattr))) tint)
        (Scall None
          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
          ((Econst_int (Int.repr 1) tint) :: nil))
        Sskip))
    (Ssequence
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _t (tptr (Tstruct _btree noattr)))
              (Tstruct _btree noattr)) _root (tptr (Tstruct _node noattr))))
        (Sassign
          (Efield
            (Ederef (Etempvar _t'7 (tptr (Tstruct _node noattr)))
              (Tstruct _node noattr)) _is_leaf tuint)
          (Econst_int (Int.repr 1) tint)))
      (Ssequence
        (Ssequence
          (Sset _t'6
            (Efield
              (Ederef (Etempvar _t (tptr (Tstruct _btree noattr)))
                (Tstruct _btree noattr)) _root (tptr (Tstruct _node noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _t'6 (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _num_keys tuint)
            (Econst_int (Int.repr 0) tint)))
        (Ssequence
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _t (tptr (Tstruct _btree noattr)))
                  (Tstruct _btree noattr)) _root
                (tptr (Tstruct _node noattr))))
            (Sassign
              (Efield
                (Ederef (Etempvar _t'5 (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _ptr0
                (tptr (Tstruct _node noattr)))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _t (tptr (Tstruct _btree noattr)))
                  (Tstruct _btree noattr)) _num_records tuint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _t (tptr (Tstruct _btree noattr)))
                    (Tstruct _btree noattr)) _depth tuint)
                (Econst_int (Int.repr 0) tint))
              (Sreturn (Some (Etempvar _t (tptr (Tstruct _btree noattr))))))))))))
|}.

Definition f_ptr_at := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_n, (tptr (Tstruct _node noattr))) :: (_i, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 0) tint)
               tint)
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
          (Tstruct _node noattr)) _ptr0 (tptr (Tstruct _node noattr))))
    (Sreturn (Some (Ecast (Etempvar _t'2 (tptr (Tstruct _node noattr)))
                     (tptr tvoid)))))
  (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                 (Ebinop Omul (Econst_int (Int.repr 2) tint)
                   (Econst_int (Int.repr 8) tint) tint) tint)
    (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _entries
                (tarray (Tstruct _entry noattr) 17)) (Etempvar _i tint)
              (tptr (Tstruct _entry noattr))) (Tstruct _entry noattr)) _ptr
          (tptr tvoid)))
      (Sreturn (Some (Etempvar _t'1 (tptr tvoid)))))))
|}.

Definition f_down_to_first := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _cursor noattr))) :: nil);
  fn_vars := ((_last, (Tstruct _cursor_entry noattr)) :: nil);
  fn_temps := ((_t'2, tint) :: (_t'1, (tptr tvoid)) :: (_t'14, tuint) ::
               (_t'13, (tptr (Tstruct _node noattr))) :: (_t'12, tuint) ::
               (_t'11, tuint) :: (_t'10, tuint) :: (_t'9, tint) ::
               (_t'8, (tptr (Tstruct _node noattr))) :: (_t'7, tuint) ::
               (_t'6, tuint) :: (_t'5, (tptr (Tstruct _node noattr))) ::
               (_t'4, tuint) :: (_t'3, tuint) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    (Ssequence
      (Sset _t'12
        (Efield
          (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
            (Tstruct _cursor noattr)) _level tuint))
      (Ssequence
        (Sset _t'13
          (Efield
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                    (Tstruct _cursor noattr)) _ancestors
                  (tarray (Tstruct _cursor_entry noattr) 20))
                (Etempvar _t'12 tuint) (tptr (Tstruct _cursor_entry noattr)))
              (Tstruct _cursor_entry noattr)) _node
            (tptr (Tstruct _node noattr))))
        (Ssequence
          (Sset _t'14
            (Efield
              (Ederef (Etempvar _t'13 (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _is_leaf tuint))
          (Sifthenelse (Eunop Onotbool (Etempvar _t'14 tuint) tint)
            Sskip
            Sbreak))))
    (Ssequence
      (Ssequence
        (Sset _t'11
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
              (Tstruct _cursor noattr)) _level tuint))
        (Sassign (Evar _last (Tstruct _cursor_entry noattr))
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                  (Tstruct _cursor noattr)) _ancestors
                (tarray (Tstruct _cursor_entry noattr) 20))
              (Etempvar _t'11 tuint) (tptr (Tstruct _cursor_entry noattr)))
            (Tstruct _cursor_entry noattr))))
      (Ssequence
        (Ssequence
          (Sset _t'10
            (Efield
              (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                (Tstruct _cursor noattr)) _level tuint))
          (Sassign
            (Efield
              (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                (Tstruct _cursor noattr)) _level tuint)
            (Ebinop Oadd (Etempvar _t'10 tuint)
              (Econst_int (Int.repr 1) tint) tuint)))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'8
                (Efield (Evar _last (Tstruct _cursor_entry noattr)) _node
                  (tptr (Tstruct _node noattr))))
              (Ssequence
                (Sset _t'9
                  (Efield (Evar _last (Tstruct _cursor_entry noattr)) _index
                    tint))
                (Scall (Some _t'1)
                  (Evar _ptr_at (Tfunction
                                  (Tcons (tptr (Tstruct _node noattr))
                                    (Tcons tint Tnil)) (tptr tvoid)
                                  cc_default))
                  ((Etempvar _t'8 (tptr (Tstruct _node noattr))) ::
                   (Etempvar _t'9 tint) :: nil))))
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                    (Tstruct _cursor noattr)) _level tuint))
              (Sassign
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                          (Tstruct _cursor noattr)) _ancestors
                        (tarray (Tstruct _cursor_entry noattr) 20))
                      (Etempvar _t'7 tuint)
                      (tptr (Tstruct _cursor_entry noattr)))
                    (Tstruct _cursor_entry noattr)) _node
                  (tptr (Tstruct _node noattr)))
                (Ecast (Etempvar _t'1 (tptr tvoid))
                  (tptr (Tstruct _node noattr))))))
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                    (Tstruct _cursor noattr)) _level tuint))
              (Ssequence
                (Sset _t'5
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _c (tptr (Tstruct _cursor noattr)))
                            (Tstruct _cursor noattr)) _ancestors
                          (tarray (Tstruct _cursor_entry noattr) 20))
                        (Etempvar _t'4 tuint)
                        (tptr (Tstruct _cursor_entry noattr)))
                      (Tstruct _cursor_entry noattr)) _node
                    (tptr (Tstruct _node noattr))))
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef (Etempvar _t'5 (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _is_leaf tuint))
                  (Sifthenelse (Etempvar _t'6 tuint)
                    (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tint))
                    (Sset _t'2
                      (Ecast (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                        tint))))))
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                    (Tstruct _cursor noattr)) _level tuint))
              (Sassign
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                          (Tstruct _cursor noattr)) _ancestors
                        (tarray (Tstruct _cursor_entry noattr) 20))
                      (Etempvar _t'3 tuint)
                      (tptr (Tstruct _cursor_entry noattr)))
                    (Tstruct _cursor_entry noattr)) _index tint)
                (Etempvar _t'2 tint))))))))
  Sskip)
|}.

Definition f_move_to_first := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: (_t'10, tint) ::
               (_t'9, tuint) :: (_t'8, tuint) :: (_t'7, tuint) ::
               (_t'6, tuint) :: (_t'5, (tptr (Tstruct _node noattr))) ::
               (_t'4, tuint) :: (_t'3, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sloop
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                (Tstruct _cursor noattr)) _level tuint))
          (Sifthenelse (Ebinop Ogt (Etempvar _t'8 tuint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Sset _t'9
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                    (Tstruct _cursor noattr)) _level tuint))
              (Ssequence
                (Sset _t'10
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _c (tptr (Tstruct _cursor noattr)))
                            (Tstruct _cursor noattr)) _ancestors
                          (tarray (Tstruct _cursor_entry noattr) 20))
                        (Etempvar _t'9 tuint)
                        (tptr (Tstruct _cursor_entry noattr)))
                      (Tstruct _cursor_entry noattr)) _index tint))
                (Sset _t'1
                  (Ecast
                    (Ebinop Ogt (Etempvar _t'10 tint)
                      (Econst_int (Int.repr 0) tint) tint) tbool))))
            (Sset _t'1 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
              (Tstruct _cursor noattr)) _level tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
              (Tstruct _cursor noattr)) _level tuint)
          (Ebinop Osub (Etempvar _t'7 tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    Sskip)
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
              (Tstruct _cursor noattr)) _level tuint))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                      (Tstruct _cursor noattr)) _ancestors
                    (tarray (Tstruct _cursor_entry noattr) 20))
                  (Etempvar _t'4 tuint)
                  (tptr (Tstruct _cursor_entry noattr)))
                (Tstruct _cursor_entry noattr)) _node
              (tptr (Tstruct _node noattr))))
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _t'5 (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _is_leaf tuint))
            (Sifthenelse (Etempvar _t'6 tuint)
              (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tint))
              (Sset _t'2
                (Ecast (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint))))))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
              (Tstruct _cursor noattr)) _level tuint))
        (Sassign
          (Efield
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                    (Tstruct _cursor noattr)) _ancestors
                  (tarray (Tstruct _cursor_entry noattr) 20))
                (Etempvar _t'3 tuint) (tptr (Tstruct _cursor_entry noattr)))
              (Tstruct _cursor_entry noattr)) _index tint)
          (Etempvar _t'2 tint))))
    (Ssequence
      (Scall None
        (Evar _down_to_first (Tfunction
                               (Tcons (tptr (Tstruct _cursor noattr)) Tnil)
                               tvoid cc_default))
        ((Etempvar _c (tptr (Tstruct _cursor noattr))) :: nil))
      (Sreturn None))))
|}.

Definition f_new_cursor := {|
  fn_return := (tptr (Tstruct _cursor noattr));
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (Tstruct _btree noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_c, (tptr (Tstruct _cursor noattr))) ::
               (_t'2, (tptr (Tstruct _cursor noattr))) ::
               (_t'1, (tptr tvoid)) ::
               (_t'3, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                          cc_default))
          ((Esizeof (Tstruct _cursor noattr) tuint) :: nil))
        (Sset _t'2
          (Ecast (Etempvar _t'1 (tptr tvoid))
            (tptr (Tstruct _cursor noattr)))))
      (Sset _c (Etempvar _t'2 (tptr (Tstruct _cursor noattr)))))
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _t'2 (tptr (Tstruct _cursor noattr))) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
          (Tstruct _cursor noattr)) _btree (tptr (Tstruct _btree noattr)))
      (Etempvar _t (tptr (Tstruct _btree noattr))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
            (Tstruct _cursor noattr)) _level tuint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _t (tptr (Tstruct _btree noattr)))
                (Tstruct _btree noattr)) _root (tptr (Tstruct _node noattr))))
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                      (Tstruct _cursor noattr)) _ancestors
                    (tarray (Tstruct _cursor_entry noattr) 20))
                  (Econst_int (Int.repr 0) tint)
                  (tptr (Tstruct _cursor_entry noattr)))
                (Tstruct _cursor_entry noattr)) _node
              (tptr (Tstruct _node noattr)))
            (Etempvar _t'3 (tptr (Tstruct _node noattr)))))
        (Ssequence
          (Scall None
            (Evar _move_to_first (Tfunction
                                   (Tcons (tptr (Tstruct _cursor noattr))
                                     Tnil) tvoid cc_default))
            ((Etempvar _c (tptr (Tstruct _cursor noattr))) :: nil))
          (Sreturn (Some (Etempvar _c (tptr (Tstruct _cursor noattr))))))))))
|}.

Definition f_move_to_next := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'18, tuint) ::
               (_t'17, (tptr (Tstruct _node noattr))) :: (_t'16, tuint) ::
               (_t'15, tint) :: (_t'14, tuint) :: (_t'13, tuint) ::
               (_t'12, tuint) :: (_t'11, tuint) ::
               (_t'10, (tptr (Tstruct _btree noattr))) :: (_t'9, tuint) ::
               (_t'8, (tptr (Tstruct _node noattr))) :: (_t'7, tuint) ::
               (_t'6, tint) :: (_t'5, tuint) :: (_t'4, tint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sloop
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'13
            (Efield
              (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                (Tstruct _cursor noattr)) _level tuint))
          (Sifthenelse (Ebinop Ogt (Etempvar _t'13 tuint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Sset _t'14
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                    (Tstruct _cursor noattr)) _level tuint))
              (Ssequence
                (Sset _t'15
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _c (tptr (Tstruct _cursor noattr)))
                            (Tstruct _cursor noattr)) _ancestors
                          (tarray (Tstruct _cursor_entry noattr) 20))
                        (Etempvar _t'14 tuint)
                        (tptr (Tstruct _cursor_entry noattr)))
                      (Tstruct _cursor_entry noattr)) _index tint))
                (Ssequence
                  (Sset _t'16
                    (Efield
                      (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                        (Tstruct _cursor noattr)) _level tuint))
                  (Ssequence
                    (Sset _t'17
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                (Tstruct _cursor noattr)) _ancestors
                              (tarray (Tstruct _cursor_entry noattr) 20))
                            (Etempvar _t'16 tuint)
                            (tptr (Tstruct _cursor_entry noattr)))
                          (Tstruct _cursor_entry noattr)) _node
                        (tptr (Tstruct _node noattr))))
                    (Ssequence
                      (Sset _t'18
                        (Efield
                          (Ederef
                            (Etempvar _t'17 (tptr (Tstruct _node noattr)))
                            (Tstruct _node noattr)) _num_keys tuint))
                      (Sset _t'1
                        (Ecast
                          (Ebinop Oge (Etempvar _t'15 tint)
                            (Ebinop Osub (Etempvar _t'18 tuint)
                              (Econst_int (Int.repr 1) tint) tuint) tint)
                          tbool)))))))
            (Sset _t'1 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
      (Ssequence
        (Sset _t'12
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
              (Tstruct _cursor noattr)) _level tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
              (Tstruct _cursor noattr)) _level tuint)
          (Ebinop Osub (Etempvar _t'12 tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
            (Tstruct _cursor noattr)) _level tuint))
      (Ssequence
        (Sset _t'6
          (Efield
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                    (Tstruct _cursor noattr)) _ancestors
                  (tarray (Tstruct _cursor_entry noattr) 20))
                (Etempvar _t'5 tuint) (tptr (Tstruct _cursor_entry noattr)))
              (Tstruct _cursor_entry noattr)) _index tint))
        (Ssequence
          (Sset _t'7
            (Efield
              (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                (Tstruct _cursor noattr)) _level tuint))
          (Ssequence
            (Sset _t'8
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                        (Tstruct _cursor noattr)) _ancestors
                      (tarray (Tstruct _cursor_entry noattr) 20))
                    (Etempvar _t'7 tuint)
                    (tptr (Tstruct _cursor_entry noattr)))
                  (Tstruct _cursor_entry noattr)) _node
                (tptr (Tstruct _node noattr))))
            (Ssequence
              (Sset _t'9
                (Efield
                  (Ederef (Etempvar _t'8 (tptr (Tstruct _node noattr)))
                    (Tstruct _node noattr)) _num_keys tuint))
              (Sifthenelse (Ebinop Oge (Etempvar _t'6 tint)
                             (Ebinop Osub (Ecast (Etempvar _t'9 tuint) tint)
                               (Econst_int (Int.repr 1) tint) tint) tint)
                (Ssequence
                  (Ssequence
                    (Sset _t'10
                      (Efield
                        (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                          (Tstruct _cursor noattr)) _btree
                        (tptr (Tstruct _btree noattr))))
                    (Ssequence
                      (Sset _t'11
                        (Efield
                          (Ederef
                            (Etempvar _t'10 (tptr (Tstruct _btree noattr)))
                            (Tstruct _btree noattr)) _depth tuint))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _c (tptr (Tstruct _cursor noattr)))
                            (Tstruct _cursor noattr)) _level tuint)
                        (Etempvar _t'11 tuint))))
                  (Sreturn None))
                Sskip))))))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
              (Tstruct _cursor noattr)) _level tuint))
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                (Tstruct _cursor noattr)) _level tuint))
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                        (Tstruct _cursor noattr)) _ancestors
                      (tarray (Tstruct _cursor_entry noattr) 20))
                    (Etempvar _t'3 tuint)
                    (tptr (Tstruct _cursor_entry noattr)))
                  (Tstruct _cursor_entry noattr)) _index tint))
            (Sassign
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                        (Tstruct _cursor noattr)) _ancestors
                      (tarray (Tstruct _cursor_entry noattr) 20))
                    (Etempvar _t'2 tuint)
                    (tptr (Tstruct _cursor_entry noattr)))
                  (Tstruct _cursor_entry noattr)) _index tint)
              (Ebinop Oadd (Etempvar _t'4 tint)
                (Econst_int (Int.repr 1) tint) tint)))))
      (Ssequence
        (Scall None
          (Evar _down_to_first (Tfunction
                                 (Tcons (tptr (Tstruct _cursor noattr)) Tnil)
                                 tvoid cc_default))
          ((Etempvar _c (tptr (Tstruct _cursor noattr))) :: nil))
        (Sreturn None)))))
|}.

Definition f_find_index := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_n, (tptr (Tstruct _node noattr))) :: (_k, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'2, tint) :: (_t'1, tint) :: (_t'7, tuint) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _t'3
      (Efield
        (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
          (Tstruct _node noattr)) _is_leaf tuint))
    (Sifthenelse (Etempvar _t'3 tuint)
      (Ssequence
        (Sloop
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _num_keys tuint))
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Etempvar _t'6 tuint) tint)
                  (Ssequence
                    (Sset _t'7
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _n (tptr (Tstruct _node noattr)))
                                (Tstruct _node noattr)) _entries
                              (tarray (Tstruct _entry noattr) 17))
                            (Etempvar _i tint)
                            (tptr (Tstruct _entry noattr)))
                          (Tstruct _entry noattr)) _key tuint))
                    (Sset _t'1
                      (Ecast
                        (Ebinop Olt (Etempvar _t'7 tuint) (Etempvar _k tuint)
                          tint) tbool)))
                  (Sset _t'1 (Econst_int (Int.repr 0) tint))))
              (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint)))
          Sskip)
        (Sreturn (Some (Etempvar _i tint))))
      (Ssequence
        (Sloop
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _num_keys tuint))
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Etempvar _t'4 tuint) tint)
                  (Ssequence
                    (Sset _t'5
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _n (tptr (Tstruct _node noattr)))
                                (Tstruct _node noattr)) _entries
                              (tarray (Tstruct _entry noattr) 17))
                            (Etempvar _i tint)
                            (tptr (Tstruct _entry noattr)))
                          (Tstruct _entry noattr)) _key tuint))
                    (Sset _t'2
                      (Ecast
                        (Ebinop Ole (Etempvar _t'5 tuint) (Etempvar _k tuint)
                          tint) tbool)))
                  (Sset _t'2 (Econst_int (Int.repr 0) tint))))
              (Sifthenelse (Etempvar _t'2 tint) Sskip Sbreak))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint)))
          Sskip)
        (Sreturn (Some (Ebinop Osub (Etempvar _i tint)
                         (Econst_int (Int.repr 1) tint) tint)))))))
|}.

Definition f_down_to_key := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _cursor noattr))) :: (_k, tuint) :: nil);
  fn_vars := ((_last, (Tstruct _cursor_entry noattr)) :: nil);
  fn_temps := ((_t'2, tint) :: (_t'1, (tptr tvoid)) :: (_t'13, tuint) ::
               (_t'12, (tptr (Tstruct _node noattr))) :: (_t'11, tuint) ::
               (_t'10, tuint) :: (_t'9, tuint) :: (_t'8, tint) ::
               (_t'7, (tptr (Tstruct _node noattr))) :: (_t'6, tuint) ::
               (_t'5, (tptr (Tstruct _node noattr))) :: (_t'4, tuint) ::
               (_t'3, tuint) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    (Ssequence
      (Sset _t'11
        (Efield
          (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
            (Tstruct _cursor noattr)) _level tuint))
      (Ssequence
        (Sset _t'12
          (Efield
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                    (Tstruct _cursor noattr)) _ancestors
                  (tarray (Tstruct _cursor_entry noattr) 20))
                (Etempvar _t'11 tuint) (tptr (Tstruct _cursor_entry noattr)))
              (Tstruct _cursor_entry noattr)) _node
            (tptr (Tstruct _node noattr))))
        (Ssequence
          (Sset _t'13
            (Efield
              (Ederef (Etempvar _t'12 (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _is_leaf tuint))
          (Sifthenelse (Eunop Onotbool (Etempvar _t'13 tuint) tint)
            Sskip
            Sbreak))))
    (Ssequence
      (Ssequence
        (Sset _t'10
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
              (Tstruct _cursor noattr)) _level tuint))
        (Sassign (Evar _last (Tstruct _cursor_entry noattr))
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                  (Tstruct _cursor noattr)) _ancestors
                (tarray (Tstruct _cursor_entry noattr) 20))
              (Etempvar _t'10 tuint) (tptr (Tstruct _cursor_entry noattr)))
            (Tstruct _cursor_entry noattr))))
      (Ssequence
        (Ssequence
          (Sset _t'9
            (Efield
              (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                (Tstruct _cursor noattr)) _level tuint))
          (Sassign
            (Efield
              (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                (Tstruct _cursor noattr)) _level tuint)
            (Ebinop Oadd (Etempvar _t'9 tuint) (Econst_int (Int.repr 1) tint)
              tuint)))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'7
                (Efield (Evar _last (Tstruct _cursor_entry noattr)) _node
                  (tptr (Tstruct _node noattr))))
              (Ssequence
                (Sset _t'8
                  (Efield (Evar _last (Tstruct _cursor_entry noattr)) _index
                    tint))
                (Scall (Some _t'1)
                  (Evar _ptr_at (Tfunction
                                  (Tcons (tptr (Tstruct _node noattr))
                                    (Tcons tint Tnil)) (tptr tvoid)
                                  cc_default))
                  ((Etempvar _t'7 (tptr (Tstruct _node noattr))) ::
                   (Etempvar _t'8 tint) :: nil))))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                    (Tstruct _cursor noattr)) _level tuint))
              (Sassign
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                          (Tstruct _cursor noattr)) _ancestors
                        (tarray (Tstruct _cursor_entry noattr) 20))
                      (Etempvar _t'6 tuint)
                      (tptr (Tstruct _cursor_entry noattr)))
                    (Tstruct _cursor_entry noattr)) _node
                  (tptr (Tstruct _node noattr)))
                (Ecast (Etempvar _t'1 (tptr tvoid))
                  (tptr (Tstruct _node noattr))))))
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                    (Tstruct _cursor noattr)) _level tuint))
              (Ssequence
                (Sset _t'5
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _c (tptr (Tstruct _cursor noattr)))
                            (Tstruct _cursor noattr)) _ancestors
                          (tarray (Tstruct _cursor_entry noattr) 20))
                        (Etempvar _t'4 tuint)
                        (tptr (Tstruct _cursor_entry noattr)))
                      (Tstruct _cursor_entry noattr)) _node
                    (tptr (Tstruct _node noattr))))
                (Scall (Some _t'2)
                  (Evar _find_index (Tfunction
                                      (Tcons (tptr (Tstruct _node noattr))
                                        (Tcons tuint Tnil)) tint cc_default))
                  ((Etempvar _t'5 (tptr (Tstruct _node noattr))) ::
                   (Etempvar _k tuint) :: nil))))
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                    (Tstruct _cursor noattr)) _level tuint))
              (Sassign
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                          (Tstruct _cursor noattr)) _ancestors
                        (tarray (Tstruct _cursor_entry noattr) 20))
                      (Etempvar _t'3 tuint)
                      (tptr (Tstruct _cursor_entry noattr)))
                    (Tstruct _cursor_entry noattr)) _index tint)
                (Etempvar _t'2 tint))))))))
  Sskip)
|}.

Definition f_move_to_key := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _cursor noattr))) :: (_k, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: (_t'16, tuint) ::
               (_t'15, tuint) :: (_t'14, (tptr (Tstruct _node noattr))) ::
               (_t'13, tuint) :: (_t'12, (tptr (Tstruct _node noattr))) ::
               (_t'11, tuint) :: (_t'10, tuint) ::
               (_t'9, (tptr (Tstruct _node noattr))) :: (_t'8, tuint) ::
               (_t'7, tuint) :: (_t'6, tuint) ::
               (_t'5, (tptr (Tstruct _node noattr))) :: (_t'4, tuint) ::
               (_t'3, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sloop
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'7
            (Efield
              (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                (Tstruct _cursor noattr)) _level tuint))
          (Sifthenelse (Ebinop Ogt (Etempvar _t'7 tuint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Sset _t'8
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                    (Tstruct _cursor noattr)) _level tuint))
              (Ssequence
                (Sset _t'9
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _c (tptr (Tstruct _cursor noattr)))
                            (Tstruct _cursor noattr)) _ancestors
                          (tarray (Tstruct _cursor_entry noattr) 20))
                        (Etempvar _t'8 tuint)
                        (tptr (Tstruct _cursor_entry noattr)))
                      (Tstruct _cursor_entry noattr)) _node
                    (tptr (Tstruct _node noattr))))
                (Ssequence
                  (Sset _t'10
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _t'9 (tptr (Tstruct _node noattr)))
                              (Tstruct _node noattr)) _entries
                            (tarray (Tstruct _entry noattr) 17))
                          (Econst_int (Int.repr 0) tint)
                          (tptr (Tstruct _entry noattr)))
                        (Tstruct _entry noattr)) _key tuint))
                  (Sifthenelse (Ebinop Olt (Etempvar _k tuint)
                                 (Etempvar _t'10 tuint) tint)
                    (Sset _t'1 (Ecast (Econst_int (Int.repr 1) tint) tbool))
                    (Ssequence
                      (Ssequence
                        (Sset _t'11
                          (Efield
                            (Ederef
                              (Etempvar _c (tptr (Tstruct _cursor noattr)))
                              (Tstruct _cursor noattr)) _level tuint))
                        (Ssequence
                          (Sset _t'12
                            (Efield
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                      (Tstruct _cursor noattr)) _ancestors
                                    (tarray (Tstruct _cursor_entry noattr) 20))
                                  (Etempvar _t'11 tuint)
                                  (tptr (Tstruct _cursor_entry noattr)))
                                (Tstruct _cursor_entry noattr)) _node
                              (tptr (Tstruct _node noattr))))
                          (Ssequence
                            (Sset _t'13
                              (Efield
                                (Ederef
                                  (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                  (Tstruct _cursor noattr)) _level tuint))
                            (Ssequence
                              (Sset _t'14
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                          (Tstruct _cursor noattr))
                                        _ancestors
                                        (tarray (Tstruct _cursor_entry noattr) 20))
                                      (Etempvar _t'13 tuint)
                                      (tptr (Tstruct _cursor_entry noattr)))
                                    (Tstruct _cursor_entry noattr)) _node
                                  (tptr (Tstruct _node noattr))))
                              (Ssequence
                                (Sset _t'15
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'14 (tptr (Tstruct _node noattr)))
                                      (Tstruct _node noattr)) _num_keys
                                    tuint))
                                (Ssequence
                                  (Sset _t'16
                                    (Efield
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _t'12 (tptr (Tstruct _node noattr)))
                                              (Tstruct _node noattr))
                                            _entries
                                            (tarray (Tstruct _entry noattr) 17))
                                          (Ebinop Osub (Etempvar _t'15 tuint)
                                            (Econst_int (Int.repr 1) tint)
                                            tuint)
                                          (tptr (Tstruct _entry noattr)))
                                        (Tstruct _entry noattr)) _key tuint))
                                  (Sset _t'1
                                    (Ecast
                                      (Ebinop Ogt (Etempvar _k tuint)
                                        (Etempvar _t'16 tuint) tint) tbool))))))))
                      (Sset _t'1 (Ecast (Etempvar _t'1 tint) tbool)))))))
            (Sset _t'1 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
      (Ssequence
        (Sset _t'6
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
              (Tstruct _cursor noattr)) _level tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
              (Tstruct _cursor noattr)) _level tuint)
          (Ebinop Osub (Etempvar _t'6 tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    Sskip)
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
              (Tstruct _cursor noattr)) _level tuint))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                      (Tstruct _cursor noattr)) _ancestors
                    (tarray (Tstruct _cursor_entry noattr) 20))
                  (Etempvar _t'4 tuint)
                  (tptr (Tstruct _cursor_entry noattr)))
                (Tstruct _cursor_entry noattr)) _node
              (tptr (Tstruct _node noattr))))
          (Scall (Some _t'2)
            (Evar _find_index (Tfunction
                                (Tcons (tptr (Tstruct _node noattr))
                                  (Tcons tuint Tnil)) tint cc_default))
            ((Etempvar _t'5 (tptr (Tstruct _node noattr))) ::
             (Etempvar _k tuint) :: nil))))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
              (Tstruct _cursor noattr)) _level tuint))
        (Sassign
          (Efield
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                    (Tstruct _cursor noattr)) _ancestors
                  (tarray (Tstruct _cursor_entry noattr) 20))
                (Etempvar _t'3 tuint) (tptr (Tstruct _cursor_entry noattr)))
              (Tstruct _cursor_entry noattr)) _index tint)
          (Etempvar _t'2 tint))))
    (Ssequence
      (Scall None
        (Evar _down_to_key (Tfunction
                             (Tcons (tptr (Tstruct _cursor noattr))
                               (Tcons tuint Tnil)) tvoid cc_default))
        ((Etempvar _c (tptr (Tstruct _cursor noattr))) ::
         (Etempvar _k tuint) :: nil))
      (Sreturn None))))
|}.

Definition f_get := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _cursor noattr))) :: (_k, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: (_t'5, tint) :: (_t'4, tuint) ::
               (_t'3, (tptr (Tstruct _node noattr))) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _move_to_key (Tfunction
                         (Tcons (tptr (Tstruct _cursor noattr))
                           (Tcons tuint Tnil)) tvoid cc_default))
    ((Etempvar _c (tptr (Tstruct _cursor noattr))) :: (Etempvar _k tuint) ::
     nil))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
            (Tstruct _cursor noattr)) _level tuint))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                    (Tstruct _cursor noattr)) _ancestors
                  (tarray (Tstruct _cursor_entry noattr) 20))
                (Etempvar _t'2 tuint) (tptr (Tstruct _cursor_entry noattr)))
              (Tstruct _cursor_entry noattr)) _node
            (tptr (Tstruct _node noattr))))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                (Tstruct _cursor noattr)) _level tuint))
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                        (Tstruct _cursor noattr)) _ancestors
                      (tarray (Tstruct _cursor_entry noattr) 20))
                    (Etempvar _t'4 tuint)
                    (tptr (Tstruct _cursor_entry noattr)))
                  (Tstruct _cursor_entry noattr)) _index tint))
            (Scall (Some _t'1)
              (Evar _ptr_at (Tfunction
                              (Tcons (tptr (Tstruct _node noattr))
                                (Tcons tint Tnil)) (tptr tvoid) cc_default))
              ((Etempvar _t'3 (tptr (Tstruct _node noattr))) ::
               (Etempvar _t'5 tint) :: nil))))))
    (Sreturn (Some (Etempvar _t'1 (tptr tvoid))))))
|}.

Definition f_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _move_to_first (Tfunction
                         (Tcons (tptr (Tstruct _cursor noattr)) Tnil) tvoid
                         cc_default))
  ((Etempvar _c (tptr (Tstruct _cursor noattr))) :: nil))
|}.

Definition f_next := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_rec, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'5, tint) :: (_t'4, tuint) ::
               (_t'3, (tptr (Tstruct _node noattr))) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
            (Tstruct _cursor noattr)) _level tuint))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                    (Tstruct _cursor noattr)) _ancestors
                  (tarray (Tstruct _cursor_entry noattr) 20))
                (Etempvar _t'2 tuint) (tptr (Tstruct _cursor_entry noattr)))
              (Tstruct _cursor_entry noattr)) _node
            (tptr (Tstruct _node noattr))))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                (Tstruct _cursor noattr)) _level tuint))
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                        (Tstruct _cursor noattr)) _ancestors
                      (tarray (Tstruct _cursor_entry noattr) 20))
                    (Etempvar _t'4 tuint)
                    (tptr (Tstruct _cursor_entry noattr)))
                  (Tstruct _cursor_entry noattr)) _index tint))
            (Scall (Some _t'1)
              (Evar _ptr_at (Tfunction
                              (Tcons (tptr (Tstruct _node noattr))
                                (Tcons tint Tnil)) (tptr tvoid) cc_default))
              ((Etempvar _t'3 (tptr (Tstruct _node noattr))) ::
               (Etempvar _t'5 tint) :: nil))))))
    (Sset _rec (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Scall None
      (Evar _move_to_next (Tfunction
                            (Tcons (tptr (Tstruct _cursor noattr)) Tnil)
                            tvoid cc_default))
      ((Etempvar _c (tptr (Tstruct _cursor noattr))) :: nil))
    (Sreturn (Some (Etempvar _rec (tptr tvoid))))))
|}.

Definition f_insert_entry := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_n, (tptr (Tstruct _node noattr))) :: (_i, tuint) ::
                (_k, tuint) :: (_ptr, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_c, tint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _c
      (Efield
        (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
          (Tstruct _node noattr)) _num_keys tuint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Ogt (Etempvar _c tint) (Etempvar _i tuint) tint)
          Sskip
          Sbreak)
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _entries
                (tarray (Tstruct _entry noattr) 17)) (Etempvar _c tint)
              (tptr (Tstruct _entry noattr))) (Tstruct _entry noattr))
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _entries
                (tarray (Tstruct _entry noattr) 17))
              (Ebinop Osub (Etempvar _c tint) (Econst_int (Int.repr 1) tint)
                tint) (tptr (Tstruct _entry noattr)))
            (Tstruct _entry noattr))))
      (Sset _c
        (Ebinop Osub (Etempvar _c tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _entries
              (tarray (Tstruct _entry noattr) 17)) (Etempvar _i tuint)
            (tptr (Tstruct _entry noattr))) (Tstruct _entry noattr)) _key
        tuint) (Etempvar _k tuint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _entries
                (tarray (Tstruct _entry noattr) 17)) (Etempvar _i tuint)
              (tptr (Tstruct _entry noattr))) (Tstruct _entry noattr)) _ptr
          (tptr tvoid)) (Etempvar _ptr (tptr tvoid)))
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
              (Tstruct _node noattr)) _num_keys tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
              (Tstruct _node noattr)) _num_keys tuint)
          (Ebinop Oadd (Etempvar _t'1 tuint) (Econst_int (Int.repr 1) tint)
            tuint))))))
|}.

Definition f_insert_aux := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _cursor noattr))) :: (_level, tint) ::
                (_k, tuint) :: (_ptr, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_new_root, (tptr (Tstruct _node noattr))) ::
               (_old_root, (tptr (Tstruct _node noattr))) :: (_j, tuint) ::
               (_i, tint) :: (_n, (tptr (Tstruct _node noattr))) ::
               (_new, (tptr (Tstruct _node noattr))) ::
               (_new__1, (tptr (Tstruct _node noattr))) ::
               (_middle_key, tuint) ::
               (_t'8, (tptr (Tstruct _node noattr))) ::
               (_t'7, (tptr tvoid)) :: (_t'6, tint) ::
               (_t'5, (tptr (Tstruct _node noattr))) ::
               (_t'4, (tptr tvoid)) :: (_t'3, tint) ::
               (_t'2, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr tvoid)) :: (_t'32, tuint) ::
               (_t'31, (tptr (Tstruct _btree noattr))) ::
               (_t'30, (tptr (Tstruct _btree noattr))) ::
               (_t'29, (tptr (Tstruct _btree noattr))) :: (_t'28, tuint) ::
               (_t'27, (tptr (Tstruct _btree noattr))) ::
               (_t'26, (tptr (Tstruct _btree noattr))) :: (_t'25, tuint) ::
               (_t'24, (tptr (Tstruct _btree noattr))) ::
               (_t'23, (tptr (Tstruct _btree noattr))) :: (_t'22, tint) ::
               (_t'21, tuint) :: (_t'20, tuint) :: (_t'19, tuint) ::
               (_t'18, (tptr (Tstruct _btree noattr))) ::
               (_t'17, (tptr (Tstruct _btree noattr))) :: (_t'16, tuint) ::
               (_t'15, tuint) :: (_t'14, tuint) ::
               (_t'13, (tptr (Tstruct _btree noattr))) ::
               (_t'12, (tptr (Tstruct _btree noattr))) ::
               (_t'11, (tptr tvoid)) :: (_t'10, tuint) :: (_t'9, tuint) ::
               nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Etempvar _level tint)
                 (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint)
    (Ssequence
      (Ssequence
        (Sset _t'31
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
              (Tstruct _cursor noattr)) _btree
            (tptr (Tstruct _btree noattr))))
        (Ssequence
          (Sset _t'32
            (Efield
              (Ederef (Etempvar _t'31 (tptr (Tstruct _btree noattr)))
                (Tstruct _btree noattr)) _depth tuint))
          (Sifthenelse (Ebinop Oge (Etempvar _t'32 tuint)
                         (Ebinop Osub (Econst_int (Int.repr 20) tint)
                           (Econst_int (Int.repr 1) tint) tint) tint)
            (Scall None
              (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
              ((Econst_int (Int.repr 1) tint) :: nil))
            Sskip)))
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                cc_default))
                ((Esizeof (Tstruct _node noattr) tuint) :: nil))
              (Sset _t'2
                (Ecast (Etempvar _t'1 (tptr tvoid))
                  (tptr (Tstruct _node noattr)))))
            (Sset _new_root (Etempvar _t'2 (tptr (Tstruct _node noattr)))))
          (Sifthenelse (Eunop Onotbool
                         (Etempvar _t'2 (tptr (Tstruct _node noattr))) tint)
            (Scall None
              (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
              ((Econst_int (Int.repr 1) tint) :: nil))
            Sskip))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _new_root (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _is_leaf tuint)
            (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _new_root (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _num_keys tuint)
              (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Ssequence
                (Sset _t'30
                  (Efield
                    (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                      (Tstruct _cursor noattr)) _btree
                    (tptr (Tstruct _btree noattr))))
                (Sset _old_root
                  (Efield
                    (Ederef (Etempvar _t'30 (tptr (Tstruct _btree noattr)))
                      (Tstruct _btree noattr)) _root
                    (tptr (Tstruct _node noattr)))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _new_root (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _ptr0
                    (tptr (Tstruct _node noattr)))
                  (Etempvar _old_root (tptr (Tstruct _node noattr))))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _new_root (tptr (Tstruct _node noattr)))
                              (Tstruct _node noattr)) _entries
                            (tarray (Tstruct _entry noattr) 17))
                          (Econst_int (Int.repr 0) tint)
                          (tptr (Tstruct _entry noattr)))
                        (Tstruct _entry noattr)) _key tuint)
                    (Etempvar _k tuint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _new_root (tptr (Tstruct _node noattr)))
                                (Tstruct _node noattr)) _entries
                              (tarray (Tstruct _entry noattr) 17))
                            (Econst_int (Int.repr 0) tint)
                            (tptr (Tstruct _entry noattr)))
                          (Tstruct _entry noattr)) _ptr (tptr tvoid))
                      (Etempvar _ptr (tptr tvoid)))
                    (Ssequence
                      (Ssequence
                        (Sset _t'29
                          (Efield
                            (Ederef
                              (Etempvar _c (tptr (Tstruct _cursor noattr)))
                              (Tstruct _cursor noattr)) _btree
                            (tptr (Tstruct _btree noattr))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _t'29 (tptr (Tstruct _btree noattr)))
                              (Tstruct _btree noattr)) _root
                            (tptr (Tstruct _node noattr)))
                          (Etempvar _new_root (tptr (Tstruct _node noattr)))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'26
                            (Efield
                              (Ederef
                                (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                (Tstruct _cursor noattr)) _btree
                              (tptr (Tstruct _btree noattr))))
                          (Ssequence
                            (Sset _t'27
                              (Efield
                                (Ederef
                                  (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                  (Tstruct _cursor noattr)) _btree
                                (tptr (Tstruct _btree noattr))))
                            (Ssequence
                              (Sset _t'28
                                (Efield
                                  (Ederef
                                    (Etempvar _t'27 (tptr (Tstruct _btree noattr)))
                                    (Tstruct _btree noattr)) _num_records
                                  tuint))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _t'26 (tptr (Tstruct _btree noattr)))
                                    (Tstruct _btree noattr)) _num_records
                                  tuint)
                                (Ebinop Oadd (Etempvar _t'28 tuint)
                                  (Econst_int (Int.repr 1) tint) tuint)))))
                        (Ssequence
                          (Ssequence
                            (Sset _t'23
                              (Efield
                                (Ederef
                                  (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                  (Tstruct _cursor noattr)) _btree
                                (tptr (Tstruct _btree noattr))))
                            (Ssequence
                              (Sset _t'24
                                (Efield
                                  (Ederef
                                    (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                    (Tstruct _cursor noattr)) _btree
                                  (tptr (Tstruct _btree noattr))))
                              (Ssequence
                                (Sset _t'25
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'24 (tptr (Tstruct _btree noattr)))
                                      (Tstruct _btree noattr)) _depth tuint))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'23 (tptr (Tstruct _btree noattr)))
                                      (Tstruct _btree noattr)) _depth tuint)
                                  (Ebinop Oadd (Etempvar _t'25 tuint)
                                    (Econst_int (Int.repr 1) tint) tuint)))))
                          (Ssequence
                            (Sset _j
                              (Efield
                                (Ederef
                                  (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                  (Tstruct _cursor noattr)) _level tuint))
                            (Ssequence
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Ogt
                                                 (Etempvar _j tuint)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    Sskip
                                    Sbreak)
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                            (Tstruct _cursor noattr))
                                          _ancestors
                                          (tarray (Tstruct _cursor_entry noattr) 20))
                                        (Etempvar _j tuint)
                                        (tptr (Tstruct _cursor_entry noattr)))
                                      (Tstruct _cursor_entry noattr))
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                            (Tstruct _cursor noattr))
                                          _ancestors
                                          (tarray (Tstruct _cursor_entry noattr) 20))
                                        (Ebinop Osub (Etempvar _j tuint)
                                          (Econst_int (Int.repr 1) tint)
                                          tuint)
                                        (tptr (Tstruct _cursor_entry noattr)))
                                      (Tstruct _cursor_entry noattr))))
                                (Sset _j
                                  (Ebinop Osub (Etempvar _j tuint)
                                    (Econst_int (Int.repr 1) tint) tuint)))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                            (Tstruct _cursor noattr))
                                          _ancestors
                                          (tarray (Tstruct _cursor_entry noattr) 20))
                                        (Econst_int (Int.repr 0) tint)
                                        (tptr (Tstruct _cursor_entry noattr)))
                                      (Tstruct _cursor_entry noattr)) _node
                                    (tptr (Tstruct _node noattr)))
                                  (Etempvar _new_root (tptr (Tstruct _node noattr))))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'22
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                                  (Tstruct _cursor noattr))
                                                _ancestors
                                                (tarray (Tstruct _cursor_entry noattr) 20))
                                              (Econst_int (Int.repr 1) tint)
                                              (tptr (Tstruct _cursor_entry noattr)))
                                            (Tstruct _cursor_entry noattr))
                                          _index tint))
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _t'22 tint)
                                                     (Ebinop Osub
                                                       (Econst_int (Int.repr 8) tint)
                                                       (Econst_int (Int.repr 1) tint)
                                                       tint) tint)
                                        (Sset _t'3
                                          (Ecast
                                            (Eunop Oneg
                                              (Econst_int (Int.repr 1) tint)
                                              tint) tint))
                                        (Sset _t'3
                                          (Ecast
                                            (Econst_int (Int.repr 0) tint)
                                            tint))))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                                (Tstruct _cursor noattr))
                                              _ancestors
                                              (tarray (Tstruct _cursor_entry noattr) 20))
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr (Tstruct _cursor_entry noattr)))
                                          (Tstruct _cursor_entry noattr))
                                        _index tint) (Etempvar _t'3 tint)))
                                  (Sreturn None))))))))))))))))
    Sskip)
  (Ssequence
    (Sset _i
      (Efield
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                (Tstruct _cursor noattr)) _ancestors
              (tarray (Tstruct _cursor_entry noattr) 20))
            (Etempvar _level tint) (tptr (Tstruct _cursor_entry noattr)))
          (Tstruct _cursor_entry noattr)) _index tint))
    (Ssequence
      (Sset _n
        (Efield
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                  (Tstruct _cursor noattr)) _ancestors
                (tarray (Tstruct _cursor_entry noattr) 20))
              (Etempvar _level tint) (tptr (Tstruct _cursor_entry noattr)))
            (Tstruct _cursor_entry noattr)) _node
          (tptr (Tstruct _node noattr))))
      (Ssequence
        (Ssequence
          (Sset _t'9
            (Efield
              (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _is_leaf tuint))
          (Sifthenelse (Etempvar _t'9 tuint)
            (Ssequence
              (Ssequence
                (Sset _t'20
                  (Efield
                    (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _num_keys tuint))
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Etempvar _t'20 tuint) tint)
                  (Ssequence
                    (Sset _t'21
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _n (tptr (Tstruct _node noattr)))
                                (Tstruct _node noattr)) _entries
                              (tarray (Tstruct _entry noattr) 17))
                            (Etempvar _i tint)
                            (tptr (Tstruct _entry noattr)))
                          (Tstruct _entry noattr)) _key tuint))
                    (Sset _t'6
                      (Ecast
                        (Ebinop Oeq (Etempvar _t'21 tuint)
                          (Etempvar _k tuint) tint) tbool)))
                  (Sset _t'6 (Econst_int (Int.repr 0) tint))))
              (Sifthenelse (Etempvar _t'6 tint)
                (Sassign
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                            (Tstruct _node noattr)) _entries
                          (tarray (Tstruct _entry noattr) 17))
                        (Etempvar _i tint) (tptr (Tstruct _entry noattr)))
                      (Tstruct _entry noattr)) _ptr (tptr tvoid))
                  (Etempvar _ptr (tptr tvoid)))
                (Ssequence
                  (Sset _t'15
                    (Efield
                      (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _num_keys tuint))
                  (Sifthenelse (Ebinop Olt (Etempvar _t'15 tuint)
                                 (Ebinop Omul (Econst_int (Int.repr 2) tint)
                                   (Econst_int (Int.repr 8) tint) tint) tint)
                    (Ssequence
                      (Scall None
                        (Evar _insert_entry (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _node noattr))
                                                (Tcons tuint
                                                  (Tcons tuint
                                                    (Tcons (tptr tvoid) Tnil))))
                                              tvoid cc_default))
                        ((Etempvar _n (tptr (Tstruct _node noattr))) ::
                         (Etempvar _i tint) :: (Etempvar _k tuint) ::
                         (Etempvar _ptr (tptr tvoid)) :: nil))
                      (Ssequence
                        (Sset _t'17
                          (Efield
                            (Ederef
                              (Etempvar _c (tptr (Tstruct _cursor noattr)))
                              (Tstruct _cursor noattr)) _btree
                            (tptr (Tstruct _btree noattr))))
                        (Ssequence
                          (Sset _t'18
                            (Efield
                              (Ederef
                                (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                (Tstruct _cursor noattr)) _btree
                              (tptr (Tstruct _btree noattr))))
                          (Ssequence
                            (Sset _t'19
                              (Efield
                                (Ederef
                                  (Etempvar _t'18 (tptr (Tstruct _btree noattr)))
                                  (Tstruct _btree noattr)) _num_records
                                tuint))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _t'17 (tptr (Tstruct _btree noattr)))
                                  (Tstruct _btree noattr)) _num_records
                                tuint)
                              (Ebinop Oadd (Etempvar _t'19 tuint)
                                (Econst_int (Int.repr 1) tint) tuint))))))
                    (Ssequence
                      (Scall None
                        (Evar _insert_entry (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _node noattr))
                                                (Tcons tuint
                                                  (Tcons tuint
                                                    (Tcons (tptr tvoid) Tnil))))
                                              tvoid cc_default))
                        ((Etempvar _n (tptr (Tstruct _node noattr))) ::
                         (Etempvar _i tint) :: (Etempvar _k tuint) ::
                         (Etempvar _ptr (tptr tvoid)) :: nil))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'4)
                                (Evar _malloc (Tfunction (Tcons tuint Tnil)
                                                (tptr tvoid) cc_default))
                                ((Esizeof (Tstruct _node noattr) tuint) ::
                                 nil))
                              (Sset _t'5
                                (Ecast (Etempvar _t'4 (tptr tvoid))
                                  (tptr (Tstruct _node noattr)))))
                            (Sset _new
                              (Etempvar _t'5 (tptr (Tstruct _node noattr)))))
                          (Sifthenelse (Eunop Onotbool
                                         (Etempvar _t'5 (tptr (Tstruct _node noattr)))
                                         tint)
                            (Scall None
                              (Evar _exit (Tfunction (Tcons tint Tnil) tvoid
                                            cc_default))
                              ((Econst_int (Int.repr 1) tint) :: nil))
                            Sskip))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _new (tptr (Tstruct _node noattr)))
                                (Tstruct _node noattr)) _ptr0
                              (tptr (Tstruct _node noattr)))
                            (Ecast (Econst_int (Int.repr 0) tint)
                              (tptr tvoid)))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _new (tptr (Tstruct _node noattr)))
                                  (Tstruct _node noattr)) _is_leaf tuint)
                              (Econst_int (Int.repr 1) tint))
                            (Ssequence
                              (Scall None
                                (Evar _memcpy (Tfunction
                                                (Tcons (tptr tvoid)
                                                  (Tcons (tptr tvoid)
                                                    (Tcons tuint Tnil)))
                                                (tptr tvoid) cc_default))
                                ((Efield
                                   (Ederef
                                     (Etempvar _new (tptr (Tstruct _node noattr)))
                                     (Tstruct _node noattr)) _entries
                                   (tarray (Tstruct _entry noattr) 17)) ::
                                 (Ebinop Oadd
                                   (Efield
                                     (Ederef
                                       (Etempvar _n (tptr (Tstruct _node noattr)))
                                       (Tstruct _node noattr)) _entries
                                     (tarray (Tstruct _entry noattr) 17))
                                   (Econst_int (Int.repr 8) tint)
                                   (tptr (Tstruct _entry noattr))) ::
                                 (Ebinop Omul
                                   (Ebinop Oadd
                                     (Econst_int (Int.repr 8) tint)
                                     (Econst_int (Int.repr 1) tint) tint)
                                   (Esizeof (Tstruct _entry noattr) tuint)
                                   tuint) :: nil))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _new (tptr (Tstruct _node noattr)))
                                      (Tstruct _node noattr)) _num_keys
                                    tuint)
                                  (Ebinop Oadd (Econst_int (Int.repr 8) tint)
                                    (Econst_int (Int.repr 1) tint) tint))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _n (tptr (Tstruct _node noattr)))
                                        (Tstruct _node noattr)) _num_keys
                                      tuint) (Econst_int (Int.repr 8) tint))
                                  (Ssequence
                                    (Sset _t'16
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _new (tptr (Tstruct _node noattr)))
                                                (Tstruct _node noattr))
                                              _entries
                                              (tarray (Tstruct _entry noattr) 17))
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr (Tstruct _entry noattr)))
                                          (Tstruct _entry noattr)) _key
                                        tuint))
                                    (Scall None
                                      (Evar _insert_aux (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _cursor noattr))
                                                            (Tcons tint
                                                              (Tcons tuint
                                                                (Tcons
                                                                  (tptr tvoid)
                                                                  Tnil))))
                                                          tvoid cc_default))
                                      ((Etempvar _c (tptr (Tstruct _cursor noattr))) ::
                                       (Ebinop Osub (Etempvar _level tint)
                                         (Econst_int (Int.repr 1) tint) tint) ::
                                       (Etempvar _t'16 tuint) ::
                                       (Ecast
                                         (Etempvar _new (tptr (Tstruct _node noattr)))
                                         (tptr tvoid)) :: nil))))))))))))))
            (Ssequence
              (Sset _t'10
                (Efield
                  (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                    (Tstruct _node noattr)) _num_keys tuint))
              (Sifthenelse (Ebinop Olt (Etempvar _t'10 tuint)
                             (Ebinop Omul (Econst_int (Int.repr 2) tint)
                               (Econst_int (Int.repr 8) tint) tint) tint)
                (Ssequence
                  (Scall None
                    (Evar _insert_entry (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _node noattr))
                                            (Tcons tuint
                                              (Tcons tuint
                                                (Tcons (tptr tvoid) Tnil))))
                                          tvoid cc_default))
                    ((Etempvar _n (tptr (Tstruct _node noattr))) ::
                     (Ebinop Oadd (Etempvar _i tint)
                       (Econst_int (Int.repr 1) tint) tint) ::
                     (Etempvar _k tuint) :: (Etempvar _ptr (tptr tvoid)) ::
                     nil))
                  (Ssequence
                    (Sset _t'12
                      (Efield
                        (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
                          (Tstruct _cursor noattr)) _btree
                        (tptr (Tstruct _btree noattr))))
                    (Ssequence
                      (Sset _t'13
                        (Efield
                          (Ederef
                            (Etempvar _c (tptr (Tstruct _cursor noattr)))
                            (Tstruct _cursor noattr)) _btree
                          (tptr (Tstruct _btree noattr))))
                      (Ssequence
                        (Sset _t'14
                          (Efield
                            (Ederef
                              (Etempvar _t'13 (tptr (Tstruct _btree noattr)))
                              (Tstruct _btree noattr)) _num_records tuint))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _t'12 (tptr (Tstruct _btree noattr)))
                              (Tstruct _btree noattr)) _num_records tuint)
                          (Ebinop Oadd (Etempvar _t'14 tuint)
                            (Econst_int (Int.repr 1) tint) tuint))))))
                (Ssequence
                  (Scall None
                    (Evar _insert_entry (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _node noattr))
                                            (Tcons tuint
                                              (Tcons tuint
                                                (Tcons (tptr tvoid) Tnil))))
                                          tvoid cc_default))
                    ((Etempvar _n (tptr (Tstruct _node noattr))) ::
                     (Ebinop Oadd (Etempvar _i tint)
                       (Econst_int (Int.repr 1) tint) tint) ::
                     (Etempvar _k tuint) :: (Etempvar _ptr (tptr tvoid)) ::
                     nil))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'7)
                            (Evar _malloc (Tfunction (Tcons tuint Tnil)
                                            (tptr tvoid) cc_default))
                            ((Esizeof (Tstruct _node noattr) tuint) :: nil))
                          (Sset _t'8
                            (Ecast (Etempvar _t'7 (tptr tvoid))
                              (tptr (Tstruct _node noattr)))))
                        (Sset _new__1
                          (Etempvar _t'8 (tptr (Tstruct _node noattr)))))
                      (Sifthenelse (Eunop Onotbool
                                     (Etempvar _t'8 (tptr (Tstruct _node noattr)))
                                     tint)
                        (Scall None
                          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid
                                        cc_default))
                          ((Econst_int (Int.repr 1) tint) :: nil))
                        Sskip))
                    (Ssequence
                      (Sset _middle_key
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _n (tptr (Tstruct _node noattr)))
                                  (Tstruct _node noattr)) _entries
                                (tarray (Tstruct _entry noattr) 17))
                              (Econst_int (Int.repr 8) tint)
                              (tptr (Tstruct _entry noattr)))
                            (Tstruct _entry noattr)) _key tuint))
                      (Ssequence
                        (Ssequence
                          (Sset _t'11
                            (Efield
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _n (tptr (Tstruct _node noattr)))
                                      (Tstruct _node noattr)) _entries
                                    (tarray (Tstruct _entry noattr) 17))
                                  (Econst_int (Int.repr 8) tint)
                                  (tptr (Tstruct _entry noattr)))
                                (Tstruct _entry noattr)) _ptr (tptr tvoid)))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _new__1 (tptr (Tstruct _node noattr)))
                                (Tstruct _node noattr)) _ptr0
                              (tptr (Tstruct _node noattr)))
                            (Ecast (Etempvar _t'11 (tptr tvoid))
                              (tptr (Tstruct _node noattr)))))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _new__1 (tptr (Tstruct _node noattr)))
                                (Tstruct _node noattr)) _is_leaf tuint)
                            (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Scall None
                              (Evar _memcpy (Tfunction
                                              (Tcons (tptr tvoid)
                                                (Tcons (tptr tvoid)
                                                  (Tcons tuint Tnil)))
                                              (tptr tvoid) cc_default))
                              ((Efield
                                 (Ederef
                                   (Etempvar _new__1 (tptr (Tstruct _node noattr)))
                                   (Tstruct _node noattr)) _entries
                                 (tarray (Tstruct _entry noattr) 17)) ::
                               (Ebinop Oadd
                                 (Ebinop Oadd
                                   (Efield
                                     (Ederef
                                       (Etempvar _n (tptr (Tstruct _node noattr)))
                                       (Tstruct _node noattr)) _entries
                                     (tarray (Tstruct _entry noattr) 17))
                                   (Econst_int (Int.repr 8) tint)
                                   (tptr (Tstruct _entry noattr)))
                                 (Econst_int (Int.repr 1) tint)
                                 (tptr (Tstruct _entry noattr))) ::
                               (Ebinop Omul
                                 (Ebinop Oadd (Econst_int (Int.repr 8) tint)
                                   (Econst_int (Int.repr 1) tint) tint)
                                 (Esizeof (Tstruct _entry noattr) tuint)
                                 tuint) :: nil))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _new__1 (tptr (Tstruct _node noattr)))
                                    (Tstruct _node noattr)) _num_keys tuint)
                                (Econst_int (Int.repr 8) tint))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _n (tptr (Tstruct _node noattr)))
                                      (Tstruct _node noattr)) _num_keys
                                    tuint) (Econst_int (Int.repr 8) tint))
                                (Scall None
                                  (Evar _insert_aux (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _cursor noattr))
                                                        (Tcons tint
                                                          (Tcons tuint
                                                            (Tcons
                                                              (tptr tvoid)
                                                              Tnil)))) tvoid
                                                      cc_default))
                                  ((Etempvar _c (tptr (Tstruct _cursor noattr))) ::
                                   (Ebinop Osub (Etempvar _level tint)
                                     (Econst_int (Int.repr 1) tint) tint) ::
                                   (Etempvar _middle_key tuint) ::
                                   (Ecast
                                     (Etempvar _new__1 (tptr (Tstruct _node noattr)))
                                     (tptr tvoid)) :: nil))))))))))))))
        (Sreturn None)))))
|}.

Definition f_insert := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _cursor noattr))) :: (_k, tuint) ::
                (_ptr, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _move_to_key (Tfunction
                         (Tcons (tptr (Tstruct _cursor noattr))
                           (Tcons tuint Tnil)) tvoid cc_default))
    ((Etempvar _c (tptr (Tstruct _cursor noattr))) :: (Etempvar _k tuint) ::
     nil))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _c (tptr (Tstruct _cursor noattr)))
          (Tstruct _cursor noattr)) _level tuint))
    (Scall None
      (Evar _insert_aux (Tfunction
                          (Tcons (tptr (Tstruct _cursor noattr))
                            (Tcons tint
                              (Tcons tuint (Tcons (tptr tvoid) Tnil)))) tvoid
                          cc_default))
      ((Etempvar _c (tptr (Tstruct _cursor noattr))) ::
       (Etempvar _t'1 tuint) :: (Etempvar _k tuint) ::
       (Etempvar _ptr (tptr tvoid)) :: nil))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t, (tptr (Tstruct _btree noattr))) ::
               (_c, (tptr (Tstruct _cursor noattr))) :: (_i, tint) ::
               (_i__1, tint) :: (_t'2, (tptr (Tstruct _cursor noattr))) ::
               (_t'1, (tptr (Tstruct _btree noattr))) :: (_t'7, tuint) ::
               (_t'6, tint) :: (_t'5, tuint) ::
               (_t'4, (tptr (Tstruct _node noattr))) :: (_t'3, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _new_btree (Tfunction Tnil (tptr (Tstruct _btree noattr))
                           cc_default)) nil)
      (Sset _t (Etempvar _t'1 (tptr (Tstruct _btree noattr)))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _new_cursor (Tfunction
                              (Tcons (tptr (Tstruct _btree noattr)) Tnil)
                              (tptr (Tstruct _cursor noattr)) cc_default))
          ((Etempvar _t (tptr (Tstruct _btree noattr))) :: nil))
        (Sset _c (Etempvar _t'2 (tptr (Tstruct _cursor noattr)))))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 100) tint) tint)
                Sskip
                Sbreak)
              (Scall None
                (Evar _insert (Tfunction
                                (Tcons (tptr (Tstruct _cursor noattr))
                                  (Tcons tuint (Tcons (tptr tvoid) Tnil)))
                                tvoid cc_default))
                ((Etempvar _c (tptr (Tstruct _cursor noattr))) ::
                 (Ebinop Omul (Econst_int (Int.repr 2) tint)
                   (Etempvar _i tint) tint) ::
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) :: nil)))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Scall None
            (Evar _insert (Tfunction
                            (Tcons (tptr (Tstruct _cursor noattr))
                              (Tcons tuint (Tcons (tptr tvoid) Tnil))) tvoid
                            cc_default))
            ((Etempvar _c (tptr (Tstruct _cursor noattr))) ::
             (Econst_int (Int.repr 11) tint) ::
             (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) :: nil))
          (Ssequence
            (Scall None
              (Evar _insert (Tfunction
                              (Tcons (tptr (Tstruct _cursor noattr))
                                (Tcons tuint (Tcons (tptr tvoid) Tnil)))
                              tvoid cc_default))
              ((Etempvar _c (tptr (Tstruct _cursor noattr))) ::
               (Econst_int (Int.repr 33) tint) ::
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) :: nil))
            (Ssequence
              (Scall None
                (Evar _move_to_key (Tfunction
                                     (Tcons (tptr (Tstruct _cursor noattr))
                                       (Tcons tuint Tnil)) tvoid cc_default))
                ((Etempvar _c (tptr (Tstruct _cursor noattr))) ::
                 (Econst_int (Int.repr 0) tint) :: nil))
              (Ssequence
                (Ssequence
                  (Sset _i__1 (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i__1 tint)
                                     (Econst_int (Int.repr 102) tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Ssequence
                          (Sset _t'3
                            (Efield
                              (Ederef
                                (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                (Tstruct _cursor noattr)) _level tuint))
                          (Ssequence
                            (Sset _t'4
                              (Efield
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                        (Tstruct _cursor noattr)) _ancestors
                                      (tarray (Tstruct _cursor_entry noattr) 20))
                                    (Etempvar _t'3 tuint)
                                    (tptr (Tstruct _cursor_entry noattr)))
                                  (Tstruct _cursor_entry noattr)) _node
                                (tptr (Tstruct _node noattr))))
                            (Ssequence
                              (Sset _t'5
                                (Efield
                                  (Ederef
                                    (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                    (Tstruct _cursor noattr)) _level tuint))
                              (Ssequence
                                (Sset _t'6
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _c (tptr (Tstruct _cursor noattr)))
                                            (Tstruct _cursor noattr))
                                          _ancestors
                                          (tarray (Tstruct _cursor_entry noattr) 20))
                                        (Etempvar _t'5 tuint)
                                        (tptr (Tstruct _cursor_entry noattr)))
                                      (Tstruct _cursor_entry noattr)) _index
                                    tint))
                                (Ssequence
                                  (Sset _t'7
                                    (Efield
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _t'4 (tptr (Tstruct _node noattr)))
                                              (Tstruct _node noattr))
                                            _entries
                                            (tarray (Tstruct _entry noattr) 17))
                                          (Etempvar _t'6 tint)
                                          (tptr (Tstruct _entry noattr)))
                                        (Tstruct _entry noattr)) _key tuint))
                                  (Scall None
                                    (Evar _printf (Tfunction
                                                    (Tcons (tptr tschar)
                                                      Tnil) tint
                                                    {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                    ((Evar ___stringlit_1 (tarray tschar 4)) ::
                                     (Etempvar _t'7 tuint) :: nil)))))))
                        (Scall None
                          (Evar _move_to_next (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _cursor noattr))
                                                  Tnil) tvoid cc_default))
                          ((Etempvar _c (tptr (Tstruct _cursor noattr))) ::
                           nil))))
                    (Sset _i__1
                      (Ebinop Oadd (Etempvar _i__1 tint)
                        (Econst_int (Int.repr 1) tint) tint))))
                (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _btree Struct
   ((_root, (tptr (Tstruct _node noattr))) :: (_num_records, tuint) ::
    (_depth, tuint) :: nil)
   noattr ::
 Composite _entry Struct
   ((_key, tuint) :: (_ptr, (tptr tvoid)) :: nil)
   noattr ::
 Composite _node Struct
   ((_is_leaf, tuint) :: (_num_keys, tuint) ::
    (_ptr0, (tptr (Tstruct _node noattr))) ::
    (_entries, (tarray (Tstruct _entry noattr) 17)) :: nil)
   noattr ::
 Composite _cursor_entry Struct
   ((_index, tint) :: (_node, (tptr (Tstruct _node noattr))) :: nil)
   noattr ::
 Composite _cursor Struct
   ((_btree, (tptr (Tstruct _btree noattr))) :: (_level, tuint) ::
    (_ancestors, (tarray (Tstruct _cursor_entry noattr) 20)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_1, Gvar v___stringlit_1) ::
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
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
     (tptr tvoid) cc_default)) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_new_btree, Gfun(Internal f_new_btree)) ::
 (_ptr_at, Gfun(Internal f_ptr_at)) ::
 (_down_to_first, Gfun(Internal f_down_to_first)) ::
 (_move_to_first, Gfun(Internal f_move_to_first)) ::
 (_new_cursor, Gfun(Internal f_new_cursor)) ::
 (_move_to_next, Gfun(Internal f_move_to_next)) ::
 (_find_index, Gfun(Internal f_find_index)) ::
 (_down_to_key, Gfun(Internal f_down_to_key)) ::
 (_move_to_key, Gfun(Internal f_move_to_key)) ::
 (_get, Gfun(Internal f_get)) :: (_init, Gfun(Internal f_init)) ::
 (_next, Gfun(Internal f_next)) ::
 (_insert_entry, Gfun(Internal f_insert_entry)) ::
 (_insert_aux, Gfun(Internal f_insert_aux)) ::
 (_insert, Gfun(Internal f_insert)) :: (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _insert :: _insert_aux :: _insert_entry :: _next :: _init ::
 _get :: _move_to_key :: _down_to_key :: _find_index :: _move_to_next ::
 _new_cursor :: _move_to_first :: _down_to_first :: _ptr_at :: _new_btree ::
 _printf :: _memcpy :: _exit :: _malloc :: ___builtin_debug ::
 ___builtin_nop :: ___builtin_write32_reversed ::
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


