From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.5"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "64"%string.
  Definition abi := "macosx"%string.
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "db_operations.c"%string.
  Definition normalized := true.
End Info.

Definition _Column : ident := 6%positive.
Definition _Cursor : ident := 13%positive.
Definition _DBIndex : ident := 18%positive.
Definition _Element : ident := 21%positive.
Definition _Iempty : ident := 80%positive.
Definition _Iput : ident := 81%positive.
Definition _KVKey : ident := 75%positive.
Definition _KVStore : ident := 15%positive.
Definition _KV_NewKVStore : ident := 77%positive.
Definition _KV_NewKey : ident := 76%positive.
Definition _KV_Put : ident := 78%positive.
Definition _Node : ident := 2%positive.
Definition _RL_NewCursor : ident := 79%positive.
Definition _Relation : ident := 11%positive.
Definition _Schema : ident := 10%positive.
Definition ___builtin_annot : ident := 28%positive.
Definition ___builtin_annot_intval : ident := 29%positive.
Definition ___builtin_bswap : ident := 22%positive.
Definition ___builtin_bswap16 : ident := 24%positive.
Definition ___builtin_bswap32 : ident := 23%positive.
Definition ___builtin_bswap64 : ident := 54%positive.
Definition ___builtin_clz : ident := 55%positive.
Definition ___builtin_clzl : ident := 56%positive.
Definition ___builtin_clzll : ident := 57%positive.
Definition ___builtin_ctz : ident := 58%positive.
Definition ___builtin_ctzl : ident := 59%positive.
Definition ___builtin_ctzll : ident := 60%positive.
Definition ___builtin_debug : ident := 72%positive.
Definition ___builtin_fabs : ident := 25%positive.
Definition ___builtin_fmadd : ident := 63%positive.
Definition ___builtin_fmax : ident := 61%positive.
Definition ___builtin_fmin : ident := 62%positive.
Definition ___builtin_fmsub : ident := 64%positive.
Definition ___builtin_fnmadd : ident := 65%positive.
Definition ___builtin_fnmsub : ident := 66%positive.
Definition ___builtin_fsqrt : ident := 26%positive.
Definition ___builtin_membar : ident := 30%positive.
Definition ___builtin_memcpy_aligned : ident := 27%positive.
Definition ___builtin_nop : ident := 71%positive.
Definition ___builtin_read16_reversed : ident := 67%positive.
Definition ___builtin_read32_reversed : ident := 68%positive.
Definition ___builtin_va_arg : ident := 32%positive.
Definition ___builtin_va_copy : ident := 33%positive.
Definition ___builtin_va_end : ident := 34%positive.
Definition ___builtin_va_start : ident := 31%positive.
Definition ___builtin_write16_reversed : ident := 69%positive.
Definition ___builtin_write32_reversed : ident := 70%positive.
Definition ___compcert_i64_dtos : ident := 39%positive.
Definition ___compcert_i64_dtou : ident := 40%positive.
Definition ___compcert_i64_sar : ident := 51%positive.
Definition ___compcert_i64_sdiv : ident := 45%positive.
Definition ___compcert_i64_shl : ident := 49%positive.
Definition ___compcert_i64_shr : ident := 50%positive.
Definition ___compcert_i64_smod : ident := 47%positive.
Definition ___compcert_i64_smulh : ident := 52%positive.
Definition ___compcert_i64_stod : ident := 41%positive.
Definition ___compcert_i64_stof : ident := 43%positive.
Definition ___compcert_i64_udiv : ident := 46%positive.
Definition ___compcert_i64_umod : ident := 48%positive.
Definition ___compcert_i64_umulh : ident := 53%positive.
Definition ___compcert_i64_utod : ident := 42%positive.
Definition ___compcert_i64_utof : ident := 44%positive.
Definition ___compcert_va_composite : ident := 38%positive.
Definition ___compcert_va_float64 : ident := 37%positive.
Definition ___compcert_va_int32 : ident := 35%positive.
Definition ___compcert_va_int64 : ident := 36%positive.
Definition __res : ident := 86%positive.
Definition _arr : ident := 87%positive.
Definition _arrLen : ident := 88%positive.
Definition _b : ident := 103%positive.
Definition _col : ident := 92%positive.
Definition _cols : ident := 8%positive.
Definition _create : ident := 104%positive.
Definition _ctr : ident := 84%positive.
Definition _current : ident := 83%positive.
Definition _cursor : ident := 14%positive.
Definition _exit : ident := 73%positive.
Definition _i : ident := 94%positive.
Definition _i__1 : ident := 98%positive.
Definition _index : ident := 89%positive.
Definition _int_elt : ident := 19%positive.
Definition _item : ident := 96%positive.
Definition _item__1 : ident := 100%positive.
Definition _key : ident := 97%positive.
Definition _keyType : ident := 17%positive.
Definition _key__1 : ident := 102%positive.
Definition _main : ident := 105%positive.
Definition _name : ident := 4%positive.
Definition _next : ident := 3%positive.
Definition _next_col : ident := 7%positive.
Definition _offset : ident := 91%positive.
Definition _pk_col_nums : ident := 9%positive.
Definition _rowLen : ident := 90%positive.
Definition _sch_len : ident := 85%positive.
Definition _schema : ident := 82%positive.
Definition _str : ident := 101%positive.
Definition _str_elt : ident := 20%positive.
Definition _strlen : ident := 74%positive.
Definition _tree : ident := 12%positive.
Definition _trie : ident := 16%positive.
Definition _val : ident := 1%positive.
Definition _valType : ident := 93%positive.
Definition _val_type : ident := 5%positive.
Definition _values : ident := 95%positive.
Definition _values__1 : ident := 99%positive.
Definition _t'1 : ident := 106%positive.
Definition _t'10 : ident := 115%positive.
Definition _t'11 : ident := 116%positive.
Definition _t'12 : ident := 117%positive.
Definition _t'13 : ident := 118%positive.
Definition _t'14 : ident := 119%positive.
Definition _t'15 : ident := 120%positive.
Definition _t'2 : ident := 107%positive.
Definition _t'3 : ident := 108%positive.
Definition _t'4 : ident := 109%positive.
Definition _t'5 : ident := 110%positive.
Definition _t'6 : ident := 111%positive.
Definition _t'7 : ident := 112%positive.
Definition _t'8 : ident := 113%positive.
Definition _t'9 : ident := 114%positive.

Definition f_sch_len := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_schema, (tptr (Tstruct _Schema noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_current, (tptr (Tstruct _Column noattr))) ::
               (_ctr, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _current
    (Efield
      (Ederef (Etempvar _schema (tptr (Tstruct _Schema noattr)))
        (Tstruct _Schema noattr)) _cols (tptr (Tstruct _Column noattr))))
  (Ssequence
    (Sset _ctr (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Ssequence
      (Swhile
        (Ebinop One (Etempvar _current (tptr (Tstruct _Column noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
        (Ssequence
          (Sset _ctr
            (Ebinop Oadd (Etempvar _ctr tulong)
              (Econst_int (Int.repr 1) tint) tulong))
          (Sset _current
            (Efield
              (Ederef (Etempvar _current (tptr (Tstruct _Column noattr)))
                (Tstruct _Column noattr)) _next_col
              (tptr (Tstruct _Column noattr))))))
      (Sreturn (Some (Etempvar _ctr tulong))))))
|}.

Definition f_create := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _DBIndex noattr))) ::
                (_arr, (tptr (Tunion _Element noattr))) :: (_arrLen, tint) ::
                (_schema, (tptr (Tstruct _Schema noattr))) :: nil);
  fn_vars := ((_index, (Tstruct _DBIndex noattr)) ::
              (_item, (Tunion _Element noattr)) ::
              (_item__1, (Tunion _Element noattr)) :: nil);
  fn_temps := ((_rowLen, tulong) :: (_offset, tulong) ::
               (_col, (tptr (Tstruct _Column noattr))) ::
               (_valType, tschar) :: (_ctr, tulong) :: (_i, tint) ::
               (_values, (tptr (Tunion _Element noattr))) ::
               (_key, tulong) :: (_i__1, tint) ::
               (_values__1, (tptr (Tunion _Element noattr))) ::
               (_str, (tptr tschar)) ::
               (_key__1, (tptr (Tstruct _KVKey noattr))) :: (_b, tint) ::
               (_t'7, tint) :: (_t'6, (tptr (Tstruct _KVKey noattr))) ::
               (_t'5, tulong) :: (_t'4, (tptr (Tstruct _KVStore noattr))) ::
               (_t'3, (tptr (Tstruct _Cursor noattr))) ::
               (_t'2, (tptr tvoid)) :: (_t'1, tulong) ::
               (_t'15, (tptr (Tstruct _Node noattr))) :: (_t'14, tschar) ::
               (_t'13, (tptr (Tstruct _Relation noattr))) ::
               (_t'12, (tptr (Tstruct _Relation noattr))) ::
               (_t'11, (tptr (Tstruct _Cursor noattr))) ::
               (_t'10, (tptr (Tstruct _Cursor noattr))) ::
               (_t'9, (tptr (Tstruct _KVStore noattr))) ::
               (_t'8, (tptr (Tstruct _KVStore noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _sch_len (Tfunction (Tcons (tptr (Tstruct _Schema noattr)) Tnil)
                       tulong cc_default))
      ((Etempvar _schema (tptr (Tstruct _Schema noattr))) :: nil))
    (Sset _rowLen (Etempvar _t'1 tulong)))
  (Ssequence
    (Ssequence
      (Sset _t'15
        (Efield
          (Ederef (Etempvar _schema (tptr (Tstruct _Schema noattr)))
            (Tstruct _Schema noattr)) _pk_col_nums
          (tptr (Tstruct _Node noattr))))
      (Sset _offset
        (Efield
          (Ederef (Etempvar _t'15 (tptr (Tstruct _Node noattr)))
            (Tstruct _Node noattr)) _val tulong)))
    (Ssequence
      (Sset _col
        (Efield
          (Ederef (Etempvar _schema (tptr (Tstruct _Schema noattr)))
            (Tstruct _Schema noattr)) _cols (tptr (Tstruct _Column noattr))))
      (Ssequence
        (Sset _valType (Ecast (Econst_int (Int.repr 117) tint) tschar))
        (Ssequence
          (Sset _ctr (Ecast (Econst_int (Int.repr 0) tint) tulong))
          (Ssequence
            (Swhile
              (Ebinop One (Etempvar _col (tptr (Tstruct _Column noattr)))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Etempvar _ctr tulong)
                               (Etempvar _offset tulong) tint)
                  (Ssequence
                    (Ssequence
                      (Sset _t'14
                        (Efield
                          (Ederef
                            (Etempvar _col (tptr (Tstruct _Column noattr)))
                            (Tstruct _Column noattr)) _val_type tschar))
                      (Sset _valType (Ecast (Etempvar _t'14 tschar) tschar)))
                    Sbreak)
                  Sskip)
                (Ssequence
                  (Sset _col
                    (Efield
                      (Ederef (Etempvar _col (tptr (Tstruct _Column noattr)))
                        (Tstruct _Column noattr)) _next_col
                      (tptr (Tstruct _Column noattr))))
                  (Sset _ctr
                    (Ebinop Oadd (Etempvar _ctr tulong)
                      (Econst_int (Int.repr 1) tint) tulong)))))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _valType tschar)
                             (Econst_int (Int.repr 105) tint) tint)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'2)
                      (Evar _Iempty (Tfunction Tnil (tptr tvoid) cc_default))
                      nil)
                    (Sassign
                      (Efield (Evar _index (Tstruct _DBIndex noattr)) _tree
                        (tptr (Tstruct _Relation noattr)))
                      (Etempvar _t'2 (tptr tvoid))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'13
                        (Efield (Evar _index (Tstruct _DBIndex noattr)) _tree
                          (tptr (Tstruct _Relation noattr))))
                      (Sifthenelse (Ebinop Oeq
                                     (Etempvar _t'13 (tptr (Tstruct _Relation noattr)))
                                     (Ecast (Econst_int (Int.repr 0) tint)
                                       (tptr tvoid)) tint)
                        (Scall None
                          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid
                                        cc_default))
                          ((Econst_int (Int.repr 1) tint) :: nil))
                        Sskip))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'12
                            (Efield (Evar _index (Tstruct _DBIndex noattr))
                              _tree (tptr (Tstruct _Relation noattr))))
                          (Scall (Some _t'3)
                            (Evar _RL_NewCursor (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _Relation noattr))
                                                    Tnil)
                                                  (tptr (Tstruct _Cursor noattr))
                                                  cc_default))
                            ((Etempvar _t'12 (tptr (Tstruct _Relation noattr))) ::
                             nil)))
                        (Sassign
                          (Efield (Evar _index (Tstruct _DBIndex noattr))
                            _cursor (tptr (Tstruct _Cursor noattr)))
                          (Etempvar _t'3 (tptr (Tstruct _Cursor noattr)))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'11
                            (Efield (Evar _index (Tstruct _DBIndex noattr))
                              _cursor (tptr (Tstruct _Cursor noattr))))
                          (Sifthenelse (Ebinop Oeq
                                         (Etempvar _t'11 (tptr (Tstruct _Cursor noattr)))
                                         (Ecast
                                           (Econst_int (Int.repr 0) tint)
                                           (tptr tvoid)) tint)
                            (Scall None
                              (Evar _exit (Tfunction (Tcons tint Tnil) tvoid
                                            cc_default))
                              ((Econst_int (Int.repr 1) tint) :: nil))
                            Sskip))
                        (Ssequence
                          (Sassign
                            (Efield (Evar _index (Tstruct _DBIndex noattr))
                              _keyType tschar)
                            (Econst_int (Int.repr 105) tint))
                          (Ssequence
                            (Sset _i (Econst_int (Int.repr 0) tint))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                               (Etempvar _arrLen tint) tint)
                                  Sskip
                                  Sbreak)
                                (Ssequence
                                  (Sset _values
                                    (Ebinop Oadd
                                      (Etempvar _arr (tptr (Tunion _Element noattr)))
                                      (Etempvar _i tint)
                                      (tptr (Tunion _Element noattr))))
                                  (Ssequence
                                    (Sassign
                                      (Evar _item (Tunion _Element noattr))
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _arr (tptr (Tunion _Element noattr)))
                                          (Ebinop Oadd (Etempvar _i tint)
                                            (Etempvar _offset tulong) tulong)
                                          (tptr (Tunion _Element noattr)))
                                        (Tunion _Element noattr)))
                                    (Ssequence
                                      (Sset _key
                                        (Efield
                                          (Evar _item (Tunion _Element noattr))
                                          _int_elt tulong))
                                      (Ssequence
                                        (Sset _t'10
                                          (Efield
                                            (Evar _index (Tstruct _DBIndex noattr))
                                            _cursor
                                            (tptr (Tstruct _Cursor noattr))))
                                        (Scall None
                                          (Evar _Iput (Tfunction
                                                        (Tcons tulong
                                                          (Tcons (tptr tvoid)
                                                            (Tcons
                                                              (tptr tvoid)
                                                              Tnil))) tvoid
                                                        cc_default))
                                          ((Etempvar _key tulong) ::
                                           (Etempvar _values (tptr (Tunion _Element noattr))) ::
                                           (Etempvar _t'10 (tptr (Tstruct _Cursor noattr))) ::
                                           nil)))))))
                              (Sset _i
                                (Ecast
                                  (Ebinop Oadd (Etempvar _i tint)
                                    (Etempvar _rowLen tulong) tulong) tint)))))))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'4)
                      (Evar _KV_NewKVStore (Tfunction Tnil
                                             (tptr (Tstruct _KVStore noattr))
                                             cc_default)) nil)
                    (Sassign
                      (Efield (Evar _index (Tstruct _DBIndex noattr)) _trie
                        (tptr (Tstruct _KVStore noattr)))
                      (Etempvar _t'4 (tptr (Tstruct _KVStore noattr)))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'9
                        (Efield (Evar _index (Tstruct _DBIndex noattr)) _trie
                          (tptr (Tstruct _KVStore noattr))))
                      (Sifthenelse (Ebinop Oeq
                                     (Etempvar _t'9 (tptr (Tstruct _KVStore noattr)))
                                     (Ecast (Econst_int (Int.repr 0) tint)
                                       (tptr tvoid)) tint)
                        (Scall None
                          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid
                                        cc_default))
                          ((Econst_int (Int.repr 1) tint) :: nil))
                        Sskip))
                    (Ssequence
                      (Sassign
                        (Efield (Evar _index (Tstruct _DBIndex noattr))
                          _keyType tschar) (Econst_int (Int.repr 115) tint))
                      (Ssequence
                        (Sset _i__1 (Econst_int (Int.repr 0) tint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _i__1 tint)
                                           (Etempvar _arrLen tint) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Sset _values__1
                                (Ebinop Oadd
                                  (Etempvar _arr (tptr (Tunion _Element noattr)))
                                  (Etempvar _i__1 tint)
                                  (tptr (Tunion _Element noattr))))
                              (Ssequence
                                (Sassign
                                  (Evar _item__1 (Tunion _Element noattr))
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _arr (tptr (Tunion _Element noattr)))
                                      (Ebinop Oadd (Etempvar _i__1 tint)
                                        (Etempvar _offset tulong) tulong)
                                      (tptr (Tunion _Element noattr)))
                                    (Tunion _Element noattr)))
                                (Ssequence
                                  (Sset _str
                                    (Efield
                                      (Evar _item__1 (Tunion _Element noattr))
                                      _str_elt (tptr tschar)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'5)
                                          (Evar _strlen (Tfunction
                                                          (Tcons
                                                            (tptr tschar)
                                                            Tnil) tulong
                                                          cc_default))
                                          ((Etempvar _str (tptr tschar)) ::
                                           nil))
                                        (Scall (Some _t'6)
                                          (Evar _KV_NewKey (Tfunction
                                                             (Tcons
                                                               (tptr tschar)
                                                               (Tcons tulong
                                                                 Tnil))
                                                             (tptr (Tstruct _KVKey noattr))
                                                             cc_default))
                                          ((Etempvar _str (tptr tschar)) ::
                                           (Etempvar _t'5 tulong) :: nil)))
                                      (Sset _key__1
                                        (Etempvar _t'6 (tptr (Tstruct _KVKey noattr)))))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'8
                                            (Efield
                                              (Evar _index (Tstruct _DBIndex noattr))
                                              _trie
                                              (tptr (Tstruct _KVStore noattr))))
                                          (Scall (Some _t'7)
                                            (Evar _KV_Put (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _KVStore noattr))
                                                              (Tcons
                                                                (tptr (Tstruct _KVKey noattr))
                                                                (Tcons
                                                                  (tptr tvoid)
                                                                  Tnil)))
                                                            tint cc_default))
                                            ((Etempvar _t'8 (tptr (Tstruct _KVStore noattr))) ::
                                             (Etempvar _key__1 (tptr (Tstruct _KVKey noattr))) ::
                                             (Etempvar _values__1 (tptr (Tunion _Element noattr))) ::
                                             nil)))
                                        (Sset _b (Etempvar _t'7 tint)))
                                      (Sifthenelse (Ebinop Oeq
                                                     (Etempvar _b tint)
                                                     (Econst_int (Int.repr 0) tint)
                                                     tint)
                                        (Scall None
                                          (Evar _exit (Tfunction
                                                        (Tcons tint Tnil)
                                                        tvoid cc_default))
                                          ((Econst_int (Int.repr 1) tint) ::
                                           nil))
                                        Sskip)))))))
                          (Sset _i__1
                            (Ecast
                              (Ebinop Oadd (Etempvar _i__1 tint)
                                (Etempvar _rowLen tulong) tulong) tint))))))))
              (Ssequence
                (Sassign
                  (Ederef (Etempvar __res (tptr (Tstruct _DBIndex noattr)))
                    (Tstruct _DBIndex noattr))
                  (Evar _index (Tstruct _DBIndex noattr)))
                (Sreturn None)))))))))
|}.

Definition composites : list composite_definition :=
(Composite _Node Struct
   ((_val, tulong) :: (_next, (tptr (Tstruct _Node noattr))) :: nil)
   noattr ::
 Composite _Column Struct
   ((_name, (tptr tschar)) :: (_val_type, tschar) ::
    (_next_col, (tptr (Tstruct _Column noattr))) :: nil)
   noattr ::
 Composite _Schema Struct
   ((_cols, (tptr (Tstruct _Column noattr))) ::
    (_pk_col_nums, (tptr (Tstruct _Node noattr))) :: nil)
   noattr ::
 Composite _DBIndex Struct
   ((_tree, (tptr (Tstruct _Relation noattr))) ::
    (_cursor, (tptr (Tstruct _Cursor noattr))) ::
    (_trie, (tptr (Tstruct _KVStore noattr))) :: (_keyType, tschar) :: nil)
   noattr ::
 Composite _Element Union
   ((_int_elt, tulong) :: (_str_elt, (tptr tschar)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap,
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
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_strlen,
   Gfun(External (EF_external "strlen"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tschar) Tnil) tulong
     cc_default)) ::
 (_KV_NewKey,
   Gfun(External (EF_external "KV_NewKey"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons (tptr tschar) (Tcons tulong Tnil)) (tptr (Tstruct _KVKey noattr))
     cc_default)) ::
 (_KV_NewKVStore,
   Gfun(External (EF_external "KV_NewKVStore"
                   (mksignature nil (Some AST.Tlong) cc_default)) Tnil
     (tptr (Tstruct _KVStore noattr)) cc_default)) ::
 (_KV_Put,
   Gfun(External (EF_external "KV_Put"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _KVStore noattr))
       (Tcons (tptr (Tstruct _KVKey noattr)) (Tcons (tptr tvoid) Tnil))) tint
     cc_default)) ::
 (_RL_NewCursor,
   Gfun(External (EF_external "RL_NewCursor"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default))
     (Tcons (tptr (Tstruct _Relation noattr)) Tnil)
     (tptr (Tstruct _Cursor noattr)) cc_default)) ::
 (_Iempty,
   Gfun(External (EF_external "Iempty"
                   (mksignature nil (Some AST.Tlong) cc_default)) Tnil
     (tptr tvoid) cc_default)) ::
 (_Iput,
   Gfun(External (EF_external "Iput"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     None cc_default))
     (Tcons tulong (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil))) tvoid
     cc_default)) :: (_sch_len, Gfun(Internal f_sch_len)) ::
 (_create, Gfun(Internal f_create)) :: nil).

Definition public_idents : list ident :=
(_create :: _sch_len :: _Iput :: _Iempty :: _RL_NewCursor :: _KV_Put ::
 _KV_NewKVStore :: _KV_NewKey :: _strlen :: _exit :: ___builtin_debug ::
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
 ___builtin_bswap :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


