From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.7"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "macosx"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "tests.c"%string.
  Definition normalized := true.
End Info.

Definition _AscendToParent : ident := 142%positive.
Definition _BtNode : ident := 26%positive.
Definition _Child_or_Record : ident := 33%positive.
Definition _Cursor : ident := 47%positive.
Definition _Entry : ident := 36%positive.
Definition _First : ident := 38%positive.
Definition _Last : ident := 39%positive.
Definition _RL_CursorIsValid : ident := 130%positive.
Definition _RL_DeleteRecord : ident := 150%positive.
Definition _RL_DeleteRelation : ident := 123%positive.
Definition _RL_FreeCursor : ident := 128%positive.
Definition _RL_GetKey : ident := 147%positive.
Definition _RL_GetRecord : ident := 145%positive.
Definition _RL_IsEmpty : ident := 160%positive.
Definition _RL_MoveToFirst : ident := 152%positive.
Definition _RL_MoveToKey : ident := 149%positive.
Definition _RL_MoveToNext : ident := 134%positive.
Definition _RL_MoveToNextValid : ident := 158%positive.
Definition _RL_MoveToPrevious : ident := 157%positive.
Definition _RL_MoveToPreviousNotFirst : ident := 159%positive.
Definition _RL_NewCursor : ident := 126%positive.
Definition _RL_NewRelation : ident := 117%positive.
Definition _RL_NumRecords : ident := 161%positive.
Definition _RL_PrintCursor : ident := 166%positive.
Definition _RL_PrintTree : ident := 164%positive.
Definition _RL_PutRecord : ident := 135%positive.
Definition _Relation : ident := 30%positive.
Definition ___builtin_annot : ident := 56%positive.
Definition ___builtin_annot_intval : ident := 57%positive.
Definition ___builtin_bswap : ident := 49%positive.
Definition ___builtin_bswap16 : ident := 51%positive.
Definition ___builtin_bswap32 : ident := 50%positive.
Definition ___builtin_bswap64 : ident := 48%positive.
Definition ___builtin_clz : ident := 82%positive.
Definition ___builtin_clzl : ident := 83%positive.
Definition ___builtin_clzll : ident := 84%positive.
Definition ___builtin_ctz : ident := 85%positive.
Definition ___builtin_ctzl : ident := 86%positive.
Definition ___builtin_ctzll : ident := 87%positive.
Definition ___builtin_debug : ident := 98%positive.
Definition ___builtin_fabs : ident := 52%positive.
Definition ___builtin_fmadd : ident := 90%positive.
Definition ___builtin_fmax : ident := 88%positive.
Definition ___builtin_fmin : ident := 89%positive.
Definition ___builtin_fmsub : ident := 91%positive.
Definition ___builtin_fnmadd : ident := 92%positive.
Definition ___builtin_fnmsub : ident := 93%positive.
Definition ___builtin_fsqrt : ident := 53%positive.
Definition ___builtin_membar : ident := 58%positive.
Definition ___builtin_memcpy_aligned : ident := 54%positive.
Definition ___builtin_read16_reversed : ident := 94%positive.
Definition ___builtin_read32_reversed : ident := 95%positive.
Definition ___builtin_sel : ident := 55%positive.
Definition ___builtin_va_arg : ident := 60%positive.
Definition ___builtin_va_copy : ident := 61%positive.
Definition ___builtin_va_end : ident := 62%positive.
Definition ___builtin_va_start : ident := 59%positive.
Definition ___builtin_write16_reversed : ident := 96%positive.
Definition ___builtin_write32_reversed : ident := 97%positive.
Definition ___compcert_i64_dtos : ident := 67%positive.
Definition ___compcert_i64_dtou : ident := 68%positive.
Definition ___compcert_i64_sar : ident := 79%positive.
Definition ___compcert_i64_sdiv : ident := 73%positive.
Definition ___compcert_i64_shl : ident := 77%positive.
Definition ___compcert_i64_shr : ident := 78%positive.
Definition ___compcert_i64_smod : ident := 75%positive.
Definition ___compcert_i64_smulh : ident := 80%positive.
Definition ___compcert_i64_stod : ident := 69%positive.
Definition ___compcert_i64_stof : ident := 71%positive.
Definition ___compcert_i64_udiv : ident := 74%positive.
Definition ___compcert_i64_umod : ident := 76%positive.
Definition ___compcert_i64_umulh : ident := 81%positive.
Definition ___compcert_i64_utod : ident := 70%positive.
Definition ___compcert_i64_utof : ident := 72%positive.
Definition ___compcert_va_composite : ident := 66%positive.
Definition ___compcert_va_float64 : ident := 65%positive.
Definition ___compcert_va_int32 : ident := 63%positive.
Definition ___compcert_va_int64 : ident := 64%positive.
Definition ___sFILE : ident := 25%positive.
Definition ___sFILEX : ident := 17%positive.
Definition ___sbuf : ident := 3%positive.
Definition ___stderrp : ident := 100%positive.
Definition ___stringlit_1 : ident := 119%positive.
Definition ___stringlit_10 : ident := 177%positive.
Definition ___stringlit_11 : ident := 178%positive.
Definition ___stringlit_12 : ident := 179%positive.
Definition ___stringlit_13 : ident := 181%positive.
Definition ___stringlit_14 : ident := 182%positive.
Definition ___stringlit_15 : ident := 183%positive.
Definition ___stringlit_16 : ident := 184%positive.
Definition ___stringlit_17 : ident := 185%positive.
Definition ___stringlit_18 : ident := 186%positive.
Definition ___stringlit_19 : ident := 187%positive.
Definition ___stringlit_2 : ident := 120%positive.
Definition ___stringlit_20 : ident := 188%positive.
Definition ___stringlit_21 : ident := 189%positive.
Definition ___stringlit_22 : ident := 190%positive.
Definition ___stringlit_3 : ident := 121%positive.
Definition ___stringlit_4 : ident := 129%positive.
Definition ___stringlit_5 : ident := 143%positive.
Definition ___stringlit_6 : ident := 146%positive.
Definition ___stringlit_7 : ident := 151%positive.
Definition ___stringlit_8 : ident := 162%positive.
Definition ___stringlit_9 : ident := 172%positive.
Definition __base : ident := 1%positive.
Definition __bf : ident := 9%positive.
Definition __blksize : ident := 23%positive.
Definition __close : ident := 12%positive.
Definition __cookie : ident := 11%positive.
Definition __extra : ident := 18%positive.
Definition __file : ident := 8%positive.
Definition __flags : ident := 7%positive.
Definition __lb : ident := 22%positive.
Definition __lbfsize : ident := 10%positive.
Definition __nbuf : ident := 21%positive.
Definition __offset : ident := 24%positive.
Definition __p : ident := 4%positive.
Definition __r : ident := 5%positive.
Definition __read : ident := 13%positive.
Definition __seek : ident := 14%positive.
Definition __size : ident := 2%positive.
Definition __ub : ident := 16%positive.
Definition __ubuf : ident := 20%positive.
Definition __ur : ident := 19%positive.
Definition __w : ident := 6%positive.
Definition __write : ident := 15%positive.
Definition _abort : ident := 99%positive.
Definition _allEntries : ident := 169%positive.
Definition _ancestors : ident := 46%positive.
Definition _ancestorsIdx : ident := 45%positive.
Definition _btCursor : ident := 127%positive.
Definition _child : ident := 31%positive.
Definition _createNewNode : ident := 116%positive.
Definition _currNode : ident := 111%positive.
Definition _currNode__1 : ident := 174%positive.
Definition _cursor : ident := 109%positive.
Definition _depth : ident := 29%positive.
Definition _e : ident := 180%positive.
Definition _entries : ident := 42%positive.
Definition _entry : ident := 168%positive.
Definition _entryIndex : ident := 110%positive.
Definition _exit : ident := 105%positive.
Definition _findChildIndex : ident := 140%positive.
Definition _findRecordIndex : ident := 171%positive.
Definition _firstpointer : ident := 154%positive.
Definition _fprintf : ident := 101%positive.
Definition _free : ident := 103%positive.
Definition _freeRecord : ident := 118%positive.
Definition _goToKey : ident := 132%positive.
Definition _handleDeleteBtree : ident := 122%positive.
Definition _highest : ident := 139%positive.
Definition _i : ident := 124%positive.
Definition _i__1 : ident := 176%positive.
Definition _idx : ident := 137%positive.
Definition _isFirst : ident := 113%positive.
Definition _isLeaf : ident := 37%positive.
Definition _isNodeParent : ident := 141%positive.
Definition _isValid : ident := 112%positive.
Definition _key : ident := 34%positive.
Definition _lastpointer : ident := 153%positive.
Definition _level : ident := 44%positive.
Definition _lowest : ident := 138%positive.
Definition _main : ident := 191%positive.
Definition _malloc : ident := 104%positive.
Definition _moveToFirst : ident := 125%positive.
Definition _moveToKey : ident := 148%positive.
Definition _moveToLast : ident := 155%positive.
Definition _moveToNext : ident := 144%positive.
Definition _moveToPrev : ident := 156%positive.
Definition _n : ident := 106%positive.
Definition _newEntry : ident := 131%positive.
Definition _newNode : ident := 167%positive.
Definition _node : ident := 136%positive.
Definition _numKeys : ident := 40%positive.
Definition _numRecords : ident := 28%positive.
Definition _p : ident := 107%positive.
Definition _pNewRelation : ident := 115%positive.
Definition _pRootNode : ident := 114%positive.
Definition _printCursor : ident := 165%positive.
Definition _printTree : ident := 163%positive.
Definition _printf : ident := 102%positive.
Definition _ptr : ident := 35%positive.
Definition _ptr0 : ident := 41%positive.
Definition _putEntry : ident := 133%positive.
Definition _rand : ident := 192%positive.
Definition _record : ident := 32%positive.
Definition _relation : ident := 43%positive.
Definition _root : ident := 27%positive.
Definition _splitnode : ident := 173%positive.
Definition _surely_malloc : ident := 108%positive.
Definition _test_insert : ident := 193%positive.
Definition _tgtIdx : ident := 170%positive.
Definition _tgtIdx__1 : ident := 175%positive.
Definition _t'1 : ident := 194%positive.
Definition _t'2 : ident := 195%positive.
Definition _t'3 : ident := 196%positive.
Definition _t'4 : ident := 197%positive.
Definition _t'5 : ident := 198%positive.

Definition f_test_insert := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_key, tuint) :: (_record, tuint) ::
               (_relation, (tptr (Tstruct _Relation noattr))) ::
               (_cursor, (tptr (Tstruct _Cursor noattr))) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, (tptr (Tstruct _Cursor noattr))) ::
               (_t'1, (tptr (Tstruct _Relation noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _RL_NewRelation (Tfunction Tnil (tptr (Tstruct _Relation noattr))
                              cc_default)) nil)
    (Sset _relation (Etempvar _t'1 (tptr (Tstruct _Relation noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _RL_NewCursor (Tfunction
                              (Tcons (tptr (Tstruct _Relation noattr)) Tnil)
                              (tptr (Tstruct _Cursor noattr)) cc_default))
        ((Etempvar _relation (tptr (Tstruct _Relation noattr))) :: nil))
      (Sset _cursor (Etempvar _t'2 (tptr (Tstruct _Cursor noattr)))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 10000) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _rand (Tfunction Tnil tint cc_default)) nil)
                (Sset _key
                  (Ebinop Omod (Etempvar _t'3 tint)
                    (Econst_int (Int.repr 3000) tint) tint)))
              (Ssequence
                (Sset _record (Etempvar _key tuint))
                (Ssequence
                  (Scall None
                    (Evar _RL_PutRecord (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _Cursor noattr))
                                            (Tcons tuint
                                              (Tcons (tptr tvoid) Tnil)))
                                          tvoid cc_default))
                    ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                     (Etempvar _key tuint) :: (Etempvar _record tuint) ::
                     nil))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _rand (Tfunction Tnil tint cc_default)) nil)
                      (Sset _key
                        (Ebinop Omod (Etempvar _t'4 tint)
                          (Econst_int (Int.repr 3000) tint) tint)))
                    (Ssequence
                      (Scall None
                        (Evar _RL_MoveToKey (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _Cursor noattr))
                                                (Tcons tuint Tnil)) tint
                                              cc_default))
                        ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                         (Etempvar _key tuint) :: nil))
                      (Ssequence
                        (Scall (Some _t'5)
                          (Evar _RL_CursorIsValid (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _Cursor noattr))
                                                      Tnil) tint cc_default))
                          ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                           nil))
                        (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tint)
                                       (Econst_int (Int.repr 1) tint) tint)
                          (Scall None
                            (Evar _RL_GetRecord (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _Cursor noattr))
                                                    Tnil) (tptr tvoid)
                                                  cc_default))
                            ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) ::
                             nil))
                          Sskip))))))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Scall None
          (Evar _RL_PrintTree (Tfunction
                                (Tcons (tptr (Tstruct _Relation noattr))
                                  Tnil) tvoid cc_default))
          ((Etempvar _relation (tptr (Tstruct _Relation noattr))) :: nil))
        (Ssequence
          (Scall None
            (Evar _RL_PrintCursor (Tfunction
                                    (Tcons (tptr (Tstruct _Cursor noattr))
                                      Tnil) tvoid cc_default))
            ((Etempvar _cursor (tptr (Tstruct _Cursor noattr))) :: nil))
          (Sreturn None))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Ssequence
    (Scall None (Evar _test_insert (Tfunction Tnil tvoid cc_default)) nil)
    (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_rand,
   Gfun(External (EF_external "rand" (mksignature nil AST.Tint cc_default))
     Tnil tint cc_default)) ::
 (_RL_NewRelation,
   Gfun(External (EF_external "RL_NewRelation"
                   (mksignature nil AST.Tint cc_default)) Tnil
     (tptr (Tstruct _Relation noattr)) cc_default)) ::
 (_RL_NewCursor,
   Gfun(External (EF_external "RL_NewCursor"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr (Tstruct _Relation noattr)) Tnil)
     (tptr (Tstruct _Cursor noattr)) cc_default)) ::
 (_RL_CursorIsValid,
   Gfun(External (EF_external "RL_CursorIsValid"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tint cc_default)) ::
 (_RL_PutRecord,
   Gfun(External (EF_external "RL_PutRecord"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _Cursor noattr))
       (Tcons tuint (Tcons (tptr tvoid) Tnil))) tvoid cc_default)) ::
 (_RL_MoveToKey,
   Gfun(External (EF_external "RL_MoveToKey"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr (Tstruct _Cursor noattr)) (Tcons tuint Tnil)) tint
     cc_default)) ::
 (_RL_GetRecord,
   Gfun(External (EF_external "RL_GetRecord"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) (tptr tvoid) cc_default)) ::
 (_RL_PrintTree,
   Gfun(External (EF_external "RL_PrintTree"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _Relation noattr)) Tnil) tvoid cc_default)) ::
 (_RL_PrintCursor,
   Gfun(External (EF_external "RL_PrintCursor"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _Cursor noattr)) Tnil) tvoid cc_default)) ::
 (_test_insert, Gfun(Internal f_test_insert)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _RL_PrintCursor :: _RL_PrintTree :: _RL_GetRecord ::
 _RL_MoveToKey :: _RL_PutRecord :: _RL_CursorIsValid :: _RL_NewCursor ::
 _RL_NewRelation :: _rand :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_fsqrt :: ___builtin_fabs :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


