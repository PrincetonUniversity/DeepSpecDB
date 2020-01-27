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
  Definition source_file := "stringlist.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := 17%positive.
Definition ___builtin_annot_intval : ident := 18%positive.
Definition ___builtin_bswap : ident := 11%positive.
Definition ___builtin_bswap16 : ident := 13%positive.
Definition ___builtin_bswap32 : ident := 12%positive.
Definition ___builtin_bswap64 : ident := 43%positive.
Definition ___builtin_clz : ident := 44%positive.
Definition ___builtin_clzl : ident := 45%positive.
Definition ___builtin_clzll : ident := 46%positive.
Definition ___builtin_ctz : ident := 47%positive.
Definition ___builtin_ctzl : ident := 48%positive.
Definition ___builtin_ctzll : ident := 49%positive.
Definition ___builtin_debug : ident := 61%positive.
Definition ___builtin_fabs : ident := 14%positive.
Definition ___builtin_fmadd : ident := 52%positive.
Definition ___builtin_fmax : ident := 50%positive.
Definition ___builtin_fmin : ident := 51%positive.
Definition ___builtin_fmsub : ident := 53%positive.
Definition ___builtin_fnmadd : ident := 54%positive.
Definition ___builtin_fnmsub : ident := 55%positive.
Definition ___builtin_fsqrt : ident := 15%positive.
Definition ___builtin_membar : ident := 19%positive.
Definition ___builtin_memcpy_aligned : ident := 16%positive.
Definition ___builtin_nop : ident := 60%positive.
Definition ___builtin_read16_reversed : ident := 56%positive.
Definition ___builtin_read32_reversed : ident := 57%positive.
Definition ___builtin_va_arg : ident := 21%positive.
Definition ___builtin_va_copy : ident := 22%positive.
Definition ___builtin_va_end : ident := 23%positive.
Definition ___builtin_va_start : ident := 20%positive.
Definition ___builtin_write16_reversed : ident := 58%positive.
Definition ___builtin_write32_reversed : ident := 59%positive.
Definition ___compcert_i64_dtos : ident := 28%positive.
Definition ___compcert_i64_dtou : ident := 29%positive.
Definition ___compcert_i64_sar : ident := 40%positive.
Definition ___compcert_i64_sdiv : ident := 34%positive.
Definition ___compcert_i64_shl : ident := 38%positive.
Definition ___compcert_i64_shr : ident := 39%positive.
Definition ___compcert_i64_smod : ident := 36%positive.
Definition ___compcert_i64_smulh : ident := 41%positive.
Definition ___compcert_i64_stod : ident := 30%positive.
Definition ___compcert_i64_stof : ident := 32%positive.
Definition ___compcert_i64_udiv : ident := 35%positive.
Definition ___compcert_i64_umod : ident := 37%positive.
Definition ___compcert_i64_umulh : ident := 42%positive.
Definition ___compcert_i64_utod : ident := 31%positive.
Definition ___compcert_i64_utof : ident := 33%positive.
Definition ___compcert_va_composite : ident := 27%positive.
Definition ___compcert_va_float64 : ident := 26%positive.
Definition ___compcert_va_int32 : ident := 24%positive.
Definition ___compcert_va_int64 : ident := 25%positive.
Definition _copy_string : ident := 71%positive.
Definition _cur : ident := 9%positive.
Definition _cursor : ident := 10%positive.
Definition _exit : ident := 63%positive.
Definition _key : ident := 1%positive.
Definition _kvpair : ident := 7%positive.
Definition _length : ident := 87%positive.
Definition _list : ident := 8%positive.
Definition _lst : ident := 86%positive.
Definition _main : ident := 90%positive.
Definition _malloc : ident := 62%positive.
Definition _mc : ident := 80%positive.
Definition _mcc : ident := 85%positive.
Definition _n : ident := 70%positive.
Definition _new_scell : ident := 72%positive.
Definition _next : ident := 4%positive.
Definition _old : ident := 75%positive.
Definition _p : ident := 67%positive.
Definition _pair : ident := 83%positive.
Definition _position : ident := 82%positive.
Definition _q : ident := 73%positive.
Definition _r : ident := 74%positive.
Definition _root : ident := 5%positive.
Definition _s : ident := 69%positive.
Definition _scell : ident := 3%positive.
Definition _size : ident := 78%positive.
Definition _strcmp : ident := 64%positive.
Definition _strcpy : ident := 65%positive.
Definition _stringlist : ident := 6%positive.
Definition _stringlist_cardinality : ident := 79%positive.
Definition _stringlist_get_cursor : ident := 81%positive.
Definition _stringlist_get_pair : ident := 84%positive.
Definition _stringlist_insert : ident := 76%positive.
Definition _stringlist_lookup : ident := 77%positive.
Definition _stringlist_move_to_first : ident := 89%positive.
Definition _stringlist_move_to_next : ident := 88%positive.
Definition _stringlist_new : ident := 68%positive.
Definition _strlen : ident := 66%positive.
Definition _value : ident := 2%positive.
Definition _t'1 : ident := 91%positive.
Definition _t'2 : ident := 92%positive.
Definition _t'3 : ident := 93%positive.

Definition f_stringlist_new := {|
  fn_return := (tptr (Tstruct _stringlist noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _stringlist noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _stringlist noattr) tulong) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _stringlist noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _p (tptr (Tstruct _stringlist noattr))) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _stringlist noattr)))
            (Tstruct _stringlist noattr)) _root
          (tptr (Tstruct _scell noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Sreturn (Some (Etempvar _p (tptr (Tstruct _stringlist noattr))))))))
|}.

Definition f_copy_string := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, tint) :: (_p, (tptr tschar)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tulong cc_default))
      ((Etempvar _s (tptr tschar)) :: nil))
    (Sset _n
      (Ecast
        (Ebinop Oadd (Etempvar _t'1 tulong) (Econst_int (Int.repr 1) tint)
          tulong) tint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
        ((Etempvar _n tint) :: nil))
      (Sset _p (Etempvar _t'2 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr tschar)) tint)
        (Scall None
          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
          ((Econst_int (Int.repr 1) tint) :: nil))
        Sskip)
      (Ssequence
        (Scall None
          (Evar _strcpy (Tfunction
                          (Tcons (tptr tschar) (Tcons (tptr tschar) Tnil))
                          (tptr tschar) cc_default))
          ((Etempvar _p (tptr tschar)) :: (Etempvar _s (tptr tschar)) :: nil))
        (Sreturn (Some (Etempvar _p (tptr tschar))))))))
|}.

Definition f_new_scell := {|
  fn_return := (tptr (Tstruct _scell noattr));
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tschar)) :: (_value, (tptr tvoid)) ::
                (_next, (tptr (Tstruct _scell noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _scell noattr))) ::
               (_t'2, (tptr tschar)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _scell noattr) tulong) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _scell noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr (Tstruct _scell noattr)))
                   tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _copy_string (Tfunction (Tcons (tptr tschar) Tnil)
                               (tptr tschar) cc_default))
          ((Etempvar _key (tptr tschar)) :: nil))
        (Sassign
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _scell noattr)))
              (Tstruct _scell noattr)) _key (tptr tschar))
          (Etempvar _t'2 (tptr tschar))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _scell noattr)))
              (Tstruct _scell noattr)) _value (tptr tvoid))
          (Etempvar _value (tptr tvoid)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _scell noattr)))
                (Tstruct _scell noattr)) _next
              (tptr (Tstruct _scell noattr)))
            (Etempvar _next (tptr (Tstruct _scell noattr))))
          (Sreturn (Some (Etempvar _p (tptr (Tstruct _scell noattr))))))))))
|}.

Definition f_stringlist_insert := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _stringlist noattr))) ::
                (_key, (tptr tschar)) :: (_value, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_q, (tptr (Tstruct _scell noattr))) ::
               (_r, (tptr (tptr (Tstruct _scell noattr)))) ::
               (_old, (tptr tvoid)) :: (_t'2, tint) ::
               (_t'1, (tptr (Tstruct _scell noattr))) ::
               (_t'3, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _r
    (Eaddrof
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _stringlist noattr)))
          (Tstruct _stringlist noattr)) _root (tptr (Tstruct _scell noattr)))
      (tptr (tptr (Tstruct _scell noattr)))))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sset _q
          (Ederef (Etempvar _r (tptr (tptr (Tstruct _scell noattr))))
            (tptr (Tstruct _scell noattr))))
        (Ssequence
          (Sifthenelse (Eunop Onotbool
                         (Etempvar _q (tptr (Tstruct _scell noattr))) tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar _new_scell (Tfunction
                                     (Tcons (tptr tschar)
                                       (Tcons (tptr tvoid)
                                         (Tcons
                                           (tptr (Tstruct _scell noattr))
                                           Tnil)))
                                     (tptr (Tstruct _scell noattr))
                                     cc_default))
                  ((Etempvar _key (tptr tschar)) ::
                   (Etempvar _value (tptr tvoid)) ::
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
                   nil))
                (Sassign
                  (Ederef (Etempvar _r (tptr (tptr (Tstruct _scell noattr))))
                    (tptr (Tstruct _scell noattr)))
                  (Etempvar _t'1 (tptr (Tstruct _scell noattr)))))
              (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)))))
            Sskip)
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
                    (Tstruct _scell noattr)) _key (tptr tschar)))
              (Scall (Some _t'2)
                (Evar _strcmp (Tfunction
                                (Tcons (tptr tschar)
                                  (Tcons (tptr tschar) Tnil)) tint
                                cc_default))
                ((Etempvar _t'3 (tptr tschar)) ::
                 (Etempvar _key (tptr tschar)) :: nil)))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Sset _old
                  (Efield
                    (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
                      (Tstruct _scell noattr)) _value (tptr tvoid)))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
                        (Tstruct _scell noattr)) _value (tptr tvoid))
                    (Etempvar _value (tptr tvoid)))
                  (Sreturn (Some (Etempvar _old (tptr tvoid))))))
              Sskip)))))
    (Sset _r
      (Eaddrof
        (Efield
          (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
            (Tstruct _scell noattr)) _next (tptr (Tstruct _scell noattr)))
        (tptr (tptr (Tstruct _scell noattr)))))))
|}.

Definition f_stringlist_lookup := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _stringlist noattr))) ::
                (_key, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_q, (tptr (Tstruct _scell noattr))) :: (_t'1, tint) ::
               (_t'3, (tptr tschar)) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _q
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _stringlist noattr)))
          (Tstruct _stringlist noattr)) _root (tptr (Tstruct _scell noattr))))
    (Sloop
      (Ssequence
        (Sifthenelse (Etempvar _q (tptr (Tstruct _scell noattr)))
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
                  (Tstruct _scell noattr)) _key (tptr tschar)))
            (Scall (Some _t'1)
              (Evar _strcmp (Tfunction
                              (Tcons (tptr tschar)
                                (Tcons (tptr tschar) Tnil)) tint cc_default))
              ((Etempvar _t'3 (tptr tschar)) ::
               (Etempvar _key (tptr tschar)) :: nil)))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
                    (Tstruct _scell noattr)) _value (tptr tvoid)))
              (Sreturn (Some (Etempvar _t'2 (tptr tvoid)))))
            Sskip)))
      (Sset _q
        (Efield
          (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
            (Tstruct _scell noattr)) _next (tptr (Tstruct _scell noattr))))))
  (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))
|}.

Definition f_stringlist_cardinality := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _stringlist noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_q, (tptr (Tstruct _scell noattr))) :: (_size, tulong) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _size (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Ssequence
      (Sset _q
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _stringlist noattr)))
            (Tstruct _stringlist noattr)) _root
          (tptr (Tstruct _scell noattr))))
      (Sloop
        (Ssequence
          (Sifthenelse (Etempvar _q (tptr (Tstruct _scell noattr)))
            Sskip
            Sbreak)
          (Sset _size
            (Ebinop Oadd (Etempvar _size tulong)
              (Econst_int (Int.repr 1) tint) tulong)))
        (Sset _q
          (Efield
            (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
              (Tstruct _scell noattr)) _next (tptr (Tstruct _scell noattr))))))
    (Sreturn (Some (Etempvar _size tulong)))))
|}.

Definition f_stringlist_get_cursor := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _stringlist noattr))) ::
                (_key, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_q, (tptr (Tstruct _scell noattr))) :: (_cur, tulong) ::
               (_mc, (tptr (Tstruct _cursor noattr))) :: (_t'2, tint) ::
               (_t'1, (tptr tvoid)) :: (_t'3, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _cur (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
        ((Esizeof (Tstruct _cursor noattr) tulong) :: nil))
      (Sset _mc
        (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _cursor noattr)))))
    (Ssequence
      (Sifthenelse (Eunop Onotbool
                     (Etempvar _mc (tptr (Tstruct _cursor noattr))) tint)
        (Scall None
          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
          ((Econst_int (Int.repr 1) tint) :: nil))
        Sskip)
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _mc (tptr (Tstruct _cursor noattr)))
              (Tstruct _cursor noattr)) _list
            (tptr (Tstruct _stringlist noattr)))
          (Etempvar _p (tptr (Tstruct _stringlist noattr))))
        (Ssequence
          (Ssequence
            (Sset _q
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _stringlist noattr)))
                  (Tstruct _stringlist noattr)) _root
                (tptr (Tstruct _scell noattr))))
            (Sloop
              (Ssequence
                (Sifthenelse (Etempvar _q (tptr (Tstruct _scell noattr)))
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'3
                        (Efield
                          (Ederef
                            (Etempvar _q (tptr (Tstruct _scell noattr)))
                            (Tstruct _scell noattr)) _key (tptr tschar)))
                      (Scall (Some _t'2)
                        (Evar _strcmp (Tfunction
                                        (Tcons (tptr tschar)
                                          (Tcons (tptr tschar) Tnil)) tint
                                        cc_default))
                        ((Etempvar _t'3 (tptr tschar)) ::
                         (Etempvar _key (tptr tschar)) :: nil)))
                    (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                                   (Econst_int (Int.repr 0) tint) tint)
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _mc (tptr (Tstruct _cursor noattr)))
                              (Tstruct _cursor noattr)) _cur tulong)
                          (Etempvar _cur tulong))
                        (Sreturn (Some (Etempvar _mc (tptr (Tstruct _cursor noattr))))))
                      Sskip))
                  (Sset _cur
                    (Ebinop Oadd (Etempvar _cur tulong)
                      (Econst_int (Int.repr 1) tint) tulong))))
              (Sset _q
                (Efield
                  (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
                    (Tstruct _scell noattr)) _next
                  (tptr (Tstruct _scell noattr))))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _mc (tptr (Tstruct _cursor noattr)))
                  (Tstruct _cursor noattr)) _cur tulong)
              (Econst_int (Int.repr 0) tint))
            (Sreturn (Some (Etempvar _mc (tptr (Tstruct _cursor noattr)))))))))))
|}.

Definition f_stringlist_get_pair := {|
  fn_return := (tptr (Tstruct _kvpair noattr));
  fn_callconv := cc_default;
  fn_params := ((_mc, (tptr (Tstruct _cursor noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _stringlist noattr))) :: (_cur, tulong) ::
               (_q, (tptr (Tstruct _scell noattr))) :: (_position, tulong) ::
               (_pair, (tptr (Tstruct _kvpair noattr))) ::
               (_t'1, (tptr tvoid)) :: (_t'3, (tptr tschar)) ::
               (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Efield
      (Ederef (Etempvar _mc (tptr (Tstruct _cursor noattr)))
        (Tstruct _cursor noattr)) _list (tptr (Tstruct _stringlist noattr))))
  (Ssequence
    (Sset _cur
      (Efield
        (Ederef (Etempvar _mc (tptr (Tstruct _cursor noattr)))
          (Tstruct _cursor noattr)) _cur tulong))
    (Ssequence
      (Sset _position (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Ssequence
        (Ssequence
          (Sset _q
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _stringlist noattr)))
                (Tstruct _stringlist noattr)) _root
              (tptr (Tstruct _scell noattr))))
          (Sloop
            (Ssequence
              (Sifthenelse (Etempvar _q (tptr (Tstruct _scell noattr)))
                Sskip
                Sbreak)
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Etempvar _cur tulong)
                               (Etempvar _position tulong) tint)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'1)
                        (Evar _malloc (Tfunction (Tcons tulong Tnil)
                                        (tptr tvoid) cc_default))
                        ((Esizeof (Tstruct _kvpair noattr) tulong) :: nil))
                      (Sset _pair
                        (Ecast (Etempvar _t'1 (tptr tvoid))
                          (tptr (Tstruct _kvpair noattr)))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'3
                          (Efield
                            (Ederef
                              (Etempvar _q (tptr (Tstruct _scell noattr)))
                              (Tstruct _scell noattr)) _key (tptr tschar)))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _pair (tptr (Tstruct _kvpair noattr)))
                              (Tstruct _kvpair noattr)) _key (tptr tschar))
                          (Etempvar _t'3 (tptr tschar))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'2
                            (Efield
                              (Ederef
                                (Etempvar _q (tptr (Tstruct _scell noattr)))
                                (Tstruct _scell noattr)) _value (tptr tvoid)))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _pair (tptr (Tstruct _kvpair noattr)))
                                (Tstruct _kvpair noattr)) _value
                              (tptr tvoid)) (Etempvar _t'2 (tptr tvoid))))
                        (Sreturn (Some (Etempvar _pair (tptr (Tstruct _kvpair noattr))))))))
                  Sskip)
                (Sset _position
                  (Ebinop Oadd (Etempvar _position tulong)
                    (Econst_int (Int.repr 1) tint) tulong))))
            (Sset _q
              (Efield
                (Ederef (Etempvar _q (tptr (Tstruct _scell noattr)))
                  (Tstruct _scell noattr)) _next
                (tptr (Tstruct _scell noattr))))))
        (Sreturn (Some (Etempvar _pair (tptr (Tstruct _kvpair noattr)))))))))
|}.

Definition f_stringlist_move_to_next := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_mcc, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_mc, (tptr (Tstruct _cursor noattr))) ::
               (_lst, (tptr (Tstruct _stringlist noattr))) ::
               (_cur, tulong) :: (_length, tulong) :: (_t'2, tint) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _mc
    (Ecast (Etempvar _mcc (tptr tvoid)) (tptr (Tstruct _cursor noattr))))
  (Ssequence
    (Sset _lst
      (Efield
        (Ederef (Etempvar _mc (tptr (Tstruct _cursor noattr)))
          (Tstruct _cursor noattr)) _list
        (tptr (Tstruct _stringlist noattr))))
    (Ssequence
      (Sset _cur
        (Efield
          (Ederef (Etempvar _mc (tptr (Tstruct _cursor noattr)))
            (Tstruct _cursor noattr)) _cur tulong))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _stringlist_cardinality (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _stringlist noattr))
                                              Tnil) tulong cc_default))
            ((Etempvar _lst (tptr (Tstruct _stringlist noattr))) :: nil))
          (Sset _length (Etempvar _t'1 tulong)))
        (Ssequence
          (Sset _cur
            (Ebinop Oadd (Etempvar _cur tulong)
              (Econst_int (Int.repr 1) tint) tulong))
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _cur tulong)
                             (Etempvar _length tulong) tint)
                (Sset _t'2
                  (Ecast
                    (Ebinop Ogt (Etempvar _cur tulong)
                      (Econst_int (Int.repr 0) tint) tint) tbool))
                (Sset _t'2 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'2 tint)
                (Sassign
                  (Efield
                    (Ederef (Etempvar _mc (tptr (Tstruct _cursor noattr)))
                      (Tstruct _cursor noattr)) _cur tulong)
                  (Etempvar _cur tulong))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _mc (tptr (Tstruct _cursor noattr)))
                      (Tstruct _cursor noattr)) _cur tulong)
                  (Econst_int (Int.repr 0) tint))))
            (Sreturn (Some (Etempvar _mc (tptr (Tstruct _cursor noattr)))))))))))
|}.

Definition f_stringlist_move_to_first := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_mc, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_mcc, (tptr (Tstruct _cursor noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _mcc
    (Ecast (Etempvar _mc (tptr tvoid)) (tptr (Tstruct _cursor noattr))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _mcc (tptr (Tstruct _cursor noattr)))
          (Tstruct _cursor noattr)) _cur tulong)
      (Econst_int (Int.repr 0) tint))
    (Sreturn (Some (Etempvar _mcc (tptr (Tstruct _cursor noattr)))))))
|}.

Definition composites : list composite_definition :=
(Composite _scell Struct
   ((_key, (tptr tschar)) :: (_value, (tptr tvoid)) ::
    (_next, (tptr (Tstruct _scell noattr))) :: nil)
   noattr ::
 Composite _stringlist Struct
   ((_root, (tptr (Tstruct _scell noattr))) :: nil)
   noattr ::
 Composite _kvpair Struct
   ((_key, (tptr tschar)) :: (_value, (tptr tvoid)) :: nil)
   noattr ::
 Composite _cursor Struct
   ((_list, (tptr (Tstruct _stringlist noattr))) :: (_cur, tulong) :: nil)
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
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_strcmp,
   Gfun(External (EF_external "strcmp"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tschar) (Tcons (tptr tschar) Tnil)) tint cc_default)) ::
 (_strcpy,
   Gfun(External (EF_external "strcpy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons (tptr tschar) (Tcons (tptr tschar) Tnil)) (tptr tschar)
     cc_default)) ::
 (_strlen,
   Gfun(External (EF_external "strlen"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tschar) Tnil) tulong
     cc_default)) :: (_stringlist_new, Gfun(Internal f_stringlist_new)) ::
 (_copy_string, Gfun(Internal f_copy_string)) ::
 (_new_scell, Gfun(Internal f_new_scell)) ::
 (_stringlist_insert, Gfun(Internal f_stringlist_insert)) ::
 (_stringlist_lookup, Gfun(Internal f_stringlist_lookup)) ::
 (_stringlist_cardinality, Gfun(Internal f_stringlist_cardinality)) ::
 (_stringlist_get_cursor, Gfun(Internal f_stringlist_get_cursor)) ::
 (_stringlist_get_pair, Gfun(Internal f_stringlist_get_pair)) ::
 (_stringlist_move_to_next, Gfun(Internal f_stringlist_move_to_next)) ::
 (_stringlist_move_to_first, Gfun(Internal f_stringlist_move_to_first)) ::
 nil).

Definition public_idents : list ident :=
(_stringlist_move_to_first :: _stringlist_move_to_next ::
 _stringlist_get_pair :: _stringlist_get_cursor :: _stringlist_cardinality ::
 _stringlist_lookup :: _stringlist_insert :: _new_scell :: _copy_string ::
 _stringlist_new :: _strlen :: _strcpy :: _strcmp :: _exit :: _malloc ::
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
 ___builtin_bswap :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


