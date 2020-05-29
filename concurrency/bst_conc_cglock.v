From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.5"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "macosx"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "bst_conc_cglock.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := 15%positive.
Definition ___builtin_annot_intval : ident := 16%positive.
Definition ___builtin_bswap : ident := 9%positive.
Definition ___builtin_bswap16 : ident := 11%positive.
Definition ___builtin_bswap32 : ident := 10%positive.
Definition ___builtin_bswap64 : ident := 41%positive.
Definition ___builtin_clz : ident := 42%positive.
Definition ___builtin_clzl : ident := 43%positive.
Definition ___builtin_clzll : ident := 44%positive.
Definition ___builtin_ctz : ident := 45%positive.
Definition ___builtin_ctzl : ident := 46%positive.
Definition ___builtin_ctzll : ident := 47%positive.
Definition ___builtin_debug : ident := 59%positive.
Definition ___builtin_fabs : ident := 12%positive.
Definition ___builtin_fmadd : ident := 50%positive.
Definition ___builtin_fmax : ident := 48%positive.
Definition ___builtin_fmin : ident := 49%positive.
Definition ___builtin_fmsub : ident := 51%positive.
Definition ___builtin_fnmadd : ident := 52%positive.
Definition ___builtin_fnmsub : ident := 53%positive.
Definition ___builtin_fsqrt : ident := 13%positive.
Definition ___builtin_membar : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 14%positive.
Definition ___builtin_nop : ident := 58%positive.
Definition ___builtin_read16_reversed : ident := 54%positive.
Definition ___builtin_read32_reversed : ident := 55%positive.
Definition ___builtin_va_arg : ident := 19%positive.
Definition ___builtin_va_copy : ident := 20%positive.
Definition ___builtin_va_end : ident := 21%positive.
Definition ___builtin_va_start : ident := 18%positive.
Definition ___builtin_write16_reversed : ident := 56%positive.
Definition ___builtin_write32_reversed : ident := 57%positive.
Definition ___compcert_i64_dtos : ident := 26%positive.
Definition ___compcert_i64_dtou : ident := 27%positive.
Definition ___compcert_i64_sar : ident := 38%positive.
Definition ___compcert_i64_sdiv : ident := 32%positive.
Definition ___compcert_i64_shl : ident := 36%positive.
Definition ___compcert_i64_shr : ident := 37%positive.
Definition ___compcert_i64_smod : ident := 34%positive.
Definition ___compcert_i64_smulh : ident := 39%positive.
Definition ___compcert_i64_stod : ident := 28%positive.
Definition ___compcert_i64_stof : ident := 30%positive.
Definition ___compcert_i64_udiv : ident := 33%positive.
Definition ___compcert_i64_umod : ident := 35%positive.
Definition ___compcert_i64_umulh : ident := 40%positive.
Definition ___compcert_i64_utod : ident := 29%positive.
Definition ___compcert_i64_utof : ident := 31%positive.
Definition ___compcert_va_composite : ident := 25%positive.
Definition ___compcert_va_float64 : ident := 24%positive.
Definition ___compcert_va_int32 : ident := 22%positive.
Definition ___compcert_va_int64 : ident := 23%positive.
Definition ___stringlit_1 : ident := 97%positive.
Definition ___stringlit_2 : ident := 100%positive.
Definition ___stringlit_3 : ident := 101%positive.
Definition ___stringlit_4 : ident := 102%positive.
Definition ___stringlit_5 : ident := 103%positive.
Definition __l : ident := 89%positive.
Definition _acquire : ident := 64%positive.
Definition _args : ident := 96%positive.
Definition _b : ident := 79%positive.
Definition _delete : ident := 95%positive.
Definition _exit : ident := 62%positive.
Definition _free : ident := 61%positive.
Definition _freelock2 : ident := 65%positive.
Definition _insert : ident := 86%positive.
Definition _key : ident := 1%positive.
Definition _l : ident := 74%positive.
Definition _left : ident := 4%positive.
Definition _lock : ident := 7%positive.
Definition _lookup : ident := 88%positive.
Definition _main : ident := 104%positive.
Definition _makelock : ident := 63%positive.
Definition _malloc : ident := 60%positive.
Definition _mid : ident := 91%positive.
Definition _n : ident := 70%positive.
Definition _newt : ident := 73%positive.
Definition _p : ident := 71%positive.
Definition _pa : ident := 76%positive.
Definition _pb : ident := 77%positive.
Definition _pushdown_left : ident := 94%positive.
Definition _q : ident := 93%positive.
Definition _r : ident := 90%positive.
Definition _release2 : ident := 66%positive.
Definition _right : ident := 5%positive.
Definition _spawn : ident := 67%positive.
Definition _surely_malloc : ident := 72%positive.
Definition _t : ident := 6%positive.
Definition _t_lock : ident := 99%positive.
Definition _tb : ident := 69%positive.
Definition _tgp : ident := 80%positive.
Definition _tgt : ident := 83%positive.
Definition _thread_func : ident := 98%positive.
Definition _thread_lock : ident := 68%positive.
Definition _tr : ident := 84%positive.
Definition _tree : ident := 3%positive.
Definition _tree_free : ident := 78%positive.
Definition _tree_t : ident := 8%positive.
Definition _treebox_free : ident := 81%positive.
Definition _treebox_new : ident := 75%positive.
Definition _turn_left : ident := 92%positive.
Definition _v : ident := 87%positive.
Definition _value : ident := 2%positive.
Definition _x : ident := 82%positive.
Definition _y : ident := 85%positive.
Definition _t'1 : ident := 105%positive.
Definition _t'2 : ident := 106%positive.
Definition _t'3 : ident := 107%positive.
Definition _t'4 : ident := 108%positive.
Definition _t'5 : ident := 109%positive.
Definition _t'6 : ident := 110%positive.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 5);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 4);
  gvar_init := (Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 4);
  gvar_init := (Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 16);
  gvar_init := (Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 72) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_thread_lock := {|
  gvar_info := (tarray (tptr tvoid) 2);
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_tb := {|
  gvar_info := (tptr (tptr (Tstruct _tree_t noattr)));
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
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

Definition f_treebox_new := {|
  fn_return := (tptr (tptr (Tstruct _tree_t noattr)));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (_newt, (tptr (Tstruct _tree_t noattr))) ::
               (_l, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (tptr (Tstruct _tree_t noattr)) tuint) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (tptr (Tstruct _tree_t noattr))))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                               cc_default))
        ((Esizeof (Tstruct _tree_t noattr) tuint) :: nil))
      (Sset _newt
        (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr (Tstruct _tree_t noattr)))))
    (Ssequence
      (Sassign
        (Ederef (Etempvar _p (tptr (tptr (Tstruct _tree_t noattr))))
          (tptr (Tstruct _tree_t noattr)))
        (Etempvar _newt (tptr (Tstruct _tree_t noattr))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                   cc_default))
            ((Esizeof (tarray (tptr tvoid) 2) tuint) :: nil))
          (Sset _l
            (Ecast (Etempvar _t'3 (tptr tvoid))
              (tptr (tarray (tptr tvoid) 2)))))
        (Ssequence
          (Scall None
            (Evar _makelock (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
            ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _newt (tptr (Tstruct _tree_t noattr)))
                  (Tstruct _tree_t noattr)) _lock
                (tptr (tarray (tptr tvoid) 2)))
              (Etempvar _l (tptr (tarray (tptr tvoid) 2))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _newt (tptr (Tstruct _tree_t noattr)))
                    (Tstruct _tree_t noattr)) _t
                  (tptr (Tstruct _tree noattr)))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
              (Ssequence
                (Scall None
                  (Evar _release2 (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                    cc_default))
                  ((Etempvar _l (tptr (tarray (tptr tvoid) 2))) :: nil))
                (Sreturn (Some (Etempvar _p (tptr (tptr (Tstruct _tree_t noattr))))))))))))))
|}.

Definition f_tree_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _tree noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_pa, (tptr (Tstruct _tree noattr))) ::
               (_pb, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Sifthenelse (Ebinop One (Etempvar _p (tptr (Tstruct _tree noattr)))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Ssequence
    (Sset _pa
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
          (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
    (Ssequence
      (Sset _pb
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _right (tptr (Tstruct _tree noattr))))
      (Ssequence
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Etempvar _p (tptr (Tstruct _tree noattr))) :: nil))
        (Ssequence
          (Scall None
            (Evar _tree_free (Tfunction
                               (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                               tvoid cc_default))
            ((Etempvar _pa (tptr (Tstruct _tree noattr))) :: nil))
          (Scall None
            (Evar _tree_free (Tfunction
                               (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                               tvoid cc_default))
            ((Etempvar _pb (tptr (Tstruct _tree noattr))) :: nil))))))
  Sskip)
|}.

Definition f_treebox_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_b, (tptr (tptr (Tstruct _tree_t noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tgp, (tptr (Tstruct _tree_t noattr))) ::
               (_p, (tptr (Tstruct _tree noattr))) :: (_l, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _tgp
    (Ederef (Etempvar _b (tptr (tptr (Tstruct _tree_t noattr))))
      (tptr (Tstruct _tree_t noattr))))
  (Ssequence
    (Sset _l
      (Efield
        (Ederef (Etempvar _tgp (tptr (Tstruct _tree_t noattr)))
          (Tstruct _tree_t noattr)) _lock (tptr (tarray (tptr tvoid) 2))))
    (Ssequence
      (Scall None
        (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Etempvar _l (tptr tvoid)) :: nil))
      (Ssequence
        (Sset _p
          (Efield
            (Ederef (Etempvar _tgp (tptr (Tstruct _tree_t noattr)))
              (Tstruct _tree_t noattr)) _t (tptr (Tstruct _tree noattr))))
        (Ssequence
          (Scall None
            (Evar _tree_free (Tfunction
                               (Tcons (tptr (Tstruct _tree noattr)) Tnil)
                               tvoid cc_default))
            ((Etempvar _p (tptr (Tstruct _tree noattr))) :: nil))
          (Ssequence
            (Scall None
              (Evar _freelock2 (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                 cc_default))
              ((Etempvar _l (tptr tvoid)) :: nil))
            (Ssequence
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Etempvar _l (tptr tvoid)) :: nil))
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Etempvar _b (tptr (tptr (Tstruct _tree_t noattr)))) :: nil)))))))))
|}.

Definition f_insert := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree_t noattr)))) :: (_x, tint) ::
                (_value, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_tgt, (tptr (Tstruct _tree_t noattr))) ::
               (_p, (tptr (Tstruct _tree noattr))) ::
               (_tr, (tptr (tptr (Tstruct _tree noattr)))) ::
               (_l, (tptr tvoid)) :: (_y, tint) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _tgt
    (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree_t noattr))))
      (tptr (Tstruct _tree_t noattr))))
  (Ssequence
    (Sset _tr
      (Eaddrof
        (Efield
          (Ederef (Etempvar _tgt (tptr (Tstruct _tree_t noattr)))
            (Tstruct _tree_t noattr)) _t (tptr (Tstruct _tree noattr)))
        (tptr (tptr (Tstruct _tree noattr)))))
    (Ssequence
      (Sset _l
        (Efield
          (Ederef (Etempvar _tgt (tptr (Tstruct _tree_t noattr)))
            (Tstruct _tree_t noattr)) _lock (tptr (tarray (tptr tvoid) 2))))
      (Ssequence
        (Scall None
          (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                           cc_default)) ((Etempvar _l (tptr tvoid)) :: nil))
        (Sloop
          (Ssequence
            Sskip
            (Ssequence
              (Sset _p
                (Ederef (Etempvar _tr (tptr (tptr (Tstruct _tree noattr))))
                  (tptr (Tstruct _tree noattr))))
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _p (tptr (Tstruct _tree noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'1)
                      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil)
                                             (tptr tvoid) cc_default))
                      ((Esizeof (Tstruct _tree noattr) tuint) :: nil))
                    (Sset _p
                      (Ecast (Etempvar _t'1 (tptr tvoid))
                        (tptr (Tstruct _tree noattr)))))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Etempvar _tr (tptr (tptr (Tstruct _tree noattr))))
                        (tptr (Tstruct _tree noattr)))
                      (Etempvar _p (tptr (Tstruct _tree noattr))))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _key tint)
                        (Etempvar _x tint))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _value (tptr tvoid))
                          (Etempvar _value (tptr tvoid)))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _p (tptr (Tstruct _tree noattr)))
                                (Tstruct _tree noattr)) _left
                              (tptr (Tstruct _tree noattr)))
                            (Ecast (Econst_int (Int.repr 0) tint)
                              (tptr tvoid)))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _p (tptr (Tstruct _tree noattr)))
                                  (Tstruct _tree noattr)) _right
                                (tptr (Tstruct _tree noattr)))
                              (Ecast (Econst_int (Int.repr 0) tint)
                                (tptr tvoid)))
                            (Ssequence
                              (Scall None
                                (Evar _release2 (Tfunction
                                                  (Tcons (tptr tvoid) Tnil)
                                                  tvoid cc_default))
                                ((Etempvar _l (tptr tvoid)) :: nil))
                              (Sreturn None))))))))
                (Ssequence
                  (Sset _y
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _key tint))
                  (Sifthenelse (Ebinop Olt (Etempvar _x tint)
                                 (Etempvar _y tint) tint)
                    (Sset _tr
                      (Eaddrof
                        (Efield
                          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _left
                          (tptr (Tstruct _tree noattr)))
                        (tptr (tptr (Tstruct _tree noattr)))))
                    (Sifthenelse (Ebinop Olt (Etempvar _y tint)
                                   (Etempvar _x tint) tint)
                      (Sset _tr
                        (Eaddrof
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _right
                            (tptr (Tstruct _tree noattr)))
                          (tptr (tptr (Tstruct _tree noattr)))))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _value (tptr tvoid))
                          (Etempvar _value (tptr tvoid)))
                        (Ssequence
                          (Scall None
                            (Evar _release2 (Tfunction
                                              (Tcons (tptr tvoid) Tnil) tvoid
                                              cc_default))
                            ((Etempvar _l (tptr tvoid)) :: nil))
                          (Sreturn None)))))))))
          Sskip)))))
|}.

Definition f_lookup := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree_t noattr)))) :: (_x, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree noattr))) :: (_v, (tptr tvoid)) ::
               (_tgt, (tptr (Tstruct _tree_t noattr))) ::
               (_l, (tptr tvoid)) :: (_y, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _tgt
    (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree_t noattr))))
      (tptr (Tstruct _tree_t noattr))))
  (Ssequence
    (Sset _l
      (Efield
        (Ederef (Etempvar _tgt (tptr (Tstruct _tree_t noattr)))
          (Tstruct _tree_t noattr)) _lock (tptr (tarray (tptr tvoid) 2))))
    (Ssequence
      (Scall None
        (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Etempvar _l (tptr tvoid)) :: nil))
      (Ssequence
        (Sset _p
          (Efield
            (Ederef (Etempvar _tgt (tptr (Tstruct _tree_t noattr)))
              (Tstruct _tree_t noattr)) _t (tptr (Tstruct _tree noattr))))
        (Ssequence
          (Swhile
            (Ebinop One (Etempvar _p (tptr (Tstruct _tree noattr)))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
            (Ssequence
              (Sset _y
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _key tint))
              (Sifthenelse (Ebinop Olt (Etempvar _x tint) (Etempvar _y tint)
                             tint)
                (Sset _p
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _left
                    (tptr (Tstruct _tree noattr))))
                (Sifthenelse (Ebinop Olt (Etempvar _y tint)
                               (Etempvar _x tint) tint)
                  (Sset _p
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _right
                      (tptr (Tstruct _tree noattr))))
                  (Ssequence
                    (Sset _v
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                          (Tstruct _tree noattr)) _value (tptr tvoid)))
                    (Ssequence
                      (Scall None
                        (Evar _release2 (Tfunction (Tcons (tptr tvoid) Tnil)
                                          tvoid cc_default))
                        ((Etempvar _l (tptr tvoid)) :: nil))
                      (Sreturn (Some (Etempvar _v (tptr tvoid))))))))))
          (Ssequence
            (Scall None
              (Evar _release2 (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                cc_default))
              ((Etempvar _l (tptr tvoid)) :: nil))
            (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid))))))))))
|}.

Definition f_turn_left := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((__l, (tptr (tptr (Tstruct _tree noattr)))) ::
                (_l, (tptr (Tstruct _tree noattr))) ::
                (_r, (tptr (Tstruct _tree noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_mid, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _mid
    (Efield
      (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
        (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
          (Tstruct _tree noattr)) _right (tptr (Tstruct _tree noattr)))
      (Etempvar _mid (tptr (Tstruct _tree noattr))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr)))
        (Etempvar _l (tptr (Tstruct _tree noattr))))
      (Sassign
        (Ederef (Etempvar __l (tptr (tptr (Tstruct _tree noattr))))
          (tptr (Tstruct _tree noattr)))
        (Etempvar _r (tptr (Tstruct _tree noattr)))))))
|}.

Definition f_pushdown_left := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree noattr))) ::
               (_q, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Ssequence
      (Sset _p
        (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
          (tptr (Tstruct _tree noattr))))
      (Ssequence
        (Sset _q
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _right (tptr (Tstruct _tree noattr))))
        (Sifthenelse (Ebinop Oeq (Etempvar _q (tptr (Tstruct _tree noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Ssequence
            (Sset _q
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _left
                (tptr (Tstruct _tree noattr))))
            (Ssequence
              (Sassign
                (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
                  (tptr (Tstruct _tree noattr)))
                (Etempvar _q (tptr (Tstruct _tree noattr))))
              (Ssequence
                (Scall None
                  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                cc_default))
                  ((Etempvar _p (tptr (Tstruct _tree noattr))) :: nil))
                (Sreturn None))))
          (Ssequence
            (Scall None
              (Evar _turn_left (Tfunction
                                 (Tcons (tptr (tptr (Tstruct _tree noattr)))
                                   (Tcons (tptr (Tstruct _tree noattr))
                                     (Tcons (tptr (Tstruct _tree noattr))
                                       Tnil))) tvoid cc_default))
              ((Etempvar _t (tptr (tptr (Tstruct _tree noattr)))) ::
               (Etempvar _p (tptr (Tstruct _tree noattr))) ::
               (Etempvar _q (tptr (Tstruct _tree noattr))) :: nil))
            (Sset _t
              (Eaddrof
                (Efield
                  (Ederef (Etempvar _q (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _left
                  (tptr (Tstruct _tree noattr)))
                (tptr (tptr (Tstruct _tree noattr))))))))))
  Sskip)
|}.

Definition f_delete := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree_t noattr)))) :: (_x, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree noattr))) ::
               (_tgt, (tptr (Tstruct _tree_t noattr))) ::
               (_l, (tptr tvoid)) ::
               (_tr, (tptr (tptr (Tstruct _tree noattr)))) :: (_y, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _tgt
    (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree_t noattr))))
      (tptr (Tstruct _tree_t noattr))))
  (Ssequence
    (Sset _l
      (Efield
        (Ederef (Etempvar _tgt (tptr (Tstruct _tree_t noattr)))
          (Tstruct _tree_t noattr)) _lock (tptr (tarray (tptr tvoid) 2))))
    (Ssequence
      (Sset _tr
        (Eaddrof
          (Efield
            (Ederef (Etempvar _tgt (tptr (Tstruct _tree_t noattr)))
              (Tstruct _tree_t noattr)) _t (tptr (Tstruct _tree noattr)))
          (tptr (tptr (Tstruct _tree noattr)))))
      (Ssequence
        (Scall None
          (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                           cc_default)) ((Etempvar _l (tptr tvoid)) :: nil))
        (Sloop
          (Ssequence
            Sskip
            (Ssequence
              (Sset _p
                (Ederef (Etempvar _tr (tptr (tptr (Tstruct _tree noattr))))
                  (tptr (Tstruct _tree noattr))))
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _p (tptr (Tstruct _tree noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Ssequence
                  (Scall None
                    (Evar _release2 (Tfunction (Tcons (tptr tvoid) Tnil)
                                      tvoid cc_default))
                    ((Etempvar _l (tptr tvoid)) :: nil))
                  (Sreturn None))
                (Ssequence
                  (Sset _y
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _key tint))
                  (Sifthenelse (Ebinop Olt (Etempvar _x tint)
                                 (Etempvar _y tint) tint)
                    (Sset _tr
                      (Eaddrof
                        (Efield
                          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                            (Tstruct _tree noattr)) _left
                          (tptr (Tstruct _tree noattr)))
                        (tptr (tptr (Tstruct _tree noattr)))))
                    (Sifthenelse (Ebinop Olt (Etempvar _y tint)
                                   (Etempvar _x tint) tint)
                      (Sset _tr
                        (Eaddrof
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tstruct _tree noattr)))
                              (Tstruct _tree noattr)) _right
                            (tptr (Tstruct _tree noattr)))
                          (tptr (tptr (Tstruct _tree noattr)))))
                      (Ssequence
                        (Scall None
                          (Evar _pushdown_left (Tfunction
                                                 (Tcons
                                                   (tptr (tptr (Tstruct _tree noattr)))
                                                   Tnil) tvoid cc_default))
                          ((Etempvar _tr (tptr (tptr (Tstruct _tree noattr)))) ::
                           nil))
                        (Sreturn None))))))))
          Sskip)))))
|}.

Definition f_thread_func := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_args, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'1, (tptr (tptr (Tstruct _tree_t noattr)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Eaddrof (Evar _thread_lock (tarray (tptr tvoid) 2))
      (tptr (tarray (tptr tvoid) 2))))
  (Ssequence
    (Ssequence
      (Sset _t'1 (Evar _tb (tptr (tptr (Tstruct _tree_t noattr)))))
      (Scall None
        (Evar _insert (Tfunction
                        (Tcons (tptr (tptr (Tstruct _tree_t noattr)))
                          (Tcons tint (Tcons (tptr tvoid) Tnil))) tvoid
                        cc_default))
        ((Etempvar _t'1 (tptr (tptr (Tstruct _tree_t noattr)))) ::
         (Econst_int (Int.repr 1) tint) ::
         (Evar ___stringlit_1 (tarray tschar 16)) :: nil)))
    (Ssequence
      (Scall None
        (Evar _release2 (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default))
        ((Ecast (Etempvar _l (tptr (tarray (tptr tvoid) 2))) (tptr tvoid)) ::
         nil))
      (Sreturn (Some (Ecast
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       (tptr tvoid)))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t_lock, (tptr (tarray (tptr tvoid) 2))) ::
               (_t'1, (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (_t'6, (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (_t'5, (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (_t'4, (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (_t'3, (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (_t'2, (tptr (tptr (Tstruct _tree_t noattr)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _treebox_new (Tfunction Tnil
                             (tptr (tptr (Tstruct _tree_t noattr)))
                             cc_default)) nil)
      (Sassign (Evar _tb (tptr (tptr (Tstruct _tree_t noattr))))
        (Etempvar _t'1 (tptr (tptr (Tstruct _tree_t noattr))))))
    (Ssequence
      (Sset _t_lock
        (Eaddrof (Evar _thread_lock (tarray (tptr tvoid) 2))
          (tptr (tarray (tptr tvoid) 2))))
      (Ssequence
        (Ssequence
          (Sset _t'6 (Evar _tb (tptr (tptr (Tstruct _tree_t noattr)))))
          (Scall None
            (Evar _insert (Tfunction
                            (Tcons (tptr (tptr (Tstruct _tree_t noattr)))
                              (Tcons tint (Tcons (tptr tvoid) Tnil))) tvoid
                            cc_default))
            ((Etempvar _t'6 (tptr (tptr (Tstruct _tree_t noattr)))) ::
             (Econst_int (Int.repr 3) tint) ::
             (Evar ___stringlit_2 (tarray tschar 6)) :: nil)))
        (Ssequence
          (Ssequence
            (Sset _t'5 (Evar _tb (tptr (tptr (Tstruct _tree_t noattr)))))
            (Scall None
              (Evar _insert (Tfunction
                              (Tcons (tptr (tptr (Tstruct _tree_t noattr)))
                                (Tcons tint (Tcons (tptr tvoid) Tnil))) tvoid
                              cc_default))
              ((Etempvar _t'5 (tptr (tptr (Tstruct _tree_t noattr)))) ::
               (Econst_int (Int.repr 1) tint) ::
               (Evar ___stringlit_3 (tarray tschar 4)) :: nil)))
          (Ssequence
            (Ssequence
              (Sset _t'4 (Evar _tb (tptr (tptr (Tstruct _tree_t noattr)))))
              (Scall None
                (Evar _insert (Tfunction
                                (Tcons (tptr (tptr (Tstruct _tree_t noattr)))
                                  (Tcons tint (Tcons (tptr tvoid) Tnil)))
                                tvoid cc_default))
                ((Etempvar _t'4 (tptr (tptr (Tstruct _tree_t noattr)))) ::
                 (Econst_int (Int.repr 4) tint) ::
                 (Evar ___stringlit_4 (tarray tschar 5)) :: nil)))
            (Ssequence
              (Scall None
                (Evar _makelock (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                ((Ecast (Etempvar _t_lock (tptr (tarray (tptr tvoid) 2)))
                   (tptr tvoid)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _spawn (Tfunction
                                 (Tcons
                                   (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                           (tptr tvoid) cc_default))
                                   (Tcons (tptr tvoid) Tnil)) tvoid
                                 cc_default))
                  ((Ecast
                     (Eaddrof
                       (Evar _thread_func (Tfunction
                                            (Tcons (tptr tvoid) Tnil)
                                            (tptr tvoid) cc_default))
                       (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                               (tptr tvoid) cc_default))) (tptr tvoid)) ::
                   (Ecast (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     (tptr tvoid)) :: nil))
                (Ssequence
                  (Ssequence
                    (Sset _t'3
                      (Evar _tb (tptr (tptr (Tstruct _tree_t noattr)))))
                    (Scall None
                      (Evar _insert (Tfunction
                                      (Tcons
                                        (tptr (tptr (Tstruct _tree_t noattr)))
                                        (Tcons tint
                                          (Tcons (tptr tvoid) Tnil))) tvoid
                                      cc_default))
                      ((Etempvar _t'3 (tptr (tptr (Tstruct _tree_t noattr)))) ::
                       (Econst_int (Int.repr 1) tint) ::
                       (Evar ___stringlit_5 (tarray tschar 4)) :: nil)))
                  (Ssequence
                    (Scall None
                      (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil)
                                       tvoid cc_default))
                      ((Ecast
                         (Etempvar _t_lock (tptr (tarray (tptr tvoid) 2)))
                         (tptr tvoid)) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _freelock2 (Tfunction (Tcons (tptr tvoid) Tnil)
                                           tvoid cc_default))
                        ((Ecast
                           (Etempvar _t_lock (tptr (tarray (tptr tvoid) 2)))
                           (tptr tvoid)) :: nil))
                      (Ssequence
                        (Ssequence
                          (Sset _t'2
                            (Evar _tb (tptr (tptr (Tstruct _tree_t noattr)))))
                          (Scall None
                            (Evar _treebox_free (Tfunction
                                                  (Tcons
                                                    (tptr (tptr (Tstruct _tree_t noattr)))
                                                    Tnil) tvoid cc_default))
                            ((Etempvar _t'2 (tptr (tptr (Tstruct _tree_t noattr)))) ::
                             nil)))
                        (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _tree Struct
   ((_key, tint) :: (_value, (tptr tvoid)) ::
    (_left, (tptr (Tstruct _tree noattr))) ::
    (_right, (tptr (Tstruct _tree noattr))) :: nil)
   noattr ::
 Composite _tree_t Struct
   ((_t, (tptr (Tstruct _tree noattr))) ::
    (_lock, (tptr (tarray (tptr tvoid) 2))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
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
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
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
 (_thread_lock, Gvar v_thread_lock) :: (_tb, Gvar v_tb) ::
 (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_treebox_new, Gfun(Internal f_treebox_new)) ::
 (_tree_free, Gfun(Internal f_tree_free)) ::
 (_treebox_free, Gfun(Internal f_treebox_free)) ::
 (_insert, Gfun(Internal f_insert)) :: (_lookup, Gfun(Internal f_lookup)) ::
 (_turn_left, Gfun(Internal f_turn_left)) ::
 (_pushdown_left, Gfun(Internal f_pushdown_left)) ::
 (_delete, Gfun(Internal f_delete)) ::
 (_thread_func, Gfun(Internal f_thread_func)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _thread_func :: _delete :: _pushdown_left :: _turn_left ::
 _lookup :: _insert :: _treebox_free :: _tree_free :: _treebox_new ::
 _surely_malloc :: _tb :: _thread_lock :: _spawn :: _release2 ::
 _freelock2 :: _acquire :: _makelock :: _exit :: _free :: _malloc ::
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


