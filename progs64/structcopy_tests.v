From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.17".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "progs64/structcopy_tests.c".
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := 13%positive.
Definition ___builtin_annot : ident := 30%positive.
Definition ___builtin_annot_intval : ident := 31%positive.
Definition ___builtin_bswap : ident := 15%positive.
Definition ___builtin_bswap16 : ident := 17%positive.
Definition ___builtin_bswap32 : ident := 16%positive.
Definition ___builtin_bswap64 : ident := 14%positive.
Definition ___builtin_clz : ident := 18%positive.
Definition ___builtin_clzl : ident := 19%positive.
Definition ___builtin_clzll : ident := 20%positive.
Definition ___builtin_ctz : ident := 21%positive.
Definition ___builtin_ctzl : ident := 22%positive.
Definition ___builtin_ctzll : ident := 23%positive.
Definition ___builtin_debug : ident := 49%positive.
Definition ___builtin_expect : ident := 38%positive.
Definition ___builtin_fabs : ident := 24%positive.
Definition ___builtin_fabsf : ident := 25%positive.
Definition ___builtin_fmadd : ident := 41%positive.
Definition ___builtin_fmax : ident := 39%positive.
Definition ___builtin_fmin : ident := 40%positive.
Definition ___builtin_fmsub : ident := 42%positive.
Definition ___builtin_fnmadd : ident := 43%positive.
Definition ___builtin_fnmsub : ident := 44%positive.
Definition ___builtin_fsqrt : ident := 26%positive.
Definition ___builtin_membar : ident := 32%positive.
Definition ___builtin_memcpy_aligned : ident := 28%positive.
Definition ___builtin_read16_reversed : ident := 45%positive.
Definition ___builtin_read32_reversed : ident := 46%positive.
Definition ___builtin_sel : ident := 29%positive.
Definition ___builtin_sqrt : ident := 27%positive.
Definition ___builtin_unreachable : ident := 37%positive.
Definition ___builtin_va_arg : ident := 34%positive.
Definition ___builtin_va_copy : ident := 35%positive.
Definition ___builtin_va_end : ident := 36%positive.
Definition ___builtin_va_start : ident := 33%positive.
Definition ___builtin_write16_reversed : ident := 47%positive.
Definition ___builtin_write32_reversed : ident := 48%positive.
Definition ___compcert_i64_dtos : ident := 69%positive.
Definition ___compcert_i64_dtou : ident := 70%positive.
Definition ___compcert_i64_sar : ident := 81%positive.
Definition ___compcert_i64_sdiv : ident := 75%positive.
Definition ___compcert_i64_shl : ident := 79%positive.
Definition ___compcert_i64_shr : ident := 80%positive.
Definition ___compcert_i64_smod : ident := 77%positive.
Definition ___compcert_i64_smulh : ident := 82%positive.
Definition ___compcert_i64_stod : ident := 71%positive.
Definition ___compcert_i64_stof : ident := 73%positive.
Definition ___compcert_i64_udiv : ident := 76%positive.
Definition ___compcert_i64_umod : ident := 78%positive.
Definition ___compcert_i64_umulh : ident := 83%positive.
Definition ___compcert_i64_utod : ident := 72%positive.
Definition ___compcert_i64_utof : ident := 74%positive.
Definition ___compcert_va_composite : ident := 68%positive.
Definition ___compcert_va_float64 : ident := 67%positive.
Definition ___compcert_va_int32 : ident := 65%positive.
Definition ___compcert_va_int64 : ident := 66%positive.
Definition _array_member : ident := 5%positive.
Definition _copy_array_fields : ident := 63%positive.
Definition _copy_array_member : ident := 55%positive.
Definition _copy_field_self : ident := 62%positive.
Definition _copy_fields : ident := 61%positive.
Definition _copy_local : ident := 53%positive.
Definition _copy_nested : ident := 54%positive.
Definition _copy_padding : ident := 57%positive.
Definition _copy_partial : ident := 58%positive.
Definition _copy_pointer : ident := 52%positive.
Definition _copy_pointer_member : ident := 56%positive.
Definition _copy_qualified : ident := 64%positive.
Definition _copy_self : ident := 60%positive.
Definition _destination : ident := 50%positive.
Definition _first : ident := 2%positive.
Definition _main : ident := 84%positive.
Definition _nested : ident := 4%positive.
Definition _object : ident := 59%positive.
Definition _padded : ident := 11%positive.
Definition _pair : ident := 1%positive.
Definition _pair_array : ident := 7%positive.
Definition _pointer : ident := 9%positive.
Definition _pointer_member : ident := 8%positive.
Definition _second : ident := 3%positive.
Definition _source : ident := 51%positive.
Definition _tag : ident := 12%positive.
Definition _value : ident := 10%positive.
Definition _values : ident := 6%positive.
Definition _t'1 : ident := 85%positive.
Definition _t'2 : ident := 86%positive.

Definition f_copy_pointer := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_destination, (tptr (Tstruct _pair noattr))) ::
                (_source, (tptr (Tstruct _pair noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Ederef (Etempvar _destination (tptr (Tstruct _pair noattr)))
    (Tstruct _pair noattr))
  (Ederef (Etempvar _source (tptr (Tstruct _pair noattr)))
    (Tstruct _pair noattr)))
|}.

Definition f_copy_local := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_source, (tptr (Tstruct _pair noattr))) :: nil);
  fn_vars := ((_destination, (Tstruct _pair noattr)) :: nil);
  fn_temps := ((_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _destination (Tstruct _pair noattr))
    (Ederef (Etempvar _source (tptr (Tstruct _pair noattr)))
      (Tstruct _pair noattr)))
  (Ssequence
    (Sset _t'1
      (Efield (Evar _destination (Tstruct _pair noattr)) _first tuint))
    (Ssequence
      (Sset _t'2
        (Efield (Evar _destination (Tstruct _pair noattr)) _second tuint))
      (Sreturn (Some (Ebinop Oadd (Etempvar _t'1 tuint) (Etempvar _t'2 tuint)
                       tuint))))))
|}.

Definition f_copy_nested := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_destination, (tptr (Tstruct _nested noattr))) ::
                (_source, (tptr (Tstruct _nested noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef (Etempvar _destination (tptr (Tstruct _nested noattr)))
      (Tstruct _nested noattr)) _first (Tstruct _pair noattr))
  (Efield
    (Ederef (Etempvar _source (tptr (Tstruct _nested noattr)))
      (Tstruct _nested noattr)) _second (Tstruct _pair noattr)))
|}.

Definition f_copy_array_member := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_destination, (tptr (Tstruct _array_member noattr))) ::
                (_source, (tptr (Tstruct _array_member noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Ederef (Etempvar _destination (tptr (Tstruct _array_member noattr)))
    (Tstruct _array_member noattr))
  (Ederef (Etempvar _source (tptr (Tstruct _array_member noattr)))
    (Tstruct _array_member noattr)))
|}.

Definition f_copy_pointer_member := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_destination, (tptr (Tstruct _pointer_member noattr))) ::
                (_source, (tptr (Tstruct _pointer_member noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Ederef (Etempvar _destination (tptr (Tstruct _pointer_member noattr)))
    (Tstruct _pointer_member noattr))
  (Ederef (Etempvar _source (tptr (Tstruct _pointer_member noattr)))
    (Tstruct _pointer_member noattr)))
|}.

Definition f_copy_padding := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_destination, (tptr (Tstruct _padded noattr))) ::
                (_source, (tptr (Tstruct _padded noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Ederef (Etempvar _destination (tptr (Tstruct _padded noattr)))
    (Tstruct _padded noattr))
  (Ederef (Etempvar _source (tptr (Tstruct _padded noattr)))
    (Tstruct _padded noattr)))
|}.

Definition f_copy_partial := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_destination, (tptr (Tstruct _pair noattr))) ::
                (_source, (tptr (Tstruct _pair noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Ederef (Etempvar _destination (tptr (Tstruct _pair noattr)))
    (Tstruct _pair noattr))
  (Ederef (Etempvar _source (tptr (Tstruct _pair noattr)))
    (Tstruct _pair noattr)))
|}.

Definition f_copy_self := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_object, (tptr (Tstruct _pair noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Ederef (Etempvar _object (tptr (Tstruct _pair noattr)))
    (Tstruct _pair noattr))
  (Ederef (Etempvar _object (tptr (Tstruct _pair noattr)))
    (Tstruct _pair noattr)))
|}.

Definition f_copy_fields := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_object, (tptr (Tstruct _nested noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef (Etempvar _object (tptr (Tstruct _nested noattr)))
      (Tstruct _nested noattr)) _first (Tstruct _pair noattr))
  (Efield
    (Ederef (Etempvar _object (tptr (Tstruct _nested noattr)))
      (Tstruct _nested noattr)) _second (Tstruct _pair noattr)))
|}.

Definition f_copy_field_self := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_object, (tptr (Tstruct _nested noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef (Etempvar _object (tptr (Tstruct _nested noattr)))
      (Tstruct _nested noattr)) _first (Tstruct _pair noattr))
  (Efield
    (Ederef (Etempvar _object (tptr (Tstruct _nested noattr)))
      (Tstruct _nested noattr)) _first (Tstruct _pair noattr)))
|}.

Definition f_copy_array_fields := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_destination, (tptr (Tstruct _pair_array noattr))) ::
                (_source, (tptr (Tstruct _pair_array noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Ederef
    (Ebinop Oadd
      (Efield
        (Ederef (Etempvar _destination (tptr (Tstruct _pair_array noattr)))
          (Tstruct _pair_array noattr)) _values
        (tarray (Tstruct _pair noattr) 2)) (Econst_int (Int.repr 0) tint)
      (tptr (Tstruct _pair noattr))) (Tstruct _pair noattr))
  (Ederef
    (Ebinop Oadd
      (Efield
        (Ederef (Etempvar _source (tptr (Tstruct _pair_array noattr)))
          (Tstruct _pair_array noattr)) _values
        (tarray (Tstruct _pair noattr) 2)) (Econst_int (Int.repr 1) tint)
      (tptr (Tstruct _pair noattr))) (Tstruct _pair noattr)))
|}.

Definition f_copy_qualified := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_destination, (tptr (Tstruct _pair noattr))) ::
                (_source, (tptr (tvolatile (Tstruct _pair noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Ederef (Etempvar _destination (tptr (Tstruct _pair noattr)))
    (Tstruct _pair noattr))
  (Ederef (Etempvar _source (tptr (tvolatile (Tstruct _pair noattr))))
    (tvolatile (Tstruct _pair noattr))))
|}.

Definition composites : list composite_definition :=
(Composite _pair Struct
   (Member_plain _first tuint :: Member_plain _second tuint :: nil)
   noattr ::
 Composite _nested Struct
   (Member_plain _first (Tstruct _pair noattr) ::
    Member_plain _second (Tstruct _pair noattr) :: nil)
   noattr ::
 Composite _array_member Struct
   (Member_plain _values (tarray tuint 2) :: nil)
   noattr ::
 Composite _pair_array Struct
   (Member_plain _values (tarray (Tstruct _pair noattr) 2) :: nil)
   noattr ::
 Composite _pointer_member Struct
   (Member_plain _pointer (tptr tuint) :: Member_plain _value tuint :: nil)
   noattr ::
 Composite _padded Struct
   (Member_plain _tag tuchar :: Member_plain _value tuint :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_copy_pointer, Gfun(Internal f_copy_pointer)) ::
 (_copy_local, Gfun(Internal f_copy_local)) ::
 (_copy_nested, Gfun(Internal f_copy_nested)) ::
 (_copy_array_member, Gfun(Internal f_copy_array_member)) ::
 (_copy_pointer_member, Gfun(Internal f_copy_pointer_member)) ::
 (_copy_padding, Gfun(Internal f_copy_padding)) ::
 (_copy_partial, Gfun(Internal f_copy_partial)) ::
 (_copy_self, Gfun(Internal f_copy_self)) ::
 (_copy_fields, Gfun(Internal f_copy_fields)) ::
 (_copy_field_self, Gfun(Internal f_copy_field_self)) ::
 (_copy_array_fields, Gfun(Internal f_copy_array_fields)) ::
 (_copy_qualified, Gfun(Internal f_copy_qualified)) :: nil).

Definition public_idents : list ident :=
(_copy_qualified :: _copy_array_fields :: _copy_field_self :: _copy_fields ::
 _copy_self :: _copy_partial :: _copy_padding :: _copy_pointer_member ::
 _copy_array_member :: _copy_nested :: _copy_local :: _copy_pointer ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


