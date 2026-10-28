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
  Definition source_file := "progs64/unioncopy.c".
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := 17%positive.
Definition ___builtin_annot : ident := 34%positive.
Definition ___builtin_annot_intval : ident := 35%positive.
Definition ___builtin_bswap : ident := 19%positive.
Definition ___builtin_bswap16 : ident := 21%positive.
Definition ___builtin_bswap32 : ident := 20%positive.
Definition ___builtin_bswap64 : ident := 18%positive.
Definition ___builtin_clz : ident := 22%positive.
Definition ___builtin_clzl : ident := 23%positive.
Definition ___builtin_clzll : ident := 24%positive.
Definition ___builtin_ctz : ident := 25%positive.
Definition ___builtin_ctzl : ident := 26%positive.
Definition ___builtin_ctzll : ident := 27%positive.
Definition ___builtin_debug : ident := 53%positive.
Definition ___builtin_expect : ident := 42%positive.
Definition ___builtin_fabs : ident := 28%positive.
Definition ___builtin_fabsf : ident := 29%positive.
Definition ___builtin_fmadd : ident := 45%positive.
Definition ___builtin_fmax : ident := 43%positive.
Definition ___builtin_fmin : ident := 44%positive.
Definition ___builtin_fmsub : ident := 46%positive.
Definition ___builtin_fnmadd : ident := 47%positive.
Definition ___builtin_fnmsub : ident := 48%positive.
Definition ___builtin_fsqrt : ident := 30%positive.
Definition ___builtin_membar : ident := 36%positive.
Definition ___builtin_memcpy_aligned : ident := 32%positive.
Definition ___builtin_read16_reversed : ident := 49%positive.
Definition ___builtin_read32_reversed : ident := 50%positive.
Definition ___builtin_sel : ident := 33%positive.
Definition ___builtin_sqrt : ident := 31%positive.
Definition ___builtin_unreachable : ident := 41%positive.
Definition ___builtin_va_arg : ident := 38%positive.
Definition ___builtin_va_copy : ident := 39%positive.
Definition ___builtin_va_end : ident := 40%positive.
Definition ___builtin_va_start : ident := 37%positive.
Definition ___builtin_write16_reversed : ident := 51%positive.
Definition ___builtin_write32_reversed : ident := 52%positive.
Definition ___compcert_i64_dtos : ident := 72%positive.
Definition ___compcert_i64_dtou : ident := 73%positive.
Definition ___compcert_i64_sar : ident := 84%positive.
Definition ___compcert_i64_sdiv : ident := 78%positive.
Definition ___compcert_i64_shl : ident := 82%positive.
Definition ___compcert_i64_shr : ident := 83%positive.
Definition ___compcert_i64_smod : ident := 80%positive.
Definition ___compcert_i64_smulh : ident := 85%positive.
Definition ___compcert_i64_stod : ident := 74%positive.
Definition ___compcert_i64_stof : ident := 76%positive.
Definition ___compcert_i64_udiv : ident := 79%positive.
Definition ___compcert_i64_umod : ident := 81%positive.
Definition ___compcert_i64_umulh : ident := 86%positive.
Definition ___compcert_i64_utod : ident := 75%positive.
Definition ___compcert_i64_utof : ident := 77%positive.
Definition ___compcert_va_composite : ident := 71%positive.
Definition ___compcert_va_float64 : ident := 70%positive.
Definition ___compcert_va_int32 : ident := 68%positive.
Definition ___compcert_va_int64 : ident := 69%positive.
Definition _choice : ident := 1%positive.
Definition _copy_choice : ident := 56%positive.
Definition _copy_choice_self : ident := 62%positive.
Definition _copy_nested_choice : ident := 58%positive.
Definition _copy_padded_choice : ident := 57%positive.
Definition _copy_union_array_fields : ident := 66%positive.
Definition _copy_union_array_whole : ident := 60%positive.
Definition _copy_union_field_self : ident := 65%positive.
Definition _copy_union_fields : ident := 63%positive.
Definition _copy_union_fields_whole : ident := 59%positive.
Definition _copy_union_pair : ident := 67%positive.
Definition _copy_union_siblings : ident := 64%positive.
Definition _destination : ident := 54%positive.
Definition _first : ident := 10%positive.
Definition _full : ident := 6%positive.
Definition _inner : ident := 8%positive.
Definition _integer : ident := 2%positive.
Definition _main : ident := 87%positive.
Definition _nested_choice : ident := 7%positive.
Definition _object : ident := 61%positive.
Definition _padded_choice : ident := 4%positive.
Definition _pair : ident := 16%positive.
Definition _pair_choice : ident := 15%positive.
Definition _pointer : ident := 3%positive.
Definition _second : ident := 11%positive.
Definition _source : ident := 55%positive.
Definition _tiny : ident := 5%positive.
Definition _union_array : ident := 12%positive.
Definition _union_fields : ident := 9%positive.
Definition _union_pair : ident := 14%positive.
Definition _values : ident := 13%positive.

Definition f_copy_choice := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_destination, (tptr (Tunion _choice noattr))) ::
                (_source, (tptr (Tunion _choice noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Ederef (Etempvar _destination (tptr (Tunion _choice noattr)))
    (Tunion _choice noattr))
  (Ederef (Etempvar _source (tptr (Tunion _choice noattr)))
    (Tunion _choice noattr)))
|}.

Definition f_copy_padded_choice := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_destination, (tptr (Tunion _padded_choice noattr))) ::
                (_source, (tptr (Tunion _padded_choice noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Ederef (Etempvar _destination (tptr (Tunion _padded_choice noattr)))
    (Tunion _padded_choice noattr))
  (Ederef (Etempvar _source (tptr (Tunion _padded_choice noattr)))
    (Tunion _padded_choice noattr)))
|}.

Definition f_copy_nested_choice := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_destination, (tptr (Tunion _nested_choice noattr))) ::
                (_source, (tptr (Tunion _nested_choice noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Ederef (Etempvar _destination (tptr (Tunion _nested_choice noattr)))
    (Tunion _nested_choice noattr))
  (Ederef (Etempvar _source (tptr (Tunion _nested_choice noattr)))
    (Tunion _nested_choice noattr)))
|}.

Definition f_copy_union_fields_whole := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_destination, (tptr (Tstruct _union_fields noattr))) ::
                (_source, (tptr (Tstruct _union_fields noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Ederef (Etempvar _destination (tptr (Tstruct _union_fields noattr)))
    (Tstruct _union_fields noattr))
  (Ederef (Etempvar _source (tptr (Tstruct _union_fields noattr)))
    (Tstruct _union_fields noattr)))
|}.

Definition f_copy_union_array_whole := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_destination, (tptr (Tstruct _union_array noattr))) ::
                (_source, (tptr (Tstruct _union_array noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Ederef (Etempvar _destination (tptr (Tstruct _union_array noattr)))
    (Tstruct _union_array noattr))
  (Ederef (Etempvar _source (tptr (Tstruct _union_array noattr)))
    (Tstruct _union_array noattr)))
|}.

Definition f_copy_choice_self := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_object, (tptr (Tunion _choice noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Ederef (Etempvar _object (tptr (Tunion _choice noattr)))
    (Tunion _choice noattr))
  (Ederef (Etempvar _object (tptr (Tunion _choice noattr)))
    (Tunion _choice noattr)))
|}.

Definition f_copy_union_fields := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_destination, (tptr (Tstruct _union_fields noattr))) ::
                (_source, (tptr (Tstruct _union_fields noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef (Etempvar _destination (tptr (Tstruct _union_fields noattr)))
      (Tstruct _union_fields noattr)) _first (Tunion _choice noattr))
  (Efield
    (Ederef (Etempvar _source (tptr (Tstruct _union_fields noattr)))
      (Tstruct _union_fields noattr)) _second (Tunion _choice noattr)))
|}.

Definition f_copy_union_siblings := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_object, (tptr (Tstruct _union_fields noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef (Etempvar _object (tptr (Tstruct _union_fields noattr)))
      (Tstruct _union_fields noattr)) _first (Tunion _choice noattr))
  (Efield
    (Ederef (Etempvar _object (tptr (Tstruct _union_fields noattr)))
      (Tstruct _union_fields noattr)) _second (Tunion _choice noattr)))
|}.

Definition f_copy_union_field_self := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_object, (tptr (Tstruct _union_fields noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef (Etempvar _object (tptr (Tstruct _union_fields noattr)))
      (Tstruct _union_fields noattr)) _first (Tunion _choice noattr))
  (Efield
    (Ederef (Etempvar _object (tptr (Tstruct _union_fields noattr)))
      (Tstruct _union_fields noattr)) _first (Tunion _choice noattr)))
|}.

Definition f_copy_union_array_fields := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_destination, (tptr (Tstruct _union_array noattr))) ::
                (_source, (tptr (Tstruct _union_array noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Ederef
    (Ebinop Oadd
      (Efield
        (Ederef (Etempvar _destination (tptr (Tstruct _union_array noattr)))
          (Tstruct _union_array noattr)) _values
        (tarray (Tunion _choice noattr) 2)) (Econst_int (Int.repr 0) tint)
      (tptr (Tunion _choice noattr))) (Tunion _choice noattr))
  (Ederef
    (Ebinop Oadd
      (Efield
        (Ederef (Etempvar _source (tptr (Tstruct _union_array noattr)))
          (Tstruct _union_array noattr)) _values
        (tarray (Tunion _choice noattr) 2)) (Econst_int (Int.repr 1) tint)
      (tptr (Tunion _choice noattr))) (Tunion _choice noattr)))
|}.

Definition f_copy_union_pair := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_destination, (tptr (Tunion _pair_choice noattr))) ::
                (_source, (tptr (Tunion _pair_choice noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef (Etempvar _destination (tptr (Tunion _pair_choice noattr)))
      (Tunion _pair_choice noattr)) _pair (Tstruct _union_pair noattr))
  (Efield
    (Ederef (Etempvar _source (tptr (Tunion _pair_choice noattr)))
      (Tunion _pair_choice noattr)) _pair (Tstruct _union_pair noattr)))
|}.

Definition composites : list composite_definition :=
(Composite _choice Union
   (Member_plain _integer tuint :: Member_plain _pointer (tptr tuint) :: nil)
   noattr ::
 Composite _padded_choice Union
   (Member_plain _tiny tuchar :: Member_plain _full tuint :: nil)
   noattr ::
 Composite _nested_choice Union
   (Member_plain _inner (Tunion _choice noattr) ::
    Member_plain _integer tuint :: nil)
   noattr ::
 Composite _union_fields Struct
   (Member_plain _first (Tunion _choice noattr) ::
    Member_plain _second (Tunion _choice noattr) :: nil)
   noattr ::
 Composite _union_array Struct
   (Member_plain _values (tarray (Tunion _choice noattr) 2) :: nil)
   noattr ::
 Composite _union_pair Struct
   (Member_plain _first tuint :: Member_plain _second tuint :: nil)
   noattr ::
 Composite _pair_choice Union
   (Member_plain _pair (Tstruct _union_pair noattr) ::
    Member_plain _integer tuint :: nil)
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
 (_copy_choice, Gfun(Internal f_copy_choice)) ::
 (_copy_padded_choice, Gfun(Internal f_copy_padded_choice)) ::
 (_copy_nested_choice, Gfun(Internal f_copy_nested_choice)) ::
 (_copy_union_fields_whole, Gfun(Internal f_copy_union_fields_whole)) ::
 (_copy_union_array_whole, Gfun(Internal f_copy_union_array_whole)) ::
 (_copy_choice_self, Gfun(Internal f_copy_choice_self)) ::
 (_copy_union_fields, Gfun(Internal f_copy_union_fields)) ::
 (_copy_union_siblings, Gfun(Internal f_copy_union_siblings)) ::
 (_copy_union_field_self, Gfun(Internal f_copy_union_field_self)) ::
 (_copy_union_array_fields, Gfun(Internal f_copy_union_array_fields)) ::
 (_copy_union_pair, Gfun(Internal f_copy_union_pair)) :: nil).

Definition public_idents : list ident :=
(_copy_union_pair :: _copy_union_array_fields :: _copy_union_field_self ::
 _copy_union_siblings :: _copy_union_fields :: _copy_choice_self ::
 _copy_union_array_whole :: _copy_union_fields_whole ::
 _copy_nested_choice :: _copy_padded_choice :: _copy_choice ::
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


