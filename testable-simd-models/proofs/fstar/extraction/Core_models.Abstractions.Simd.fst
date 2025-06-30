module Core_models.Abstractions.Simd
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Core_models.Abstractions.Bit in
  let open Core_models.Abstractions.Funarr in
  ()

let simd_insert
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Marker.t_Copy v_T)
      (x: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
      (idx: u64)
      (v_val: v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T
    (fun i ->
        let i:u64 = i in
        if i =. idx <: bool then v_val else x.[ i ] <: v_T)

/// Extracts an element from a vector.
/// `T` must be a vector with element type `U`.
/// # Safety
/// `idx` must be in-bounds of the vector.
let simd_extract
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (x: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
      (idx: u64)
    : v_T =
  Core.Clone.f_clone #v_T
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Funarr.impl_5__get v_N #v_T x idx <: v_T)

/// Adds two simd vectors elementwise.
/// `T` must be a vector of integer or floating point primitive types.
let simd_add
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Abstractions.Bit.t_MachineInteger v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T
    (fun i ->
        let i:u64 = i in
        Core_models.Abstractions.Bit.f_wrapping_add #v_T
          #FStar.Tactics.Typeclasses.solve
          (x.[ i ] <: v_T)
          (y.[ i ] <: v_T)
        <:
        v_T)

/// Subtracts `rhs` from `lhs` elementwise.
/// `T` must be a vector of integer or floating point primitive types.
let simd_sub
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Abstractions.Bit.t_MachineInteger v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T
    (fun i ->
        let i:u64 = i in
        Core_models.Abstractions.Bit.f_wrapping_sub #v_T
          #FStar.Tactics.Typeclasses.solve
          (x.[ i ] <: v_T)
          (y.[ i ] <: v_T)
        <:
        v_T)

/// Multiplies two simd vectors elementwise.
/// `T` must be a vector of integer or floating point primitive types.
let simd_mul
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Abstractions.Bit.t_MachineInteger v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T
    (fun i ->
        let i:u64 = i in
        Core_models.Abstractions.Bit.f_overflowing_mul #v_T
          #FStar.Tactics.Typeclasses.solve
          (x.[ i ] <: v_T)
          (y.[ i ] <: v_T)
        <:
        v_T)

let simd_abs
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Abstractions.Bit.t_MachineInteger v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Marker.t_Copy v_T)
      (x: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T
    (fun i ->
        let i:u64 = i in
        Core_models.Abstractions.Bit.f_absolute_val #v_T
          #FStar.Tactics.Typeclasses.solve
          (x.[ i ] <: v_T)
        <:
        v_T)

let simd_abs_diff
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Abstractions.Bit.t_MachineInteger v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T
    (fun i ->
        let i:u64 = i in
        Core_models.Abstractions.Bit.f_absolute_diff #v_T
          #FStar.Tactics.Typeclasses.solve
          (x.[ i ] <: v_T)
          (y.[ i ] <: v_T)
        <:
        v_T)

/// Shifts vector left elementwise, with UB on overflow.
/// # Safety
/// Each element of `rhs` must be less than `<int>::BITS`.
let simd_shl
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Ops.Bit.t_Shl v_T v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N i1.f_Output =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #i1.f_Output
    (fun i ->
        let i:u64 = i in
        Core.Ops.Bit.f_shl #v_T
          #v_T
          #FStar.Tactics.Typeclasses.solve
          (x.[ i ] <: v_T)
          (y.[ i ] <: v_T)
        <:
        i1.f_Output)

/// Shifts vector right elementwise, with UB on overflow.
/// `T` must be a vector of integer primitive types.
/// Shifts `lhs` right by `rhs`, shifting in sign bits for signed types.
/// # Safety
/// Each element of `rhs` must be less than `<int>::BITS`.
let simd_shr
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Ops.Bit.t_Shr v_T v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N i1.f_Output =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #i1.f_Output
    (fun i ->
        let i:u64 = i in
        Core.Ops.Bit.f_shr #v_T
          #v_T
          #FStar.Tactics.Typeclasses.solve
          (x.[ i ] <: v_T)
          (y.[ i ] <: v_T)
        <:
        i1.f_Output)

/// "Ands" vectors elementwise.
/// `T` must be a vector of integer primitive types.
let simd_and
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Ops.Bit.t_BitAnd v_T v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N i1.f_Output =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #i1.f_Output
    (fun i ->
        let i:u64 = i in
        Core.Ops.Bit.f_bitand #v_T
          #v_T
          #FStar.Tactics.Typeclasses.solve
          (x.[ i ] <: v_T)
          (y.[ i ] <: v_T)
        <:
        i1.f_Output)

/// "Ors" vectors elementwise.
/// `T` must be a vector of integer primitive types.
let simd_or
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Ops.Bit.t_BitOr v_T v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N i1.f_Output =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #i1.f_Output
    (fun i ->
        let i:u64 = i in
        Core.Ops.Bit.f_bitor #v_T
          #v_T
          #FStar.Tactics.Typeclasses.solve
          (x.[ i ] <: v_T)
          (y.[ i ] <: v_T)
        <:
        i1.f_Output)

/// "Exclusive ors" vectors elementwise.
/// `T` must be a vector of integer primitive types.
let simd_xor
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Ops.Bit.t_BitXor v_T v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N i1.f_Output =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #i1.f_Output
    (fun i ->
        let i:u64 = i in
        Core.Ops.Bit.f_bitxor #v_T
          #v_T
          #FStar.Tactics.Typeclasses.solve
          (x.[ i ] <: v_T)
          (y.[ i ] <: v_T)
        <:
        i1.f_Output)

/// Numerically casts a vector, elementwise.
/// `T` and `U` must be vectors of integer or floating point primitive types, and must have the
/// same length.
/// When casting floats to integers, the result is truncated. Out-of-bounds result lead to UB.
/// When casting integers to floats, the result is rounded.
/// Otherwise, truncates or extends the value, maintaining the sign for signed integers.
/// # Safety
/// Casting from integer types is always safe.
/// Casting between two float types is also always safe.
/// Casting floats to integers truncates, following the same rules as `to_int_unchecked`.
/// Specifically, each element must:
/// * Not be `NaN`
/// * Not be infinite
/// * Be representable in the return type, after truncating off its fractional part
class t_CastsFrom (v_Self: Type0) (v_T: Type0) = {
  f_cast_pre:v_T -> Type0;
  f_cast_post:v_T -> v_Self -> Type0;
  f_cast:x0: v_T -> Prims.Pure v_Self (f_cast_pre x0) (fun result -> f_cast_post x0 result)
}

class t_TruncateFrom (v_Self: Type0) (v_T: Type0) = {
  f_truncate_from_pre:v_T -> Type0;
  f_truncate_from_post:v_T -> v_Self -> Type0;
  f_truncate_from:x0: v_T
    -> Prims.Pure v_Self (f_truncate_from_pre x0) (fun result -> f_truncate_from_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_TruncateFrom u8 u16 =
  {
    f_truncate_from_pre = (fun (v: u16) -> true);
    f_truncate_from_post = (fun (v: u16) (out: u8) -> true);
    f_truncate_from = fun (v: u16) -> cast (v <: u16) <: u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: t_TruncateFrom u8 u32 =
  {
    f_truncate_from_pre = (fun (v: u32) -> true);
    f_truncate_from_post = (fun (v: u32) (out: u8) -> true);
    f_truncate_from = fun (v: u32) -> cast (v <: u32) <: u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: t_TruncateFrom u8 u64 =
  {
    f_truncate_from_pre = (fun (v: u64) -> true);
    f_truncate_from_post = (fun (v: u64) (out: u8) -> true);
    f_truncate_from = fun (v: u64) -> cast (v <: u64) <: u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: t_TruncateFrom u8 u128 =
  {
    f_truncate_from_pre = (fun (v: u128) -> true);
    f_truncate_from_post = (fun (v: u128) (out: u8) -> true);
    f_truncate_from = fun (v: u128) -> cast (v <: u128) <: u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: t_TruncateFrom u16 u32 =
  {
    f_truncate_from_pre = (fun (v: u32) -> true);
    f_truncate_from_post = (fun (v: u32) (out: u16) -> true);
    f_truncate_from = fun (v: u32) -> cast (v <: u32) <: u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: t_TruncateFrom u16 u64 =
  {
    f_truncate_from_pre = (fun (v: u64) -> true);
    f_truncate_from_post = (fun (v: u64) (out: u16) -> true);
    f_truncate_from = fun (v: u64) -> cast (v <: u64) <: u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: t_TruncateFrom u16 u128 =
  {
    f_truncate_from_pre = (fun (v: u128) -> true);
    f_truncate_from_post = (fun (v: u128) (out: u16) -> true);
    f_truncate_from = fun (v: u128) -> cast (v <: u128) <: u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: t_TruncateFrom u32 u64 =
  {
    f_truncate_from_pre = (fun (v: u64) -> true);
    f_truncate_from_post = (fun (v: u64) (out: u32) -> true);
    f_truncate_from = fun (v: u64) -> cast (v <: u64) <: u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: t_TruncateFrom u32 u128 =
  {
    f_truncate_from_pre = (fun (v: u128) -> true);
    f_truncate_from_post = (fun (v: u128) (out: u32) -> true);
    f_truncate_from = fun (v: u128) -> cast (v <: u128) <: u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: t_TruncateFrom u64 u128 =
  {
    f_truncate_from_pre = (fun (v: u128) -> true);
    f_truncate_from_post = (fun (v: u128) (out: u64) -> true);
    f_truncate_from = fun (v: u128) -> cast (v <: u128) <: u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: t_TruncateFrom i8 i16 =
  {
    f_truncate_from_pre = (fun (v: i16) -> true);
    f_truncate_from_post = (fun (v: i16) (out: i8) -> true);
    f_truncate_from = fun (v: i16) -> cast (v <: i16) <: i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: t_TruncateFrom i8 i32 =
  {
    f_truncate_from_pre = (fun (v: i32) -> true);
    f_truncate_from_post = (fun (v: i32) (out: i8) -> true);
    f_truncate_from = fun (v: i32) -> cast (v <: i32) <: i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: t_TruncateFrom i8 i64 =
  {
    f_truncate_from_pre = (fun (v: i64) -> true);
    f_truncate_from_post = (fun (v: i64) (out: i8) -> true);
    f_truncate_from = fun (v: i64) -> cast (v <: i64) <: i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: t_TruncateFrom i8 i128 =
  {
    f_truncate_from_pre = (fun (v: i128) -> true);
    f_truncate_from_post = (fun (v: i128) (out: i8) -> true);
    f_truncate_from = fun (v: i128) -> cast (v <: i128) <: i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: t_TruncateFrom i16 i32 =
  {
    f_truncate_from_pre = (fun (v: i32) -> true);
    f_truncate_from_post = (fun (v: i32) (out: i16) -> true);
    f_truncate_from = fun (v: i32) -> cast (v <: i32) <: i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: t_TruncateFrom i16 i64 =
  {
    f_truncate_from_pre = (fun (v: i64) -> true);
    f_truncate_from_post = (fun (v: i64) (out: i16) -> true);
    f_truncate_from = fun (v: i64) -> cast (v <: i64) <: i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: t_TruncateFrom i16 i128 =
  {
    f_truncate_from_pre = (fun (v: i128) -> true);
    f_truncate_from_post = (fun (v: i128) (out: i16) -> true);
    f_truncate_from = fun (v: i128) -> cast (v <: i128) <: i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: t_TruncateFrom i32 i64 =
  {
    f_truncate_from_pre = (fun (v: i64) -> true);
    f_truncate_from_post = (fun (v: i64) (out: i32) -> true);
    f_truncate_from = fun (v: i64) -> cast (v <: i64) <: i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: t_TruncateFrom i32 i128 =
  {
    f_truncate_from_pre = (fun (v: i128) -> true);
    f_truncate_from_post = (fun (v: i128) (out: i32) -> true);
    f_truncate_from = fun (v: i128) -> cast (v <: i128) <: i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: t_TruncateFrom i64 i128 =
  {
    f_truncate_from_pre = (fun (v: i128) -> true);
    f_truncate_from_post = (fun (v: i128) (out: i64) -> true);
    f_truncate_from = fun (v: i128) -> cast (v <: i128) <: i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: t_CastsFrom u16 u8 =
  {
    f_cast_pre = (fun (a: u8) -> true);
    f_cast_post = (fun (a: u8) (out: u16) -> true);
    f_cast = fun (a: u8) -> Core.Convert.f_from #u16 #u8 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: t_CastsFrom u32 u8 =
  {
    f_cast_pre = (fun (a: u8) -> true);
    f_cast_post = (fun (a: u8) (out: u32) -> true);
    f_cast = fun (a: u8) -> Core.Convert.f_from #u32 #u8 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: t_CastsFrom u32 u16 =
  {
    f_cast_pre = (fun (a: u16) -> true);
    f_cast_post = (fun (a: u16) (out: u32) -> true);
    f_cast = fun (a: u16) -> Core.Convert.f_from #u32 #u16 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: t_CastsFrom u64 u8 =
  {
    f_cast_pre = (fun (a: u8) -> true);
    f_cast_post = (fun (a: u8) (out: u64) -> true);
    f_cast = fun (a: u8) -> Core.Convert.f_from #u64 #u8 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24: t_CastsFrom u64 u16 =
  {
    f_cast_pre = (fun (a: u16) -> true);
    f_cast_post = (fun (a: u16) (out: u64) -> true);
    f_cast = fun (a: u16) -> Core.Convert.f_from #u64 #u16 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25: t_CastsFrom u64 u32 =
  {
    f_cast_pre = (fun (a: u32) -> true);
    f_cast_post = (fun (a: u32) (out: u64) -> true);
    f_cast = fun (a: u32) -> Core.Convert.f_from #u64 #u32 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26: t_CastsFrom u128 u8 =
  {
    f_cast_pre = (fun (a: u8) -> true);
    f_cast_post = (fun (a: u8) (out: u128) -> true);
    f_cast = fun (a: u8) -> Core.Convert.f_from #u128 #u8 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: t_CastsFrom u128 u16 =
  {
    f_cast_pre = (fun (a: u16) -> true);
    f_cast_post = (fun (a: u16) (out: u128) -> true);
    f_cast = fun (a: u16) -> Core.Convert.f_from #u128 #u16 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28: t_CastsFrom u128 u32 =
  {
    f_cast_pre = (fun (a: u32) -> true);
    f_cast_post = (fun (a: u32) (out: u128) -> true);
    f_cast = fun (a: u32) -> Core.Convert.f_from #u128 #u32 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: t_CastsFrom u128 u64 =
  {
    f_cast_pre = (fun (a: u64) -> true);
    f_cast_post = (fun (a: u64) (out: u128) -> true);
    f_cast = fun (a: u64) -> Core.Convert.f_from #u128 #u64 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: t_CastsFrom i16 i8 =
  {
    f_cast_pre = (fun (a: i8) -> true);
    f_cast_post = (fun (a: i8) (out: i16) -> true);
    f_cast = fun (a: i8) -> Core.Convert.f_from #i16 #i8 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31: t_CastsFrom i32 i8 =
  {
    f_cast_pre = (fun (a: i8) -> true);
    f_cast_post = (fun (a: i8) (out: i32) -> true);
    f_cast = fun (a: i8) -> Core.Convert.f_from #i32 #i8 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: t_CastsFrom i32 i16 =
  {
    f_cast_pre = (fun (a: i16) -> true);
    f_cast_post = (fun (a: i16) (out: i32) -> true);
    f_cast = fun (a: i16) -> Core.Convert.f_from #i32 #i16 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: t_CastsFrom i64 i8 =
  {
    f_cast_pre = (fun (a: i8) -> true);
    f_cast_post = (fun (a: i8) (out: i64) -> true);
    f_cast = fun (a: i8) -> Core.Convert.f_from #i64 #i8 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: t_CastsFrom i64 i16 =
  {
    f_cast_pre = (fun (a: i16) -> true);
    f_cast_post = (fun (a: i16) (out: i64) -> true);
    f_cast = fun (a: i16) -> Core.Convert.f_from #i64 #i16 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: t_CastsFrom i64 i32 =
  {
    f_cast_pre = (fun (a: i32) -> true);
    f_cast_post = (fun (a: i32) (out: i64) -> true);
    f_cast = fun (a: i32) -> Core.Convert.f_from #i64 #i32 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: t_CastsFrom i128 i8 =
  {
    f_cast_pre = (fun (a: i8) -> true);
    f_cast_post = (fun (a: i8) (out: i128) -> true);
    f_cast = fun (a: i8) -> Core.Convert.f_from #i128 #i8 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: t_CastsFrom i128 i16 =
  {
    f_cast_pre = (fun (a: i16) -> true);
    f_cast_post = (fun (a: i16) (out: i128) -> true);
    f_cast = fun (a: i16) -> Core.Convert.f_from #i128 #i16 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: t_CastsFrom i128 i32 =
  {
    f_cast_pre = (fun (a: i32) -> true);
    f_cast_post = (fun (a: i32) (out: i128) -> true);
    f_cast = fun (a: i32) -> Core.Convert.f_from #i128 #i32 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39: t_CastsFrom i128 i64 =
  {
    f_cast_pre = (fun (a: i64) -> true);
    f_cast_post = (fun (a: i64) (out: i128) -> true);
    f_cast = fun (a: i64) -> Core.Convert.f_from #i128 #i64 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: t_CastsFrom u8 u16 =
  {
    f_cast_pre = (fun (a: u16) -> true);
    f_cast_post = (fun (a: u16) (out: u8) -> true);
    f_cast = fun (a: u16) -> f_truncate_from #u8 #u16 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41: t_CastsFrom u8 u32 =
  {
    f_cast_pre = (fun (a: u32) -> true);
    f_cast_post = (fun (a: u32) (out: u8) -> true);
    f_cast = fun (a: u32) -> f_truncate_from #u8 #u32 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_42: t_CastsFrom u16 u32 =
  {
    f_cast_pre = (fun (a: u32) -> true);
    f_cast_post = (fun (a: u32) (out: u16) -> true);
    f_cast = fun (a: u32) -> f_truncate_from #u16 #u32 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_43: t_CastsFrom u8 u64 =
  {
    f_cast_pre = (fun (a: u64) -> true);
    f_cast_post = (fun (a: u64) (out: u8) -> true);
    f_cast = fun (a: u64) -> f_truncate_from #u8 #u64 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_44: t_CastsFrom u16 u64 =
  {
    f_cast_pre = (fun (a: u64) -> true);
    f_cast_post = (fun (a: u64) (out: u16) -> true);
    f_cast = fun (a: u64) -> f_truncate_from #u16 #u64 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_45: t_CastsFrom u32 u64 =
  {
    f_cast_pre = (fun (a: u64) -> true);
    f_cast_post = (fun (a: u64) (out: u32) -> true);
    f_cast = fun (a: u64) -> f_truncate_from #u32 #u64 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_46: t_CastsFrom u8 u128 =
  {
    f_cast_pre = (fun (a: u128) -> true);
    f_cast_post = (fun (a: u128) (out: u8) -> true);
    f_cast = fun (a: u128) -> f_truncate_from #u8 #u128 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_47: t_CastsFrom u16 u128 =
  {
    f_cast_pre = (fun (a: u128) -> true);
    f_cast_post = (fun (a: u128) (out: u16) -> true);
    f_cast = fun (a: u128) -> f_truncate_from #u16 #u128 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_48: t_CastsFrom u32 u128 =
  {
    f_cast_pre = (fun (a: u128) -> true);
    f_cast_post = (fun (a: u128) (out: u32) -> true);
    f_cast = fun (a: u128) -> f_truncate_from #u32 #u128 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_49: t_CastsFrom u64 u128 =
  {
    f_cast_pre = (fun (a: u128) -> true);
    f_cast_post = (fun (a: u128) (out: u64) -> true);
    f_cast = fun (a: u128) -> f_truncate_from #u64 #u128 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_50: t_CastsFrom i8 i16 =
  {
    f_cast_pre = (fun (a: i16) -> true);
    f_cast_post = (fun (a: i16) (out: i8) -> true);
    f_cast = fun (a: i16) -> f_truncate_from #i8 #i16 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_51: t_CastsFrom i8 i32 =
  {
    f_cast_pre = (fun (a: i32) -> true);
    f_cast_post = (fun (a: i32) (out: i8) -> true);
    f_cast = fun (a: i32) -> f_truncate_from #i8 #i32 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_52: t_CastsFrom i16 i32 =
  {
    f_cast_pre = (fun (a: i32) -> true);
    f_cast_post = (fun (a: i32) (out: i16) -> true);
    f_cast = fun (a: i32) -> f_truncate_from #i16 #i32 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_53: t_CastsFrom i8 i64 =
  {
    f_cast_pre = (fun (a: i64) -> true);
    f_cast_post = (fun (a: i64) (out: i8) -> true);
    f_cast = fun (a: i64) -> f_truncate_from #i8 #i64 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_54: t_CastsFrom i16 i64 =
  {
    f_cast_pre = (fun (a: i64) -> true);
    f_cast_post = (fun (a: i64) (out: i16) -> true);
    f_cast = fun (a: i64) -> f_truncate_from #i16 #i64 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_55: t_CastsFrom i32 i64 =
  {
    f_cast_pre = (fun (a: i64) -> true);
    f_cast_post = (fun (a: i64) (out: i32) -> true);
    f_cast = fun (a: i64) -> f_truncate_from #i32 #i64 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_56: t_CastsFrom i8 i128 =
  {
    f_cast_pre = (fun (a: i128) -> true);
    f_cast_post = (fun (a: i128) (out: i8) -> true);
    f_cast = fun (a: i128) -> f_truncate_from #i8 #i128 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_57: t_CastsFrom i16 i128 =
  {
    f_cast_pre = (fun (a: i128) -> true);
    f_cast_post = (fun (a: i128) (out: i16) -> true);
    f_cast = fun (a: i128) -> f_truncate_from #i16 #i128 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_58: t_CastsFrom i32 i128 =
  {
    f_cast_pre = (fun (a: i128) -> true);
    f_cast_post = (fun (a: i128) (out: i32) -> true);
    f_cast = fun (a: i128) -> f_truncate_from #i32 #i128 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_59: t_CastsFrom i64 i128 =
  {
    f_cast_pre = (fun (a: i128) -> true);
    f_cast_post = (fun (a: i128) (out: i64) -> true);
    f_cast = fun (a: i128) -> f_truncate_from #i64 #i128 #FStar.Tactics.Typeclasses.solve a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_60: t_CastsFrom u8 i8 =
  {
    f_cast_pre = (fun (a: i8) -> true);
    f_cast_post = (fun (a: i8) (out: u8) -> true);
    f_cast = fun (a: i8) -> cast (a <: i8) <: u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_61: t_CastsFrom i8 u8 =
  {
    f_cast_pre = (fun (a: u8) -> true);
    f_cast_post = (fun (a: u8) (out: i8) -> true);
    f_cast = fun (a: u8) -> cast (a <: u8) <: i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_62: t_CastsFrom u16 i16 =
  {
    f_cast_pre = (fun (a: i16) -> true);
    f_cast_post = (fun (a: i16) (out: u16) -> true);
    f_cast = fun (a: i16) -> cast (a <: i16) <: u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_63: t_CastsFrom i16 u16 =
  {
    f_cast_pre = (fun (a: u16) -> true);
    f_cast_post = (fun (a: u16) (out: i16) -> true);
    f_cast = fun (a: u16) -> cast (a <: u16) <: i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_64: t_CastsFrom u32 i32 =
  {
    f_cast_pre = (fun (a: i32) -> true);
    f_cast_post = (fun (a: i32) (out: u32) -> true);
    f_cast = fun (a: i32) -> cast (a <: i32) <: u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_65: t_CastsFrom i32 u32 =
  {
    f_cast_pre = (fun (a: u32) -> true);
    f_cast_post = (fun (a: u32) (out: i32) -> true);
    f_cast = fun (a: u32) -> cast (a <: u32) <: i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_66: t_CastsFrom u64 i64 =
  {
    f_cast_pre = (fun (a: i64) -> true);
    f_cast_post = (fun (a: i64) (out: u64) -> true);
    f_cast = fun (a: i64) -> cast (a <: i64) <: u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_67: t_CastsFrom i64 u64 =
  {
    f_cast_pre = (fun (a: u64) -> true);
    f_cast_post = (fun (a: u64) (out: i64) -> true);
    f_cast = fun (a: u64) -> cast (a <: u64) <: i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_68: t_CastsFrom u128 i128 =
  {
    f_cast_pre = (fun (a: i128) -> true);
    f_cast_post = (fun (a: i128) (out: u128) -> true);
    f_cast = fun (a: i128) -> cast (a <: i128) <: u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_69: t_CastsFrom i128 u128 =
  {
    f_cast_pre = (fun (a: u128) -> true);
    f_cast_post = (fun (a: u128) (out: i128) -> true);
    f_cast = fun (a: u128) -> cast (a <: u128) <: i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_70: t_CastsFrom u8 u8 =
  {
    f_cast_pre = (fun (a: u8) -> true);
    f_cast_post = (fun (a: u8) (out: u8) -> true);
    f_cast = fun (a: u8) -> a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_71: t_CastsFrom u16 u16 =
  {
    f_cast_pre = (fun (a: u16) -> true);
    f_cast_post = (fun (a: u16) (out: u16) -> true);
    f_cast = fun (a: u16) -> a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_72: t_CastsFrom u32 u32 =
  {
    f_cast_pre = (fun (a: u32) -> true);
    f_cast_post = (fun (a: u32) (out: u32) -> true);
    f_cast = fun (a: u32) -> a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_73: t_CastsFrom u64 u64 =
  {
    f_cast_pre = (fun (a: u64) -> true);
    f_cast_post = (fun (a: u64) (out: u64) -> true);
    f_cast = fun (a: u64) -> a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_74: t_CastsFrom u128 u128 =
  {
    f_cast_pre = (fun (a: u128) -> true);
    f_cast_post = (fun (a: u128) (out: u128) -> true);
    f_cast = fun (a: u128) -> a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_75: t_CastsFrom i8 i8 =
  {
    f_cast_pre = (fun (a: i8) -> true);
    f_cast_post = (fun (a: i8) (out: i8) -> true);
    f_cast = fun (a: i8) -> a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_76: t_CastsFrom i16 i16 =
  {
    f_cast_pre = (fun (a: i16) -> true);
    f_cast_post = (fun (a: i16) (out: i16) -> true);
    f_cast = fun (a: i16) -> a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_77: t_CastsFrom i32 i32 =
  {
    f_cast_pre = (fun (a: i32) -> true);
    f_cast_post = (fun (a: i32) (out: i32) -> true);
    f_cast = fun (a: i32) -> a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_78: t_CastsFrom i64 i64 =
  {
    f_cast_pre = (fun (a: i64) -> true);
    f_cast_post = (fun (a: i64) (out: i64) -> true);
    f_cast = fun (a: i64) -> a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_79: t_CastsFrom i128 i128 =
  {
    f_cast_pre = (fun (a: i128) -> true);
    f_cast_post = (fun (a: i128) (out: i128) -> true);
    f_cast = fun (a: i128) -> a
  }

let simd_cast
      (v_N: u64)
      (#v_T1 #v_T2: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Marker.t_Copy v_T1)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: t_CastsFrom v_T2 v_T1)
      (x: Core_models.Abstractions.Funarr.t_FunArray v_N v_T1)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T2 =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T2
    (fun i ->
        let i:u64 = i in
        f_cast #v_T2 #v_T1 #FStar.Tactics.Typeclasses.solve (x.[ i ] <: v_T1) <: v_T2)

/// Negates a vector elementwise.
/// `T` must be a vector of integer or floating-point primitive types.
/// Rust panics for `-<int>::Min` due to overflow, but it is not UB with this intrinsic.
let simd_neg
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core.Convert.t_From v_T v_11690907798620021094.f_Output)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Core_models.Abstractions.Bit.t_MachineInteger v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: Core.Cmp.t_Eq v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i4: Core.Ops.Arith.t_Neg v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i5: Core.Marker.t_Copy v_T)
      (x: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T
    (fun i ->
        let i:u64 = i in
        if
          (x.[ i ] <: v_T) =.
          (Core_models.Abstractions.Bit.f_MIN #v_T #FStar.Tactics.Typeclasses.solve <: v_T)
          <:
          bool
        then Core_models.Abstractions.Bit.f_MIN #v_T #FStar.Tactics.Typeclasses.solve <: v_T
        else
          Core.Convert.f_from #v_T
            #i4.f_Output
            #FStar.Tactics.Typeclasses.solve
            (Core.Ops.Arith.f_neg #v_T #FStar.Tactics.Typeclasses.solve (x.[ i ] <: v_T)
              <:
              i4.f_Output)
          <:
          v_T)

/// Tests elementwise equality of two vectors.
/// `T` must be a vector of floating-point primitive types.
/// `U` must be a vector of integers with the same number of elements and element size as `T`.
/// Returns `0` for false and `!0` for true.
let simd_eq
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Cmp.t_Eq v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Core_models.Abstractions.Bit.t_MachineInteger v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T
    (fun i ->
        let i:u64 = i in
        if (x.[ i ] <: v_T) =. (y.[ i ] <: v_T) <: bool
        then Core_models.Abstractions.Bit.f_ONES #v_T #FStar.Tactics.Typeclasses.solve <: v_T
        else Core_models.Abstractions.Bit.f_ZEROS #v_T #FStar.Tactics.Typeclasses.solve <: v_T)

/// Tests elementwise inequality equality of two vectors.
/// `T` must be a vector of floating-point primitive types.
/// `U` must be a vector of integers with the same number of elements and element size as `T`.
/// Returns `0` for false and `!0` for true.
let simd_ne
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Cmp.t_Eq v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Core_models.Abstractions.Bit.t_MachineInteger v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T
    (fun i ->
        let i:u64 = i in
        if (x.[ i ] <: v_T) <>. (y.[ i ] <: v_T) <: bool
        then Core_models.Abstractions.Bit.f_ONES #v_T #FStar.Tactics.Typeclasses.solve <: v_T
        else Core_models.Abstractions.Bit.f_ZEROS #v_T #FStar.Tactics.Typeclasses.solve <: v_T)

/// Tests if `x` is less than `y`, elementwise.
/// `T` must be a vector of floating-point primitive types.
/// `U` must be a vector of integers with the same number of elements and element size as `T`.
/// Returns `0` for false and `!0` for true.
let simd_lt
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Cmp.t_Ord v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Core_models.Abstractions.Bit.t_MachineInteger v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T
    (fun i ->
        let i:u64 = i in
        if
          Core.Cmp.f_lt #v_T #v_T #FStar.Tactics.Typeclasses.solve (x.[ i ] <: v_T) (y.[ i ] <: v_T)
          <:
          bool
        then Core_models.Abstractions.Bit.f_ONES #v_T #FStar.Tactics.Typeclasses.solve <: v_T
        else Core_models.Abstractions.Bit.f_ZEROS #v_T #FStar.Tactics.Typeclasses.solve <: v_T)

/// Tests if `x` is less than or equal to `y`, elementwise.
/// `T` must be a vector of floating-point primitive types.
/// `U` must be a vector of integers with the same number of elements and element size as `T`.
/// Returns `0` for false and `!0` for true.
let simd_le
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Cmp.t_Ord v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Core_models.Abstractions.Bit.t_MachineInteger v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T
    (fun i ->
        let i:u64 = i in
        if
          Core.Cmp.f_le #v_T #v_T #FStar.Tactics.Typeclasses.solve (x.[ i ] <: v_T) (y.[ i ] <: v_T)
          <:
          bool
        then Core_models.Abstractions.Bit.f_ONES #v_T #FStar.Tactics.Typeclasses.solve <: v_T
        else Core_models.Abstractions.Bit.f_ZEROS #v_T #FStar.Tactics.Typeclasses.solve <: v_T)

/// Tests if `x` is greater than `y`, elementwise.
/// `T` must be a vector of floating-point primitive types.
/// `U` must be a vector of integers with the same number of elements and element size as `T`.
/// Returns `0` for false and `!0` for true.
let simd_gt
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Cmp.t_Ord v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Core_models.Abstractions.Bit.t_MachineInteger v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T
    (fun i ->
        let i:u64 = i in
        if
          Core.Cmp.f_gt #v_T #v_T #FStar.Tactics.Typeclasses.solve (x.[ i ] <: v_T) (y.[ i ] <: v_T)
          <:
          bool
        then Core_models.Abstractions.Bit.f_ONES #v_T #FStar.Tactics.Typeclasses.solve <: v_T
        else Core_models.Abstractions.Bit.f_ZEROS #v_T #FStar.Tactics.Typeclasses.solve <: v_T)

/// Tests if `x` is greater than or equal to `y`, elementwise.
/// `T` must be a vector of floating-point primitive types.
/// `U` must be a vector of integers with the same number of elements and element size as `T`.
/// Returns `0` for false and `!0` for true.
let simd_ge
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Cmp.t_Ord v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Core_models.Abstractions.Bit.t_MachineInteger v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T
    (fun i ->
        let i:u64 = i in
        if
          Core.Cmp.f_ge #v_T #v_T #FStar.Tactics.Typeclasses.solve (x.[ i ] <: v_T) (y.[ i ] <: v_T)
          <:
          bool
        then Core_models.Abstractions.Bit.f_ONES #v_T #FStar.Tactics.Typeclasses.solve <: v_T
        else Core_models.Abstractions.Bit.f_ZEROS #v_T #FStar.Tactics.Typeclasses.solve <: v_T)

/// Shuffles two vectors by const indices.
/// `T` must be a vector.
/// `U` must be a **const** vector of `u32`s. This means it must either refer to a named
/// const or be given as an inline const expression (`const { ... }`).
/// `V` must be a vector with the same element type as `T` and the same length as `U`.
/// Returns a new vector such that element `i` is selected from `xy[idx[i]]`, where `xy`
/// is the concatenation of `x` and `y`. It is a compile-time error if `idx[i]` is out-of-bounds
/// of `xy`.
let simd_shuffle
      (#v_T: Type0)
      (v_N1: u64)
      (v_N2: usize)
      (v_N3: u64)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N1 v_T)
      (idx: t_Array u64 v_N2)
    : Core_models.Abstractions.Funarr.t_FunArray v_N3 v_T =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N3
    #v_T
    (fun i ->
        let i:u64 = i in
        let i:u64 = idx.[ cast (i <: u64) <: usize ] in
        if i <. v_N1 then x.[ i ] else y.[ i -! v_N1 <: u64 ])

/// Adds two simd vectors elementwise, with saturation.
/// `T` must be a vector of integer primitive types.
let simd_saturating_add
      (#v_T: Type0)
      (v_N: u64)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Abstractions.Bit.t_MachineInteger v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T
    (fun i ->
        let i:u64 = i in
        Core_models.Abstractions.Bit.f_saturating_add #v_T
          #FStar.Tactics.Typeclasses.solve
          (x.[ i ] <: v_T)
          (y.[ i ] <: v_T)
        <:
        v_T)

/// Subtracts two simd vectors elementwise, with saturation.
/// `T` must be a vector of integer primitive types.
/// Subtract `rhs` from `lhs`.
let simd_saturating_sub
      (#v_T: Type0)
      (v_N: u64)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Abstractions.Bit.t_MachineInteger v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Marker.t_Copy v_T)
      (x y: Core_models.Abstractions.Funarr.t_FunArray v_N v_T)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T
    (fun i ->
        let i:u64 = i in
        Core_models.Abstractions.Bit.f_saturating_sub #v_T
          #FStar.Tactics.Typeclasses.solve
          (x.[ i ] <: v_T)
          (y.[ i ] <: v_T)
        <:
        v_T)

/// Selects elements from a mask.
/// `M` must be an integer vector.
/// `T` must be a vector with the same number of elements as `M`.
/// For each element, if the corresponding value in `mask` is `!0`, select the element from
/// `if_true`.  If the corresponding value in `mask` is `0`, select the element from
/// `if_false`.
/// # Safety
/// `mask` must only contain `0` and `!0`.
let simd_select
      (v_N: u64)
      (#v_T1 #v_T2: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Cmp.t_Eq v_T1)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Core_models.Abstractions.Bit.t_MachineInteger v_T1)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i4: Core.Marker.t_Copy v_T2)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Core_models.Abstractions.Bit.t_MachineInteger v_T2)
      (mask: Core_models.Abstractions.Funarr.t_FunArray v_N v_T1)
      (if_true if_false: Core_models.Abstractions.Funarr.t_FunArray v_N v_T2)
    : Core_models.Abstractions.Funarr.t_FunArray v_N v_T2 =
  Core_models.Abstractions.Funarr.impl_5__from_fn v_N
    #v_T2
    (fun i ->
        let i:u64 = i in
        if
          (mask.[ i ] <: v_T1) =.
          (Core_models.Abstractions.Bit.f_ONES #v_T1 #FStar.Tactics.Typeclasses.solve <: v_T1)
          <:
          bool
        then if_true.[ i ] <: v_T2
        else if_false.[ i ] <: v_T2)
