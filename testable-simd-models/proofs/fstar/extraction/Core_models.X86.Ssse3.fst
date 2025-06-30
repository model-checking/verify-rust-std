module Core_models.X86.Ssse3
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Core_models.Abstractions.Bit in
  let open Core_models.Abstractions.Funarr in
  ()

/// Computes the absolute value of packed 8-bit signed integers in `a` and
/// return the unsigned results.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_abs_epi8)
let e_mm_abs_epi8 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_2__to_i8x16 a
  in
  let zero:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
      #i8
      (fun temp_0_ ->
          let _:u64 = temp_0_ in
          mk_i8 0)
  in
  let r:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
    Core_models.Abstractions.Simd.simd_select (mk_u64 16)
      #i8
      #i8
      (Core_models.Abstractions.Simd.simd_lt (mk_u64 16) #i8 a zero
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
      (Core_models.Abstractions.Simd.simd_neg (mk_u64 16) #i8 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
      a
  in
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_2__from_i8x16 r

/// Computes the absolute value of each of the packed 16-bit signed integers in
/// `a` and
/// return the 16-bit unsigned integer
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_abs_epi16)
let e_mm_abs_epi16 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 a
  in
  let zero:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
      #i16
      (fun temp_0_ ->
          let _:u64 = temp_0_ in
          mk_i16 0)
  in
  let r:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
    Core_models.Abstractions.Simd.simd_select (mk_u64 8)
      #i16
      #i16
      (Core_models.Abstractions.Simd.simd_lt (mk_u64 8) #i16 a zero
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
      (Core_models.Abstractions.Simd.simd_neg (mk_u64 8) #i16 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
      a
  in
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__from_i16x8 r

/// Computes the absolute value of each of the packed 32-bit signed integers in
/// `a` and
/// return the 32-bit unsigned integer
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_abs_epi32)
let e_mm_abs_epi32 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 a
  in
  let zero:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
      #i32
      (fun temp_0_ ->
          let _:u64 = temp_0_ in
          mk_i32 0)
  in
  let r:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
    Core_models.Abstractions.Simd.simd_select (mk_u64 4)
      #i32
      #i32
      (Core_models.Abstractions.Simd.simd_lt (mk_u64 4) #i32 a zero
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
      (Core_models.Abstractions.Simd.simd_neg (mk_u64 4) #i32 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
      a
  in
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__from_i32x4 r

let pshufb128 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #u8
    (fun i ->
        let i:u64 = i in
        if (b.[ i ] <: u8) >. mk_u8 127 <: bool
        then mk_u8 0
        else a.[ cast ((b.[ i ] <: u8) %! mk_u8 16 <: u8) <: u64 ] <: u8)

/// Shuffles bytes from `a` according to the content of `b`.
/// The last 4 bits of each byte of `b` are used as addresses
/// into the 16 bytes of `a`.
/// In addition, if the highest significant bit of a byte of `b`
/// is set, the respective destination byte is set to 0.
/// Picturing `a` and `b` as `[u8; 16]`, `_mm_shuffle_epi8` is
/// logically equivalent to:
/// ```
/// fn mm_shuffle_epi8(a: [u8; 16], b: [u8; 16]) -> [u8; 16] {
///     let mut r = [0u8; 16];
///     for i in 0..16 {
///         // if the most significant bit of b is set,
///         // then the destination byte is set to 0.
///         if b[i] & 0x80 == 0u8 {
///             r[i] = a[(b[i] % 16) as usize];
///         }
///     }
///     r
/// }
/// ```
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_shuffle_epi8)
let e_mm_shuffle_epi8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_18__impl_2__from_u8x16 (pshufb128 (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_18__impl_2__to_u8x16
            a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_18__impl_2__to_u8x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
