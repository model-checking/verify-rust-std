module Core_models.X86.Avx
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Core_models.Abstractions.Bit in
  let open Core_models.Abstractions.Bitvec in
  let open Core_models.Abstractions.Funarr in
  ()

/// Blends packed single-precision (32-bit) floating-point elements from
/// `a` and `b` using `c` as a mask.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blendv_ps)
let e_mm256_blendv_ps (a b c: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let (mask: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) i32 =
    Core_models.Abstractions.Simd.simd_lt (mk_u64 8)
      #i32
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 c
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
          #i32
          (fun temp_0_ ->
              let _:u64 = temp_0_ in
              mk_i32 0)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
  in
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Abstractions.Simd.simd_select
        (mk_u64 8)
        #i32
        #i32
        mask
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Computes the bitwise AND of 256 bits (representing integer data) in `a` and
/// `b`, and set `ZF` to 1 if the result is zero, otherwise set `ZF` to 0.
/// Computes the bitwise NOT of `a` and then AND with `b`, and set `CF` to 1 if
/// the result is zero, otherwise set `CF` to 0. Return the `ZF` value.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_testz_si256)
let e_mm256_testz_si256 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) : i32 =
  let c:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 256)
      (fun i ->
          let i:u64 = i in
          match
            (a.[ i ] <: Core_models.Abstractions.Bit.t_Bit),
            (b.[ i ] <: Core_models.Abstractions.Bit.t_Bit)
            <:
            (Core_models.Abstractions.Bit.t_Bit & Core_models.Abstractions.Bit.t_Bit)
          with
          | Core_models.Abstractions.Bit.Bit_One , Core_models.Abstractions.Bit.Bit_One  ->
            Core_models.Abstractions.Bit.Bit_One <: Core_models.Abstractions.Bit.t_Bit
          | _ -> Core_models.Abstractions.Bit.Bit_Zero <: Core_models.Abstractions.Bit.t_Bit)
  in
  let all_zero:bool =
    Core_models.Abstractions.Bitvec.impl_10__fold (mk_u64 256)
      #bool
      c
      true
      (fun acc bit ->
          let acc:bool = acc in
          let bit:Core_models.Abstractions.Bit.t_Bit = bit in
          acc &&
          (bit =. (Core_models.Abstractions.Bit.Bit_Zero <: Core_models.Abstractions.Bit.t_Bit)
            <:
            bool))
  in
  if all_zero then mk_i32 1 else mk_i32 0

/// Sets each bit of the returned mask based on the most significant bit of the
/// corresponding packed single-precision (32-bit) floating-point element in
/// `a`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_movemask_ps)
let e_mm256_movemask_ps (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) : i32 =
  let (mask: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) i32 =
    Core_models.Abstractions.Simd.simd_lt (mk_u64 8)
      #i32
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
          #i32
          (fun temp_0_ ->
              let _:u64 = temp_0_ in
              mk_i32 0)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
  in
  let r:u8 =
    (mk_u8 128 *!
      (cast ((if (mask.[ mk_u64 7 ] <: i32) <. mk_i32 0 <: bool then mk_i32 1 else mk_i32 0) <: i32)
        <:
        u8)
      <:
      u8) +!
    ((mk_u8 64 *!
        (cast ((if (mask.[ mk_u64 6 ] <: i32) <. mk_i32 0 <: bool then mk_i32 1 else mk_i32 0)
              <:
              i32)
          <:
          u8)
        <:
        u8) +!
      ((mk_u8 32 *!
          (cast ((if (mask.[ mk_u64 5 ] <: i32) <. mk_i32 0 <: bool then mk_i32 1 else mk_i32 0)
                <:
                i32)
            <:
            u8)
          <:
          u8) +!
        ((mk_u8 16 *!
            (cast ((if (mask.[ mk_u64 4 ] <: i32) <. mk_i32 0 <: bool then mk_i32 1 else mk_i32 0)
                  <:
                  i32)
              <:
              u8)
            <:
            u8) +!
          ((mk_u8 8 *!
              (cast ((if (mask.[ mk_u64 3 ] <: i32) <. mk_i32 0 <: bool then mk_i32 1 else mk_i32 0)
                    <:
                    i32)
                <:
                u8)
              <:
              u8) +!
            ((mk_u8 4 *!
                (cast ((if (mask.[ mk_u64 2 ] <: i32) <. mk_i32 0 <: bool
                        then mk_i32 1
                        else mk_i32 0)
                      <:
                      i32)
                  <:
                  u8)
                <:
                u8) +!
              ((mk_u8 2 *!
                  (cast ((if (mask.[ mk_u64 1 ] <: i32) <. mk_i32 0 <: bool
                          then mk_i32 1
                          else mk_i32 0)
                        <:
                        i32)
                    <:
                    u8)
                  <:
                  u8) +!
                (cast ((if (mask.[ mk_u64 0 ] <: i32) <. mk_i32 0 <: bool
                        then mk_i32 1
                        else mk_i32 0)
                      <:
                      i32)
                  <:
                  u8)
                <:
                u8)
              <:
              u8)
            <:
            u8)
          <:
          u8)
        <:
        u8)
      <:
      u8)
  in
  cast (cast (r <: u8) <: u32) <: i32

/// Returns vector of type __m256 with all elements set to zero.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_setzero_ps)
let e_mm256_setzero_ps (_: Prims.unit) : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 256)
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        Core_models.Abstractions.Bit.Bit_Zero <: Core_models.Abstractions.Bit.t_Bit)

/// Returns vector of type __m256i with all elements set to zero.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_setzero_si256)
let e_mm256_setzero_si256 (_: Prims.unit) : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 256)
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        Core_models.Abstractions.Bit.Bit_Zero <: Core_models.Abstractions.Bit.t_Bit)

/// Sets packed 8-bit integers in returned vector with the supplied values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set_epi8)
let e_mm256_set_epi8
      (e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31:
          i8)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let vec:t_Array i8 (mk_usize 32) =
    let list =
      [
        e00; e01; e02; e03; e04; e05; e06; e07; e08; e09; e10; e11; e12; e13; e14; e15; e16; e17;
        e18; e19; e20; e21; e22; e23; e24; e25; e26; e27; e28; e29; e30; e31
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
    Rust_primitives.Hax.array_of_list 32 list
  in
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__from_i8x32 (Core_models.Abstractions.Funarr.impl_5__from_fn
        (mk_u64 32)
        #i8
        (fun i ->
            let i:u64 = i in
            vec.[ cast (mk_u64 31 -! i <: u64) <: usize ] <: i8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)

/// Sets packed 16-bit integers in returned vector with the supplied values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set_epi16)
let e_mm256_set_epi16 (e00 e01 e02 e03 e04 e05 e06 e07 e08 e09 e10 e11 e12 e13 e14 e15: i16)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let vec:t_Array i16 (mk_usize 16) =
    let list = [e00; e01; e02; e03; e04; e05; e06; e07; e08; e09; e10; e11; e12; e13; e14; e15] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
    Rust_primitives.Hax.array_of_list 16 list
  in
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__from_i16x16 (Core_models.Abstractions.Funarr.impl_5__from_fn
        (mk_u64 16)
        #i16
        (fun i ->
            let i:u64 = i in
            vec.[ cast (mk_u64 15 -! i <: u64) <: usize ] <: i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Sets packed 32-bit integers in returned vector with the supplied values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set_epi32)
let e_mm256_set_epi32 (e0 e1 e2 e3 e4 e5 e6 e7: i32)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let vec:t_Array i32 (mk_usize 8) =
    let list = [e0; e1; e2; e3; e4; e5; e6; e7] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
    Rust_primitives.Hax.array_of_list 8 list
  in
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Abstractions.Funarr.impl_5__from_fn
        (mk_u64 8)
        #i32
        (fun i ->
            let i:u64 = i in
            vec.[ cast (mk_u64 7 -! i <: u64) <: usize ] <: i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Sets packed 64-bit integers in returned vector with the supplied values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set_epi64x)
let e_mm256_set_epi64x (a b c d: i64) : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let vec:t_Array i64 (mk_usize 4) =
    let list = [d; c; b; a] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
    Rust_primitives.Hax.array_of_list 4 list
  in
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__from_i64x4 (Core_models.Abstractions.Funarr.impl_5__from_fn
        (mk_u64 4)
        #i64
        (fun i ->
            let i:u64 = i in
            vec.[ cast (i <: u64) <: usize ] <: i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Broadcasts 16-bit integer `a` to all elements of returned vector.
/// This intrinsic may generate the `vpbroadcastw`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set1_epi16)
let e_mm256_set1_epi16 (a: i16) : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__from_i16x16 (Core_models.Abstractions.Funarr.impl_5__from_fn
        (mk_u64 16)
        #i16
        (fun temp_0_ ->
            let _:u64 = temp_0_ in
            a)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Broadcasts 32-bit integer `a` to all elements of returned vector.
/// This intrinsic may generate the `vpbroadcastd`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set1_epi32)
let e_mm256_set1_epi32 (a: i32) : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Abstractions.Funarr.impl_5__from_fn
        (mk_u64 8)
        #i32
        (fun temp_0_ ->
            let _:u64 = temp_0_ in
            a)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Broadcasts 64-bit integer `a` to all elements of returned vector.
/// This intrinsic may generate the `vpbroadcastq`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set1_epi64x)
let e_mm256_set1_epi64x (a: i64) : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__from_i64x4 (Core_models.Abstractions.Funarr.impl_5__from_fn
        (mk_u64 4)
        #i64
        (fun temp_0_ ->
            let _:u64 = temp_0_ in
            a)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Casts vector of type __m256 to type __m256i.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_castps_si256)
let e_mm256_castps_si256 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = a

/// Casts vector of type __m256i to type __m256.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_castsi256_ps)
let e_mm256_castsi256_ps (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = a

let e_mm256_castsi256_si128 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 128)
    (fun i ->
        let i:u64 = i in
        a.[ i ] <: Core_models.Abstractions.Bit.t_Bit)

/// Casts vector of type __m128i to type __m256i;
/// the upper 128 bits of the result are undefined.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_castsi128_si256)
let e_mm256_castsi128_si256 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_2__to_i64x2 a
  in
  let undefined:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
      #i64
      (fun temp_0_ ->
          let _:u64 = temp_0_ in
          mk_i64 0)
  in
  let (dst: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i64 =
    Core_models.Abstractions.Simd.simd_shuffle #i64
      (mk_u64 2)
      (mk_usize 4)
      (mk_u64 4)
      a
      undefined
      (let list = [mk_u64 0; mk_u64 1; mk_u64 2; mk_u64 2] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__from_i64x4 dst

let e_mm256_set_m128i (hi lo: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 256)
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 128 <: bool
        then lo.[ i ] <: Core_models.Abstractions.Bit.t_Bit
        else hi.[ i -! mk_u64 128 <: u64 ] <: Core_models.Abstractions.Bit.t_Bit)
