module Core_models.Core_arch.X86.Interpretations.Int_vec
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

let e_mm256_set1_epi32 (x: i32) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        x)

let e_mm256_mul_epi32 (x y: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        (cast (x.[ i *! mk_u64 2 <: u64 ] <: i32) <: i64) *!
        (cast (y.[ i *! mk_u64 2 <: u64 ] <: i32) <: i64)
        <:
        i64)

let e_mm256_sub_epi32 (x y: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        Core.Num.impl_i32__wrapping_sub (x.[ i ] <: i32) (y.[ i ] <: i32) <: i32)

let e_mm256_shuffle_epi32
      (v_CONTROL: i32)
      (x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  let (indexes: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) u64 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
      #u64
      (fun i ->
          let i:u64 = i in
          cast ((v_CONTROL >>! (i *! mk_u64 2 <: u64) <: i32) %! mk_i32 4 <: i32) <: u64)
  in
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 4 <: bool
        then x.[ indexes.[ i ] <: u64 ] <: i32
        else x.[ mk_u64 4 +! (indexes.[ i -! mk_u64 4 <: u64 ] <: u64) <: u64 ] <: i32)

let e_mm256_blend_epi32
      (v_CONTROL: i32)
      (x y: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if ((v_CONTROL >>! i <: i32) %! mk_i32 2 <: i32) =. mk_i32 0 <: bool
        then x.[ i ] <: i32
        else y.[ i ] <: i32)

let e_mm256_setzero_si256 (_: Prims.unit) : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 256)
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        Core_models.Abstractions.Bit.Bit_Zero <: Core_models.Abstractions.Bit.t_Bit)

let e_mm256_set_m128i (hi lo: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 256)
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 128 <: bool
        then lo.[ i ] <: Core_models.Abstractions.Bit.t_Bit
        else hi.[ i -! mk_u64 128 <: u64 ] <: Core_models.Abstractions.Bit.t_Bit)

let e_mm256_set1_epi16 (a: i16) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        a)

let e_mm_set1_epi16 (a: i16) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i16
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        a)

let e_mm_set_epi32 (e3 e2 e1 e0: i32) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i32
    (fun i ->
        let i:u64 = i in
        match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 -> e0
        | Rust_primitives.Integers.MkInt 1 -> e1
        | Rust_primitives.Integers.MkInt 2 -> e2
        | Rust_primitives.Integers.MkInt 3 -> e3
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          i32)

let e_mm_add_epi16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i16
    (fun i ->
        let i:u64 = i in
        Core.Num.impl_i16__wrapping_add (a.[ i ] <: i16) (b.[ i ] <: i16) <: i16)

let e_mm256_add_epi16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        Core.Num.impl_i16__wrapping_add (a.[ i ] <: i16) (b.[ i ] <: i16) <: i16)

let e_mm256_add_epi32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        Core.Num.impl_i32__wrapping_add (a.[ i ] <: i32) (b.[ i ] <: i32) <: i32)

let e_mm256_add_epi64 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        Core.Num.impl_i64__wrapping_add (a.[ i ] <: i64) (b.[ i ] <: i64) <: i64)

let e_mm256_abs_epi32 (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if (a.[ i ] <: i32) =. Core.Num.impl_i32__MIN <: bool
        then a.[ i ] <: i32
        else Core.Num.impl_i32__abs (a.[ i ] <: i32) <: i32)

let e_mm256_sub_epi16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        Core.Num.impl_i16__wrapping_sub (a.[ i ] <: i16) (b.[ i ] <: i16) <: i16)

let e_mm_sub_epi16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i16
    (fun i ->
        let i:u64 = i in
        Core.Num.impl_i16__wrapping_sub (a.[ i ] <: i16) (b.[ i ] <: i16) <: i16)

let e_mm_mullo_epi16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i16
    (fun i ->
        let i:u64 = i in
        (Core.Num.impl_i16__overflowing_mul (a.[ i ] <: i16) (b.[ i ] <: i16) <: (i16 & bool))._1)

let e_mm256_cmpgt_epi16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        if (a.[ i ] <: i16) >. (b.[ i ] <: i16) <: bool then mk_i16 (-1) else mk_i16 0)

let e_mm256_cmpgt_epi32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if (a.[ i ] <: i32) >. (b.[ i ] <: i32) <: bool then mk_i32 (-1) else mk_i32 0)

let e_mm256_cmpeq_epi32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if (a.[ i ] <: i32) =. (b.[ i ] <: i32) <: bool then mk_i32 (-1) else mk_i32 0)

let e_mm256_sign_epi32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if (b.[ i ] <: i32) <. mk_i32 0 <: bool
        then
          if (a.[ i ] <: i32) =. Core.Num.impl_i32__MIN <: bool
          then a.[ i ] <: i32
          else Core.Ops.Arith.f_neg (a.[ i ] <: i32) <: i32
        else if (b.[ i ] <: i32) >. mk_i32 0 <: bool then a.[ i ] <: i32 else mk_i32 0)

let e_mm256_castsi256_ps (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = a

let e_mm256_castps_si256 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = a

let e_mm256_movemask_ps (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) : i32 =
  let (a0: i32):i32 = if (a.[ mk_u64 0 ] <: i32) <. mk_i32 0 then mk_i32 1 else mk_i32 0 in
  let a1:i32 = if (a.[ mk_u64 1 ] <: i32) <. mk_i32 0 then mk_i32 2 else mk_i32 0 in
  let a2:i32 = if (a.[ mk_u64 2 ] <: i32) <. mk_i32 0 then mk_i32 4 else mk_i32 0 in
  let a3:i32 = if (a.[ mk_u64 3 ] <: i32) <. mk_i32 0 then mk_i32 8 else mk_i32 0 in
  let a4:i32 = if (a.[ mk_u64 4 ] <: i32) <. mk_i32 0 then mk_i32 16 else mk_i32 0 in
  let a5:i32 = if (a.[ mk_u64 5 ] <: i32) <. mk_i32 0 then mk_i32 32 else mk_i32 0 in
  let a6:i32 = if (a.[ mk_u64 6 ] <: i32) <. mk_i32 0 then mk_i32 64 else mk_i32 0 in
  let a7:i32 = if (a.[ mk_u64 7 ] <: i32) <. mk_i32 0 then mk_i32 128 else mk_i32 0 in
  ((((((a0 +! a1 <: i32) +! a2 <: i32) +! a3 <: i32) +! a4 <: i32) +! a5 <: i32) +! a6 <: i32) +! a7

#push-options "--z3rlimit 200"

let e_mm_mulhi_epi16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i16
    (fun i ->
        let i:u64 = i in
        cast (((cast (a.[ i ] <: i16) <: i32) *! (cast (b.[ i ] <: i16) <: i32) <: i32) >>!
            mk_i32 16
            <:
            i32)
        <:
        i16)

#pop-options

let e_mm256_mullo_epi32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        (Core.Num.impl_i32__overflowing_mul (a.[ i ] <: i32) (b.[ i ] <: i32) <: (i32 & bool))._1)

#push-options "--admit_smt_queries true"

let e_mm256_mulhi_epi16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        cast (((cast (a.[ i ] <: i16) <: i32) *! (cast (b.[ i ] <: i16) <: i32) <: i32) >>!
            mk_i32 16
            <:
            i32)
        <:
        i16)

#pop-options

let e_mm256_mul_epu32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #u64
    (fun i ->
        let i:u64 = i in
        (cast (a.[ i *! mk_u64 2 <: u64 ] <: u32) <: u64) *!
        (cast (b.[ i *! mk_u64 2 <: u64 ] <: u32) <: u64)
        <:
        u64)

let e_mm256_and_si256 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__from_i64x4 (Core_models.Abstractions.Simd.simd_and
        (mk_u64 4)
        #i64
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

let e_mm256_or_si256 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__from_i64x4 (Core_models.Abstractions.Simd.simd_or
        (mk_u64 4)
        #i64
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

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

let e_mm256_xor_si256 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__from_i64x4 (Core_models.Abstractions.Simd.simd_xor
        (mk_u64 4)
        #i64
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

let e_mm256_srai_epi16 (v_IMM8: i32) (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        let imm8:i32 = Core.Num.impl_i32__rem_euclid v_IMM8 (mk_i32 256) in
        if imm8 >. mk_i32 15
        then if (a.[ i ] <: i16) <. mk_i16 0 then mk_i16 (-1) else mk_i16 0
        else (a.[ i ] <: i16) >>! imm8)

let e_mm256_srai_epi32 (v_IMM8: i32) (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        let imm8:i32 = Core.Num.impl_i32__rem_euclid v_IMM8 (mk_i32 256) in
        if imm8 >. mk_i32 31
        then if (a.[ i ] <: i32) <. mk_i32 0 then mk_i32 (-1) else mk_i32 0
        else (a.[ i ] <: i32) >>! imm8)

let e_mm256_srli_epi16 (v_IMM8: i32) (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        let imm8:i32 = Core.Num.impl_i32__rem_euclid v_IMM8 (mk_i32 256) in
        if imm8 >. mk_i32 15
        then mk_i16 0
        else cast ((cast (a.[ i ] <: i16) <: u16) >>! imm8 <: u16) <: i16)

let e_mm256_srli_epi32 (v_IMM8: i32) (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        let imm8:i32 = Core.Num.impl_i32__rem_euclid v_IMM8 (mk_i32 256) in
        if imm8 >. mk_i32 31
        then mk_i32 0
        else cast ((cast (a.[ i ] <: i32) <: u32) >>! imm8 <: u32) <: i32)

let e_mm_srli_epi64 (v_IMM8: i32) (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
    #i64
    (fun i ->
        let i:u64 = i in
        let imm8:i32 = Core.Num.impl_i32__rem_euclid v_IMM8 (mk_i32 256) in
        if imm8 >. mk_i32 63
        then mk_i64 0
        else cast ((cast (a.[ i ] <: i64) <: u64) >>! imm8 <: u64) <: i64)

let e_mm256_slli_epi32 (v_IMM8: i32) (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        let imm8:i32 = Core.Num.impl_i32__rem_euclid v_IMM8 (mk_i32 256) in
        if imm8 >. mk_i32 31
        then mk_i32 0
        else cast ((cast (a.[ i ] <: i32) <: u32) <<! imm8 <: u32) <: i32)

let e_mm256_permute4x64_epi64
      (v_IMM8: i32)
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  let (indexes: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) u64 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
      #u64
      (fun i ->
          let i:u64 = i in
          cast ((v_IMM8 >>! (i *! mk_u64 2 <: u64) <: i32) %! mk_i32 4 <: i32) <: u64)
  in
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        a.[ indexes.[ i ] <: u64 ] <: i64)

let e_mm256_unpackhi_epi64 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 -> a.[ mk_u64 1 ] <: i64
        | Rust_primitives.Integers.MkInt 1 -> b.[ mk_u64 1 ] <: i64
        | Rust_primitives.Integers.MkInt 2 -> a.[ mk_u64 3 ] <: i64
        | Rust_primitives.Integers.MkInt 3 -> b.[ mk_u64 3 ] <: i64
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          i64)

let e_mm256_unpacklo_epi32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 -> a.[ mk_u64 0 ] <: i32
        | Rust_primitives.Integers.MkInt 1 -> b.[ mk_u64 0 ] <: i32
        | Rust_primitives.Integers.MkInt 2 -> a.[ mk_u64 1 ] <: i32
        | Rust_primitives.Integers.MkInt 3 -> b.[ mk_u64 1 ] <: i32
        | Rust_primitives.Integers.MkInt 4 -> a.[ mk_u64 4 ] <: i32
        | Rust_primitives.Integers.MkInt 5 -> b.[ mk_u64 4 ] <: i32
        | Rust_primitives.Integers.MkInt 6 -> a.[ mk_u64 5 ] <: i32
        | Rust_primitives.Integers.MkInt 7 -> b.[ mk_u64 5 ] <: i32
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          i32)

let e_mm256_unpackhi_epi32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 -> a.[ mk_u64 2 ] <: i32
        | Rust_primitives.Integers.MkInt 1 -> b.[ mk_u64 2 ] <: i32
        | Rust_primitives.Integers.MkInt 2 -> a.[ mk_u64 3 ] <: i32
        | Rust_primitives.Integers.MkInt 3 -> b.[ mk_u64 3 ] <: i32
        | Rust_primitives.Integers.MkInt 4 -> a.[ mk_u64 6 ] <: i32
        | Rust_primitives.Integers.MkInt 5 -> b.[ mk_u64 6 ] <: i32
        | Rust_primitives.Integers.MkInt 6 -> a.[ mk_u64 7 ] <: i32
        | Rust_primitives.Integers.MkInt 7 -> b.[ mk_u64 7 ] <: i32
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          i32)

let e_mm256_castsi128_si256 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 256)
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 128 <: bool
        then a.[ i ] <: Core_models.Abstractions.Bit.t_Bit
        else Core_models.Abstractions.Bit.Bit_Zero <: Core_models.Abstractions.Bit.t_Bit)

let e_mm256_cvtepi16_epi32 (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        cast (a.[ i ] <: i16) <: i32)

let e_mm_packs_epi16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i8
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 8 <: bool
        then
          if (a.[ i ] <: i16) >. (cast (Core.Num.impl_i8__MAX <: i8) <: i16) <: bool
          then Core.Num.impl_i8__MAX
          else
            if (a.[ i ] <: i16) <. (cast (Core.Num.impl_i8__MIN <: i8) <: i16) <: bool
            then Core.Num.impl_i8__MIN
            else cast (a.[ i ] <: i16) <: i8
        else
          if
            (b.[ i -! mk_u64 8 <: u64 ] <: i16) >. (cast (Core.Num.impl_i8__MAX <: i8) <: i16)
            <:
            bool
          then Core.Num.impl_i8__MAX
          else
            if
              (b.[ i -! mk_u64 8 <: u64 ] <: i16) <. (cast (Core.Num.impl_i8__MIN <: i8) <: i16)
              <:
              bool
            then Core.Num.impl_i8__MIN
            else cast (b.[ i -! mk_u64 8 <: u64 ] <: i16) <: i8)

let e_mm256_packs_epi32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 4 <: bool
        then
          if (a.[ i ] <: i32) >. (cast (Core.Num.impl_i16__MAX <: i16) <: i32) <: bool
          then Core.Num.impl_i16__MAX
          else
            if (a.[ i ] <: i32) <. (cast (Core.Num.impl_i16__MIN <: i16) <: i32) <: bool
            then Core.Num.impl_i16__MIN
            else cast (a.[ i ] <: i32) <: i16
        else
          if i <. mk_u64 8 <: bool
          then
            if
              (b.[ i -! mk_u64 4 <: u64 ] <: i32) >. (cast (Core.Num.impl_i16__MAX <: i16) <: i32)
              <:
              bool
            then Core.Num.impl_i16__MAX
            else
              if
                (b.[ i -! mk_u64 4 <: u64 ] <: i32) <. (cast (Core.Num.impl_i16__MIN <: i16) <: i32)
                <:
                bool
              then Core.Num.impl_i16__MIN
              else cast (b.[ i -! mk_u64 4 <: u64 ] <: i32) <: i16
          else
            if i <. mk_u64 12 <: bool
            then
              if
                (a.[ i -! mk_u64 4 <: u64 ] <: i32) >. (cast (Core.Num.impl_i16__MAX <: i16) <: i32)
                <:
                bool
              then Core.Num.impl_i16__MAX
              else
                if
                  (a.[ i -! mk_u64 4 <: u64 ] <: i32) <.
                  (cast (Core.Num.impl_i16__MIN <: i16) <: i32)
                  <:
                  bool
                then Core.Num.impl_i16__MIN
                else cast (a.[ i -! mk_u64 4 <: u64 ] <: i32) <: i16
            else
              if
                (b.[ i -! mk_u64 8 <: u64 ] <: i32) >. (cast (Core.Num.impl_i16__MAX <: i16) <: i32)
                <:
                bool
              then Core.Num.impl_i16__MAX
              else
                if
                  (b.[ i -! mk_u64 8 <: u64 ] <: i32) <.
                  (cast (Core.Num.impl_i16__MIN <: i16) <: i32)
                  <:
                  bool
                then Core.Num.impl_i16__MIN
                else cast (b.[ i -! mk_u64 8 <: u64 ] <: i32) <: i16)

let e_mm256_inserti128_si256
      (v_IMM8: i32)
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128)
      (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
    #i128
    (fun i ->
        let i:u64 = i in
        if (v_IMM8 %! mk_i32 2 <: i32) =. mk_i32 0 <: bool
        then
          match i <: u64 with
          | Rust_primitives.Integers.MkInt 0 -> b.[ mk_u64 0 ] <: i128
          | Rust_primitives.Integers.MkInt 1 -> a.[ mk_u64 1 ] <: i128
          | _ ->
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

                <:
                Rust_primitives.Hax.t_Never)
            <:
            i128
        else
          match i <: u64 with
          | Rust_primitives.Integers.MkInt 0 -> a.[ mk_u64 0 ] <: i128
          | Rust_primitives.Integers.MkInt 1 -> b.[ mk_u64 0 ] <: i128
          | _ ->
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

                <:
                Rust_primitives.Hax.t_Never)
            <:
            i128)

let e_mm256_blend_epi16
      (v_IMM8: i32)
      (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        if ((v_IMM8 >>! (i %! mk_u64 8 <: u64) <: i32) %! mk_i32 2 <: i32) =. mk_i32 0 <: bool
        then a.[ i ] <: i16
        else b.[ i ] <: i16)

let e_mm256_blendv_ps (a b mask: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if (mask.[ i ] <: i32) <. mk_i32 0 <: bool then b.[ i ] <: i32 else a.[ i ] <: i32)

#push-options "--admit_smt_queries true"

let e_mm_movemask_epi8 (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8) : i32 =
  let a0:i32 = if (a.[ mk_u64 0 ] <: i8) <. mk_i8 0 then mk_i32 1 else mk_i32 0 in
  let a1:i32 = if (a.[ mk_u64 1 ] <: i8) <. mk_i8 0 then mk_i32 2 else mk_i32 0 in
  let a2:i32 = if (a.[ mk_u64 2 ] <: i8) <. mk_i8 0 then mk_i32 4 else mk_i32 0 in
  let a3:i32 = if (a.[ mk_u64 3 ] <: i8) <. mk_i8 0 then mk_i32 8 else mk_i32 0 in
  let a4:i32 = if (a.[ mk_u64 4 ] <: i8) <. mk_i8 0 then mk_i32 16 else mk_i32 0 in
  let a5:i32 = if (a.[ mk_u64 5 ] <: i8) <. mk_i8 0 then mk_i32 32 else mk_i32 0 in
  let a6:i32 = if (a.[ mk_u64 6 ] <: i8) <. mk_i8 0 then mk_i32 64 else mk_i32 0 in
  let a7:i32 = if (a.[ mk_u64 7 ] <: i8) <. mk_i8 0 then mk_i32 128 else mk_i32 0 in
  let a8:i32 = if (a.[ mk_u64 8 ] <: i8) <. mk_i8 0 then mk_i32 256 else mk_i32 0 in
  let a9:i32 = if (a.[ mk_u64 9 ] <: i8) <. mk_i8 0 then mk_i32 512 else mk_i32 0 in
  let a10:i32 = if (a.[ mk_u64 10 ] <: i8) <. mk_i8 0 then mk_i32 1024 else mk_i32 0 in
  let a11:i32 = if (a.[ mk_u64 11 ] <: i8) <. mk_i8 0 then mk_i32 2048 else mk_i32 0 in
  let a12:i32 = if (a.[ mk_u64 12 ] <: i8) <. mk_i8 0 then mk_i32 4096 else mk_i32 0 in
  let a13:i32 = if (a.[ mk_u64 13 ] <: i8) <. mk_i8 0 then mk_i32 8192 else mk_i32 0 in
  let a14:i32 = if (a.[ mk_u64 14 ] <: i8) <. mk_i8 0 then mk_i32 16384 else mk_i32 0 in
  let a15:i32 = if (a.[ mk_u64 15 ] <: i8) <. mk_i8 0 then mk_i32 32768 else mk_i32 0 in
  ((((((((((((((a0 +! a1 <: i32) +! a2 <: i32) +! a3 <: i32) +! a4 <: i32) +! a5 <: i32) +! a6
                    <:
                    i32) +!
                  a7
                  <:
                  i32) +!
                a8
                <:
                i32) +!
              a9
              <:
              i32) +!
            a10
            <:
            i32) +!
          a11
          <:
          i32) +!
        a12
        <:
        i32) +!
      a13
      <:
      i32) +!
    a14
    <:
    i32) +!
  a15

#pop-options

let e_mm256_srlv_epi64 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        if ((b.[ i ] <: i64) >. mk_i64 63 <: bool) || ((b.[ i ] <: i64) <. mk_i64 0 <: bool)
        then mk_i64 0
        else cast ((cast (a.[ i ] <: i64) <: u64) >>! (b.[ i ] <: i64) <: u64) <: i64)

let e_mm_sllv_epi32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i32
    (fun i ->
        let i:u64 = i in
        if ((b.[ i ] <: i32) >. mk_i32 31 <: bool) || ((b.[ i ] <: i32) <. mk_i32 0 <: bool)
        then mk_i32 0
        else cast ((cast (a.[ i ] <: i32) <: u32) <<! (b.[ i ] <: i32) <: u32) <: i32)

let e_mm256_slli_epi64 (v_IMM8: i32) (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        let imm8:i32 = v_IMM8 %! mk_i32 256 in
        if imm8 >. mk_i32 63
        then mk_i64 0
        else cast ((cast (a.[ i ] <: i64) <: u64) <<! imm8 <: u64) <: i64)

let e_mm256_bsrli_epi128
      (v_IMM8: i32)
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
    #i128
    (fun i ->
        let i:u64 = i in
        let tmp:i32 = v_IMM8 %! mk_i32 256 in
        let tmp:i32 = tmp %! mk_i32 16 in
        cast ((cast (a.[ i ] <: i128) <: u128) >>! (tmp *! mk_i32 8 <: i32) <: u128) <: i128)

let e_mm256_andnot_si256 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 256)
    (fun i ->
        let i:u64 = i in
        match
          (a.[ i ] <: Core_models.Abstractions.Bit.t_Bit),
          (b.[ i ] <: Core_models.Abstractions.Bit.t_Bit)
          <:
          (Core_models.Abstractions.Bit.t_Bit & Core_models.Abstractions.Bit.t_Bit)
        with
        | Core_models.Abstractions.Bit.Bit_Zero , Core_models.Abstractions.Bit.Bit_One  ->
          Core_models.Abstractions.Bit.Bit_One <: Core_models.Abstractions.Bit.t_Bit
        | _ -> Core_models.Abstractions.Bit.Bit_Zero <: Core_models.Abstractions.Bit.t_Bit)

let e_mm256_set1_epi64x (a: i64) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        a)

let e_mm256_set_epi64x (e3 e2 e1 e0: i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 -> e0
        | Rust_primitives.Integers.MkInt 1 -> e1
        | Rust_primitives.Integers.MkInt 2 -> e2
        | Rust_primitives.Integers.MkInt 3 -> e3
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          i64)

let e_mm256_unpacklo_epi64 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 -> a.[ mk_u64 0 ] <: i64
        | Rust_primitives.Integers.MkInt 1 -> b.[ mk_u64 0 ] <: i64
        | Rust_primitives.Integers.MkInt 2 -> a.[ mk_u64 2 ] <: i64
        | Rust_primitives.Integers.MkInt 3 -> b.[ mk_u64 2 ] <: i64
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          i64)

let e_mm256_permute2x128_si256
      (v_IMM8: i32)
      (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
    #i128
    (fun i ->
        let i:u64 = i in
        let control:i32 = v_IMM8 >>! (i *! mk_u64 4 <: u64) in
        if ((control >>! mk_i32 3 <: i32) %! mk_i32 2 <: i32) =. mk_i32 1
        then mk_i128 0
        else
          match control %! mk_i32 4 <: i32 with
          | Rust_primitives.Integers.MkInt 0 -> a.[ mk_u64 0 ]
          | Rust_primitives.Integers.MkInt 1 -> a.[ mk_u64 1 ]
          | Rust_primitives.Integers.MkInt 2 -> b.[ mk_u64 0 ]
          | Rust_primitives.Integers.MkInt 3 -> b.[ mk_u64 1 ]
          | _ ->
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

                <:
                Rust_primitives.Hax.t_Never))
