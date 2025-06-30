module Core_models.X86.Sse2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Core_models.Abstractions.Bit in
  let open Core_models.Abstractions.Funarr in
  let open Core_models.Abstractions.Simd in
  ()

let e_mm_add_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__from_i16x8 (Core_models.Abstractions.Simd.simd_add
        (mk_u64 8)
        #i16
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)

let e_mm_mulhi_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
      #i16
      #i32
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
      #i16
      #i32
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 b
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
  in
  let r:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
    Core_models.Abstractions.Simd.simd_shr (mk_u64 8)
      #i32
      (Core_models.Abstractions.Simd.simd_mul (mk_u64 8) #i32 a b
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_1__splat (mk_i32 16)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
  in
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__from_i16x8 (Core_models.Abstractions.Simd.simd_cast
        (mk_u64 8)
        #i32
        #i16
        r
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)

let e_mm_mullo_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__from_i16x8 (Core_models.Abstractions.Simd.simd_mul
        (mk_u64 8)
        #i16
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)

/// Subtracts packed 8-bit integers in `b` from packed 8-bit integers in `a`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sub_epi8)
let e_mm_sub_epi8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_2__from_i8x16 (Core_models.Abstractions.Simd.simd_sub
        (mk_u64 16)
        #i8
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_2__to_i8x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_2__to_i8x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)

let e_mm_sub_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__from_i16x8 (Core_models.Abstractions.Simd.simd_sub
        (mk_u64 8)
        #i16
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)

let e_mm_srli_epi64 (v_IMM8: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  if v_IMM8 >=. mk_i32 64
  then
    Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 128)
      (fun temp_0_ ->
          let _:u64 = temp_0_ in
          Core_models.Abstractions.Bit.Bit_Zero <: Core_models.Abstractions.Bit.t_Bit)
  else
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_16__impl_2__from_u64x2 (Core_models.Abstractions.Simd.simd_shr
          (mk_u64 2)
          #u64
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_16__impl_2__to_u64x2 a
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_16__impl_1__splat (cast (v_IMM8
                    <:
                    i32)
                <:
                u64)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)

/// Sets packed 32-bit integers with the supplied values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set_epi32)
let e_mm_set_epi32 (e3 e2 e1 e0: i32) : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let vec:t_Array i32 (mk_usize 4) =
    let list = [e0; e1; e2; e3] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
    Rust_primitives.Hax.array_of_list 4 list
  in
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__from_i32x4 (Core_models.Abstractions.Funarr.impl_5__from_fn
        (mk_u64 4)
        #i32
        (fun i ->
            let i:u64 = i in
            vec.[ cast (i <: u64) <: usize ] <: i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)

/// Sets packed 8-bit integers with the supplied values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set_epi8)
let e_mm_set_epi8 (e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0: i8)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let vec:t_Array i8 (mk_usize 16) =
    let list = [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
    Rust_primitives.Hax.array_of_list 16 list
  in
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_2__from_i8x16 (Core_models.Abstractions.Funarr.impl_5__from_fn
        (mk_u64 16)
        #i8
        (fun i ->
            let i:u64 = i in
            vec.[ cast (i <: u64) <: usize ] <: i8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)

let e_mm_set1_epi16 (a: i16) : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__from_i16x8 (Core_models.Abstractions.Funarr.impl_5__from_fn
        (mk_u64 8)
        #i16
        (fun temp_0_ ->
            let _:u64 = temp_0_ in
            a)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)

let e_mm_movemask_epi8 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) : i32 =
  let z:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
      #i8
      (fun temp_0_ ->
          let _:u64 = temp_0_ in
          mk_i8 0)
  in
  let (m: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 16) i8 =
    Core_models.Abstractions.Simd.simd_lt (mk_u64 16)
      #i8
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_2__to_i8x16 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
      z
  in
  let r:u16 =
    (mk_u16 32768 *!
      (cast ((if (m.[ mk_u64 15 ] <: i8) <. mk_i8 0 <: bool then mk_i32 1 else mk_i32 0) <: i32)
        <:
        u16)
      <:
      u16) +!
    ((mk_u16 16384 *!
        (cast ((if (m.[ mk_u64 14 ] <: i8) <. mk_i8 0 <: bool then mk_i32 1 else mk_i32 0) <: i32)
          <:
          u16)
        <:
        u16) +!
      ((mk_u16 8192 *!
          (cast ((if (m.[ mk_u64 13 ] <: i8) <. mk_i8 0 <: bool then mk_i32 1 else mk_i32 0) <: i32)
            <:
            u16)
          <:
          u16) +!
        ((mk_u16 4096 *!
            (cast ((if (m.[ mk_u64 12 ] <: i8) <. mk_i8 0 <: bool then mk_i32 1 else mk_i32 0)
                  <:
                  i32)
              <:
              u16)
            <:
            u16) +!
          ((mk_u16 2048 *!
              (cast ((if (m.[ mk_u64 11 ] <: i8) <. mk_i8 0 <: bool then mk_i32 1 else mk_i32 0)
                    <:
                    i32)
                <:
                u16)
              <:
              u16) +!
            ((mk_u16 1024 *!
                (cast ((if (m.[ mk_u64 10 ] <: i8) <. mk_i8 0 <: bool then mk_i32 1 else mk_i32 0)
                      <:
                      i32)
                  <:
                  u16)
                <:
                u16) +!
              ((mk_u16 512 *!
                  (cast ((if (m.[ mk_u64 9 ] <: i8) <. mk_i8 0 <: bool then mk_i32 1 else mk_i32 0)
                        <:
                        i32)
                    <:
                    u16)
                  <:
                  u16) +!
                ((mk_u16 256 *!
                    (cast ((if (m.[ mk_u64 8 ] <: i8) <. mk_i8 0 <: bool then mk_i32 1 else mk_i32 0
                          )
                          <:
                          i32)
                      <:
                      u16)
                    <:
                    u16) +!
                  ((mk_u16 128 *!
                      (cast ((if (m.[ mk_u64 7 ] <: i8) <. mk_i8 0 <: bool
                              then mk_i32 1
                              else mk_i32 0)
                            <:
                            i32)
                        <:
                        u16)
                      <:
                      u16) +!
                    ((mk_u16 64 *!
                        (cast ((if (m.[ mk_u64 6 ] <: i8) <. mk_i8 0 <: bool
                                then mk_i32 1
                                else mk_i32 0)
                              <:
                              i32)
                          <:
                          u16)
                        <:
                        u16) +!
                      ((mk_u16 32 *!
                          (cast ((if (m.[ mk_u64 5 ] <: i8) <. mk_i8 0 <: bool
                                  then mk_i32 1
                                  else mk_i32 0)
                                <:
                                i32)
                            <:
                            u16)
                          <:
                          u16) +!
                        ((mk_u16 16 *!
                            (cast ((if (m.[ mk_u64 4 ] <: i8) <. mk_i8 0 <: bool
                                    then mk_i32 1
                                    else mk_i32 0)
                                  <:
                                  i32)
                              <:
                              u16)
                            <:
                            u16) +!
                          ((mk_u16 8 *!
                              (cast ((if (m.[ mk_u64 3 ] <: i8) <. mk_i8 0 <: bool
                                      then mk_i32 1
                                      else mk_i32 0)
                                    <:
                                    i32)
                                <:
                                u16)
                              <:
                              u16) +!
                            ((mk_u16 4 *!
                                (cast ((if (m.[ mk_u64 2 ] <: i8) <. mk_i8 0 <: bool
                                        then mk_i32 1
                                        else mk_i32 0)
                                      <:
                                      i32)
                                  <:
                                  u16)
                                <:
                                u16) +!
                              ((mk_u16 2 *!
                                  (cast ((if (m.[ mk_u64 1 ] <: i8) <. mk_i8 0 <: bool
                                          then mk_i32 1
                                          else mk_i32 0)
                                        <:
                                        i32)
                                    <:
                                    u16)
                                  <:
                                  u16) +!
                                (cast ((if (m.[ mk_u64 0 ] <: i8) <. mk_i8 0 <: bool
                                        then mk_i32 1
                                        else mk_i32 0)
                                      <:
                                      i32)
                                  <:
                                  u16)
                                <:
                                u16)
                              <:
                              u16)
                            <:
                            u16)
                          <:
                          u16)
                        <:
                        u16)
                      <:
                      u16)
                    <:
                    u16)
                  <:
                  u16)
                <:
                u16)
              <:
              u16)
            <:
            u16)
          <:
          u16)
        <:
        u16)
      <:
      u16)
  in
  cast (cast (r <: u16) <: u32) <: i32

let packsswb (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
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
