module Core_models.Neon.Generated
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Core_models.Abstractions.Bit in
  let open Core_models.Abstractions.Simd in
  ()

let vabd_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8 =
  Core_models.Abstractions.Simd.simd_abs_diff (mk_u64 8) #i8 a b

let vaba_s8 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 8)
    #i8
    a
    (vabd_s8 b c <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)

let vabdq_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
  Core_models.Abstractions.Simd.simd_abs_diff (mk_u64 16) #i8 a b

let vabaq_s8 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 16)
    #i8
    a
    (vabdq_s8 b c <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)

let vabd_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16 =
  Core_models.Abstractions.Simd.simd_abs_diff (mk_u64 4) #i16 a b

let vaba_s16 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 4)
    #i16
    a
    (vabd_s16 b c <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)

let vabdq_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  Core_models.Abstractions.Simd.simd_abs_diff (mk_u64 8) #i16 a b

let vabaq_s16 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 8)
    #i16
    a
    (vabdq_s16 b c <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)

let vabd_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32 =
  Core_models.Abstractions.Simd.simd_abs_diff (mk_u64 2) #i32 a b

let vaba_s32 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 2)
    #i32
    a
    (vabd_s32 b c <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)

let vabdq_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  Core_models.Abstractions.Simd.simd_abs_diff (mk_u64 4) #i32 a b

let vabaq_s32 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 4)
    #i32
    a
    (vabdq_s32 b c <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)

let vabd_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
  Core_models.Abstractions.Simd.simd_abs_diff (mk_u64 8) #u8 a b

let vaba_u8 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 8)
    #u8
    a
    (vabd_u8 b c <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)

let vabal_u8
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
      (b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  let (d: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) u8 =
    vabd_u8 b c
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 8)
    #u16
    a
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #u8 #u16 d
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)

let vabdq_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  Core_models.Abstractions.Simd.simd_abs_diff (mk_u64 16) #u8 a b

let vabaq_u8 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 16)
    #u8
    a
    (vabdq_u8 b c <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)

let vabd_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
  Core_models.Abstractions.Simd.simd_abs_diff (mk_u64 4) #u16 a b

let vaba_u16 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 4)
    #u16
    a
    (vabd_u16 b c <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)

let vabal_u16
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
      (b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  let (d: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) u16 =
    vabd_u16 b c
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 4)
    #u32
    a
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #u16 #u32 d
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)

let vabdq_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  Core_models.Abstractions.Simd.simd_abs_diff (mk_u64 8) #u16 a b

let vabaq_u16 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 8)
    #u16
    a
    (vabdq_u16 b c <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)

let vabd_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
  Core_models.Abstractions.Simd.simd_abs_diff (mk_u64 2) #u32 a b

let vaba_u32 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 2)
    #u32
    a
    (vabd_u32 b c <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)

let vabal_u32
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
      (b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64 =
  let (d: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) u32 =
    vabd_u32 b c
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 2)
    #u64
    a
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #u32 #u64 d
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)

let vabdq_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  Core_models.Abstractions.Simd.simd_abs_diff (mk_u64 4) #u32 a b

let vabaq_u32 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 4)
    #u32
    a
    (vabdq_u32 b c <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)

let vabdl_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
    #u8
    #u16
    (vabd_u8 a b <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)

let vabdl_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
    #u16
    #u32
    (vabd_u16 a b <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)

let vabdl_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 2)
    #u32
    #u64
    (vabd_u32 a b <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)

let vabs_s8 (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8 =
  Core_models.Abstractions.Simd.simd_abs (mk_u64 8) #i8 a

let vabsq_s8 (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
  Core_models.Abstractions.Simd.simd_abs (mk_u64 16) #i8 a

let vabs_s16 (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16 =
  Core_models.Abstractions.Simd.simd_abs (mk_u64 4) #i16 a

let vabsq_s16 (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  Core_models.Abstractions.Simd.simd_abs (mk_u64 8) #i16 a

let vabs_s32 (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32 =
  Core_models.Abstractions.Simd.simd_abs (mk_u64 2) #i32 a

let vabsq_s32 (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  Core_models.Abstractions.Simd.simd_abs (mk_u64 4) #i32 a

let vadd_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 4) #i16 a b

let vadd_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 2) #i32 a b

let vadd_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 8) #i8 a b

let vadd_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 4) #u16 a b

let vadd_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 2) #u32 a b

let vadd_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 8) #u8 a b

let vaddq_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 8) #i16 a b

let vaddq_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 4) #i32 a b

let vaddq_s64 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 2) #i64 a b

let vaddq_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 16) #i8 a b

let vaddq_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 8) #u16 a b

let vaddq_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 4) #u32 a b

let vaddq_u64 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 2) #u64 a b

let vaddq_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  Core_models.Abstractions.Simd.simd_add (mk_u64 16) #u8 a b

let vaddhn_high_s16
      (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
      (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
  let x:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
      #i16
      #i8
      (Core_models.Abstractions.Simd.simd_shr (mk_u64 8)
          #i16
          (Core_models.Abstractions.Simd.simd_add (mk_u64 8) #i16 a b
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_1__splat (mk_i16 8)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
  in
  Core_models.Abstractions.Simd.simd_shuffle #i8
    (mk_u64 8)
    (mk_usize 16)
    (mk_u64 16)
    r
    x
    (let list =
        [
          mk_u64 0; mk_u64 1; mk_u64 2; mk_u64 3; mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7; mk_u64 8;
          mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15
        ]
      in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
      Rust_primitives.Hax.array_of_list 16 list)

let vaddhn_high_s32
      (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
      (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  let x:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
      #i32
      #i16
      (Core_models.Abstractions.Simd.simd_shr (mk_u64 4)
          #i32
          (Core_models.Abstractions.Simd.simd_add (mk_u64 4) #i32 a b
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_1__splat (mk_i32 16)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
  in
  Core_models.Abstractions.Simd.simd_shuffle #i16
    (mk_u64 4)
    (mk_usize 8)
    (mk_u64 8)
    r
    x
    (let list = [mk_u64 0; mk_u64 1; mk_u64 2; mk_u64 3; mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
      Rust_primitives.Hax.array_of_list 8 list)

let vaddhn_high_s64
      (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
      (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  let x:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 2)
      #i64
      #i32
      (Core_models.Abstractions.Simd.simd_shr (mk_u64 2)
          #i64
          (Core_models.Abstractions.Simd.simd_add (mk_u64 2) #i64 a b
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_1__splat (mk_i64 32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
  in
  Core_models.Abstractions.Simd.simd_shuffle #i32
    (mk_u64 2)
    (mk_usize 4)
    (mk_u64 4)
    r
    x
    (let list = [mk_u64 0; mk_u64 1; mk_u64 2; mk_u64 3] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
      Rust_primitives.Hax.array_of_list 4 list)

let vaddhn_high_u16
      (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
      (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  let x:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
      #u16
      #u8
      (Core_models.Abstractions.Simd.simd_shr (mk_u64 8)
          #u16
          (Core_models.Abstractions.Simd.simd_add (mk_u64 8) #u16 a b
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_17__impl_1__splat (mk_u16 8)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
  in
  Core_models.Abstractions.Simd.simd_shuffle #u8
    (mk_u64 8)
    (mk_usize 16)
    (mk_u64 16)
    r
    x
    (let list =
        [
          mk_u64 0; mk_u64 1; mk_u64 2; mk_u64 3; mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7; mk_u64 8;
          mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15
        ]
      in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
      Rust_primitives.Hax.array_of_list 16 list)

let vaddhn_high_u32
      (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
      (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  let x:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
      #u32
      #u16
      (Core_models.Abstractions.Simd.simd_shr (mk_u64 4)
          #u32
          (Core_models.Abstractions.Simd.simd_add (mk_u64 4) #u32 a b
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_15__impl_1__splat (mk_u32 16)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
  in
  Core_models.Abstractions.Simd.simd_shuffle #u16
    (mk_u64 4)
    (mk_usize 8)
    (mk_u64 8)
    r
    x
    (let list = [mk_u64 0; mk_u64 1; mk_u64 2; mk_u64 3; mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
      Rust_primitives.Hax.array_of_list 8 list)

let vaddhn_high_u64
      (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
      (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  let x:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 2)
      #u64
      #u32
      (Core_models.Abstractions.Simd.simd_shr (mk_u64 2)
          #u64
          (Core_models.Abstractions.Simd.simd_add (mk_u64 2) #u64 a b
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_16__impl_1__splat (mk_u64 32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
  in
  Core_models.Abstractions.Simd.simd_shuffle #u32
    (mk_u64 2)
    (mk_usize 4)
    (mk_u64 4)
    r
    x
    (let list = [mk_u64 0; mk_u64 1; mk_u64 2; mk_u64 3] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
      Rust_primitives.Hax.array_of_list 4 list)

let vaddhn_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
    #i16
    #i8
    (Core_models.Abstractions.Simd.simd_shr (mk_u64 8)
        #i16
        (Core_models.Abstractions.Simd.simd_add (mk_u64 8) #i16 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_1__splat (mk_i16 8)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)

let vaddhn_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
    #i32
    #i16
    (Core_models.Abstractions.Simd.simd_shr (mk_u64 4)
        #i32
        (Core_models.Abstractions.Simd.simd_add (mk_u64 4) #i32 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_1__splat (mk_i32 16)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)

let vaddhn_s64 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 2)
    #i64
    #i32
    (Core_models.Abstractions.Simd.simd_shr (mk_u64 2)
        #i64
        (Core_models.Abstractions.Simd.simd_add (mk_u64 2) #i64 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_1__splat (mk_i64 32)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)

let vaddhn_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
    #u16
    #u8
    (Core_models.Abstractions.Simd.simd_shr (mk_u64 8)
        #u16
        (Core_models.Abstractions.Simd.simd_add (mk_u64 8) #u16 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_17__impl_1__splat (mk_u16 8)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)

let vaddhn_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
    #u32
    #u16
    (Core_models.Abstractions.Simd.simd_shr (mk_u64 4)
        #u32
        (Core_models.Abstractions.Simd.simd_add (mk_u64 4) #u32 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_15__impl_1__splat (mk_u32 16)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)

let vaddhn_u64 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 2)
    #u64
    #u32
    (Core_models.Abstractions.Simd.simd_shr (mk_u64 2)
        #u64
        (Core_models.Abstractions.Simd.simd_add (mk_u64 2) #u64 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_16__impl_1__splat (mk_u64 32)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)

let vaddl_high_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i16 =
    Core_models.Abstractions.Simd.simd_shuffle #i16
      (mk_u64 8)
      (mk_usize 4)
      (mk_u64 4)
      a
      a
      (let list = [mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i16 =
    Core_models.Abstractions.Simd.simd_shuffle #i16
      (mk_u64 8)
      (mk_usize 4)
      (mk_u64 4)
      b
      b
      (let list = [mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i16 #i32 a
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i16 #i32 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 4) #i32 a b

let vaddl_high_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) i32 =
    Core_models.Abstractions.Simd.simd_shuffle #i32
      (mk_u64 4)
      (mk_usize 2)
      (mk_u64 2)
      a
      a
      (let list = [mk_u64 2; mk_u64 3] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) i32 =
    Core_models.Abstractions.Simd.simd_shuffle #i32
      (mk_u64 4)
      (mk_usize 2)
      (mk_u64 2)
      b
      b
      (let list = [mk_u64 2; mk_u64 3] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
  in
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) i64 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #i32 #i64 a
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) i64 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #i32 #i64 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 2) #i64 a b

let vaddl_high_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) i8 =
    Core_models.Abstractions.Simd.simd_shuffle #i8
      (mk_u64 16)
      (mk_usize 8)
      (mk_u64 8)
      a
      a
      (let list =
          [mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
        Rust_primitives.Hax.array_of_list 8 list)
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) i8 =
    Core_models.Abstractions.Simd.simd_shuffle #i8
      (mk_u64 16)
      (mk_usize 8)
      (mk_u64 8)
      b
      b
      (let list =
          [mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
        Rust_primitives.Hax.array_of_list 8 list)
  in
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) i16 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i8 #i16 a
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) i16 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i8 #i16 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 8) #i16 a b

let vaddl_high_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) u16 =
    Core_models.Abstractions.Simd.simd_shuffle #u16
      (mk_u64 8)
      (mk_usize 4)
      (mk_u64 4)
      a
      a
      (let list = [mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) u16 =
    Core_models.Abstractions.Simd.simd_shuffle #u16
      (mk_u64 8)
      (mk_usize 4)
      (mk_u64 4)
      b
      b
      (let list = [mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) u32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #u16 #u32 a
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) u32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #u16 #u32 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 4) #u32 a b

let vaddl_high_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64 =
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) u32 =
    Core_models.Abstractions.Simd.simd_shuffle #u32
      (mk_u64 4)
      (mk_usize 2)
      (mk_u64 2)
      a
      a
      (let list = [mk_u64 2; mk_u64 3] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) u32 =
    Core_models.Abstractions.Simd.simd_shuffle #u32
      (mk_u64 4)
      (mk_usize 2)
      (mk_u64 2)
      b
      b
      (let list = [mk_u64 2; mk_u64 3] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
  in
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) u64 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #u32 #u64 a
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) u64 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #u32 #u64 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 2) #u64 a b

let vaddl_high_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) u8 =
    Core_models.Abstractions.Simd.simd_shuffle #u8
      (mk_u64 16)
      (mk_usize 8)
      (mk_u64 8)
      a
      a
      (let list =
          [mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
        Rust_primitives.Hax.array_of_list 8 list)
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) u8 =
    Core_models.Abstractions.Simd.simd_shuffle #u8
      (mk_u64 16)
      (mk_usize 8)
      (mk_u64 8)
      b
      b
      (let list =
          [mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
        Rust_primitives.Hax.array_of_list 8 list)
  in
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) u16 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #u8 #u16 a
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) u16 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #u8 #u16 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 8) #u16 a b

let vaddl_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i16 #i32 a
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i16 #i32 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 4) #i32 a b

let vaddl_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) i64 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #i32 #i64 a
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) i64 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #i32 #i64 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 2) #i64 a b

let vaddl_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) i16 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i8 #i16 a
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) i16 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i8 #i16 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 8) #i16 a b

let vaddl_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) u32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #u16 #u32 a
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) u32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #u16 #u32 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 4) #u32 a b

let vaddl_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64 =
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) u64 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #u32 #u64 a
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) u64 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #u32 #u64 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 2) #u64 a b

let vaddl_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  let (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) u16 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #u8 #u16 a
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) u16 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #u8 #u16 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 8) #u16 a b

let vaddw_high_s16
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
      (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i16 =
    Core_models.Abstractions.Simd.simd_shuffle #i16
      (mk_u64 8)
      (mk_usize 4)
      (mk_u64 4)
      b
      b
      (let list = [mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i16 #i32 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 4) #i32 a b

let vaddw_high_s32
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
      (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) i32 =
    Core_models.Abstractions.Simd.simd_shuffle #i32
      (mk_u64 4)
      (mk_usize 2)
      (mk_u64 2)
      b
      b
      (let list = [mk_u64 2; mk_u64 3] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) i64 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #i32 #i64 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 2) #i64 a b

let vaddw_high_s8
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
      (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) i8 =
    Core_models.Abstractions.Simd.simd_shuffle #i8
      (mk_u64 16)
      (mk_usize 8)
      (mk_u64 8)
      b
      b
      (let list =
          [mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
        Rust_primitives.Hax.array_of_list 8 list)
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) i16 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i8 #i16 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 8) #i16 a b

let vaddw_high_u16
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
      (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) u16 =
    Core_models.Abstractions.Simd.simd_shuffle #u16
      (mk_u64 8)
      (mk_usize 4)
      (mk_u64 4)
      b
      b
      (let list = [mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) u32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #u16 #u32 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 4) #u32 a b

let vaddw_high_u32
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
      (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64 =
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) u32 =
    Core_models.Abstractions.Simd.simd_shuffle #u32
      (mk_u64 4)
      (mk_usize 2)
      (mk_u64 2)
      b
      b
      (let list = [mk_u64 2; mk_u64 3] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) u64 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #u32 #u64 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 2) #u64 a b

let vaddw_high_u8
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
      (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) u8 =
    Core_models.Abstractions.Simd.simd_shuffle #u8
      (mk_u64 16)
      (mk_usize 8)
      (mk_u64 8)
      b
      b
      (let list =
          [mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
        Rust_primitives.Hax.array_of_list 8 list)
  in
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) u16 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #u8 #u16 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 8) #u16 a b

let vaddw_s16
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
      (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i16 #i32 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 4) #i32 a b

let vaddw_s32
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
      (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) i64 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #i32 #i64 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 2) #i64 a b

let vaddw_s8
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
      (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) i16 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i8 #i16 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 8) #i16 a b

let vaddw_u16
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
      (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) u32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #u16 #u32 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 4) #u32 a b

let vaddw_u32
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
      (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64 =
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) u64 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #u32 #u64 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 2) #u64 a b

let vaddw_u8
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
      (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  let (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) u16 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #u8 #u16 b
  in
  Core_models.Abstractions.Simd.simd_add (mk_u64 8) #u16 a b

let vand_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8 =
  Core_models.Abstractions.Simd.simd_and (mk_u64 8) #i8 a b

let vandq_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
  Core_models.Abstractions.Simd.simd_and (mk_u64 16) #i8 a b

let vand_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16 =
  Core_models.Abstractions.Simd.simd_and (mk_u64 4) #i16 a b

let vandq_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  Core_models.Abstractions.Simd.simd_and (mk_u64 8) #i16 a b

let vand_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32 =
  Core_models.Abstractions.Simd.simd_and (mk_u64 2) #i32 a b

let vandq_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  Core_models.Abstractions.Simd.simd_and (mk_u64 4) #i32 a b

let vand_s64 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64 =
  Core_models.Abstractions.Simd.simd_and (mk_u64 1) #i64 a b

let vandq_s64 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
  Core_models.Abstractions.Simd.simd_and (mk_u64 2) #i64 a b

let vand_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
  Core_models.Abstractions.Simd.simd_and (mk_u64 8) #u8 a b

let vandq_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  Core_models.Abstractions.Simd.simd_and (mk_u64 16) #u8 a b

let vand_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
  Core_models.Abstractions.Simd.simd_and (mk_u64 4) #u16 a b

let vandq_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  Core_models.Abstractions.Simd.simd_and (mk_u64 8) #u16 a b

let vand_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
  Core_models.Abstractions.Simd.simd_and (mk_u64 2) #u32 a b

let vandq_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  Core_models.Abstractions.Simd.simd_and (mk_u64 4) #u32 a b

let vand_u64 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64 =
  Core_models.Abstractions.Simd.simd_and (mk_u64 1) #u64 a b

let vandq_u64 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64 =
  Core_models.Abstractions.Simd.simd_and (mk_u64 2) #u64 a b

let vbic_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16 =
  let c:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_25__impl_1__splat (mk_i16 (-1))
  in
  Core_models.Abstractions.Simd.simd_and (mk_u64 4)
    #i16
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 4) #i16 b c
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
    a

let vbic_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32 =
  let c:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_24__impl_1__splat (mk_i32 (-1))
  in
  Core_models.Abstractions.Simd.simd_and (mk_u64 2)
    #i32
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 2) #i32 b c
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
    a

let vbic_s64 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64 =
  let c:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_23__impl_1__splat (mk_i64 (-1))
  in
  Core_models.Abstractions.Simd.simd_and (mk_u64 1)
    #i64
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 1) #i64 b c
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64)
    a

let vbic_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8 =
  let c:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_26__impl_1__splat (mk_i8 (-1))
  in
  Core_models.Abstractions.Simd.simd_and (mk_u64 8)
    #i8
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 8) #i8 b c
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
    a

let vbicq_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  let c:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_1__splat (mk_i16 (-1))
  in
  Core_models.Abstractions.Simd.simd_and (mk_u64 8)
    #i16
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 8) #i16 b c
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    a

let vbicq_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  let c:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_1__splat (mk_i32 (-1))
  in
  Core_models.Abstractions.Simd.simd_and (mk_u64 4)
    #i32
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 4) #i32 b c
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    a

let vbicq_s64 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
  let c:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_1__splat (mk_i64 (-1))
  in
  Core_models.Abstractions.Simd.simd_and (mk_u64 2)
    #i64
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 2) #i64 b c
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
    a

let vbicq_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
  let c:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_1__splat (mk_i8 (-1))
  in
  Core_models.Abstractions.Simd.simd_and (mk_u64 16)
    #i8
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 16) #i8 b c
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
    a

let vbic_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
  let c:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_25__impl_1__splat (mk_i16 (-1))
  in
  Core_models.Abstractions.Simd.simd_and (mk_u64 4)
    #u16
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 4)
        #u16
        b
        (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i16 #u16 c
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
    a

let vbic_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
  let c:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_24__impl_1__splat (mk_i32 (-1))
  in
  Core_models.Abstractions.Simd.simd_and (mk_u64 2)
    #u32
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 2)
        #u32
        b
        (Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #i32 #u32 c
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
    a

let vbic_u64 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64 =
  let c:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_23__impl_1__splat (mk_i64 (-1))
  in
  Core_models.Abstractions.Simd.simd_and (mk_u64 1)
    #u64
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 1)
        #u64
        b
        (Core_models.Abstractions.Simd.simd_cast (mk_u64 1) #i64 #u64 c
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
    a

let vbic_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
  let c:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_26__impl_1__splat (mk_i8 (-1))
  in
  Core_models.Abstractions.Simd.simd_and (mk_u64 8)
    #u8
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 8)
        #u8
        b
        (Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i8 #u8 c
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
    a

let vbicq_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  let c:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_1__splat (mk_i16 (-1))
  in
  Core_models.Abstractions.Simd.simd_and (mk_u64 8)
    #u16
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 8)
        #u16
        b
        (Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i16 #u16 c
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
    a

let vbicq_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  let c:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_1__splat (mk_i32 (-1))
  in
  Core_models.Abstractions.Simd.simd_and (mk_u64 4)
    #u32
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 4)
        #u32
        b
        (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i32 #u32 c
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
    a

let vbicq_u64 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64 =
  let c:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_1__splat (mk_i64 (-1))
  in
  Core_models.Abstractions.Simd.simd_and (mk_u64 2)
    #u64
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 2)
        #u64
        b
        (Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #i64 #u64 c
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
    a

let vbicq_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  let c:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_1__splat (mk_i8 (-1))
  in
  Core_models.Abstractions.Simd.simd_and (mk_u64 16)
    #u8
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 16)
        #u8
        b
        (Core_models.Abstractions.Simd.simd_cast (mk_u64 16) #i8 #u8 c
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    a

let vbsl_s16
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
      (b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16 =
  let not:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_25__impl_1__splat (mk_i16 (-1))
  in
  Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
    #u16
    #i16
    (Core_models.Abstractions.Simd.simd_or (mk_u64 4)
        #u16
        (Core_models.Abstractions.Simd.simd_and (mk_u64 4)
            #u16
            a
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i16 #u16 b
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
        (Core_models.Abstractions.Simd.simd_and (mk_u64 4)
            #u16
            (Core_models.Abstractions.Simd.simd_xor (mk_u64 4)
                #u16
                a
                (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i16 #u16 not
                  <:
                  Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i16 #u16 c
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)

let vbsl_s32
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
      (b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32 =
  let not:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_24__impl_1__splat (mk_i32 (-1))
  in
  Core_models.Abstractions.Simd.simd_cast (mk_u64 2)
    #u32
    #i32
    (Core_models.Abstractions.Simd.simd_or (mk_u64 2)
        #u32
        (Core_models.Abstractions.Simd.simd_and (mk_u64 2)
            #u32
            a
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #i32 #u32 b
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
        (Core_models.Abstractions.Simd.simd_and (mk_u64 2)
            #u32
            (Core_models.Abstractions.Simd.simd_xor (mk_u64 2)
                #u32
                a
                (Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #i32 #u32 not
                  <:
                  Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #i32 #u32 c
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)

let vbsl_s64
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
      (b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64 =
  let not:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_23__impl_1__splat (mk_i64 (-1))
  in
  Core_models.Abstractions.Simd.simd_cast (mk_u64 1)
    #u64
    #i64
    (Core_models.Abstractions.Simd.simd_or (mk_u64 1)
        #u64
        (Core_models.Abstractions.Simd.simd_and (mk_u64 1)
            #u64
            a
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 1) #i64 #u64 b
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
        (Core_models.Abstractions.Simd.simd_and (mk_u64 1)
            #u64
            (Core_models.Abstractions.Simd.simd_xor (mk_u64 1)
                #u64
                a
                (Core_models.Abstractions.Simd.simd_cast (mk_u64 1) #i64 #u64 not
                  <:
                  Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 1) #i64 #u64 c
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)

let vbsl_s8
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
      (b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8 =
  let not:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_26__impl_1__splat (mk_i8 (-1))
  in
  Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
    #u8
    #i8
    (Core_models.Abstractions.Simd.simd_or (mk_u64 8)
        #u8
        (Core_models.Abstractions.Simd.simd_and (mk_u64 8)
            #u8
            a
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i8 #u8 b
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
        (Core_models.Abstractions.Simd.simd_and (mk_u64 8)
            #u8
            (Core_models.Abstractions.Simd.simd_xor (mk_u64 8)
                #u8
                a
                (Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i8 #u8 not
                  <:
                  Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i8 #u8 c
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)

let vbslq_s16
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
      (b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  let not:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_1__splat (mk_i16 (-1))
  in
  Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
    #u16
    #i16
    (Core_models.Abstractions.Simd.simd_or (mk_u64 8)
        #u16
        (Core_models.Abstractions.Simd.simd_and (mk_u64 8)
            #u16
            a
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i16 #u16 b
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
        (Core_models.Abstractions.Simd.simd_and (mk_u64 8)
            #u16
            (Core_models.Abstractions.Simd.simd_xor (mk_u64 8)
                #u16
                a
                (Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i16 #u16 not
                  <:
                  Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i16 #u16 c
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)

let vbslq_s32
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
      (b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  let not:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_1__splat (mk_i32 (-1))
  in
  Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
    #u32
    #i32
    (Core_models.Abstractions.Simd.simd_or (mk_u64 4)
        #u32
        (Core_models.Abstractions.Simd.simd_and (mk_u64 4)
            #u32
            a
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i32 #u32 b
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
        (Core_models.Abstractions.Simd.simd_and (mk_u64 4)
            #u32
            (Core_models.Abstractions.Simd.simd_xor (mk_u64 4)
                #u32
                a
                (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i32 #u32 not
                  <:
                  Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i32 #u32 c
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)

let vbslq_s64
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
      (b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
  let not:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_1__splat (mk_i64 (-1))
  in
  Core_models.Abstractions.Simd.simd_cast (mk_u64 2)
    #u64
    #i64
    (Core_models.Abstractions.Simd.simd_or (mk_u64 2)
        #u64
        (Core_models.Abstractions.Simd.simd_and (mk_u64 2)
            #u64
            a
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #i64 #u64 b
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
        (Core_models.Abstractions.Simd.simd_and (mk_u64 2)
            #u64
            (Core_models.Abstractions.Simd.simd_xor (mk_u64 2)
                #u64
                a
                (Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #i64 #u64 not
                  <:
                  Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #i64 #u64 c
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)

let vbslq_s8
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
      (b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
  let not:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_1__splat (mk_i8 (-1))
  in
  Core_models.Abstractions.Simd.simd_cast (mk_u64 16)
    #u8
    #i8
    (Core_models.Abstractions.Simd.simd_or (mk_u64 16)
        #u8
        (Core_models.Abstractions.Simd.simd_and (mk_u64 16)
            #u8
            a
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 16) #i8 #u8 b
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
        (Core_models.Abstractions.Simd.simd_and (mk_u64 16)
            #u8
            (Core_models.Abstractions.Simd.simd_xor (mk_u64 16)
                #u8
                a
                (Core_models.Abstractions.Simd.simd_cast (mk_u64 16) #i8 #u8 not
                  <:
                  Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 16) #i8 #u8 c
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)

let vbsl_u16 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
  let not:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_25__impl_1__splat (mk_i16 (-1))
  in
  Core_models.Abstractions.Simd.simd_or (mk_u64 4)
    #u16
    (Core_models.Abstractions.Simd.simd_and (mk_u64 4)
        #u16
        a
        (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #u16 #u16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
    (Core_models.Abstractions.Simd.simd_and (mk_u64 4)
        #u16
        (Core_models.Abstractions.Simd.simd_xor (mk_u64 4)
            #u16
            a
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i16 #u16 not
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
        c
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)

let vbsl_u32 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
  let not:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_24__impl_1__splat (mk_i32 (-1))
  in
  Core_models.Abstractions.Simd.simd_or (mk_u64 2)
    #u32
    (Core_models.Abstractions.Simd.simd_and (mk_u64 2)
        #u32
        a
        (Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #u32 #u32 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
    (Core_models.Abstractions.Simd.simd_and (mk_u64 2)
        #u32
        (Core_models.Abstractions.Simd.simd_xor (mk_u64 2)
            #u32
            a
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #i32 #u32 not
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
        c
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)

let vbsl_u64 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64 =
  let not:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_23__impl_1__splat (mk_i64 (-1))
  in
  Core_models.Abstractions.Simd.simd_or (mk_u64 1)
    #u64
    (Core_models.Abstractions.Simd.simd_and (mk_u64 1)
        #u64
        a
        (Core_models.Abstractions.Simd.simd_cast (mk_u64 1) #u64 #u64 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
    (Core_models.Abstractions.Simd.simd_and (mk_u64 1)
        #u64
        (Core_models.Abstractions.Simd.simd_xor (mk_u64 1)
            #u64
            a
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 1) #i64 #u64 not
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
        c
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)

let vbsl_u8 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
  let not:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_26__impl_1__splat (mk_i8 (-1))
  in
  Core_models.Abstractions.Simd.simd_or (mk_u64 8)
    #u8
    (Core_models.Abstractions.Simd.simd_and (mk_u64 8)
        #u8
        a
        (Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #u8 #u8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
    (Core_models.Abstractions.Simd.simd_and (mk_u64 8)
        #u8
        (Core_models.Abstractions.Simd.simd_xor (mk_u64 8)
            #u8
            a
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i8 #u8 not
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
        c
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)

let vbslq_u16 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  let not:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_1__splat (mk_i16 (-1))
  in
  Core_models.Abstractions.Simd.simd_or (mk_u64 8)
    #u16
    (Core_models.Abstractions.Simd.simd_and (mk_u64 8)
        #u16
        a
        (Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #u16 #u16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
    (Core_models.Abstractions.Simd.simd_and (mk_u64 8)
        #u16
        (Core_models.Abstractions.Simd.simd_xor (mk_u64 8)
            #u16
            a
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i16 #u16 not
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
        c
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)

let vbslq_u32 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  let not:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_1__splat (mk_i32 (-1))
  in
  Core_models.Abstractions.Simd.simd_or (mk_u64 4)
    #u32
    (Core_models.Abstractions.Simd.simd_and (mk_u64 4)
        #u32
        a
        (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #u32 #u32 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
    (Core_models.Abstractions.Simd.simd_and (mk_u64 4)
        #u32
        (Core_models.Abstractions.Simd.simd_xor (mk_u64 4)
            #u32
            a
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i32 #u32 not
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
        c
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)

let vbslq_u64 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64 =
  let not:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_1__splat (mk_i64 (-1))
  in
  Core_models.Abstractions.Simd.simd_or (mk_u64 2)
    #u64
    (Core_models.Abstractions.Simd.simd_and (mk_u64 2)
        #u64
        a
        (Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #u64 #u64 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
    (Core_models.Abstractions.Simd.simd_and (mk_u64 2)
        #u64
        (Core_models.Abstractions.Simd.simd_xor (mk_u64 2)
            #u64
            a
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 2) #i64 #u64 not
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
        c
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)

let vbslq_u8 (a b c: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  let not:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_1__splat (mk_i8 (-1))
  in
  Core_models.Abstractions.Simd.simd_or (mk_u64 16)
    #u8
    (Core_models.Abstractions.Simd.simd_and (mk_u64 16)
        #u8
        a
        (Core_models.Abstractions.Simd.simd_cast (mk_u64 16) #u8 #u8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    (Core_models.Abstractions.Simd.simd_and (mk_u64 16)
        #u8
        (Core_models.Abstractions.Simd.simd_xor (mk_u64 16)
            #u8
            a
            (Core_models.Abstractions.Simd.simd_cast (mk_u64 16) #i8 #u8 not
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
        c
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)

let vceq_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
    #i8
    #u8
    (Core_models.Abstractions.Simd.simd_eq (mk_u64 8) #i8 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)

let vceqq_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 16)
    #i8
    #u8
    (Core_models.Abstractions.Simd.simd_eq (mk_u64 16) #i8 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)

let vceq_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
    #i16
    #u16
    (Core_models.Abstractions.Simd.simd_eq (mk_u64 4) #i16 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)

let vceqq_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
    #i16
    #u16
    (Core_models.Abstractions.Simd.simd_eq (mk_u64 8) #i16 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)

let vceq_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 2)
    #i32
    #u32
    (Core_models.Abstractions.Simd.simd_eq (mk_u64 2) #i32 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)

let vceqq_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
    #i32
    #u32
    (Core_models.Abstractions.Simd.simd_eq (mk_u64 4) #i32 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)

let vceq_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
  Core_models.Abstractions.Simd.simd_eq (mk_u64 8) #u8 a b

let vceqq_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  Core_models.Abstractions.Simd.simd_eq (mk_u64 16) #u8 a b

let vceq_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
  Core_models.Abstractions.Simd.simd_eq (mk_u64 4) #u16 a b

let vceqq_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  Core_models.Abstractions.Simd.simd_eq (mk_u64 8) #u16 a b

let vceq_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
  Core_models.Abstractions.Simd.simd_eq (mk_u64 2) #u32 a b

let vceqq_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  Core_models.Abstractions.Simd.simd_eq (mk_u64 4) #u32 a b

let vcge_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
    #i8
    #u8
    (Core_models.Abstractions.Simd.simd_ge (mk_u64 8) #i8 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)

let vcgeq_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 16)
    #i8
    #u8
    (Core_models.Abstractions.Simd.simd_ge (mk_u64 16) #i8 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)

let vcge_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
    #i16
    #u16
    (Core_models.Abstractions.Simd.simd_ge (mk_u64 4) #i16 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)

let vcgeq_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
    #i16
    #u16
    (Core_models.Abstractions.Simd.simd_ge (mk_u64 8) #i16 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)

let vcge_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 2)
    #i32
    #u32
    (Core_models.Abstractions.Simd.simd_ge (mk_u64 2) #i32 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)

let vcgeq_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
    #i32
    #u32
    (Core_models.Abstractions.Simd.simd_ge (mk_u64 4) #i32 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)

let vcge_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
  Core_models.Abstractions.Simd.simd_ge (mk_u64 8) #u8 a b

let vcgeq_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  Core_models.Abstractions.Simd.simd_ge (mk_u64 16) #u8 a b

let vcge_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
  Core_models.Abstractions.Simd.simd_ge (mk_u64 4) #u16 a b

let vcgeq_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  Core_models.Abstractions.Simd.simd_ge (mk_u64 8) #u16 a b

let vcge_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
  Core_models.Abstractions.Simd.simd_ge (mk_u64 2) #u32 a b

let vcgeq_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  Core_models.Abstractions.Simd.simd_ge (mk_u64 4) #u32 a b

let vcgt_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
    #i8
    #u8
    (Core_models.Abstractions.Simd.simd_gt (mk_u64 8) #i8 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)

let vcgtq_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 16)
    #i8
    #u8
    (Core_models.Abstractions.Simd.simd_gt (mk_u64 16) #i8 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)

let vcgt_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
    #i16
    #u16
    (Core_models.Abstractions.Simd.simd_gt (mk_u64 4) #i16 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)

let vcgtq_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
    #i16
    #u16
    (Core_models.Abstractions.Simd.simd_gt (mk_u64 8) #i16 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)

let vcgt_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 2)
    #i32
    #u32
    (Core_models.Abstractions.Simd.simd_gt (mk_u64 2) #i32 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)

let vcgtq_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
    #i32
    #u32
    (Core_models.Abstractions.Simd.simd_gt (mk_u64 4) #i32 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)

let vcgt_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
  Core_models.Abstractions.Simd.simd_gt (mk_u64 8) #u8 a b

let vcgtq_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  Core_models.Abstractions.Simd.simd_gt (mk_u64 16) #u8 a b

let vcgt_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
  Core_models.Abstractions.Simd.simd_gt (mk_u64 4) #u16 a b

let vcgtq_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  Core_models.Abstractions.Simd.simd_gt (mk_u64 8) #u16 a b

let vcgt_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
  Core_models.Abstractions.Simd.simd_gt (mk_u64 2) #u32 a b

let vcgtq_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  Core_models.Abstractions.Simd.simd_gt (mk_u64 4) #u32 a b

let vcle_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
    #i8
    #u8
    (Core_models.Abstractions.Simd.simd_le (mk_u64 8) #i8 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)

let vcleq_s8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 16)
    #i8
    #u8
    (Core_models.Abstractions.Simd.simd_le (mk_u64 16) #i8 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)

let vcle_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
    #i16
    #u16
    (Core_models.Abstractions.Simd.simd_le (mk_u64 4) #i16 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)

let vcleq_s16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
    #i16
    #u16
    (Core_models.Abstractions.Simd.simd_le (mk_u64 8) #i16 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)

let vcle_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 2)
    #i32
    #u32
    (Core_models.Abstractions.Simd.simd_le (mk_u64 2) #i32 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)

let vcleq_s32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
    #i32
    #u32
    (Core_models.Abstractions.Simd.simd_le (mk_u64 4) #i32 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)

let vcle_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
  Core_models.Abstractions.Simd.simd_le (mk_u64 8) #u8 a b

let vcleq_u8 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  Core_models.Abstractions.Simd.simd_le (mk_u64 16) #u8 a b

let vcle_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
  Core_models.Abstractions.Simd.simd_le (mk_u64 4) #u16 a b

let vcleq_u16 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  Core_models.Abstractions.Simd.simd_le (mk_u64 8) #u16 a b

let vcle_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
  Core_models.Abstractions.Simd.simd_le (mk_u64 2) #u32 a b

let vcleq_u32 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  Core_models.Abstractions.Simd.simd_le (mk_u64 4) #u32 a b
