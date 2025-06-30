module Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

irreducible

/// An F* attribute that marks an item as being an lifting lemma.
let v_ETA_MATCH_EXPAND: Prims.unit = () <: Prims.unit

[@@ v_ETA_MATCH_EXPAND ]

assume
val pointwise_i32x8': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32
  -> Lemma
    (ensures
      x ==
      (Core_models.Abstractions.Funarr.impl_7__pointwise #i32 x
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32))

unfold
let pointwise_i32x8 = pointwise_i32x8'

[@@ v_ETA_MATCH_EXPAND ]

assume
val pointwise_i64x4': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64
  -> Lemma
    (ensures
      x ==
      (Core_models.Abstractions.Funarr.impl_6__pointwise #i64 x
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64))

unfold
let pointwise_i64x4 = pointwise_i64x4'

irreducible

/// An F* attribute that marks an item as being an lifting lemma.
let v_LIFT_LEMMA: Prims.unit = () <: Prims.unit

[@@ v_LIFT_LEMMA ]
assume val _mm256_set_epi32_interp: e7: i32 -> e6: i32 -> e5: i32 -> e4: i32 -> e3: i32 -> e2: i32 -> e1: i32 -> e0: i32 -> (i: u64 {v i < 8})
  -> Lemma
        (
            (
                Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl__to_i32x8
                    (Core_models.Core_arch.X86.Avx.e_mm256_set_epi32 e7 e6 e5 e4 e3 e2 e1 e0)
            ).[ i ]
         == ( match i with
            | MkInt 0 -> e0 | MkInt 1 -> e1 | MkInt 2 -> e2 | MkInt 3 -> e3
            | MkInt 4 -> e4 | MkInt 5 -> e5 | MkInt 6 -> e6 | MkInt 7 -> e7 )
        )

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_set1_epi32': x: i32
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx.e_mm256_set1_epi32 x
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_set1_epi32
              x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_set1_epi32 = e_mm256_set1_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_mul_epi32':
    x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    y: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_mul_epi32 x y
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__from_i64x4 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_mul_epi32
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 x
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 y
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_mul_epi32 = e_mm256_mul_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_sub_epi32':
    x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    y: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_sub_epi32 x y
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_sub_epi32
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 x
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 y
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_sub_epi32 = e_mm256_sub_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_shuffle_epi32':
    v_CONTROL: i32 ->
    x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_shuffle_epi32 v_CONTROL x
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_shuffle_epi32
              v_CONTROL
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 x
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_shuffle_epi32 (v_CONTROL: i32) = e_mm256_shuffle_epi32' v_CONTROL

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_blend_epi32':
    v_CONTROL: i32 ->
    x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    y: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_blend_epi32 v_CONTROL x y
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_blend_epi32
              v_CONTROL
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 x
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 y
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_blend_epi32 (v_CONTROL: i32) = e_mm256_blend_epi32' v_CONTROL

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_set1_epi16': x: i16
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx.e_mm256_set1_epi16 x
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__from_i16x16 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_set1_epi16
              x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_set1_epi16 = e_mm256_set1_epi16'

[@@ v_LIFT_LEMMA ]

assume
val e_mm_set1_epi16': x: i16
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Sse2.e_mm_set1_epi16 x
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__from_i16x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm_set1_epi16
              x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)))

unfold
let e_mm_set1_epi16 = e_mm_set1_epi16'

[@@ v_LIFT_LEMMA ]

assume
val e_mm_set_epi32': e3: i32 -> e2: i32 -> e1: i32 -> e0: i32
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Sse2.e_mm_set_epi32 e3 e2 e1 e0
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__from_i32x4 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm_set_epi32
              e3
              e2
              e1
              e0
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)))

unfold
let e_mm_set_epi32 = e_mm_set_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm_add_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Sse2.e_mm_add_epi16 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__from_i16x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm_add_epi16
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)))

unfold
let e_mm_add_epi16 = e_mm_add_epi16'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_add_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_add_epi16 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__from_i16x16 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_add_epi16
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_add_epi16 = e_mm256_add_epi16'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_add_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_add_epi32 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_add_epi32
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_add_epi32 = e_mm256_add_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_add_epi64':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_add_epi64 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__from_i64x4 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_add_epi64
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_add_epi64 = e_mm256_add_epi64'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_abs_epi32': a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_abs_epi32 a
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_abs_epi32
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_abs_epi32 = e_mm256_abs_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_sub_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_sub_epi16 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__from_i16x16 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_sub_epi16
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_sub_epi16 = e_mm256_sub_epi16'

[@@ v_LIFT_LEMMA ]

assume
val e_mm_mullo_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Sse2.e_mm_mullo_epi16 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__from_i16x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm_mullo_epi16
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)))

unfold
let e_mm_mullo_epi16 = e_mm_mullo_epi16'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_cmpgt_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_cmpgt_epi16 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__from_i16x16 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_cmpgt_epi16
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_cmpgt_epi16 = e_mm256_cmpgt_epi16'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_cmpgt_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_cmpgt_epi32 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_cmpgt_epi32
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_cmpgt_epi32 = e_mm256_cmpgt_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_sign_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_sign_epi32 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_sign_epi32
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_sign_epi32 = e_mm256_sign_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_movemask_ps': a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx.e_mm256_movemask_ps a <: i32) ==
      (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_movemask_ps (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8
              a
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        i32))

unfold
let e_mm256_movemask_ps = e_mm256_movemask_ps'

[@@ v_LIFT_LEMMA ]

assume
val e_mm_mulhi_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Sse2.e_mm_mulhi_epi16 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__from_i16x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm_mulhi_epi16
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)))

unfold
let e_mm_mulhi_epi16 = e_mm_mulhi_epi16'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_mullo_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_mullo_epi32 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_mullo_epi32
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_mullo_epi32 = e_mm256_mullo_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_mulhi_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_mulhi_epi16 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__from_i16x16 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_mulhi_epi16
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_mulhi_epi16 = e_mm256_mulhi_epi16'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_mul_epu32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_mul_epu32 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_7__impl_2__from_u64x4 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_mul_epu32
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_6__impl_2__to_u32x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_6__impl_2__to_u32x8 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_mul_epu32 = e_mm256_mul_epu32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_srai_epi16': v_IMM8: i32 -> a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_srai_epi16 v_IMM8 a
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__from_i16x16 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_srai_epi16
              v_IMM8
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_srai_epi16 (v_IMM8: i32) = e_mm256_srai_epi16' v_IMM8

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_srai_epi32': v_IMM8: i32 -> a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_srai_epi32 v_IMM8 a
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_srai_epi32
              v_IMM8
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_srai_epi32 (v_IMM8: i32) = e_mm256_srai_epi32' v_IMM8

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_srli_epi16': v_IMM8: i32 -> a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_srli_epi16 v_IMM8 a
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__from_i16x16 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_srli_epi16
              v_IMM8
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_srli_epi16 (v_IMM8: i32) = e_mm256_srli_epi16' v_IMM8

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_srli_epi32': v_IMM8: i32 -> a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_srli_epi32 v_IMM8 a
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_srli_epi32
              v_IMM8
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_srli_epi32 (v_IMM8: i32) = e_mm256_srli_epi32' v_IMM8

[@@ v_LIFT_LEMMA ]

assume
val e_mm_srli_epi64': v_IMM8: i32 -> a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Sse2.e_mm_srli_epi64 v_IMM8 a
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_2__from_i64x2 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm_srli_epi64
              v_IMM8
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_2__to_i64x2 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)))

unfold
let e_mm_srli_epi64 (v_IMM8: i32) = e_mm_srli_epi64' v_IMM8

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_slli_epi32': v_IMM8: i32 -> a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_slli_epi32 v_IMM8 a
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_slli_epi32
              v_IMM8
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_slli_epi32 (v_IMM8: i32) = e_mm256_slli_epi32' v_IMM8

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_permute4x64_epi64':
    v_IMM8: i32 ->
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_permute4x64_epi64 v_IMM8 a
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__from_i64x4 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_permute4x64_epi64
              v_IMM8
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_permute4x64_epi64 (v_IMM8: i32) = e_mm256_permute4x64_epi64' v_IMM8

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_unpackhi_epi64':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_unpackhi_epi64 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__from_i64x4 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_unpackhi_epi64
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_unpackhi_epi64 = e_mm256_unpackhi_epi64'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_unpacklo_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_unpacklo_epi32 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_unpacklo_epi32
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_unpacklo_epi32 = e_mm256_unpacklo_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_unpackhi_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_unpackhi_epi32 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_unpackhi_epi32
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_unpackhi_epi32 = e_mm256_unpackhi_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_cvtepi16_epi32': a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_cvtepi16_epi32 a
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_cvtepi16_epi32
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_cvtepi16_epi32 = e_mm256_cvtepi16_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm_packs_epi16':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Sse2.e_mm_packs_epi16 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_2__from_i8x16 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm_packs_epi16
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)))

unfold
let e_mm_packs_epi16 = e_mm_packs_epi16'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_packs_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_packs_epi32 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__from_i16x16 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_packs_epi32
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_packs_epi32 = e_mm256_packs_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_inserti128_si256':
    v_IMM8: i32 ->
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_inserti128_si256 v_IMM8 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_4__impl_2__from_i128x2 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_inserti128_si256
              v_IMM8
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_4__impl_2__to_i128x2 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_13__impl_2__to_i128x1 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_inserti128_si256 (v_IMM8: i32) = e_mm256_inserti128_si256' v_IMM8

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_blend_epi16':
    v_IMM8: i32 ->
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_blend_epi16 v_IMM8 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__from_i16x16 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_blend_epi16
              v_IMM8
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_blend_epi16 (v_IMM8: i32) = e_mm256_blend_epi16' v_IMM8

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_blendv_ps':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    c: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx.e_mm256_blendv_ps a b c
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_blendv_ps
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 c
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_blendv_ps = e_mm256_blendv_ps'

[@@ v_LIFT_LEMMA ]

assume
val e_mm_movemask_epi8': a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Sse2.e_mm_movemask_epi8 a <: i32) ==
      (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm_movemask_epi8 (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_2__to_i8x16
              a
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
        <:
        i32))

unfold
let e_mm_movemask_epi8 = e_mm_movemask_epi8'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_srlv_epi64':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_srlv_epi64 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__from_i64x4 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_srlv_epi64
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_srlv_epi64 = e_mm256_srlv_epi64'

[@@ v_LIFT_LEMMA ]

assume
val e_mm_sllv_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm_sllv_epi32 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__from_i32x4 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm_sllv_epi32
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)))

unfold
let e_mm_sllv_epi32 = e_mm_sllv_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_slli_epi64': v_IMM8: i32 -> a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_slli_epi64 v_IMM8 a
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__from_i64x4 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_slli_epi64
              v_IMM8
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_slli_epi64 (v_IMM8: i32) = e_mm256_slli_epi64' v_IMM8

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_bsrli_epi128': v_IMM8: i32 -> a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_bsrli_epi128 v_IMM8 a
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_4__impl_2__from_i128x2 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_bsrli_epi128
              v_IMM8
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_4__impl_2__to_i128x2 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_bsrli_epi128 (v_IMM8: i32) = e_mm256_bsrli_epi128' v_IMM8

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_set1_epi64x': a: i64
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx.e_mm256_set1_epi64x a
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__from_i64x4 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_set1_epi64x
              a
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_set1_epi64x = e_mm256_set1_epi64x'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_set_epi64x': e3: i64 -> e2: i64 -> e1: i64 -> e0: i64
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx.e_mm256_set_epi64x e3 e2 e1 e0
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__from_i64x4 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_set_epi64x
              e3
              e2
              e1
              e0
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_set_epi64x = e_mm256_set_epi64x'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_unpacklo_epi64':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_unpacklo_epi64 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__from_i64x4 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_unpacklo_epi64
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_unpacklo_epi64 = e_mm256_unpacklo_epi64'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_permute2x128_si256':
    v_IMM8: i32 ->
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_permute2x128_si256 v_IMM8 a b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_4__impl_2__from_i128x2 (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_permute2x128_si256
              v_IMM8
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_4__impl_2__to_i128x2 a
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128)
              (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_4__impl_2__to_i128x2 b
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_permute2x128_si256 (v_IMM8: i32) = e_mm256_permute2x128_si256' v_IMM8

let flatten_circuit (): FStar.Tactics.Tac unit =
            let open Tactics.Circuits in
            flatten_circuit
                [
                    "Core_models";
                    "FStar.FunctionalExtensionality";
                    `%Rust_primitives.cast_tc; `%Rust_primitives.unsize_tc;
                    "Core.Ops"; `%(.[]);
                ]
                (top_levels_of_attr (` v_LIFT_LEMMA ))
                (top_levels_of_attr (` Core_models.Abstractions.Bitvec.Int_vec_interp.v_SIMPLIFICATION_LEMMA ))
                (top_levels_of_attr (` v_ETA_MATCH_EXPAND ))
