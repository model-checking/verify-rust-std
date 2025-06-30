module Core_models.Core_arch.X86.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Core_models.Abstractions.Bitvec in
  ()

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blend_epi32)
assume
val e_mm256_blend_epi32':
    v_IMM8: i32 ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_blend_epi32 (v_IMM8: i32) = e_mm256_blend_epi32' v_IMM8

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shuffle_epi32)
assume
val e_mm256_shuffle_epi32': v_MASK: i32 -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_shuffle_epi32 (v_MASK: i32) = e_mm256_shuffle_epi32' v_MASK

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi32)
assume
val e_mm256_sub_epi32':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_sub_epi32 = e_mm256_sub_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mul_epi32)
assume
val e_mm256_mul_epi32':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_mul_epi32 = e_mm256_mul_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi16)
assume
val e_mm256_add_epi16':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_add_epi16 = e_mm256_add_epi16'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_madd_epi16)
assume
val e_mm256_madd_epi16':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_madd_epi16 = e_mm256_madd_epi16'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi32)
assume
val e_mm256_add_epi32':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_add_epi32 = e_mm256_add_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi64)
assume
val e_mm256_add_epi64':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_add_epi64 = e_mm256_add_epi64'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_abs_epi32)
assume
val e_mm256_abs_epi32': Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_abs_epi32 = e_mm256_abs_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi16)
assume
val e_mm256_sub_epi16':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_sub_epi16 = e_mm256_sub_epi16'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi16)
assume
val e_mm256_cmpgt_epi16':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_cmpgt_epi16 = e_mm256_cmpgt_epi16'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi32)
assume
val e_mm256_cmpgt_epi32':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_cmpgt_epi32 = e_mm256_cmpgt_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpeq_epi32)
assume
val e_mm256_cmpeq_epi32':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_cmpeq_epi32 = e_mm256_cmpeq_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sign_epi32)
assume
val e_mm256_sign_epi32':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_sign_epi32 = e_mm256_sign_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mullo_epi32)
assume
val e_mm256_mullo_epi32':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_mullo_epi32 = e_mm256_mullo_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mulhi_epi16)
assume
val e_mm256_mulhi_epi16':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_mulhi_epi16 = e_mm256_mulhi_epi16'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mul_epu32)
assume
val e_mm256_mul_epu32':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_mul_epu32 = e_mm256_mul_epu32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_and_si256)
assume
val e_mm256_and_si256':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_and_si256 = e_mm256_and_si256'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_or_si256)
assume
val e_mm256_or_si256':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_or_si256 = e_mm256_or_si256'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_xor_si256)
assume
val e_mm256_xor_si256':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_xor_si256 = e_mm256_xor_si256'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srai_epi16)
assume
val e_mm256_srai_epi16': v_IMM8: i32 -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_srai_epi16 (v_IMM8: i32) = e_mm256_srai_epi16' v_IMM8

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srai_epi32)
assume
val e_mm256_srai_epi32': v_IMM8: i32 -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_srai_epi32 (v_IMM8: i32) = e_mm256_srai_epi32' v_IMM8

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi16)
assume
val e_mm256_srli_epi16': v_IMM8: i32 -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_srli_epi16 (v_IMM8: i32) = e_mm256_srli_epi16' v_IMM8

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi32)
assume
val e_mm256_srli_epi32': v_IMM8: i32 -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_srli_epi32 (v_IMM8: i32) = e_mm256_srli_epi32' v_IMM8

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi32)
assume
val e_mm256_slli_epi32': v_IMM8: i32 -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_slli_epi32 (v_IMM8: i32) = e_mm256_slli_epi32' v_IMM8

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permute4x64_epi64)
assume
val e_mm256_permute4x64_epi64': v_IMM8: i32 -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_permute4x64_epi64 (v_IMM8: i32) = e_mm256_permute4x64_epi64' v_IMM8

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi64)
assume
val e_mm256_unpackhi_epi64':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_unpackhi_epi64 = e_mm256_unpackhi_epi64'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi32)
assume
val e_mm256_unpacklo_epi32':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_unpacklo_epi32 = e_mm256_unpacklo_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi32)
assume
val e_mm256_unpackhi_epi32':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_unpackhi_epi32 = e_mm256_unpackhi_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi16_epi32)
assume
val e_mm256_cvtepi16_epi32': Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_cvtepi16_epi32 = e_mm256_cvtepi16_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_packs_epi32)
assume
val e_mm256_packs_epi32':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_packs_epi32 = e_mm256_packs_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_inserti128_si256)
assume
val e_mm256_inserti128_si256':
    v_IMM8: i32 ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_inserti128_si256 (v_IMM8: i32) = e_mm256_inserti128_si256' v_IMM8

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blend_epi16)
assume
val e_mm256_blend_epi16':
    v_IMM8: i32 ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_blend_epi16 (v_IMM8: i32) = e_mm256_blend_epi16' v_IMM8

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srlv_epi64)
assume
val e_mm256_srlv_epi64':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_srlv_epi64 = e_mm256_srlv_epi64'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sllv_epi32)
assume
val e_mm_sllv_epi32':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_sllv_epi32 = e_mm_sllv_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi64)
assume
val e_mm256_slli_epi64': v_IMM8: i32 -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_slli_epi64 (v_IMM8: i32) = e_mm256_slli_epi64' v_IMM8

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_bsrli_epi128)
/// NOTE: the bsrli here is different from intel specification. In the intel specification, if an IMM8 is given whose first 8 bits are higher than 15, it fixes it to 16.
/// However, the Rust implementation erroneously takes the input modulo 16. Thus, instead of shifting by 16 bits at an input of 16, it shifts by 0.
/// We are currently modelling the Rust implementation.
assume
val e_mm256_bsrli_epi128': v_IMM8: i32 -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_bsrli_epi128 (v_IMM8: i32) = e_mm256_bsrli_epi128' v_IMM8

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_andnot_si256)
assume
val e_mm256_andnot_si256':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_andnot_si256 = e_mm256_andnot_si256'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi64)
assume
val e_mm256_unpacklo_epi64':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_unpacklo_epi64 = e_mm256_unpacklo_epi64'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permute2x128_si256)
assume
val e_mm256_permute2x128_si256':
    v_IMM8: i32 ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_permute2x128_si256 (v_IMM8: i32) = e_mm256_permute2x128_si256' v_IMM8

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi16)
let e_mm256_slli_epi16
      (v_SHIFT_BY: i32)
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.impl_10__chunked_shift (mk_u64 256)
    (mk_u64 16)
    (mk_u64 16)
    vector
    (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
        #i128
        (fun temp_0_ ->
            let _:u64 = temp_0_ in
            cast (v_SHIFT_BY <: i32) <: i128)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i128)

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi64)
let e_mm256_srli_epi64
      (v_SHIFT_BY: i32)
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.impl_10__chunked_shift (mk_u64 256)
    (mk_u64 64)
    (mk_u64 4)
    vector
    (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
        #i128
        (fun temp_0_ ->
            let _:u64 = temp_0_ in
            Core.Ops.Arith.f_neg (cast (v_SHIFT_BY <: i32) <: i128) <: i128)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i128)

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mullo_epi16)
assume
val e_mm256_mullo_epi16':
    e_vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    e_shifts: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_mullo_epi16 = e_mm256_mullo_epi16'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sllv_epi32)
assume
val e_mm256_sllv_epi32':
    vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    counts: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_sllv_epi32 = e_mm256_sllv_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srlv_epi32)
assume
val e_mm256_srlv_epi32':
    vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    counts: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_srlv_epi32 = e_mm256_srlv_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permutevar8x32_epi32)
assume
val e_mm256_permutevar8x32_epi32':
    a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_permutevar8x32_epi32 = e_mm256_permutevar8x32_epi32'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_extracti128_si256)
let e_mm256_extracti128_si256
      (v_IMM8: i32)
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 128)
    (fun i ->
        let i:u64 = i in
        vector.[ i +! (if v_IMM8 =. mk_i32 0 <: bool then mk_u64 0 else mk_u64 128) <: u64 ]
        <:
        Core_models.Abstractions.Bit.t_Bit)

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shuffle_epi8)
assume
val e_mm256_shuffle_epi8':
    vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    indexes: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_shuffle_epi8 = e_mm256_shuffle_epi8'
