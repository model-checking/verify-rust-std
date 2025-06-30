module Core_models.Core_arch.X86.Avx
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Core_models.Abstractions.Bitvec in
  ()

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set1_epi64x)
assume
val e_mm256_set1_epi64x': i64 -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_set1_epi64x = e_mm256_set1_epi64x'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set_epi64x)
assume
val e_mm256_set_epi64x': i64 -> i64 -> i64 -> i64
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_set_epi64x = e_mm256_set_epi64x'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blendv_ps)
assume
val e_mm256_blendv_ps':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_blendv_ps = e_mm256_blendv_ps'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_castsi128_si256)
assume
val e_mm256_castsi128_si256': Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_castsi128_si256 = e_mm256_castsi128_si256'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_testz_si256)
assume
val e_mm256_testz_si256':
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> i32

unfold
let e_mm256_testz_si256 = e_mm256_testz_si256'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_castsi256_ps)
assume
val e_mm256_castsi256_ps': Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_castsi256_ps = e_mm256_castsi256_ps'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_castps_si256)
assume
val e_mm256_castps_si256': Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_castps_si256 = e_mm256_castps_si256'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_movemask_ps)
assume
val e_mm256_movemask_ps': Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) -> i32

unfold
let e_mm256_movemask_ps = e_mm256_movemask_ps'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_setzero_si256)
assume
val e_mm256_setzero_si256': Prims.unit -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_setzero_si256 = e_mm256_setzero_si256'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set_m128i)
assume
val e_mm256_set_m128i':
    hi: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    lo: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_set_m128i = e_mm256_set_m128i'

let e_mm256_castsi256_si128 (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 128)
    (fun i ->
        let i:u64 = i in
        vector.[ i ] <: Core_models.Abstractions.Bit.t_Bit)

/// This is opaque to Hax: it is defined only via the integer
/// interpretation. See `interpretations::int_vec::_mm256_set1_epi32`.
assume
val e_mm256_set1_epi32': i32 -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_set1_epi32 = e_mm256_set1_epi32'

/// This is opaque to Hax: we have lemmas about this intrinsics
/// composed with others. See e.g. `_rw_mm256_sllv_epi32`.
assume
val e_mm256_set_epi32':
    e_e0: i32 ->
    e_e1: i32 ->
    e_e2: i32 ->
    e_e3: i32 ->
    e_e4: i32 ->
    e_e5: i32 ->
    e_e6: i32 ->
    e_e7: i32
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_set_epi32 = e_mm256_set_epi32'

/// This is opaque to Hax: we have lemmas about this intrinsics
/// composed with others. See e.g. `_rw_mm256_mullo_epi16_shifts`.
assume
val e_mm256_set_epi16':
    e_e00: i16 ->
    e_e01: i16 ->
    e_e02: i16 ->
    e_e03: i16 ->
    e_e04: i16 ->
    e_e05: i16 ->
    e_e06: i16 ->
    e_e07: i16 ->
    e_e08: i16 ->
    e_e09: i16 ->
    e_e10: i16 ->
    e_e11: i16 ->
    e_e12: i16 ->
    e_e13: i16 ->
    e_e14: i16 ->
    e_e15: i16
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_set_epi16 = e_mm256_set_epi16'

/// This is opaque to Hax: we have lemmas about this intrinsics
/// composed with others. See e.g. `_rw_mm256_shuffle_epi8`.
assume
val e_mm256_set_epi8':
    e_e00: i8 ->
    e_e01: i8 ->
    e_e02: i8 ->
    e_e03: i8 ->
    e_e04: i8 ->
    e_e05: i8 ->
    e_e06: i8 ->
    e_e07: i8 ->
    e_e08: i8 ->
    e_e09: i8 ->
    e_e10: i8 ->
    e_e11: i8 ->
    e_e12: i8 ->
    e_e13: i8 ->
    e_e14: i8 ->
    e_e15: i8 ->
    e_e16: i8 ->
    e_e17: i8 ->
    e_e18: i8 ->
    e_e19: i8 ->
    e_e20: i8 ->
    e_e21: i8 ->
    e_e22: i8 ->
    e_e23: i8 ->
    e_e24: i8 ->
    e_e25: i8 ->
    e_e26: i8 ->
    e_e27: i8 ->
    e_e28: i8 ->
    e_e29: i8 ->
    e_e30: i8 ->
    e_e31: i8
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_set_epi8 = e_mm256_set_epi8'

/// [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set1_epi16)
assume
val e_mm256_set1_epi16': i16 -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_mm256_set1_epi16 = e_mm256_set1_epi16'
