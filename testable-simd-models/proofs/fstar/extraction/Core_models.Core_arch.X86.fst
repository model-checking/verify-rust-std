module Core_models.Core_arch.X86
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

unfold type t_e_ee_m256i = Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
    unfold type t_e_ee_m128i = Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

/// Rewrite lemmas
let e_: Prims.unit = ()

[@@ Core_models.Abstractions.Bitvec.v_REWRITE_RULE ]

assume
val e___e_rw_mm256_sllv_epi32':
    vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b7: i32 ->
    b6: i32 ->
    b5: i32 ->
    b4: i32 ->
    b3: i32 ->
    b2: i32 ->
    b1: i32 ->
    b0: i32
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_sllv_epi32 vector
          (Core_models.Core_arch.X86.Avx.e_mm256_set_epi32 b7 b6 b5 b4 b3 b2 b1 b0
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Core_arch.X86.Extra.mm256_sllv_epi32_u32 vector
          (cast (b7 <: i32) <: u32)
          (cast (b6 <: i32) <: u32)
          (cast (b5 <: i32) <: u32)
          (cast (b4 <: i32) <: u32)
          (cast (b3 <: i32) <: u32)
          (cast (b2 <: i32) <: u32)
          (cast (b1 <: i32) <: u32)
          (cast (b0 <: i32) <: u32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e___e_rw_mm256_sllv_epi32 = e___e_rw_mm256_sllv_epi32'

[@@ Core_models.Abstractions.Bitvec.v_REWRITE_RULE ]

assume
val e___e_rw_mm256_srlv_epi32':
    vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b7: i32 ->
    b6: i32 ->
    b5: i32 ->
    b4: i32 ->
    b3: i32 ->
    b2: i32 ->
    b1: i32 ->
    b0: i32
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_srlv_epi32 vector
          (Core_models.Core_arch.X86.Avx.e_mm256_set_epi32 b7 b6 b5 b4 b3 b2 b1 b0
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Core_arch.X86.Extra.mm256_srlv_epi32_u32 vector
          (cast (b7 <: i32) <: u32)
          (cast (b6 <: i32) <: u32)
          (cast (b5 <: i32) <: u32)
          (cast (b4 <: i32) <: u32)
          (cast (b3 <: i32) <: u32)
          (cast (b2 <: i32) <: u32)
          (cast (b1 <: i32) <: u32)
          (cast (b0 <: i32) <: u32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e___e_rw_mm256_srlv_epi32 = e___e_rw_mm256_srlv_epi32'

[@@ Core_models.Abstractions.Bitvec.v_REWRITE_RULE ]

assume
val e___e_rw_mm256_permutevar8x32_epi32':
    vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    b7: i32 ->
    b6: i32 ->
    b5: i32 ->
    b4: i32 ->
    b3: i32 ->
    b2: i32 ->
    b1: i32 ->
    b0: i32
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_permutevar8x32_epi32 vector
          (Core_models.Core_arch.X86.Avx.e_mm256_set_epi32 b7 b6 b5 b4 b3 b2 b1 b0
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Core_arch.X86.Extra.mm256_permutevar8x32_epi32_u32 vector
          (cast (b7 <: i32) <: u32)
          (cast (b6 <: i32) <: u32)
          (cast (b5 <: i32) <: u32)
          (cast (b4 <: i32) <: u32)
          (cast (b3 <: i32) <: u32)
          (cast (b2 <: i32) <: u32)
          (cast (b1 <: i32) <: u32)
          (cast (b0 <: i32) <: u32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e___e_rw_mm256_permutevar8x32_epi32 = e___e_rw_mm256_permutevar8x32_epi32'

[@@ Core_models.Abstractions.Bitvec.v_REWRITE_RULE ]

assume
val e___e_rw_mm256_mullo_epi16_shifts':
    vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    s15: (n: u8 {v n < 16}) ->
    s14: (n: u8 {v n < 16}) ->
    s13: (n: u8 {v n < 16}) ->
    s12: (n: u8 {v n < 16}) ->
    s11: (n: u8 {v n < 16}) ->
    s10: (n: u8 {v n < 16}) ->
    s9: (n: u8 {v n < 16}) ->
    s8: (n: u8 {v n < 16}) ->
    s7: (n: u8 {v n < 16}) ->
    s6: (n: u8 {v n < 16}) ->
    s5: (n: u8 {v n < 16}) ->
    s4: (n: u8 {v n < 16}) ->
    s3: (n: u8 {v n < 16}) ->
    s2: (n: u8 {v n < 16}) ->
    s1: (n: u8 {v n < 16}) ->
    s0: (n: u8 {v n < 16})
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_mullo_epi16 vector
          (Core_models.Core_arch.X86.Avx.e_mm256_set_epi16 (mk_i16 1 <<! s15 <: i16)
              (mk_i16 1 <<! s14 <: i16) (mk_i16 1 <<! s13 <: i16) (mk_i16 1 <<! s12 <: i16)
              (mk_i16 1 <<! s11 <: i16) (mk_i16 1 <<! s10 <: i16) (mk_i16 1 <<! s9 <: i16)
              (mk_i16 1 <<! s8 <: i16) (mk_i16 1 <<! s7 <: i16) (mk_i16 1 <<! s6 <: i16)
              (mk_i16 1 <<! s5 <: i16) (mk_i16 1 <<! s4 <: i16) (mk_i16 1 <<! s3 <: i16)
              (mk_i16 1 <<! s2 <: i16) (mk_i16 1 <<! s1 <: i16) (mk_i16 1 <<! s0 <: i16)
            )
        ) ==
      (Core_models.Core_arch.X86.Extra.mm256_mullo_epi16_shifts vector s15 s14 s13 s12 s11 s10 s9 s8 s7
          s6 s5 s4 s3 s2 s1 s0))

let e___e_rw_mm256_mullo_epi16_shifts = e___e_rw_mm256_mullo_epi16_shifts'

[@@ Core_models.Abstractions.Bitvec.v_REWRITE_RULE ]

assume
val e___e_rw_mm_shuffle_epi8':
    vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    e15: i8 ->
    e14: i8 ->
    e13: i8 ->
    e12: i8 ->
    e11: i8 ->
    e10: i8 ->
    e9: i8 ->
    e8: i8 ->
    e7: i8 ->
    e6: i8 ->
    e5: i8 ->
    e4: i8 ->
    e3: i8 ->
    e2: i8 ->
    e1: i8 ->
    e0: i8
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Ssse3.e_mm_shuffle_epi8 vector
          (Core_models.Core_arch.X86.Sse2.e_mm_set_epi8 e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3
              e2 e1 e0
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      (Core_models.Core_arch.X86.Extra.mm_shuffle_epi8_u8 vector (cast (e15 <: i8) <: u8)
          (cast (e14 <: i8) <: u8) (cast (e13 <: i8) <: u8) (cast (e12 <: i8) <: u8)
          (cast (e11 <: i8) <: u8) (cast (e10 <: i8) <: u8) (cast (e9 <: i8) <: u8)
          (cast (e8 <: i8) <: u8) (cast (e7 <: i8) <: u8) (cast (e6 <: i8) <: u8)
          (cast (e5 <: i8) <: u8) (cast (e4 <: i8) <: u8) (cast (e3 <: i8) <: u8)
          (cast (e2 <: i8) <: u8) (cast (e1 <: i8) <: u8) (cast (e0 <: i8) <: u8)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)))

unfold
let e___e_rw_mm_shuffle_epi8 = e___e_rw_mm_shuffle_epi8'

[@@ Core_models.Abstractions.Bitvec.v_REWRITE_RULE ]

assume
val e___e_rw_mm256_shuffle_epi8':
    vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    byte31: i8 ->
    byte30: i8 ->
    byte29: i8 ->
    byte28: i8 ->
    byte27: i8 ->
    byte26: i8 ->
    byte25: i8 ->
    byte24: i8 ->
    byte23: i8 ->
    byte22: i8 ->
    byte21: i8 ->
    byte20: i8 ->
    byte19: i8 ->
    byte18: i8 ->
    byte17: i8 ->
    byte16: i8 ->
    byte15: i8 ->
    byte14: i8 ->
    byte13: i8 ->
    byte12: i8 ->
    byte11: i8 ->
    byte10: i8 ->
    byte9: i8 ->
    byte8: i8 ->
    byte7: i8 ->
    byte6: i8 ->
    byte5: i8 ->
    byte4: i8 ->
    byte3: i8 ->
    byte2: i8 ->
    byte1: i8 ->
    byte0: i8
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_shuffle_epi8 vector
          (Core_models.Core_arch.X86.Avx.e_mm256_set_epi8 byte31 byte30 byte29 byte28 byte27 byte26
              byte25 byte24 byte23 byte22 byte21 byte20 byte19 byte18 byte17 byte16 byte15 byte14
              byte13 byte12 byte11 byte10 byte9 byte8 byte7 byte6 byte5 byte4 byte3 byte2 byte1
              byte0
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core_models.Core_arch.X86.Extra.mm256_shuffle_epi8_i8 vector byte31 byte30 byte29 byte28
          byte27 byte26 byte25 byte24 byte23 byte22 byte21 byte20 byte19 byte18 byte17 byte16 byte15
          byte14 byte13 byte12 byte11 byte10 byte9 byte8 byte7 byte6 byte5 byte4 byte3 byte2 byte1
          byte0
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e___e_rw_mm256_shuffle_epi8 = e___e_rw_mm256_shuffle_epi8'
