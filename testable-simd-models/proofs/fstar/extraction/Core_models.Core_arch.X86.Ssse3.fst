module Core_models.Core_arch.X86.Ssse3
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

assume
val e_mm_shuffle_epi8':
    vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) ->
    indexes: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_mm_shuffle_epi8 = e_mm_shuffle_epi8'
