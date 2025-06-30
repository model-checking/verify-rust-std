module Core_models.Abstractions.Bitvec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Core_models.Abstractions.Bit in
  let open Core_models.Abstractions.Funarr in
  ()

noeq

/// A fixed-size bit vector type.
/// `BitVec<N>` is a specification-friendly, fixed-length bit vector that internally
/// stores an array of [`Bit`] values, where each `Bit` represents a single binary digit (0 or 1).
/// This type provides several utility methods for constructing and converting bit vectors:
/// The [`Debug`] implementation for `BitVec` pretty-prints the bits in groups of eight,
/// making the bit pattern more human-readable. The type also implements indexing,
/// allowing for easy access to individual bits.
type t_BitVec (v_N: u64) =
  | BitVec : Core_models.Abstractions.Funarr.t_FunArray v_N Core_models.Abstractions.Bit.t_Bit
    -> t_BitVec v_N

let impl_1 (v_N: u64) : Core.Clone.t_Clone (t_BitVec v_N) = { f_clone = (fun x -> x) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': v_N: u64 -> Core.Marker.t_Copy (t_BitVec v_N)

unfold
let impl (v_N: u64) = impl' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': v_N: u64 -> Core.Marker.t_StructuralPartialEq (t_BitVec v_N)

unfold
let impl_3 (v_N: u64) = impl_3' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': v_N: u64 -> Core.Cmp.t_PartialEq (t_BitVec v_N) (t_BitVec v_N)

unfold
let impl_4 (v_N: u64) = impl_4' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': v_N: u64 -> Core.Cmp.t_Eq (t_BitVec v_N)

unfold
let impl_2 (v_N: u64) = impl_2' v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6 (v_N: u64) : Core.Ops.Index.t_Index (t_BitVec v_N) u64 =
  {
    f_Output = Core_models.Abstractions.Bit.t_Bit;
    f_index_pre = (fun (self_: t_BitVec v_N) (index: u64) -> index <. v_N);
    f_index_post
    =
    (fun (self: t_BitVec v_N) (index: u64) (out: Core_models.Abstractions.Bit.t_Bit) -> true);
    f_index
    =
    fun (self: t_BitVec v_N) (index: u64) ->
      Core_models.Abstractions.Funarr.impl_5__get v_N
        #Core_models.Abstractions.Bit.t_Bit
        self._0
        index
  }

let impl_9__from_fn
    (v_N: u64)
    (f: (i: u64 {v i < v v_N}) -> Core_models.Abstractions.Bit.t_Bit)
    : t_BitVec v_N = 
    BitVec(Core_models.Abstractions.Funarr.impl_5__from_fn v_N f)

let impl_7__pointwise (self: t_BitVec (mk_u64 128)) : t_BitVec (mk_u64 128) =
  impl_9__from_fn (mk_u64 128)
    (fun i ->
        let i:u64 = i in
        match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 ->
          self.[ mk_u64 0 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 1 ->
          self.[ mk_u64 1 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 2 ->
          self.[ mk_u64 2 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 3 ->
          self.[ mk_u64 3 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 4 ->
          self.[ mk_u64 4 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 5 ->
          self.[ mk_u64 5 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 6 ->
          self.[ mk_u64 6 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 7 ->
          self.[ mk_u64 7 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 8 ->
          self.[ mk_u64 8 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 9 ->
          self.[ mk_u64 9 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 10 ->
          self.[ mk_u64 10 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 11 ->
          self.[ mk_u64 11 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 12 ->
          self.[ mk_u64 12 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 13 ->
          self.[ mk_u64 13 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 14 ->
          self.[ mk_u64 14 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 15 ->
          self.[ mk_u64 15 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 16 ->
          self.[ mk_u64 16 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 17 ->
          self.[ mk_u64 17 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 18 ->
          self.[ mk_u64 18 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 19 ->
          self.[ mk_u64 19 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 20 ->
          self.[ mk_u64 20 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 21 ->
          self.[ mk_u64 21 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 22 ->
          self.[ mk_u64 22 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 23 ->
          self.[ mk_u64 23 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 24 ->
          self.[ mk_u64 24 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 25 ->
          self.[ mk_u64 25 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 26 ->
          self.[ mk_u64 26 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 27 ->
          self.[ mk_u64 27 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 28 ->
          self.[ mk_u64 28 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 29 ->
          self.[ mk_u64 29 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 30 ->
          self.[ mk_u64 30 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 31 ->
          self.[ mk_u64 31 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 32 ->
          self.[ mk_u64 32 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 33 ->
          self.[ mk_u64 33 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 34 ->
          self.[ mk_u64 34 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 35 ->
          self.[ mk_u64 35 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 36 ->
          self.[ mk_u64 36 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 37 ->
          self.[ mk_u64 37 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 38 ->
          self.[ mk_u64 38 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 39 ->
          self.[ mk_u64 39 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 40 ->
          self.[ mk_u64 40 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 41 ->
          self.[ mk_u64 41 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 42 ->
          self.[ mk_u64 42 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 43 ->
          self.[ mk_u64 43 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 44 ->
          self.[ mk_u64 44 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 45 ->
          self.[ mk_u64 45 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 46 ->
          self.[ mk_u64 46 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 47 ->
          self.[ mk_u64 47 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 48 ->
          self.[ mk_u64 48 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 49 ->
          self.[ mk_u64 49 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 50 ->
          self.[ mk_u64 50 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 51 ->
          self.[ mk_u64 51 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 52 ->
          self.[ mk_u64 52 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 53 ->
          self.[ mk_u64 53 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 54 ->
          self.[ mk_u64 54 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 55 ->
          self.[ mk_u64 55 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 56 ->
          self.[ mk_u64 56 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 57 ->
          self.[ mk_u64 57 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 58 ->
          self.[ mk_u64 58 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 59 ->
          self.[ mk_u64 59 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 60 ->
          self.[ mk_u64 60 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 61 ->
          self.[ mk_u64 61 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 62 ->
          self.[ mk_u64 62 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 63 ->
          self.[ mk_u64 63 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 64 ->
          self.[ mk_u64 64 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 65 ->
          self.[ mk_u64 65 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 66 ->
          self.[ mk_u64 66 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 67 ->
          self.[ mk_u64 67 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 68 ->
          self.[ mk_u64 68 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 69 ->
          self.[ mk_u64 69 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 70 ->
          self.[ mk_u64 70 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 71 ->
          self.[ mk_u64 71 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 72 ->
          self.[ mk_u64 72 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 73 ->
          self.[ mk_u64 73 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 74 ->
          self.[ mk_u64 74 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 75 ->
          self.[ mk_u64 75 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 76 ->
          self.[ mk_u64 76 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 77 ->
          self.[ mk_u64 77 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 78 ->
          self.[ mk_u64 78 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 79 ->
          self.[ mk_u64 79 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 80 ->
          self.[ mk_u64 80 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 81 ->
          self.[ mk_u64 81 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 82 ->
          self.[ mk_u64 82 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 83 ->
          self.[ mk_u64 83 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 84 ->
          self.[ mk_u64 84 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 85 ->
          self.[ mk_u64 85 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 86 ->
          self.[ mk_u64 86 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 87 ->
          self.[ mk_u64 87 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 88 ->
          self.[ mk_u64 88 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 89 ->
          self.[ mk_u64 89 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 90 ->
          self.[ mk_u64 90 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 91 ->
          self.[ mk_u64 91 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 92 ->
          self.[ mk_u64 92 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 93 ->
          self.[ mk_u64 93 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 94 ->
          self.[ mk_u64 94 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 95 ->
          self.[ mk_u64 95 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 96 ->
          self.[ mk_u64 96 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 97 ->
          self.[ mk_u64 97 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 98 ->
          self.[ mk_u64 98 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 99 ->
          self.[ mk_u64 99 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 100 ->
          self.[ mk_u64 100 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 101 ->
          self.[ mk_u64 101 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 102 ->
          self.[ mk_u64 102 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 103 ->
          self.[ mk_u64 103 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 104 ->
          self.[ mk_u64 104 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 105 ->
          self.[ mk_u64 105 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 106 ->
          self.[ mk_u64 106 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 107 ->
          self.[ mk_u64 107 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 108 ->
          self.[ mk_u64 108 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 109 ->
          self.[ mk_u64 109 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 110 ->
          self.[ mk_u64 110 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 111 ->
          self.[ mk_u64 111 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 112 ->
          self.[ mk_u64 112 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 113 ->
          self.[ mk_u64 113 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 114 ->
          self.[ mk_u64 114 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 115 ->
          self.[ mk_u64 115 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 116 ->
          self.[ mk_u64 116 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 117 ->
          self.[ mk_u64 117 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 118 ->
          self.[ mk_u64 118 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 119 ->
          self.[ mk_u64 119 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 120 ->
          self.[ mk_u64 120 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 121 ->
          self.[ mk_u64 121 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 122 ->
          self.[ mk_u64 122 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 123 ->
          self.[ mk_u64 123 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 124 ->
          self.[ mk_u64 124 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 125 ->
          self.[ mk_u64 125 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 126 ->
          self.[ mk_u64 126 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 127 ->
          self.[ mk_u64 127 ] <: Core_models.Abstractions.Bit.t_Bit
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          Core_models.Abstractions.Bit.t_Bit)

let impl_8__pointwise (self: t_BitVec (mk_u64 256)) : t_BitVec (mk_u64 256) =
  impl_9__from_fn (mk_u64 256)
    (fun i ->
        let i:u64 = i in
        match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 ->
          self.[ mk_u64 0 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 1 ->
          self.[ mk_u64 1 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 2 ->
          self.[ mk_u64 2 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 3 ->
          self.[ mk_u64 3 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 4 ->
          self.[ mk_u64 4 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 5 ->
          self.[ mk_u64 5 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 6 ->
          self.[ mk_u64 6 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 7 ->
          self.[ mk_u64 7 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 8 ->
          self.[ mk_u64 8 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 9 ->
          self.[ mk_u64 9 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 10 ->
          self.[ mk_u64 10 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 11 ->
          self.[ mk_u64 11 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 12 ->
          self.[ mk_u64 12 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 13 ->
          self.[ mk_u64 13 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 14 ->
          self.[ mk_u64 14 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 15 ->
          self.[ mk_u64 15 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 16 ->
          self.[ mk_u64 16 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 17 ->
          self.[ mk_u64 17 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 18 ->
          self.[ mk_u64 18 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 19 ->
          self.[ mk_u64 19 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 20 ->
          self.[ mk_u64 20 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 21 ->
          self.[ mk_u64 21 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 22 ->
          self.[ mk_u64 22 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 23 ->
          self.[ mk_u64 23 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 24 ->
          self.[ mk_u64 24 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 25 ->
          self.[ mk_u64 25 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 26 ->
          self.[ mk_u64 26 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 27 ->
          self.[ mk_u64 27 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 28 ->
          self.[ mk_u64 28 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 29 ->
          self.[ mk_u64 29 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 30 ->
          self.[ mk_u64 30 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 31 ->
          self.[ mk_u64 31 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 32 ->
          self.[ mk_u64 32 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 33 ->
          self.[ mk_u64 33 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 34 ->
          self.[ mk_u64 34 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 35 ->
          self.[ mk_u64 35 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 36 ->
          self.[ mk_u64 36 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 37 ->
          self.[ mk_u64 37 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 38 ->
          self.[ mk_u64 38 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 39 ->
          self.[ mk_u64 39 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 40 ->
          self.[ mk_u64 40 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 41 ->
          self.[ mk_u64 41 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 42 ->
          self.[ mk_u64 42 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 43 ->
          self.[ mk_u64 43 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 44 ->
          self.[ mk_u64 44 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 45 ->
          self.[ mk_u64 45 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 46 ->
          self.[ mk_u64 46 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 47 ->
          self.[ mk_u64 47 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 48 ->
          self.[ mk_u64 48 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 49 ->
          self.[ mk_u64 49 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 50 ->
          self.[ mk_u64 50 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 51 ->
          self.[ mk_u64 51 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 52 ->
          self.[ mk_u64 52 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 53 ->
          self.[ mk_u64 53 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 54 ->
          self.[ mk_u64 54 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 55 ->
          self.[ mk_u64 55 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 56 ->
          self.[ mk_u64 56 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 57 ->
          self.[ mk_u64 57 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 58 ->
          self.[ mk_u64 58 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 59 ->
          self.[ mk_u64 59 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 60 ->
          self.[ mk_u64 60 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 61 ->
          self.[ mk_u64 61 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 62 ->
          self.[ mk_u64 62 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 63 ->
          self.[ mk_u64 63 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 64 ->
          self.[ mk_u64 64 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 65 ->
          self.[ mk_u64 65 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 66 ->
          self.[ mk_u64 66 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 67 ->
          self.[ mk_u64 67 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 68 ->
          self.[ mk_u64 68 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 69 ->
          self.[ mk_u64 69 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 70 ->
          self.[ mk_u64 70 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 71 ->
          self.[ mk_u64 71 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 72 ->
          self.[ mk_u64 72 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 73 ->
          self.[ mk_u64 73 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 74 ->
          self.[ mk_u64 74 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 75 ->
          self.[ mk_u64 75 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 76 ->
          self.[ mk_u64 76 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 77 ->
          self.[ mk_u64 77 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 78 ->
          self.[ mk_u64 78 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 79 ->
          self.[ mk_u64 79 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 80 ->
          self.[ mk_u64 80 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 81 ->
          self.[ mk_u64 81 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 82 ->
          self.[ mk_u64 82 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 83 ->
          self.[ mk_u64 83 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 84 ->
          self.[ mk_u64 84 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 85 ->
          self.[ mk_u64 85 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 86 ->
          self.[ mk_u64 86 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 87 ->
          self.[ mk_u64 87 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 88 ->
          self.[ mk_u64 88 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 89 ->
          self.[ mk_u64 89 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 90 ->
          self.[ mk_u64 90 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 91 ->
          self.[ mk_u64 91 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 92 ->
          self.[ mk_u64 92 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 93 ->
          self.[ mk_u64 93 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 94 ->
          self.[ mk_u64 94 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 95 ->
          self.[ mk_u64 95 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 96 ->
          self.[ mk_u64 96 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 97 ->
          self.[ mk_u64 97 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 98 ->
          self.[ mk_u64 98 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 99 ->
          self.[ mk_u64 99 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 100 ->
          self.[ mk_u64 100 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 101 ->
          self.[ mk_u64 101 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 102 ->
          self.[ mk_u64 102 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 103 ->
          self.[ mk_u64 103 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 104 ->
          self.[ mk_u64 104 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 105 ->
          self.[ mk_u64 105 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 106 ->
          self.[ mk_u64 106 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 107 ->
          self.[ mk_u64 107 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 108 ->
          self.[ mk_u64 108 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 109 ->
          self.[ mk_u64 109 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 110 ->
          self.[ mk_u64 110 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 111 ->
          self.[ mk_u64 111 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 112 ->
          self.[ mk_u64 112 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 113 ->
          self.[ mk_u64 113 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 114 ->
          self.[ mk_u64 114 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 115 ->
          self.[ mk_u64 115 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 116 ->
          self.[ mk_u64 116 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 117 ->
          self.[ mk_u64 117 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 118 ->
          self.[ mk_u64 118 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 119 ->
          self.[ mk_u64 119 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 120 ->
          self.[ mk_u64 120 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 121 ->
          self.[ mk_u64 121 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 122 ->
          self.[ mk_u64 122 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 123 ->
          self.[ mk_u64 123 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 124 ->
          self.[ mk_u64 124 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 125 ->
          self.[ mk_u64 125 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 126 ->
          self.[ mk_u64 126 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 127 ->
          self.[ mk_u64 127 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 128 ->
          self.[ mk_u64 128 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 129 ->
          self.[ mk_u64 129 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 130 ->
          self.[ mk_u64 130 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 131 ->
          self.[ mk_u64 131 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 132 ->
          self.[ mk_u64 132 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 133 ->
          self.[ mk_u64 133 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 134 ->
          self.[ mk_u64 134 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 135 ->
          self.[ mk_u64 135 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 136 ->
          self.[ mk_u64 136 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 137 ->
          self.[ mk_u64 137 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 138 ->
          self.[ mk_u64 138 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 139 ->
          self.[ mk_u64 139 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 140 ->
          self.[ mk_u64 140 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 141 ->
          self.[ mk_u64 141 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 142 ->
          self.[ mk_u64 142 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 143 ->
          self.[ mk_u64 143 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 144 ->
          self.[ mk_u64 144 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 145 ->
          self.[ mk_u64 145 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 146 ->
          self.[ mk_u64 146 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 147 ->
          self.[ mk_u64 147 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 148 ->
          self.[ mk_u64 148 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 149 ->
          self.[ mk_u64 149 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 150 ->
          self.[ mk_u64 150 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 151 ->
          self.[ mk_u64 151 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 152 ->
          self.[ mk_u64 152 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 153 ->
          self.[ mk_u64 153 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 154 ->
          self.[ mk_u64 154 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 155 ->
          self.[ mk_u64 155 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 156 ->
          self.[ mk_u64 156 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 157 ->
          self.[ mk_u64 157 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 158 ->
          self.[ mk_u64 158 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 159 ->
          self.[ mk_u64 159 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 160 ->
          self.[ mk_u64 160 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 161 ->
          self.[ mk_u64 161 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 162 ->
          self.[ mk_u64 162 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 163 ->
          self.[ mk_u64 163 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 164 ->
          self.[ mk_u64 164 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 165 ->
          self.[ mk_u64 165 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 166 ->
          self.[ mk_u64 166 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 167 ->
          self.[ mk_u64 167 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 168 ->
          self.[ mk_u64 168 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 169 ->
          self.[ mk_u64 169 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 170 ->
          self.[ mk_u64 170 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 171 ->
          self.[ mk_u64 171 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 172 ->
          self.[ mk_u64 172 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 173 ->
          self.[ mk_u64 173 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 174 ->
          self.[ mk_u64 174 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 175 ->
          self.[ mk_u64 175 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 176 ->
          self.[ mk_u64 176 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 177 ->
          self.[ mk_u64 177 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 178 ->
          self.[ mk_u64 178 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 179 ->
          self.[ mk_u64 179 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 180 ->
          self.[ mk_u64 180 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 181 ->
          self.[ mk_u64 181 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 182 ->
          self.[ mk_u64 182 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 183 ->
          self.[ mk_u64 183 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 184 ->
          self.[ mk_u64 184 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 185 ->
          self.[ mk_u64 185 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 186 ->
          self.[ mk_u64 186 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 187 ->
          self.[ mk_u64 187 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 188 ->
          self.[ mk_u64 188 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 189 ->
          self.[ mk_u64 189 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 190 ->
          self.[ mk_u64 190 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 191 ->
          self.[ mk_u64 191 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 192 ->
          self.[ mk_u64 192 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 193 ->
          self.[ mk_u64 193 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 194 ->
          self.[ mk_u64 194 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 195 ->
          self.[ mk_u64 195 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 196 ->
          self.[ mk_u64 196 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 197 ->
          self.[ mk_u64 197 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 198 ->
          self.[ mk_u64 198 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 199 ->
          self.[ mk_u64 199 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 200 ->
          self.[ mk_u64 200 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 201 ->
          self.[ mk_u64 201 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 202 ->
          self.[ mk_u64 202 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 203 ->
          self.[ mk_u64 203 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 204 ->
          self.[ mk_u64 204 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 205 ->
          self.[ mk_u64 205 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 206 ->
          self.[ mk_u64 206 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 207 ->
          self.[ mk_u64 207 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 208 ->
          self.[ mk_u64 208 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 209 ->
          self.[ mk_u64 209 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 210 ->
          self.[ mk_u64 210 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 211 ->
          self.[ mk_u64 211 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 212 ->
          self.[ mk_u64 212 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 213 ->
          self.[ mk_u64 213 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 214 ->
          self.[ mk_u64 214 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 215 ->
          self.[ mk_u64 215 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 216 ->
          self.[ mk_u64 216 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 217 ->
          self.[ mk_u64 217 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 218 ->
          self.[ mk_u64 218 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 219 ->
          self.[ mk_u64 219 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 220 ->
          self.[ mk_u64 220 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 221 ->
          self.[ mk_u64 221 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 222 ->
          self.[ mk_u64 222 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 223 ->
          self.[ mk_u64 223 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 224 ->
          self.[ mk_u64 224 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 225 ->
          self.[ mk_u64 225 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 226 ->
          self.[ mk_u64 226 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 227 ->
          self.[ mk_u64 227 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 228 ->
          self.[ mk_u64 228 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 229 ->
          self.[ mk_u64 229 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 230 ->
          self.[ mk_u64 230 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 231 ->
          self.[ mk_u64 231 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 232 ->
          self.[ mk_u64 232 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 233 ->
          self.[ mk_u64 233 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 234 ->
          self.[ mk_u64 234 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 235 ->
          self.[ mk_u64 235 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 236 ->
          self.[ mk_u64 236 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 237 ->
          self.[ mk_u64 237 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 238 ->
          self.[ mk_u64 238 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 239 ->
          self.[ mk_u64 239 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 240 ->
          self.[ mk_u64 240 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 241 ->
          self.[ mk_u64 241 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 242 ->
          self.[ mk_u64 242 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 243 ->
          self.[ mk_u64 243 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 244 ->
          self.[ mk_u64 244 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 245 ->
          self.[ mk_u64 245 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 246 ->
          self.[ mk_u64 246 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 247 ->
          self.[ mk_u64 247 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 248 ->
          self.[ mk_u64 248 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 249 ->
          self.[ mk_u64 249 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 250 ->
          self.[ mk_u64 250 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 251 ->
          self.[ mk_u64 251 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 252 ->
          self.[ mk_u64 252 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 253 ->
          self.[ mk_u64 253 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 254 ->
          self.[ mk_u64 254 ] <: Core_models.Abstractions.Bit.t_Bit
        | Rust_primitives.Integers.MkInt 255 ->
          self.[ mk_u64 255 ] <: Core_models.Abstractions.Bit.t_Bit
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          Core_models.Abstractions.Bit.t_Bit)

/// An F* attribute that indiquates a rewritting lemma should be applied
let v_REWRITE_RULE: Prims.unit = ()

open FStar.FunctionalExtensionality

let extensionality' (#a: Type) (#b: Type) (f g: FStar.FunctionalExtensionality.(a ^-> b))
  : Lemma (ensures (FStar.FunctionalExtensionality.feq f g <==> f == g))
  = ()

let mark_to_normalize #t (x: t): t = x

open FStar.Tactics.V2
#push-options "--z3rlimit 80 --admit_smt_queries true"
let bitvec_rewrite_lemma_128 (x: t_BitVec (mk_u64 128))
: Lemma (x == mark_to_normalize (impl_7__pointwise x)) =
    let a = x._0 in
    let b = (impl_7__pointwise x)._0 in
    assert_norm (FStar.FunctionalExtensionality.feq a b);
    extensionality' a b

let bitvec_rewrite_lemma_256 (x: t_BitVec (mk_u64 256))
: Lemma (x == mark_to_normalize (impl_8__pointwise x)) =
    let a = x._0 in
    let b = (impl_8__pointwise x)._0 in
    assert_norm (FStar.FunctionalExtensionality.feq a b);
    extensionality' a b
#pop-options

let bitvec_postprocess_norm_aux (): Tac unit = with_compat_pre_core 1 (fun () ->
    let debug_mode = ext_enabled "debug_bv_postprocess_rewrite" in
    let crate = match cur_module () with | crate::_ -> crate | _ -> fail "Empty module name" in
    // Remove indirections
    norm [primops; iota; delta_namespace [crate; "Libcrux_intrinsics"]; zeta_full];
    // Rewrite call chains
    let lemmas = FStar.List.Tot.map (fun f -> pack_ln (FStar.Stubs.Reflection.V2.Data.Tv_FVar f)) (lookup_attr (`v_REWRITE_RULE) (top_env ())) in
    l_to_r lemmas;
    /// Get rid of casts
    norm [primops; iota; delta_namespace ["Rust_primitives"; "Prims.pow2"]; zeta_full];
    if debug_mode then print ("[postprocess_rewrite_helper] lemmas = " ^ term_to_string (quote lemmas));

    l_to_r [`bitvec_rewrite_lemma_128; `bitvec_rewrite_lemma_256];

    let round _: Tac unit =
        if debug_mode then dump "[postprocess_rewrite_helper] Rewrote goal";
        // Normalize as much as possible
        norm [primops; iota; delta_namespace ["Core"; crate; "Core_models"; "Libcrux_intrinsics"; "FStar.FunctionalExtensionality"; "Rust_primitives"]; zeta_full];
        if debug_mode then print ("[postprocess_rewrite_helper] first norm done");
        // Compute the last bits
        // compute ();
        // if debug_mode then dump ("[postprocess_rewrite_helper] compute done");
        // Force full normalization
        norm [primops; iota; delta; unascribe; zeta_full];
        if debug_mode then dump "[postprocess_rewrite_helper] after full normalization";
        // Solves the goal `<normalized body> == ?u`
        trefl ()
    in

    ctrl_rewrite BottomUp (fun t ->
        let f, args = collect_app t in
        let matches = match inspect f with | Tv_UInst f _ | Tv_FVar f -> (inspect_fv f) = explode_qn (`%mark_to_normalize) | _ -> false in
        let has_two_args = match args with | [_; _] -> true | _ -> false in
        (matches && has_two_args, Continue)
    ) round;

    // Solves the goal `<normalized body> == ?u`
    trefl ()
)

let bitvec_postprocess_norm (): Tac unit =
    if lax_on ()
    then trefl () // don't bother rewritting the goal
    else bitvec_postprocess_norm_aux ()

/// Folds over the array, accumulating a result.
/// # Arguments
/// * `init` - The initial value of the accumulator.
/// * `f` - A function combining the accumulator and each element.
let impl_10__fold
      (v_N: u64)
      (#v_A: Type0)
      (self: t_BitVec v_N)
      (init: v_A)
      (f: (v_A -> Core_models.Abstractions.Bit.t_Bit -> v_A))
    : v_A =
  Core_models.Abstractions.Funarr.impl_5__fold v_N
    #Core_models.Abstractions.Bit.t_Bit
    #v_A
    self._0
    init
    f

#push-options "--z3rlimit 50 --split_queries always"

let impl_10__chunked_shift__chunked_shift
      (v_N v_CHUNK v_SHIFTS: u64)
      (bitvec: t_BitVec v_N)
      (shl: Core_models.Abstractions.Funarr.t_FunArray v_SHIFTS i128)
    : Prims.Pure (t_BitVec v_N)
      (requires
        v_CHUNK >. mk_u64 0 &&
        ((Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine v_SHIFTS <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) =
        (Rust_primitives.Hax.Int.from_machine v_N <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  impl_9__from_fn v_N
    (fun i ->
        let i:u64 = i in
        let nth_bit:u64 = i %! v_CHUNK in
        let nth_chunk:u64 = i /! v_CHUNK in
        let _:Prims.unit =
          Hax_lib.assert_prop (b2t
              ((Rust_primitives.Hax.Int.from_machine nth_chunk <: Hax_lib.Int.t_Int) <=
                ((Rust_primitives.Hax.Int.from_machine v_SHIFTS <: Hax_lib.Int.t_Int) -
                  (1 <: Hax_lib.Int.t_Int)
                  <:
                  Hax_lib.Int.t_Int)
                <:
                bool))
        in
        let _:Prims.unit = () in
        let _:Prims.unit =
          Hax_lib.assert_prop (b2t
              (((Rust_primitives.Hax.Int.from_machine nth_chunk <: Hax_lib.Int.t_Int) *
                  (Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int)
                  <:
                  Hax_lib.Int.t_Int) <=
                (((Rust_primitives.Hax.Int.from_machine v_SHIFTS <: Hax_lib.Int.t_Int) -
                    (1 <: Hax_lib.Int.t_Int)
                    <:
                    Hax_lib.Int.t_Int) *
                  (Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int)
                  <:
                  Hax_lib.Int.t_Int)
                <:
                bool))
        in
        let _:Prims.unit = () in
        let (shift: i128):i128 = if nth_chunk <. v_SHIFTS then shl.[ nth_chunk ] else mk_i128 0 in
        let local_index:i128 =
          Core.Num.impl_i128__wrapping_sub (cast (nth_bit <: u64) <: i128) shift
        in
        if local_index <. (cast (v_CHUNK <: u64) <: i128) && local_index >=. mk_i128 0
        then
          let local_index:u64 = cast (local_index <: i128) <: u64 in
          let _:Prims.unit =
            Hax_lib.assert_prop (b2t
                ((((Rust_primitives.Hax.Int.from_machine nth_chunk <: Hax_lib.Int.t_Int) *
                      (Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int)
                      <:
                      Hax_lib.Int.t_Int) +
                    (Rust_primitives.Hax.Int.from_machine local_index <: Hax_lib.Int.t_Int)
                    <:
                    Hax_lib.Int.t_Int) <
                  ((Rust_primitives.Hax.Int.from_machine v_SHIFTS <: Hax_lib.Int.t_Int) *
                    (Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int)
                    <:
                    Hax_lib.Int.t_Int)
                  <:
                  bool))
          in
          let _:Prims.unit = () in
          bitvec.[ (nth_chunk *! v_CHUNK <: u64) +! local_index <: u64 ]
        else Core_models.Abstractions.Bit.Bit_Zero <: Core_models.Abstractions.Bit.t_Bit)

#pop-options

let impl_10__chunked_shift
      (v_N v_CHUNK v_SHIFTS: u64)
      (self: t_BitVec v_N)
      (shl: Core_models.Abstractions.Funarr.t_FunArray v_SHIFTS i128)
    : Prims.Pure (t_BitVec v_N)
      (requires
        v_CHUNK >. mk_u64 0 &&
        ((Rust_primitives.Hax.Int.from_machine v_CHUNK <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine v_SHIFTS <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) =
        (Rust_primitives.Hax.Int.from_machine v_N <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = impl_10__chunked_shift__chunked_shift v_N v_CHUNK v_SHIFTS self shl
