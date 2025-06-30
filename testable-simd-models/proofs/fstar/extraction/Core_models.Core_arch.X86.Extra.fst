module Core_models.Core_arch.X86.Extra
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Core_models.Abstractions.Bitvec in
  let open Core_models.Abstractions.Funarr in
  ()

let mm256_sllv_epi32_u32_array
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (counts: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.impl_10__chunked_shift (mk_u64 256)
    (mk_u64 32)
    (mk_u64 8)
    vector
    (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
        #i128
        (fun i ->
            let i:u64 = i in
            cast (counts.[ i ] <: u32) <: i128)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i128)

let mm256_sllv_epi32_u32
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (b7 b6 b5 b4 b3 b2 b1 b0: u32)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  mm256_sllv_epi32_u32_array vector
    (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
        #u32
        (fun i ->
            let i:u64 = i in
            match i <: u64 with
            | Rust_primitives.Integers.MkInt 7 -> b7
            | Rust_primitives.Integers.MkInt 6 -> b6
            | Rust_primitives.Integers.MkInt 5 -> b5
            | Rust_primitives.Integers.MkInt 4 -> b4
            | Rust_primitives.Integers.MkInt 3 -> b3
            | Rust_primitives.Integers.MkInt 2 -> b2
            | Rust_primitives.Integers.MkInt 1 -> b1
            | Rust_primitives.Integers.MkInt 0 -> b0
            | _ ->
              Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

                  <:
                  Rust_primitives.Hax.t_Never)
              <:
              u32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)

let mm256_srlv_epi32_u32_array
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (counts: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.impl_10__chunked_shift (mk_u64 256)
    (mk_u64 32)
    (mk_u64 8)
    vector
    (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
        #i128
        (fun i ->
            let i:u64 = i in
            Core.Ops.Arith.f_neg (cast (counts.[ i ] <: u32) <: i128) <: i128)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i128)

let mm256_srlv_epi32_u32
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (b7 b6 b5 b4 b3 b2 b1 b0: u32)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  mm256_srlv_epi32_u32_array vector
    (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
        #u32
        (fun i ->
            let i:u64 = i in
            match i <: u64 with
            | Rust_primitives.Integers.MkInt 7 -> b7
            | Rust_primitives.Integers.MkInt 6 -> b6
            | Rust_primitives.Integers.MkInt 5 -> b5
            | Rust_primitives.Integers.MkInt 4 -> b4
            | Rust_primitives.Integers.MkInt 3 -> b3
            | Rust_primitives.Integers.MkInt 2 -> b2
            | Rust_primitives.Integers.MkInt 1 -> b1
            | Rust_primitives.Integers.MkInt 0 -> b0
            | _ ->
              Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

                  <:
                  Rust_primitives.Hax.t_Never)
              <:
              u32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)

let mm256_permutevar8x32_epi32_u32_array
      (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 256)
    (fun i ->
        let i:u64 = i in
        let j:u64 = i /! mk_u64 32 in
        let index:u64 = (cast ((b.[ j ] <: u32) %! mk_u32 8 <: u32) <: u64) *! mk_u64 32 in
        a.[ index +! (i %! mk_u64 32 <: u64) <: u64 ])

let mm256_permutevar8x32_epi32_u32
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (b7 b6 b5 b4 b3 b2 b1 b0: u32)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  mm256_permutevar8x32_epi32_u32_array vector
    (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
        #u32
        (fun i ->
            let i:u64 = i in
            match i <: u64 with
            | Rust_primitives.Integers.MkInt 7 -> b7
            | Rust_primitives.Integers.MkInt 6 -> b6
            | Rust_primitives.Integers.MkInt 5 -> b5
            | Rust_primitives.Integers.MkInt 4 -> b4
            | Rust_primitives.Integers.MkInt 3 -> b3
            | Rust_primitives.Integers.MkInt 2 -> b2
            | Rust_primitives.Integers.MkInt 1 -> b1
            | Rust_primitives.Integers.MkInt 0 -> b0
            | _ ->
              Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

                  <:
                  Rust_primitives.Hax.t_Never)
              <:
              u32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)

let mm_shuffle_epi8_u8_array
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
      (indexes: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 128)
    (fun i ->
        let i:u64 = i in
        let nth:u64 = i /! mk_u64 8 in
        let index:u8 = indexes.[ nth ] in
        if index >. mk_u8 127
        then Core_models.Abstractions.Bit.Bit_Zero <: Core_models.Abstractions.Bit.t_Bit
        else
          let index:u64 = cast (index %! mk_u8 16 <: u8) <: u64 in
          vector.[ (index *! mk_u64 8 <: u64) +! (i %! mk_u64 8 <: u64) <: u64 ])

let mm_shuffle_epi8_u8
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
      (b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0: u8)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let indexes:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
      #u8
      (fun i ->
          let i:u64 = i in
          match i <: u64 with
          | Rust_primitives.Integers.MkInt 15 -> b15
          | Rust_primitives.Integers.MkInt 14 -> b14
          | Rust_primitives.Integers.MkInt 13 -> b13
          | Rust_primitives.Integers.MkInt 12 -> b12
          | Rust_primitives.Integers.MkInt 11 -> b11
          | Rust_primitives.Integers.MkInt 10 -> b10
          | Rust_primitives.Integers.MkInt 9 -> b9
          | Rust_primitives.Integers.MkInt 8 -> b8
          | Rust_primitives.Integers.MkInt 7 -> b7
          | Rust_primitives.Integers.MkInt 6 -> b6
          | Rust_primitives.Integers.MkInt 5 -> b5
          | Rust_primitives.Integers.MkInt 4 -> b4
          | Rust_primitives.Integers.MkInt 3 -> b3
          | Rust_primitives.Integers.MkInt 2 -> b2
          | Rust_primitives.Integers.MkInt 1 -> b1
          | Rust_primitives.Integers.MkInt 0 -> b0
          | _ ->
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

                <:
                Rust_primitives.Hax.t_Never)
            <:
            u8)
  in
  mm_shuffle_epi8_u8_array vector indexes

let mm256_shuffle_epi8_i8_array
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (indexes: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 256)
    (fun i ->
        let i:u64 = i in
        let nth:u64 = i /! mk_u64 8 in
        let index:i8 = indexes.[ nth ] in
        if index <. mk_i8 0
        then Core_models.Abstractions.Bit.Bit_Zero <: Core_models.Abstractions.Bit.t_Bit
        else
          let index:u64 = cast (index %! mk_i8 16 <: i8) <: u64 in
          vector.[ ((if i <. mk_u64 128 <: bool then mk_u64 0 else mk_u64 128) +!
              (index *! mk_u64 8 <: u64)
              <:
              u64) +!
            (i %! mk_u64 8 <: u64)
            <:
            u64 ])

let mm256_shuffle_epi8_i8
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (byte31 byte30 byte29 byte28 byte27 byte26 byte25 byte24 byte23 byte22 byte21 byte20 byte19 byte18 byte17 byte16 byte15 byte14 byte13 byte12 byte11 byte10 byte9 byte8 byte7 byte6 byte5 byte4 byte3 byte2 byte1 byte0:
          i8)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let indexes:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 32)
      #i8
      (fun i ->
          let i:u64 = i in
          match i <: u64 with
          | Rust_primitives.Integers.MkInt 31 -> byte31
          | Rust_primitives.Integers.MkInt 30 -> byte30
          | Rust_primitives.Integers.MkInt 29 -> byte29
          | Rust_primitives.Integers.MkInt 28 -> byte28
          | Rust_primitives.Integers.MkInt 27 -> byte27
          | Rust_primitives.Integers.MkInt 26 -> byte26
          | Rust_primitives.Integers.MkInt 25 -> byte25
          | Rust_primitives.Integers.MkInt 24 -> byte24
          | Rust_primitives.Integers.MkInt 23 -> byte23
          | Rust_primitives.Integers.MkInt 22 -> byte22
          | Rust_primitives.Integers.MkInt 21 -> byte21
          | Rust_primitives.Integers.MkInt 20 -> byte20
          | Rust_primitives.Integers.MkInt 19 -> byte19
          | Rust_primitives.Integers.MkInt 18 -> byte18
          | Rust_primitives.Integers.MkInt 17 -> byte17
          | Rust_primitives.Integers.MkInt 16 -> byte16
          | Rust_primitives.Integers.MkInt 15 -> byte15
          | Rust_primitives.Integers.MkInt 14 -> byte14
          | Rust_primitives.Integers.MkInt 13 -> byte13
          | Rust_primitives.Integers.MkInt 12 -> byte12
          | Rust_primitives.Integers.MkInt 11 -> byte11
          | Rust_primitives.Integers.MkInt 10 -> byte10
          | Rust_primitives.Integers.MkInt 9 -> byte9
          | Rust_primitives.Integers.MkInt 8 -> byte8
          | Rust_primitives.Integers.MkInt 7 -> byte7
          | Rust_primitives.Integers.MkInt 6 -> byte6
          | Rust_primitives.Integers.MkInt 5 -> byte5
          | Rust_primitives.Integers.MkInt 4 -> byte4
          | Rust_primitives.Integers.MkInt 3 -> byte3
          | Rust_primitives.Integers.MkInt 2 -> byte2
          | Rust_primitives.Integers.MkInt 1 -> byte1
          | Rust_primitives.Integers.MkInt 0 -> byte0
          | _ ->
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

                <:
                Rust_primitives.Hax.t_Never)
            <:
            i8)
  in
  mm256_shuffle_epi8_i8_array vector indexes

let mm256_mullo_epi16_shifts_array
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (shifts: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 256)
    (fun i ->
        let i:u64 = i in
        let nth_bit:u64 = i %! mk_u64 16 in
        let nth_i16:u64 = i /! mk_u64 16 in
        let shift:u64 = cast (shifts.[ nth_i16 ] <: u8) <: u64 in
        if nth_bit >=. shift
        then vector.[ ((nth_i16 *! mk_u64 16 <: u64) +! nth_bit <: u64) -! shift <: u64 ]
        else Core_models.Abstractions.Bit.Bit_Zero <: Core_models.Abstractions.Bit.t_Bit)

let mm256_mullo_epi16_shifts
      (vector: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (s15 s14 s13 s12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0: u8)
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let shifts:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
      #u8
      (fun i ->
          let i:u64 = i in
          match i <: u64 with
          | Rust_primitives.Integers.MkInt 15 -> s15
          | Rust_primitives.Integers.MkInt 14 -> s14
          | Rust_primitives.Integers.MkInt 13 -> s13
          | Rust_primitives.Integers.MkInt 12 -> s12
          | Rust_primitives.Integers.MkInt 11 -> s11
          | Rust_primitives.Integers.MkInt 10 -> s10
          | Rust_primitives.Integers.MkInt 9 -> s9
          | Rust_primitives.Integers.MkInt 8 -> s8
          | Rust_primitives.Integers.MkInt 7 -> s7
          | Rust_primitives.Integers.MkInt 6 -> s6
          | Rust_primitives.Integers.MkInt 5 -> s5
          | Rust_primitives.Integers.MkInt 4 -> s4
          | Rust_primitives.Integers.MkInt 3 -> s3
          | Rust_primitives.Integers.MkInt 2 -> s2
          | Rust_primitives.Integers.MkInt 1 -> s1
          | Rust_primitives.Integers.MkInt 0 -> s0
          | _ ->
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

                <:
                Rust_primitives.Hax.t_Never)
            <:
            u8)
  in
  mm256_mullo_epi16_shifts_array vector shifts
