module Core_models.Abstractions.Bitvec.Int_vec_interp
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

irreducible

/// An F* attribute that marks an item as being an interpretation lemma.
let v_SIMPLIFICATION_LEMMA: Prims.unit = () <: Prims.unit

let e_ee_1: Prims.unit = ()

///Conversion from i32 vectors of size 8to  bit vectors of size 256
assume
val e_ee_1__impl_2__from_i32x8': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_1__impl_2__from_i32x8 = e_ee_1__impl_2__from_i32x8'

///Conversion from bit vectors of size 256 to i32 vectors of size 8
assume
val e_ee_1__impl_2__to_i32x8': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32

unfold
let e_ee_1__impl_2__to_i32x8 = e_ee_1__impl_2__to_i32x8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_1__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) =
  {
    e_ee_1__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) -> true);
    e_ee_1__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        ->
        true);
    e_ee_1__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) ->
      e_ee_1__impl_2__from_i32x8 iv
  }

let e_ee_1__impl_1__splat (value: i32) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then i32x8 :: from is the identity.
assume
val e_ee_1__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32
  -> Lemma
    (ensures
      (e_ee_1__impl_2__to_i32x8 (e_ee_1__impl_2__from_i32x8 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) ==
      x)

unfold
let e_ee_1__lemma_cancel_iv = e_ee_1__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i32x8 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_1__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_1__impl_2__from_i32x8 (e_ee_1__impl_2__to_i32x8 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_1__lemma_cancel_bv = e_ee_1__lemma_cancel_bv'

let e_ee_2: Prims.unit = ()

///Conversion from i64 vectors of size 4to  bit vectors of size 256
assume
val e_ee_2__impl_2__from_i64x4': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_2__impl_2__from_i64x4 = e_ee_2__impl_2__from_i64x4'

///Conversion from bit vectors of size 256 to i64 vectors of size 4
assume
val e_ee_2__impl_2__to_i64x4': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64

unfold
let e_ee_2__impl_2__to_i64x4 = e_ee_2__impl_2__to_i64x4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_2__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) =
  {
    e_ee_2__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) -> true);
    e_ee_2__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        ->
        true);
    e_ee_2__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) ->
      e_ee_2__impl_2__from_i64x4 iv
  }

let e_ee_2__impl_1__splat (value: i64) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then i64x4 :: from is the identity.
assume
val e_ee_2__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64
  -> Lemma
    (ensures
      (e_ee_2__impl_2__to_i64x4 (e_ee_2__impl_2__from_i64x4 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) ==
      x)

unfold
let e_ee_2__lemma_cancel_iv = e_ee_2__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i64x4 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_2__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_2__impl_2__from_i64x4 (e_ee_2__impl_2__to_i64x4 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_2__lemma_cancel_bv = e_ee_2__lemma_cancel_bv'

let e_ee_3: Prims.unit = ()

///Conversion from i16 vectors of size 16to  bit vectors of size 256
assume
val e_ee_3__impl_2__from_i16x16': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_3__impl_2__from_i16x16 = e_ee_3__impl_2__from_i16x16'

///Conversion from bit vectors of size 256 to i16 vectors of size 16
assume
val e_ee_3__impl_2__to_i16x16': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16

unfold
let e_ee_3__impl_2__to_i16x16 = e_ee_3__impl_2__to_i16x16'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_3__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16) =
  {
    e_ee_3__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16) -> true);
    e_ee_3__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        ->
        true);
    e_ee_3__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16) ->
      e_ee_3__impl_2__from_i16x16 iv
  }

let e_ee_3__impl_1__splat (value: i16) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then i16x16 :: from is the identity.
assume
val e_ee_3__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16
  -> Lemma
    (ensures
      (e_ee_3__impl_2__to_i16x16 (e_ee_3__impl_2__from_i16x16 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16) ==
      x)

unfold
let e_ee_3__lemma_cancel_iv = e_ee_3__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i16x16 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_3__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_3__impl_2__from_i16x16 (e_ee_3__impl_2__to_i16x16 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_3__lemma_cancel_bv = e_ee_3__lemma_cancel_bv'

let e_ee_4: Prims.unit = ()

///Conversion from i128 vectors of size 2to  bit vectors of size 256
assume
val e_ee_4__impl_2__from_i128x2': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_4__impl_2__from_i128x2 = e_ee_4__impl_2__from_i128x2'

///Conversion from bit vectors of size 256 to i128 vectors of size 2
assume
val e_ee_4__impl_2__to_i128x2': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128

unfold
let e_ee_4__impl_2__to_i128x2 = e_ee_4__impl_2__to_i128x2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_4__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128) =
  {
    e_ee_4__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128) -> true);
    e_ee_4__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        ->
        true);
    e_ee_4__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128) ->
      e_ee_4__impl_2__from_i128x2 iv
  }

let e_ee_4__impl_1__splat (value: i128) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
    #i128
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then i128x2 :: from is the identity.
assume
val e_ee_4__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128
  -> Lemma
    (ensures
      (e_ee_4__impl_2__to_i128x2 (e_ee_4__impl_2__from_i128x2 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128) ==
      x)

unfold
let e_ee_4__lemma_cancel_iv = e_ee_4__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i128x2 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_4__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_4__impl_2__from_i128x2 (e_ee_4__impl_2__to_i128x2 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_4__lemma_cancel_bv = e_ee_4__lemma_cancel_bv'

let e_ee_5: Prims.unit = ()

///Conversion from i8 vectors of size 32to  bit vectors of size 256
assume
val e_ee_5__impl_2__from_i8x32': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_5__impl_2__from_i8x32 = e_ee_5__impl_2__from_i8x32'

///Conversion from bit vectors of size 256 to i8 vectors of size 32
assume
val e_ee_5__impl_2__to_i8x32': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8

unfold
let e_ee_5__impl_2__to_i8x32 = e_ee_5__impl_2__to_i8x32'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_5__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8) =
  {
    e_ee_5__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8) -> true);
    e_ee_5__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        ->
        true);
    e_ee_5__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8) ->
      e_ee_5__impl_2__from_i8x32 iv
  }

let e_ee_5__impl_1__splat (value: i8) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 32)
    #i8
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then i8x32 :: from is the identity.
assume
val e_ee_5__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8
  -> Lemma
    (ensures
      (e_ee_5__impl_2__to_i8x32 (e_ee_5__impl_2__from_i8x32 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8) ==
      x)

unfold
let e_ee_5__lemma_cancel_iv = e_ee_5__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i8x32 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_5__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_5__impl_2__from_i8x32 (e_ee_5__impl_2__to_i8x32 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_5__lemma_cancel_bv = e_ee_5__lemma_cancel_bv'

let e_ee_6: Prims.unit = ()

///Conversion from u32 vectors of size 8to  bit vectors of size 256
assume
val e_ee_6__impl_2__from_u32x8': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_6__impl_2__from_u32x8 = e_ee_6__impl_2__from_u32x8'

///Conversion from bit vectors of size 256 to u32 vectors of size 8
assume
val e_ee_6__impl_2__to_u32x8': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32

unfold
let e_ee_6__impl_2__to_u32x8 = e_ee_6__impl_2__to_u32x8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_6__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32) =
  {
    e_ee_6__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32) -> true);
    e_ee_6__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        ->
        true);
    e_ee_6__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32) ->
      e_ee_6__impl_2__from_u32x8 iv
  }

let e_ee_6__impl_1__splat (value: u32) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #u32
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then u32x8 :: from is the identity.
assume
val e_ee_6__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32
  -> Lemma
    (ensures
      (e_ee_6__impl_2__to_u32x8 (e_ee_6__impl_2__from_u32x8 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32) ==
      x)

unfold
let e_ee_6__lemma_cancel_iv = e_ee_6__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u32x8 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_6__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_6__impl_2__from_u32x8 (e_ee_6__impl_2__to_u32x8 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_6__lemma_cancel_bv = e_ee_6__lemma_cancel_bv'

let e_ee_7: Prims.unit = ()

///Conversion from u64 vectors of size 4to  bit vectors of size 256
assume
val e_ee_7__impl_2__from_u64x4': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_7__impl_2__from_u64x4 = e_ee_7__impl_2__from_u64x4'

///Conversion from bit vectors of size 256 to u64 vectors of size 4
assume
val e_ee_7__impl_2__to_u64x4': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64

unfold
let e_ee_7__impl_2__to_u64x4 = e_ee_7__impl_2__to_u64x4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_7__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64) =
  {
    e_ee_7__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64) -> true);
    e_ee_7__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        ->
        true);
    e_ee_7__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64) ->
      e_ee_7__impl_2__from_u64x4 iv
  }

let e_ee_7__impl_1__splat (value: u64) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #u64
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then u64x4 :: from is the identity.
assume
val e_ee_7__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64
  -> Lemma
    (ensures
      (e_ee_7__impl_2__to_u64x4 (e_ee_7__impl_2__from_u64x4 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64) ==
      x)

unfold
let e_ee_7__lemma_cancel_iv = e_ee_7__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u64x4 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_7__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_7__impl_2__from_u64x4 (e_ee_7__impl_2__to_u64x4 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_7__lemma_cancel_bv = e_ee_7__lemma_cancel_bv'

let e_ee_8: Prims.unit = ()

///Conversion from u16 vectors of size 16to  bit vectors of size 256
assume
val e_ee_8__impl_2__from_u16x16': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_8__impl_2__from_u16x16 = e_ee_8__impl_2__from_u16x16'

///Conversion from bit vectors of size 256 to u16 vectors of size 16
assume
val e_ee_8__impl_2__to_u16x16': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16

unfold
let e_ee_8__impl_2__to_u16x16 = e_ee_8__impl_2__to_u16x16'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_8__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16) =
  {
    e_ee_8__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16) -> true);
    e_ee_8__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        ->
        true);
    e_ee_8__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16) ->
      e_ee_8__impl_2__from_u16x16 iv
  }

let e_ee_8__impl_1__splat (value: u16) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #u16
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then u16x16 :: from is the identity.
assume
val e_ee_8__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16
  -> Lemma
    (ensures
      (e_ee_8__impl_2__to_u16x16 (e_ee_8__impl_2__from_u16x16 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16) ==
      x)

unfold
let e_ee_8__lemma_cancel_iv = e_ee_8__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u16x16 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_8__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_8__impl_2__from_u16x16 (e_ee_8__impl_2__to_u16x16 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_8__lemma_cancel_bv = e_ee_8__lemma_cancel_bv'

let e_ee_9: Prims.unit = ()

///Conversion from u8 vectors of size 32to  bit vectors of size 256
assume
val e_ee_9__impl_2__from_u8x32': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)

unfold
let e_ee_9__impl_2__from_u8x32 = e_ee_9__impl_2__from_u8x32'

///Conversion from bit vectors of size 256 to u8 vectors of size 32
assume
val e_ee_9__impl_2__to_u8x32': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8

unfold
let e_ee_9__impl_2__to_u8x32 = e_ee_9__impl_2__to_u8x32'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_9__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8) =
  {
    e_ee_9__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8) -> true);
    e_ee_9__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        ->
        true);
    e_ee_9__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8) ->
      e_ee_9__impl_2__from_u8x32 iv
  }

let e_ee_9__impl_1__splat (value: u8) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 32)
    #u8
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 256 > :: from and then u8x32 :: from is the identity.
assume
val e_ee_9__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8
  -> Lemma
    (ensures
      (e_ee_9__impl_2__to_u8x32 (e_ee_9__impl_2__from_u8x32 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8) ==
      x)

unfold
let e_ee_9__lemma_cancel_iv = e_ee_9__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u8x32 :: from and then BitVec :: < 256 > :: from is the identity.
assume
val e_ee_9__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (e_ee_9__impl_2__from_u8x32 (e_ee_9__impl_2__to_u8x32 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      x)

unfold
let e_ee_9__lemma_cancel_bv = e_ee_9__lemma_cancel_bv'

let e_ee_10: Prims.unit = ()

///Conversion from i32 vectors of size 4to  bit vectors of size 128
assume
val e_ee_10__impl_2__from_i32x4': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_10__impl_2__from_i32x4 = e_ee_10__impl_2__from_i32x4'

///Conversion from bit vectors of size 128 to i32 vectors of size 4
assume
val e_ee_10__impl_2__to_i32x4': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32

unfold
let e_ee_10__impl_2__to_i32x4 = e_ee_10__impl_2__to_i32x4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_10__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32) =
  {
    e_ee_10__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32) -> true);
    e_ee_10__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        ->
        true);
    e_ee_10__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32) ->
      e_ee_10__impl_2__from_i32x4 iv
  }

let e_ee_10__impl_1__splat (value: i32) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i32
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then i32x4 :: from is the identity.
assume
val e_ee_10__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32
  -> Lemma
    (ensures
      (e_ee_10__impl_2__to_i32x4 (e_ee_10__impl_2__from_i32x4 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32) ==
      x)

unfold
let e_ee_10__lemma_cancel_iv = e_ee_10__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i32x4 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_10__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_10__impl_2__from_i32x4 (e_ee_10__impl_2__to_i32x4 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_10__lemma_cancel_bv = e_ee_10__lemma_cancel_bv'

let e_ee_11: Prims.unit = ()

///Conversion from i64 vectors of size 2to  bit vectors of size 128
assume
val e_ee_11__impl_2__from_i64x2': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_11__impl_2__from_i64x2 = e_ee_11__impl_2__from_i64x2'

///Conversion from bit vectors of size 128 to i64 vectors of size 2
assume
val e_ee_11__impl_2__to_i64x2': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64

unfold
let e_ee_11__impl_2__to_i64x2 = e_ee_11__impl_2__to_i64x2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_11__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64) =
  {
    e_ee_11__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64) -> true);
    e_ee_11__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        ->
        true);
    e_ee_11__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64) ->
      e_ee_11__impl_2__from_i64x2 iv
  }

let e_ee_11__impl_1__splat (value: i64) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
    #i64
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then i64x2 :: from is the identity.
assume
val e_ee_11__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64
  -> Lemma
    (ensures
      (e_ee_11__impl_2__to_i64x2 (e_ee_11__impl_2__from_i64x2 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64) ==
      x)

unfold
let e_ee_11__lemma_cancel_iv = e_ee_11__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i64x2 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_11__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_11__impl_2__from_i64x2 (e_ee_11__impl_2__to_i64x2 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_11__lemma_cancel_bv = e_ee_11__lemma_cancel_bv'

let e_ee_12: Prims.unit = ()

///Conversion from i16 vectors of size 8to  bit vectors of size 128
assume
val e_ee_12__impl_2__from_i16x8': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_12__impl_2__from_i16x8 = e_ee_12__impl_2__from_i16x8'

///Conversion from bit vectors of size 128 to i16 vectors of size 8
assume
val e_ee_12__impl_2__to_i16x8': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16

unfold
let e_ee_12__impl_2__to_i16x8 = e_ee_12__impl_2__to_i16x8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_12__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16) =
  {
    e_ee_12__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16) -> true);
    e_ee_12__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        ->
        true);
    e_ee_12__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16) ->
      e_ee_12__impl_2__from_i16x8 iv
  }

let e_ee_12__impl_1__splat (value: i16) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i16
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then i16x8 :: from is the identity.
assume
val e_ee_12__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16
  -> Lemma
    (ensures
      (e_ee_12__impl_2__to_i16x8 (e_ee_12__impl_2__from_i16x8 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16) ==
      x)

unfold
let e_ee_12__lemma_cancel_iv = e_ee_12__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i16x8 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_12__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_12__impl_2__from_i16x8 (e_ee_12__impl_2__to_i16x8 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_12__lemma_cancel_bv = e_ee_12__lemma_cancel_bv'

let e_ee_13: Prims.unit = ()

///Conversion from i128 vectors of size 1to  bit vectors of size 128
assume
val e_ee_13__impl_2__from_i128x1': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_13__impl_2__from_i128x1 = e_ee_13__impl_2__from_i128x1'

///Conversion from bit vectors of size 128 to i128 vectors of size 1
assume
val e_ee_13__impl_2__to_i128x1': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128

unfold
let e_ee_13__impl_2__to_i128x1 = e_ee_13__impl_2__to_i128x1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_13__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128) =
  {
    e_ee_13__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128) -> true);
    e_ee_13__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        ->
        true);
    e_ee_13__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128) ->
      e_ee_13__impl_2__from_i128x1 iv
  }

let e_ee_13__impl_1__splat (value: i128)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 1)
    #i128
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then i128x1 :: from is the identity.
assume
val e_ee_13__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128
  -> Lemma
    (ensures
      (e_ee_13__impl_2__to_i128x1 (e_ee_13__impl_2__from_i128x1 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128) ==
      x)

unfold
let e_ee_13__lemma_cancel_iv = e_ee_13__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i128x1 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_13__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_13__impl_2__from_i128x1 (e_ee_13__impl_2__to_i128x1 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i128)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_13__lemma_cancel_bv = e_ee_13__lemma_cancel_bv'

let e_ee_14: Prims.unit = ()

///Conversion from i8 vectors of size 16to  bit vectors of size 128
assume
val e_ee_14__impl_2__from_i8x16': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_14__impl_2__from_i8x16 = e_ee_14__impl_2__from_i8x16'

///Conversion from bit vectors of size 128 to i8 vectors of size 16
assume
val e_ee_14__impl_2__to_i8x16': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8

unfold
let e_ee_14__impl_2__to_i8x16 = e_ee_14__impl_2__to_i8x16'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_14__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8) =
  {
    e_ee_14__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8) -> true);
    e_ee_14__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        ->
        true);
    e_ee_14__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8) ->
      e_ee_14__impl_2__from_i8x16 iv
  }

let e_ee_14__impl_1__splat (value: i8) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i8
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then i8x16 :: from is the identity.
assume
val e_ee_14__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8
  -> Lemma
    (ensures
      (e_ee_14__impl_2__to_i8x16 (e_ee_14__impl_2__from_i8x16 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8) ==
      x)

unfold
let e_ee_14__lemma_cancel_iv = e_ee_14__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i8x16 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_14__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_14__impl_2__from_i8x16 (e_ee_14__impl_2__to_i8x16 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_14__lemma_cancel_bv = e_ee_14__lemma_cancel_bv'

let e_ee_15: Prims.unit = ()

///Conversion from u32 vectors of size 4to  bit vectors of size 128
assume
val e_ee_15__impl_2__from_u32x4': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_15__impl_2__from_u32x4 = e_ee_15__impl_2__from_u32x4'

///Conversion from bit vectors of size 128 to u32 vectors of size 4
assume
val e_ee_15__impl_2__to_u32x4': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32

unfold
let e_ee_15__impl_2__to_u32x4 = e_ee_15__impl_2__to_u32x4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_15__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32) =
  {
    e_ee_15__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32) -> true);
    e_ee_15__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        ->
        true);
    e_ee_15__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32) ->
      e_ee_15__impl_2__from_u32x4 iv
  }

let e_ee_15__impl_1__splat (value: u32) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #u32
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then u32x4 :: from is the identity.
assume
val e_ee_15__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32
  -> Lemma
    (ensures
      (e_ee_15__impl_2__to_u32x4 (e_ee_15__impl_2__from_u32x4 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32) ==
      x)

unfold
let e_ee_15__lemma_cancel_iv = e_ee_15__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u32x4 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_15__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_15__impl_2__from_u32x4 (e_ee_15__impl_2__to_u32x4 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_15__lemma_cancel_bv = e_ee_15__lemma_cancel_bv'

let e_ee_16: Prims.unit = ()

///Conversion from u64 vectors of size 2to  bit vectors of size 128
assume
val e_ee_16__impl_2__from_u64x2': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_16__impl_2__from_u64x2 = e_ee_16__impl_2__from_u64x2'

///Conversion from bit vectors of size 128 to u64 vectors of size 2
assume
val e_ee_16__impl_2__to_u64x2': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64

unfold
let e_ee_16__impl_2__to_u64x2 = e_ee_16__impl_2__to_u64x2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_16__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64) =
  {
    e_ee_16__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64) -> true);
    e_ee_16__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        ->
        true);
    e_ee_16__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64) ->
      e_ee_16__impl_2__from_u64x2 iv
  }

let e_ee_16__impl_1__splat (value: u64) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
    #u64
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then u64x2 :: from is the identity.
assume
val e_ee_16__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64
  -> Lemma
    (ensures
      (e_ee_16__impl_2__to_u64x2 (e_ee_16__impl_2__from_u64x2 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64) ==
      x)

unfold
let e_ee_16__lemma_cancel_iv = e_ee_16__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u64x2 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_16__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_16__impl_2__from_u64x2 (e_ee_16__impl_2__to_u64x2 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_16__lemma_cancel_bv = e_ee_16__lemma_cancel_bv'

let e_ee_17: Prims.unit = ()

///Conversion from u16 vectors of size 8to  bit vectors of size 128
assume
val e_ee_17__impl_2__from_u16x8': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_17__impl_2__from_u16x8 = e_ee_17__impl_2__from_u16x8'

///Conversion from bit vectors of size 128 to u16 vectors of size 8
assume
val e_ee_17__impl_2__to_u16x8': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16

unfold
let e_ee_17__impl_2__to_u16x8 = e_ee_17__impl_2__to_u16x8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_17__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16) =
  {
    e_ee_17__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16) -> true);
    e_ee_17__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        ->
        true);
    e_ee_17__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16) ->
      e_ee_17__impl_2__from_u16x8 iv
  }

let e_ee_17__impl_1__splat (value: u16) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #u16
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then u16x8 :: from is the identity.
assume
val e_ee_17__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16
  -> Lemma
    (ensures
      (e_ee_17__impl_2__to_u16x8 (e_ee_17__impl_2__from_u16x8 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16) ==
      x)

unfold
let e_ee_17__lemma_cancel_iv = e_ee_17__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u16x8 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_17__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_17__impl_2__from_u16x8 (e_ee_17__impl_2__to_u16x8 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_17__lemma_cancel_bv = e_ee_17__lemma_cancel_bv'

let e_ee_18: Prims.unit = ()

///Conversion from u8 vectors of size 16to  bit vectors of size 128
assume
val e_ee_18__impl_2__from_u8x16': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)

unfold
let e_ee_18__impl_2__from_u8x16 = e_ee_18__impl_2__from_u8x16'

///Conversion from bit vectors of size 128 to u8 vectors of size 16
assume
val e_ee_18__impl_2__to_u8x16': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8

unfold
let e_ee_18__impl_2__to_u8x16 = e_ee_18__impl_2__to_u8x16'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_18__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8) =
  {
    e_ee_18__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8) -> true);
    e_ee_18__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        ->
        true);
    e_ee_18__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8) ->
      e_ee_18__impl_2__from_u8x16 iv
  }

let e_ee_18__impl_1__splat (value: u8) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #u8
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 128 > :: from and then u8x16 :: from is the identity.
assume
val e_ee_18__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8
  -> Lemma
    (ensures
      (e_ee_18__impl_2__to_u8x16 (e_ee_18__impl_2__from_u8x16 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8) ==
      x)

unfold
let e_ee_18__lemma_cancel_iv = e_ee_18__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u8x16 :: from and then BitVec :: < 128 > :: from is the identity.
assume
val e_ee_18__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)
  -> Lemma
    (ensures
      (e_ee_18__impl_2__from_u8x16 (e_ee_18__impl_2__to_u8x16 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128)) ==
      x)

unfold
let e_ee_18__lemma_cancel_bv = e_ee_18__lemma_cancel_bv'

let e_ee_19: Prims.unit = ()

///Conversion from u32 vectors of size 16to  bit vectors of size 512
assume
val e_ee_19__impl_2__from_u32x16': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512)

unfold
let e_ee_19__impl_2__from_u32x16 = e_ee_19__impl_2__from_u32x16'

///Conversion from bit vectors of size 512 to u32 vectors of size 16
assume
val e_ee_19__impl_2__to_u32x16': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32

unfold
let e_ee_19__impl_2__to_u32x16 = e_ee_19__impl_2__to_u32x16'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_19__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32) =
  {
    e_ee_19__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32) -> true);
    e_ee_19__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512))
        ->
        true);
    e_ee_19__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32) ->
      e_ee_19__impl_2__from_u32x16 iv
  }

let e_ee_19__impl_1__splat (value: u32) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #u32
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 512 > :: from and then u32x16 :: from is the identity.
assume
val e_ee_19__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32
  -> Lemma
    (ensures
      (e_ee_19__impl_2__to_u32x16 (e_ee_19__impl_2__from_u32x16 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32) ==
      x)

unfold
let e_ee_19__lemma_cancel_iv = e_ee_19__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u32x16 :: from and then BitVec :: < 512 > :: from is the identity.
assume
val e_ee_19__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512)
  -> Lemma
    (ensures
      (e_ee_19__impl_2__from_u32x16 (e_ee_19__impl_2__to_u32x16 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512)) ==
      x)

unfold
let e_ee_19__lemma_cancel_bv = e_ee_19__lemma_cancel_bv'

let e_ee_20: Prims.unit = ()

///Conversion from u16 vectors of size 32to  bit vectors of size 512
assume
val e_ee_20__impl_2__from_u16x32': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512)

unfold
let e_ee_20__impl_2__from_u16x32 = e_ee_20__impl_2__from_u16x32'

///Conversion from bit vectors of size 512 to u16 vectors of size 32
assume
val e_ee_20__impl_2__to_u16x32': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16

unfold
let e_ee_20__impl_2__to_u16x32 = e_ee_20__impl_2__to_u16x32'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_20__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16) =
  {
    e_ee_20__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16) -> true);
    e_ee_20__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512))
        ->
        true);
    e_ee_20__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16) ->
      e_ee_20__impl_2__from_u16x32 iv
  }

let e_ee_20__impl_1__splat (value: u16) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 32)
    #u16
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 512 > :: from and then u16x32 :: from is the identity.
assume
val e_ee_20__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16
  -> Lemma
    (ensures
      (e_ee_20__impl_2__to_u16x32 (e_ee_20__impl_2__from_u16x32 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16) ==
      x)

unfold
let e_ee_20__lemma_cancel_iv = e_ee_20__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u16x32 :: from and then BitVec :: < 512 > :: from is the identity.
assume
val e_ee_20__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512)
  -> Lemma
    (ensures
      (e_ee_20__impl_2__from_u16x32 (e_ee_20__impl_2__to_u16x32 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512)) ==
      x)

unfold
let e_ee_20__lemma_cancel_bv = e_ee_20__lemma_cancel_bv'

let e_ee_21: Prims.unit = ()

///Conversion from i32 vectors of size 16to  bit vectors of size 512
assume
val e_ee_21__impl_2__from_i32x16': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i32
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512)

unfold
let e_ee_21__impl_2__from_i32x16 = e_ee_21__impl_2__from_i32x16'

///Conversion from bit vectors of size 512 to i32 vectors of size 16
assume
val e_ee_21__impl_2__to_i32x16': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i32

unfold
let e_ee_21__impl_2__to_i32x16 = e_ee_21__impl_2__to_i32x16'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_21__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i32) =
  {
    e_ee_21__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i32) -> true);
    e_ee_21__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i32)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512))
        ->
        true);
    e_ee_21__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i32) ->
      e_ee_21__impl_2__from_i32x16 iv
  }

let e_ee_21__impl_1__splat (value: i32) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i32
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 512 > :: from and then i32x16 :: from is the identity.
assume
val e_ee_21__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i32
  -> Lemma
    (ensures
      (e_ee_21__impl_2__to_i32x16 (e_ee_21__impl_2__from_i32x16 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i32) ==
      x)

unfold
let e_ee_21__lemma_cancel_iv = e_ee_21__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i32x16 :: from and then BitVec :: < 512 > :: from is the identity.
assume
val e_ee_21__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512)
  -> Lemma
    (ensures
      (e_ee_21__impl_2__from_i32x16 (e_ee_21__impl_2__to_i32x16 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512)) ==
      x)

unfold
let e_ee_21__lemma_cancel_bv = e_ee_21__lemma_cancel_bv'

let e_ee_22: Prims.unit = ()

///Conversion from i16 vectors of size 32to  bit vectors of size 512
assume
val e_ee_22__impl_2__from_i16x32': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i16
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512)

unfold
let e_ee_22__impl_2__from_i16x32 = e_ee_22__impl_2__from_i16x32'

///Conversion from bit vectors of size 512 to i16 vectors of size 32
assume
val e_ee_22__impl_2__to_i16x32': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i16

unfold
let e_ee_22__impl_2__to_i16x32 = e_ee_22__impl_2__to_i16x32'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_22__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i16) =
  {
    e_ee_22__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i16) -> true);
    e_ee_22__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i16)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512))
        ->
        true);
    e_ee_22__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i16) ->
      e_ee_22__impl_2__from_i16x32 iv
  }

let e_ee_22__impl_1__splat (value: i16) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 32)
    #i16
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 512 > :: from and then i16x32 :: from is the identity.
assume
val e_ee_22__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i16
  -> Lemma
    (ensures
      (e_ee_22__impl_2__to_i16x32 (e_ee_22__impl_2__from_i16x32 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i16) ==
      x)

unfold
let e_ee_22__lemma_cancel_iv = e_ee_22__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i16x32 :: from and then BitVec :: < 512 > :: from is the identity.
assume
val e_ee_22__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512)
  -> Lemma
    (ensures
      (e_ee_22__impl_2__from_i16x32 (e_ee_22__impl_2__to_i16x32 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 512)) ==
      x)

unfold
let e_ee_22__lemma_cancel_bv = e_ee_22__lemma_cancel_bv'

let e_ee_23: Prims.unit = ()

///Conversion from i64 vectors of size 1to  bit vectors of size 64
assume
val e_ee_23__impl_2__from_i64x1': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)

unfold
let e_ee_23__impl_2__from_i64x1 = e_ee_23__impl_2__from_i64x1'

///Conversion from bit vectors of size 64 to i64 vectors of size 1
assume
val e_ee_23__impl_2__to_i64x1': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64

unfold
let e_ee_23__impl_2__to_i64x1 = e_ee_23__impl_2__to_i64x1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_23__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64) =
  {
    e_ee_23__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64) -> true);
    e_ee_23__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
        ->
        true);
    e_ee_23__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64) ->
      e_ee_23__impl_2__from_i64x1 iv
  }

let e_ee_23__impl_1__splat (value: i64) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 1)
    #i64
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 64 > :: from and then i64x1 :: from is the identity.
assume
val e_ee_23__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64
  -> Lemma
    (ensures
      (e_ee_23__impl_2__to_i64x1 (e_ee_23__impl_2__from_i64x1 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64) ==
      x)

unfold
let e_ee_23__lemma_cancel_iv = e_ee_23__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i64x1 :: from and then BitVec :: < 64 > :: from is the identity.
assume
val e_ee_23__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)
  -> Lemma
    (ensures
      (e_ee_23__impl_2__from_i64x1 (e_ee_23__impl_2__to_i64x1 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) i64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)) ==
      x)

unfold
let e_ee_23__lemma_cancel_bv = e_ee_23__lemma_cancel_bv'

let e_ee_24: Prims.unit = ()

///Conversion from i32 vectors of size 2to  bit vectors of size 64
assume
val e_ee_24__impl_2__from_i32x2': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)

unfold
let e_ee_24__impl_2__from_i32x2 = e_ee_24__impl_2__from_i32x2'

///Conversion from bit vectors of size 64 to i32 vectors of size 2
assume
val e_ee_24__impl_2__to_i32x2': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32

unfold
let e_ee_24__impl_2__to_i32x2 = e_ee_24__impl_2__to_i32x2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_24__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32) =
  {
    e_ee_24__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32) -> true);
    e_ee_24__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
        ->
        true);
    e_ee_24__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32) ->
      e_ee_24__impl_2__from_i32x2 iv
  }

let e_ee_24__impl_1__splat (value: i32) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
    #i32
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 64 > :: from and then i32x2 :: from is the identity.
assume
val e_ee_24__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32
  -> Lemma
    (ensures
      (e_ee_24__impl_2__to_i32x2 (e_ee_24__impl_2__from_i32x2 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32) ==
      x)

unfold
let e_ee_24__lemma_cancel_iv = e_ee_24__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i32x2 :: from and then BitVec :: < 64 > :: from is the identity.
assume
val e_ee_24__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)
  -> Lemma
    (ensures
      (e_ee_24__impl_2__from_i32x2 (e_ee_24__impl_2__to_i32x2 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)) ==
      x)

unfold
let e_ee_24__lemma_cancel_bv = e_ee_24__lemma_cancel_bv'

let e_ee_25: Prims.unit = ()

///Conversion from i16 vectors of size 4to  bit vectors of size 64
assume
val e_ee_25__impl_2__from_i16x4': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)

unfold
let e_ee_25__impl_2__from_i16x4 = e_ee_25__impl_2__from_i16x4'

///Conversion from bit vectors of size 64 to i16 vectors of size 4
assume
val e_ee_25__impl_2__to_i16x4': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16

unfold
let e_ee_25__impl_2__to_i16x4 = e_ee_25__impl_2__to_i16x4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_25__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16) =
  {
    e_ee_25__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16) -> true);
    e_ee_25__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
        ->
        true);
    e_ee_25__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16) ->
      e_ee_25__impl_2__from_i16x4 iv
  }

let e_ee_25__impl_1__splat (value: i16) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i16
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 64 > :: from and then i16x4 :: from is the identity.
assume
val e_ee_25__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16
  -> Lemma
    (ensures
      (e_ee_25__impl_2__to_i16x4 (e_ee_25__impl_2__from_i16x4 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16) ==
      x)

unfold
let e_ee_25__lemma_cancel_iv = e_ee_25__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i16x4 :: from and then BitVec :: < 64 > :: from is the identity.
assume
val e_ee_25__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)
  -> Lemma
    (ensures
      (e_ee_25__impl_2__from_i16x4 (e_ee_25__impl_2__to_i16x4 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)) ==
      x)

unfold
let e_ee_25__lemma_cancel_bv = e_ee_25__lemma_cancel_bv'

let e_ee_26: Prims.unit = ()

///Conversion from i8 vectors of size 8to  bit vectors of size 64
assume
val e_ee_26__impl_2__from_i8x8': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)

unfold
let e_ee_26__impl_2__from_i8x8 = e_ee_26__impl_2__from_i8x8'

///Conversion from bit vectors of size 64 to i8 vectors of size 8
assume
val e_ee_26__impl_2__to_i8x8': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8

unfold
let e_ee_26__impl_2__to_i8x8 = e_ee_26__impl_2__to_i8x8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_26__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8) =
  {
    e_ee_26__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8) -> true);
    e_ee_26__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
        ->
        true);
    e_ee_26__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8) ->
      e_ee_26__impl_2__from_i8x8 iv
  }

let e_ee_26__impl_1__splat (value: i8) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i8
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 64 > :: from and then i8x8 :: from is the identity.
assume
val e_ee_26__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8
  -> Lemma
    (ensures
      (e_ee_26__impl_2__to_i8x8 (e_ee_26__impl_2__from_i8x8 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8) ==
      x)

unfold
let e_ee_26__lemma_cancel_iv = e_ee_26__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i8x8 :: from and then BitVec :: < 64 > :: from is the identity.
assume
val e_ee_26__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)
  -> Lemma
    (ensures
      (e_ee_26__impl_2__from_i8x8 (e_ee_26__impl_2__to_i8x8 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)) ==
      x)

unfold
let e_ee_26__lemma_cancel_bv = e_ee_26__lemma_cancel_bv'

let e_ee_27: Prims.unit = ()

///Conversion from u64 vectors of size 1to  bit vectors of size 64
assume
val e_ee_27__impl_2__from_u64x1': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)

unfold
let e_ee_27__impl_2__from_u64x1 = e_ee_27__impl_2__from_u64x1'

///Conversion from bit vectors of size 64 to u64 vectors of size 1
assume
val e_ee_27__impl_2__to_u64x1': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64

unfold
let e_ee_27__impl_2__to_u64x1 = e_ee_27__impl_2__to_u64x1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_27__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64) =
  {
    e_ee_27__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64) -> true);
    e_ee_27__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
        ->
        true);
    e_ee_27__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64) ->
      e_ee_27__impl_2__from_u64x1 iv
  }

let e_ee_27__impl_1__splat (value: u64) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 1)
    #u64
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 64 > :: from and then u64x1 :: from is the identity.
assume
val e_ee_27__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64
  -> Lemma
    (ensures
      (e_ee_27__impl_2__to_u64x1 (e_ee_27__impl_2__from_u64x1 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64) ==
      x)

unfold
let e_ee_27__lemma_cancel_iv = e_ee_27__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u64x1 :: from and then BitVec :: < 64 > :: from is the identity.
assume
val e_ee_27__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)
  -> Lemma
    (ensures
      (e_ee_27__impl_2__from_u64x1 (e_ee_27__impl_2__to_u64x1 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 1) u64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)) ==
      x)

unfold
let e_ee_27__lemma_cancel_bv = e_ee_27__lemma_cancel_bv'

let e_ee_28: Prims.unit = ()

///Conversion from u32 vectors of size 2to  bit vectors of size 64
assume
val e_ee_28__impl_2__from_u32x2': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)

unfold
let e_ee_28__impl_2__from_u32x2 = e_ee_28__impl_2__from_u32x2'

///Conversion from bit vectors of size 64 to u32 vectors of size 2
assume
val e_ee_28__impl_2__to_u32x2': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32

unfold
let e_ee_28__impl_2__to_u32x2 = e_ee_28__impl_2__to_u32x2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_28__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32) =
  {
    e_ee_28__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32) -> true);
    e_ee_28__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
        ->
        true);
    e_ee_28__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32) ->
      e_ee_28__impl_2__from_u32x2 iv
  }

let e_ee_28__impl_1__splat (value: u32) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
    #u32
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 64 > :: from and then u32x2 :: from is the identity.
assume
val e_ee_28__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32
  -> Lemma
    (ensures
      (e_ee_28__impl_2__to_u32x2 (e_ee_28__impl_2__from_u32x2 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32) ==
      x)

unfold
let e_ee_28__lemma_cancel_iv = e_ee_28__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u32x2 :: from and then BitVec :: < 64 > :: from is the identity.
assume
val e_ee_28__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)
  -> Lemma
    (ensures
      (e_ee_28__impl_2__from_u32x2 (e_ee_28__impl_2__to_u32x2 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) u32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)) ==
      x)

unfold
let e_ee_28__lemma_cancel_bv = e_ee_28__lemma_cancel_bv'

let e_ee_29: Prims.unit = ()

///Conversion from u16 vectors of size 4to  bit vectors of size 64
assume
val e_ee_29__impl_2__from_u16x4': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)

unfold
let e_ee_29__impl_2__from_u16x4 = e_ee_29__impl_2__from_u16x4'

///Conversion from bit vectors of size 64 to u16 vectors of size 4
assume
val e_ee_29__impl_2__to_u16x4': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16

unfold
let e_ee_29__impl_2__to_u16x4 = e_ee_29__impl_2__to_u16x4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_29__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16) =
  {
    e_ee_29__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16) -> true);
    e_ee_29__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
        ->
        true);
    e_ee_29__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16) ->
      e_ee_29__impl_2__from_u16x4 iv
  }

let e_ee_29__impl_1__splat (value: u16) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #u16
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 64 > :: from and then u16x4 :: from is the identity.
assume
val e_ee_29__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16
  -> Lemma
    (ensures
      (e_ee_29__impl_2__to_u16x4 (e_ee_29__impl_2__from_u16x4 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16) ==
      x)

unfold
let e_ee_29__lemma_cancel_iv = e_ee_29__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u16x4 :: from and then BitVec :: < 64 > :: from is the identity.
assume
val e_ee_29__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)
  -> Lemma
    (ensures
      (e_ee_29__impl_2__from_u16x4 (e_ee_29__impl_2__to_u16x4 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)) ==
      x)

unfold
let e_ee_29__lemma_cancel_bv = e_ee_29__lemma_cancel_bv'

let e_ee_30: Prims.unit = ()

///Conversion from u8 vectors of size 8to  bit vectors of size 64
assume
val e_ee_30__impl_2__from_u8x8': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)

unfold
let e_ee_30__impl_2__from_u8x8 = e_ee_30__impl_2__from_u8x8'

///Conversion from bit vectors of size 64 to u8 vectors of size 8
assume
val e_ee_30__impl_2__to_u8x8': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8

unfold
let e_ee_30__impl_2__to_u8x8 = e_ee_30__impl_2__to_u8x8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_30__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8) =
  {
    e_ee_30__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8) -> true);
    e_ee_30__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
        ->
        true);
    e_ee_30__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8) ->
      e_ee_30__impl_2__from_u8x8 iv
  }

let e_ee_30__impl_1__splat (value: u8) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #u8
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 64 > :: from and then u8x8 :: from is the identity.
assume
val e_ee_30__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8
  -> Lemma
    (ensures
      (e_ee_30__impl_2__to_u8x8 (e_ee_30__impl_2__from_u8x8 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8) ==
      x)

unfold
let e_ee_30__lemma_cancel_iv = e_ee_30__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u8x8 :: from and then BitVec :: < 64 > :: from is the identity.
assume
val e_ee_30__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)
  -> Lemma
    (ensures
      (e_ee_30__impl_2__from_u8x8 (e_ee_30__impl_2__to_u8x8 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 64)) ==
      x)

unfold
let e_ee_30__lemma_cancel_bv = e_ee_30__lemma_cancel_bv'

let e_ee_31: Prims.unit = ()

///Conversion from i8 vectors of size 4to  bit vectors of size 32
assume
val e_ee_31__impl_2__from_i8x4': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i8
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 32)

unfold
let e_ee_31__impl_2__from_i8x4 = e_ee_31__impl_2__from_i8x4'

///Conversion from bit vectors of size 32 to i8 vectors of size 4
assume
val e_ee_31__impl_2__to_i8x4': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 32)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i8

unfold
let e_ee_31__impl_2__to_i8x4 = e_ee_31__impl_2__to_i8x4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_31__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 32))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i8) =
  {
    e_ee_31__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i8) -> true);
    e_ee_31__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i8)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 32))
        ->
        true);
    e_ee_31__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i8) ->
      e_ee_31__impl_2__from_i8x4 iv
  }

let e_ee_31__impl_1__splat (value: i8) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i8 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i8
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 32 > :: from and then i8x4 :: from is the identity.
assume
val e_ee_31__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i8
  -> Lemma
    (ensures
      (e_ee_31__impl_2__to_i8x4 (e_ee_31__impl_2__from_i8x4 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 32))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i8) ==
      x)

unfold
let e_ee_31__lemma_cancel_iv = e_ee_31__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying i8x4 :: from and then BitVec :: < 32 > :: from is the identity.
assume
val e_ee_31__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 32)
  -> Lemma
    (ensures
      (e_ee_31__impl_2__from_i8x4 (e_ee_31__impl_2__to_i8x4 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i8)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 32)) ==
      x)

unfold
let e_ee_31__lemma_cancel_bv = e_ee_31__lemma_cancel_bv'

let e_ee_32: Prims.unit = ()

///Conversion from u8 vectors of size 4to  bit vectors of size 32
assume
val e_ee_32__impl_2__from_u8x4': iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u8
  -> Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 32)

unfold
let e_ee_32__impl_2__from_u8x4 = e_ee_32__impl_2__from_u8x4'

///Conversion from bit vectors of size 32 to u8 vectors of size 4
assume
val e_ee_32__impl_2__to_u8x4': bv: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 32)
  -> Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u8

unfold
let e_ee_32__impl_2__to_u8x4 = e_ee_32__impl_2__to_u8x4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let e_ee_32__impl: Core.Convert.t_From (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 32))
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u8) =
  {
    e_ee_32__f_from_pre
    =
    (fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u8) -> true);
    e_ee_32__f_from_post
    =
    (fun
        (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u8)
        (out: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 32))
        ->
        true);
    e_ee_32__f_from
    =
    fun (iv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u8) ->
      e_ee_32__impl_2__from_u8x4 iv
  }

let e_ee_32__impl_1__splat (value: u8) : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u8 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #u8
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        value)

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying BitVec :: < 32 > :: from and then u8x4 :: from is the identity.
assume
val e_ee_32__lemma_cancel_iv': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u8
  -> Lemma
    (ensures
      (e_ee_32__impl_2__to_u8x4 (e_ee_32__impl_2__from_u8x4 x
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 32))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u8) ==
      x)

unfold
let e_ee_32__lemma_cancel_iv = e_ee_32__lemma_cancel_iv'

[@@ v_SIMPLIFICATION_LEMMA ]

///Lemma that asserts that applying u8x4 :: from and then BitVec :: < 32 > :: from is the identity.
assume
val e_ee_32__lemma_cancel_bv': x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 32)
  -> Lemma
    (ensures
      (e_ee_32__impl_2__from_u8x4 (e_ee_32__impl_2__to_u8x4 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u8)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 32)) ==
      x)

unfold
let e_ee_32__lemma_cancel_bv = e_ee_32__lemma_cancel_bv'

let impl__into_i32x8 (self: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        let value:i64 =
          Core_models.Abstractions.Funarr.impl_5__get (mk_u64 4) #i64 self (i /! mk_u64 2 <: u64)
        in
        cast ((if (i %! mk_u64 2 <: u64) =. mk_u64 0 then value else value >>! mk_i32 32) <: i64)
        <:
        i32)

let impl_1__into_i64x4 (self: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        let low:u64 =
          cast (cast (Core_models.Abstractions.Funarr.impl_5__get (mk_u64 8)
                    #i32
                    self
                    (mk_u64 2 *! i <: u64)
                  <:
                  i32)
              <:
              u32)
          <:
          u64
        in
        let high:i64 =
          cast (Core_models.Abstractions.Funarr.impl_5__get (mk_u64 8)
                #i32
                self
                ((mk_u64 2 *! i <: u64) +! mk_u64 1 <: u64)
              <:
              i32)
          <:
          i64
        in
        (high <<! mk_i32 32 <: i64) |. (cast (low <: u64) <: i64))

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Convert.t_From (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
  (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) =
  {
    f_from_pre = (fun (vec: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) -> true);
    f_from_post
    =
    (fun
        (vec: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (out: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        ->
        true);
    f_from
    =
    fun (vec: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) -> impl__into_i32x8 vec
  }

[@@ v_SIMPLIFICATION_LEMMA ]

/// Lemma stating that converting an `i64x4` vector to a `BitVec<256>` and then into an `i32x8`
/// yields the same result as directly converting the `i64x4` into an `i32x8`.
assume
val lemma_rewrite_i64x4_bv_i32x8': bv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64
  -> Lemma
    (ensures
      (e_ee_1__impl_2__to_i32x8 (e_ee_2__impl_2__from_i64x4 bv
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) ==
      (impl__into_i32x8 bv <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32))

unfold
let lemma_rewrite_i64x4_bv_i32x8 = lemma_rewrite_i64x4_bv_i32x8'

[@@ v_SIMPLIFICATION_LEMMA ]

/// Lemma stating that converting an `i64x4` vector to a `BitVec<256>` and then into an `i32x8`
/// yields the same result as directly converting the `i64x4` into an `i32x8`.
assume
val lemma_rewrite_i32x8_bv_i64x4': bv: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32
  -> Lemma
    (ensures
      (e_ee_2__impl_2__to_i64x4 (e_ee_1__impl_2__from_i32x8 bv
            <:
            Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) ==
      (impl_1__into_i64x4 bv <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64))

unfold
let lemma_rewrite_i32x8_bv_i64x4 = lemma_rewrite_i32x8_bv_i64x4'

[@@ v_SIMPLIFICATION_LEMMA ]
        let lemma (t: Type) (i: Core.Convert.t_From t t) (x: t)
            : Lemma (Core.Convert.f_from #t #t #i x == (norm [primops; iota; delta; zeta] i.f_from) x)
            = ()
