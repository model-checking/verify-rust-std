module Core_models.Abstractions.Bit
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

/// Represent a bit: `0` or `1`.
type t_Bit =
  | Bit_Zero : t_Bit
  | Bit_One : t_Bit

let t_Bit_cast_to_repr (x: t_Bit) : isize =
  match x <: t_Bit with
  | Bit_Zero  -> mk_isize 0
  | Bit_One  -> mk_isize 1

let impl_3: Core.Clone.t_Clone t_Bit = { f_clone = (fun x -> x) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core.Marker.t_Copy t_Bit

unfold
let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core.Marker.t_StructuralPartialEq t_Bit

unfold
let impl_5 = impl_5'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': Core.Cmp.t_PartialEq t_Bit t_Bit

unfold
let impl_6 = impl_6'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core.Cmp.t_Eq t_Bit

unfold
let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core.Fmt.t_Debug t_Bit

unfold
let impl_7 = impl_7'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Convert.t_From bool t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: bool) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      match bit <: t_Bit with
      | Bit_Zero  -> false
      | Bit_One  -> true
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Convert.t_From u8 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: u8) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Convert.t_From u16 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: u16) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Convert.t_From u32 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: u32) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Convert.t_From u64 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: u64) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Convert.t_From u128 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: u128) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Convert.t_From i8 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: i8) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core.Convert.t_From i16 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: i16) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Convert.t_From i32 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: i32) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core.Convert.t_From i64 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: i64) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Convert.t_From i128 t_Bit =
  {
    f_from_pre = (fun (bit: t_Bit) -> true);
    f_from_post = (fun (bit: t_Bit) (out: i128) -> true);
    f_from
    =
    fun (bit: t_Bit) ->
      cast (Core.Convert.f_from #bool #t_Bit #FStar.Tactics.Typeclasses.solve bit <: bool) <: i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From t_Bit bool =
  {
    f_from_pre = (fun (b: bool) -> true);
    f_from_post = (fun (b: bool) (out: t_Bit) -> true);
    f_from
    =
    fun (b: bool) ->
      match b <: bool with
      | false -> Bit_Zero <: t_Bit
      | true -> Bit_One <: t_Bit
  }

/// A trait for types that represent machine integers.
class t_MachineInteger (v_Self: Type0) = {
  f_bits_pre:x: Prims.unit
    -> pred:
      Type0
        { (let _:Prims.unit = x in
            true) ==>
          pred };
  f_bits_post:x: Prims.unit -> bits: u32
    -> pred:
      Type0
        { pred ==>
          (let _:Prims.unit = x in
            bits >=. mk_u32 8) };
  f_bits:x0: Prims.unit -> Prims.Pure u32 (f_bits_pre x0) (fun result -> f_bits_post x0 result);
  f_SIGNED:bool;
  f_ZEROS:v_Self;
  f_ONE:v_Self;
  f_ONES:v_Self;
  f_MIN:v_Self;
  f_MAX:v_Self;
  f_wrapping_add_pre:v_Self -> v_Self -> Type0;
  f_wrapping_add_post:v_Self -> v_Self -> v_Self -> Type0;
  f_wrapping_add:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_wrapping_add_pre x0 x1) (fun result -> f_wrapping_add_post x0 x1 result);
  f_wrapping_sub_pre:v_Self -> v_Self -> Type0;
  f_wrapping_sub_post:v_Self -> v_Self -> v_Self -> Type0;
  f_wrapping_sub:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_wrapping_sub_pre x0 x1) (fun result -> f_wrapping_sub_post x0 x1 result);
  f_overflowing_mul_pre:v_Self -> v_Self -> Type0;
  f_overflowing_mul_post:v_Self -> v_Self -> v_Self -> Type0;
  f_overflowing_mul:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self
        (f_overflowing_mul_pre x0 x1)
        (fun result -> f_overflowing_mul_post x0 x1 result);
  f_saturating_add_pre:v_Self -> v_Self -> Type0;
  f_saturating_add_post:v_Self -> v_Self -> v_Self -> Type0;
  f_saturating_add:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self
        (f_saturating_add_pre x0 x1)
        (fun result -> f_saturating_add_post x0 x1 result);
  f_saturating_sub_pre:v_Self -> v_Self -> Type0;
  f_saturating_sub_post:v_Self -> v_Self -> v_Self -> Type0;
  f_saturating_sub:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self
        (f_saturating_sub_pre x0 x1)
        (fun result -> f_saturating_sub_post x0 x1 result);
  f_absolute_diff_pre:v_Self -> v_Self -> Type0;
  f_absolute_diff_post:v_Self -> v_Self -> v_Self -> Type0;
  f_absolute_diff:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self
        (f_absolute_diff_pre x0 x1)
        (fun result -> f_absolute_diff_post x0 x1 result);
  f_absolute_val_pre:v_Self -> Type0;
  f_absolute_val_post:v_Self -> v_Self -> Type0;
  f_absolute_val:x0: v_Self
    -> Prims.Pure v_Self (f_absolute_val_pre x0) (fun result -> f_absolute_val_post x0 result)
}

instance impl_MachineInteger_poly (t: inttype): t_MachineInteger (int_t t) =
  { f_bits = (fun () -> mk_u32 (bits t));
    f_bits_pre = (fun () -> True);
    f_bits_post = (fun () r -> r == mk_u32 (bits t));
    f_SIGNED = signed t;
    f_ZEROS = MkInt 0;
    f_ONE = MkInt 1;
    f_ONES = if unsigned t then MkInt (maxint t) else MkInt (-1);
    f_MAX = MkInt (maxint t);
    f_MIN = MkInt (minint t);
    f_wrapping_add = admit();
    f_wrapping_add_post = admit();
    f_wrapping_add_pre = admit();
    f_saturating_sub = admit();
    f_saturating_sub_post = admit();
    f_saturating_sub_pre = admit();
    f_saturating_add = admit();
    f_saturating_add_post = admit();
    f_saturating_add_pre = admit();
    f_overflowing_mul = admit();
    f_overflowing_mul_post = admit();
    f_overflowing_mul_pre = admit();
    f_wrapping_sub = admit();
    f_wrapping_sub_post = admit();
    f_wrapping_sub_pre = admit();
    f_absolute_val = admit();
    f_absolute_val_post = admit();
    f_absolute_val_pre = admit();
    f_absolute_diff = admit();
    f_absolute_diff_post = admit();
    f_absolute_diff_pre = admit();
    }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_MachineInteger_for_i8: t_MachineInteger i8 =
  {
    f_SIGNED = true;
    f_ZEROS = mk_i8 0;
    f_ONE = mk_i8 1;
    f_ONES = mk_i8 (-1);
    f_MIN = Core.Num.impl_i8__MIN;
    f_MAX = Core.Num.impl_i8__MAX;
    f_bits_pre = (fun (_: Prims.unit) -> true);
    f_bits_post = (fun (_: Prims.unit) (out: u32) -> true);
    f_bits = (fun (_: Prims.unit) -> Core.Num.impl_i8__BITS);
    f_wrapping_add_pre = (fun (self: i8) (rhs: i8) -> true);
    f_wrapping_add_post = (fun (self: i8) (rhs: i8) (out: i8) -> true);
    f_wrapping_add = (fun (self: i8) (rhs: i8) -> Core.Num.impl_i8__wrapping_add self rhs);
    f_wrapping_sub_pre = (fun (self: i8) (rhs: i8) -> true);
    f_wrapping_sub_post = (fun (self: i8) (rhs: i8) (out: i8) -> true);
    f_wrapping_sub = (fun (self: i8) (rhs: i8) -> Core.Num.impl_i8__wrapping_sub self rhs);
    f_overflowing_mul_pre = (fun (self: i8) (rhs: i8) -> true);
    f_overflowing_mul_post = (fun (self: i8) (rhs: i8) (out: i8) -> true);
    f_overflowing_mul
    =
    (fun (self: i8) (rhs: i8) -> (Core.Num.impl_i8__overflowing_mul self rhs)._1);
    f_saturating_add_pre = (fun (self: i8) (rhs: i8) -> true);
    f_saturating_add_post = (fun (self: i8) (rhs: i8) (out: i8) -> true);
    f_saturating_add = (fun (self: i8) (rhs: i8) -> Core.Num.impl_i8__saturating_add self rhs);
    f_saturating_sub_pre = (fun (self: i8) (rhs: i8) -> true);
    f_saturating_sub_post = (fun (self: i8) (rhs: i8) (out: i8) -> true);
    f_saturating_sub = (fun (self: i8) (rhs: i8) -> Core.Num.impl_i8__saturating_sub self rhs);
    f_absolute_diff_pre = (fun (self: i8) (rhs: i8) -> true);
    f_absolute_diff_post = (fun (self: i8) (rhs: i8) (out: i8) -> true);
    f_absolute_diff
    =
    (fun (self: i8) (rhs: i8) ->
        if self >. rhs
        then Core.Num.impl_i8__wrapping_sub self rhs
        else Core.Num.impl_i8__wrapping_sub rhs self);
    f_absolute_val_pre = (fun (self: i8) -> true);
    f_absolute_val_post = (fun (self: i8) (out: i8) -> true);
    f_absolute_val
    =
    fun (self: i8) -> if self =. Core.Num.impl_i8__MIN then self else Core.Num.impl_i8__abs self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_MachineInteger_for_i16: t_MachineInteger i16 =
  {
    f_SIGNED = true;
    f_ZEROS = mk_i16 0;
    f_ONE = mk_i16 1;
    f_ONES = mk_i16 (-1);
    f_MIN = Core.Num.impl_i16__MIN;
    f_MAX = Core.Num.impl_i16__MAX;
    f_bits_pre = (fun (_: Prims.unit) -> true);
    f_bits_post = (fun (_: Prims.unit) (out: u32) -> true);
    f_bits = (fun (_: Prims.unit) -> Core.Num.impl_i16__BITS);
    f_wrapping_add_pre = (fun (self: i16) (rhs: i16) -> true);
    f_wrapping_add_post = (fun (self: i16) (rhs: i16) (out: i16) -> true);
    f_wrapping_add = (fun (self: i16) (rhs: i16) -> Core.Num.impl_i16__wrapping_add self rhs);
    f_wrapping_sub_pre = (fun (self: i16) (rhs: i16) -> true);
    f_wrapping_sub_post = (fun (self: i16) (rhs: i16) (out: i16) -> true);
    f_wrapping_sub = (fun (self: i16) (rhs: i16) -> Core.Num.impl_i16__wrapping_sub self rhs);
    f_overflowing_mul_pre = (fun (self: i16) (rhs: i16) -> true);
    f_overflowing_mul_post = (fun (self: i16) (rhs: i16) (out: i16) -> true);
    f_overflowing_mul
    =
    (fun (self: i16) (rhs: i16) -> (Core.Num.impl_i16__overflowing_mul self rhs)._1);
    f_saturating_add_pre = (fun (self: i16) (rhs: i16) -> true);
    f_saturating_add_post = (fun (self: i16) (rhs: i16) (out: i16) -> true);
    f_saturating_add = (fun (self: i16) (rhs: i16) -> Core.Num.impl_i16__saturating_add self rhs);
    f_saturating_sub_pre = (fun (self: i16) (rhs: i16) -> true);
    f_saturating_sub_post = (fun (self: i16) (rhs: i16) (out: i16) -> true);
    f_saturating_sub = (fun (self: i16) (rhs: i16) -> Core.Num.impl_i16__saturating_sub self rhs);
    f_absolute_diff_pre = (fun (self: i16) (rhs: i16) -> true);
    f_absolute_diff_post = (fun (self: i16) (rhs: i16) (out: i16) -> true);
    f_absolute_diff
    =
    (fun (self: i16) (rhs: i16) ->
        if self >. rhs
        then Core.Num.impl_i16__wrapping_sub self rhs
        else Core.Num.impl_i16__wrapping_sub rhs self);
    f_absolute_val_pre = (fun (self: i16) -> true);
    f_absolute_val_post = (fun (self: i16) (out: i16) -> true);
    f_absolute_val
    =
    fun (self: i16) -> if self =. Core.Num.impl_i16__MIN then self else Core.Num.impl_i16__abs self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_MachineInteger_for_i32: t_MachineInteger i32 =
  {
    f_SIGNED = true;
    f_ZEROS = mk_i32 0;
    f_ONE = mk_i32 1;
    f_ONES = mk_i32 (-1);
    f_MIN = Core.Num.impl_i32__MIN;
    f_MAX = Core.Num.impl_i32__MAX;
    f_bits_pre = (fun (_: Prims.unit) -> true);
    f_bits_post = (fun (_: Prims.unit) (out: u32) -> true);
    f_bits = (fun (_: Prims.unit) -> Core.Num.impl_i32__BITS);
    f_wrapping_add_pre = (fun (self: i32) (rhs: i32) -> true);
    f_wrapping_add_post = (fun (self: i32) (rhs: i32) (out: i32) -> true);
    f_wrapping_add = (fun (self: i32) (rhs: i32) -> Core.Num.impl_i32__wrapping_add self rhs);
    f_wrapping_sub_pre = (fun (self: i32) (rhs: i32) -> true);
    f_wrapping_sub_post = (fun (self: i32) (rhs: i32) (out: i32) -> true);
    f_wrapping_sub = (fun (self: i32) (rhs: i32) -> Core.Num.impl_i32__wrapping_sub self rhs);
    f_overflowing_mul_pre = (fun (self: i32) (rhs: i32) -> true);
    f_overflowing_mul_post = (fun (self: i32) (rhs: i32) (out: i32) -> true);
    f_overflowing_mul
    =
    (fun (self: i32) (rhs: i32) -> (Core.Num.impl_i32__overflowing_mul self rhs)._1);
    f_saturating_add_pre = (fun (self: i32) (rhs: i32) -> true);
    f_saturating_add_post = (fun (self: i32) (rhs: i32) (out: i32) -> true);
    f_saturating_add = (fun (self: i32) (rhs: i32) -> Core.Num.impl_i32__saturating_add self rhs);
    f_saturating_sub_pre = (fun (self: i32) (rhs: i32) -> true);
    f_saturating_sub_post = (fun (self: i32) (rhs: i32) (out: i32) -> true);
    f_saturating_sub = (fun (self: i32) (rhs: i32) -> Core.Num.impl_i32__saturating_sub self rhs);
    f_absolute_diff_pre = (fun (self: i32) (rhs: i32) -> true);
    f_absolute_diff_post = (fun (self: i32) (rhs: i32) (out: i32) -> true);
    f_absolute_diff
    =
    (fun (self: i32) (rhs: i32) ->
        if self >. rhs
        then Core.Num.impl_i32__wrapping_sub self rhs
        else Core.Num.impl_i32__wrapping_sub rhs self);
    f_absolute_val_pre = (fun (self: i32) -> true);
    f_absolute_val_post = (fun (self: i32) (out: i32) -> true);
    f_absolute_val
    =
    fun (self: i32) -> if self =. Core.Num.impl_i32__MIN then self else Core.Num.impl_i32__abs self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_MachineInteger_for_i64: t_MachineInteger i64 =
  {
    f_SIGNED = true;
    f_ZEROS = mk_i64 0;
    f_ONE = mk_i64 1;
    f_ONES = mk_i64 (-1);
    f_MIN = Core.Num.impl_i64__MIN;
    f_MAX = Core.Num.impl_i64__MAX;
    f_bits_pre = (fun (_: Prims.unit) -> true);
    f_bits_post = (fun (_: Prims.unit) (out: u32) -> true);
    f_bits = (fun (_: Prims.unit) -> Core.Num.impl_i64__BITS);
    f_wrapping_add_pre = (fun (self: i64) (rhs: i64) -> true);
    f_wrapping_add_post = (fun (self: i64) (rhs: i64) (out: i64) -> true);
    f_wrapping_add = (fun (self: i64) (rhs: i64) -> Core.Num.impl_i64__wrapping_add self rhs);
    f_wrapping_sub_pre = (fun (self: i64) (rhs: i64) -> true);
    f_wrapping_sub_post = (fun (self: i64) (rhs: i64) (out: i64) -> true);
    f_wrapping_sub = (fun (self: i64) (rhs: i64) -> Core.Num.impl_i64__wrapping_sub self rhs);
    f_overflowing_mul_pre = (fun (self: i64) (rhs: i64) -> true);
    f_overflowing_mul_post = (fun (self: i64) (rhs: i64) (out: i64) -> true);
    f_overflowing_mul
    =
    (fun (self: i64) (rhs: i64) -> (Core.Num.impl_i64__overflowing_mul self rhs)._1);
    f_saturating_add_pre = (fun (self: i64) (rhs: i64) -> true);
    f_saturating_add_post = (fun (self: i64) (rhs: i64) (out: i64) -> true);
    f_saturating_add = (fun (self: i64) (rhs: i64) -> Core.Num.impl_i64__saturating_add self rhs);
    f_saturating_sub_pre = (fun (self: i64) (rhs: i64) -> true);
    f_saturating_sub_post = (fun (self: i64) (rhs: i64) (out: i64) -> true);
    f_saturating_sub = (fun (self: i64) (rhs: i64) -> Core.Num.impl_i64__saturating_sub self rhs);
    f_absolute_diff_pre = (fun (self: i64) (rhs: i64) -> true);
    f_absolute_diff_post = (fun (self: i64) (rhs: i64) (out: i64) -> true);
    f_absolute_diff
    =
    (fun (self: i64) (rhs: i64) ->
        if self >. rhs
        then Core.Num.impl_i64__wrapping_sub self rhs
        else Core.Num.impl_i64__wrapping_sub rhs self);
    f_absolute_val_pre = (fun (self: i64) -> true);
    f_absolute_val_post = (fun (self: i64) (out: i64) -> true);
    f_absolute_val
    =
    fun (self: i64) -> if self =. Core.Num.impl_i64__MIN then self else Core.Num.impl_i64__abs self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_MachineInteger_for_i128: t_MachineInteger i128 =
  {
    f_SIGNED = true;
    f_ZEROS = mk_i128 0;
    f_ONE = mk_i128 1;
    f_ONES = mk_i128 (-1);
    f_MIN = Core.Num.impl_i128__MIN;
    f_MAX = Core.Num.impl_i128__MAX;
    f_bits_pre = (fun (_: Prims.unit) -> true);
    f_bits_post = (fun (_: Prims.unit) (out: u32) -> true);
    f_bits = (fun (_: Prims.unit) -> Core.Num.impl_i128__BITS);
    f_wrapping_add_pre = (fun (self: i128) (rhs: i128) -> true);
    f_wrapping_add_post = (fun (self: i128) (rhs: i128) (out: i128) -> true);
    f_wrapping_add = (fun (self: i128) (rhs: i128) -> Core.Num.impl_i128__wrapping_add self rhs);
    f_wrapping_sub_pre = (fun (self: i128) (rhs: i128) -> true);
    f_wrapping_sub_post = (fun (self: i128) (rhs: i128) (out: i128) -> true);
    f_wrapping_sub = (fun (self: i128) (rhs: i128) -> Core.Num.impl_i128__wrapping_sub self rhs);
    f_overflowing_mul_pre = (fun (self: i128) (rhs: i128) -> true);
    f_overflowing_mul_post = (fun (self: i128) (rhs: i128) (out: i128) -> true);
    f_overflowing_mul
    =
    (fun (self: i128) (rhs: i128) -> (Core.Num.impl_i128__overflowing_mul self rhs)._1);
    f_saturating_add_pre = (fun (self: i128) (rhs: i128) -> true);
    f_saturating_add_post = (fun (self: i128) (rhs: i128) (out: i128) -> true);
    f_saturating_add = (fun (self: i128) (rhs: i128) -> Core.Num.impl_i128__saturating_add self rhs);
    f_saturating_sub_pre = (fun (self: i128) (rhs: i128) -> true);
    f_saturating_sub_post = (fun (self: i128) (rhs: i128) (out: i128) -> true);
    f_saturating_sub = (fun (self: i128) (rhs: i128) -> Core.Num.impl_i128__saturating_sub self rhs);
    f_absolute_diff_pre = (fun (self: i128) (rhs: i128) -> true);
    f_absolute_diff_post = (fun (self: i128) (rhs: i128) (out: i128) -> true);
    f_absolute_diff
    =
    (fun (self: i128) (rhs: i128) ->
        if self >. rhs
        then Core.Num.impl_i128__wrapping_sub self rhs
        else Core.Num.impl_i128__wrapping_sub rhs self);
    f_absolute_val_pre = (fun (self: i128) -> true);
    f_absolute_val_post = (fun (self: i128) (out: i128) -> true);
    f_absolute_val
    =
    fun (self: i128) ->
      if self =. Core.Num.impl_i128__MIN then self else Core.Num.impl_i128__abs self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_MachineInteger_for_u8: t_MachineInteger u8 =
  {
    f_SIGNED = false;
    f_ZEROS = mk_u8 0;
    f_ONE = mk_u8 1;
    f_ONES = Core.Num.impl_u8__MAX;
    f_MIN = Core.Num.impl_u8__MIN;
    f_MAX = Core.Num.impl_u8__MAX;
    f_bits_pre = (fun (_: Prims.unit) -> true);
    f_bits_post = (fun (_: Prims.unit) (out: u32) -> true);
    f_bits = (fun (_: Prims.unit) -> Core.Num.impl_u8__BITS);
    f_wrapping_add_pre = (fun (self: u8) (rhs: u8) -> true);
    f_wrapping_add_post = (fun (self: u8) (rhs: u8) (out: u8) -> true);
    f_wrapping_add = (fun (self: u8) (rhs: u8) -> Core.Num.impl_u8__wrapping_add self rhs);
    f_wrapping_sub_pre = (fun (self: u8) (rhs: u8) -> true);
    f_wrapping_sub_post = (fun (self: u8) (rhs: u8) (out: u8) -> true);
    f_wrapping_sub = (fun (self: u8) (rhs: u8) -> Core.Num.impl_u8__wrapping_sub self rhs);
    f_overflowing_mul_pre = (fun (self: u8) (rhs: u8) -> true);
    f_overflowing_mul_post = (fun (self: u8) (rhs: u8) (out: u8) -> true);
    f_overflowing_mul
    =
    (fun (self: u8) (rhs: u8) -> (Core.Num.impl_u8__overflowing_mul self rhs)._1);
    f_saturating_add_pre = (fun (self: u8) (rhs: u8) -> true);
    f_saturating_add_post = (fun (self: u8) (rhs: u8) (out: u8) -> true);
    f_saturating_add = (fun (self: u8) (rhs: u8) -> Core.Num.impl_u8__saturating_add self rhs);
    f_saturating_sub_pre = (fun (self: u8) (rhs: u8) -> true);
    f_saturating_sub_post = (fun (self: u8) (rhs: u8) (out: u8) -> true);
    f_saturating_sub = (fun (self: u8) (rhs: u8) -> Core.Num.impl_u8__saturating_sub self rhs);
    f_absolute_diff_pre = (fun (self: u8) (rhs: u8) -> true);
    f_absolute_diff_post = (fun (self: u8) (rhs: u8) (out: u8) -> true);
    f_absolute_diff = (fun (self: u8) (rhs: u8) -> if self >. rhs then self -! rhs else rhs -! self);
    f_absolute_val_pre = (fun (self: u8) -> true);
    f_absolute_val_post = (fun (self: u8) (out: u8) -> true);
    f_absolute_val = fun (self: u8) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_MachineInteger_for_u16: t_MachineInteger u16 =
  {
    f_SIGNED = false;
    f_ZEROS = mk_u16 0;
    f_ONE = mk_u16 1;
    f_ONES = Core.Num.impl_u16__MAX;
    f_MIN = Core.Num.impl_u16__MIN;
    f_MAX = Core.Num.impl_u16__MAX;
    f_bits_pre = (fun (_: Prims.unit) -> true);
    f_bits_post = (fun (_: Prims.unit) (out: u32) -> true);
    f_bits = (fun (_: Prims.unit) -> Core.Num.impl_u16__BITS);
    f_wrapping_add_pre = (fun (self: u16) (rhs: u16) -> true);
    f_wrapping_add_post = (fun (self: u16) (rhs: u16) (out: u16) -> true);
    f_wrapping_add = (fun (self: u16) (rhs: u16) -> Core.Num.impl_u16__wrapping_add self rhs);
    f_wrapping_sub_pre = (fun (self: u16) (rhs: u16) -> true);
    f_wrapping_sub_post = (fun (self: u16) (rhs: u16) (out: u16) -> true);
    f_wrapping_sub = (fun (self: u16) (rhs: u16) -> Core.Num.impl_u16__wrapping_sub self rhs);
    f_overflowing_mul_pre = (fun (self: u16) (rhs: u16) -> true);
    f_overflowing_mul_post = (fun (self: u16) (rhs: u16) (out: u16) -> true);
    f_overflowing_mul
    =
    (fun (self: u16) (rhs: u16) -> (Core.Num.impl_u16__overflowing_mul self rhs)._1);
    f_saturating_add_pre = (fun (self: u16) (rhs: u16) -> true);
    f_saturating_add_post = (fun (self: u16) (rhs: u16) (out: u16) -> true);
    f_saturating_add = (fun (self: u16) (rhs: u16) -> Core.Num.impl_u16__saturating_add self rhs);
    f_saturating_sub_pre = (fun (self: u16) (rhs: u16) -> true);
    f_saturating_sub_post = (fun (self: u16) (rhs: u16) (out: u16) -> true);
    f_saturating_sub = (fun (self: u16) (rhs: u16) -> Core.Num.impl_u16__saturating_sub self rhs);
    f_absolute_diff_pre = (fun (self: u16) (rhs: u16) -> true);
    f_absolute_diff_post = (fun (self: u16) (rhs: u16) (out: u16) -> true);
    f_absolute_diff
    =
    (fun (self: u16) (rhs: u16) -> if self >. rhs then self -! rhs else rhs -! self);
    f_absolute_val_pre = (fun (self: u16) -> true);
    f_absolute_val_post = (fun (self: u16) (out: u16) -> true);
    f_absolute_val = fun (self: u16) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_MachineInteger_for_u32: t_MachineInteger u32 =
  {
    f_SIGNED = false;
    f_ZEROS = mk_u32 0;
    f_ONE = mk_u32 1;
    f_ONES = Core.Num.impl_u32__MAX;
    f_MIN = Core.Num.impl_u32__MIN;
    f_MAX = Core.Num.impl_u32__MAX;
    f_bits_pre = (fun (_: Prims.unit) -> true);
    f_bits_post = (fun (_: Prims.unit) (out: u32) -> true);
    f_bits = (fun (_: Prims.unit) -> Core.Num.impl_u32__BITS);
    f_wrapping_add_pre = (fun (self: u32) (rhs: u32) -> true);
    f_wrapping_add_post = (fun (self: u32) (rhs: u32) (out: u32) -> true);
    f_wrapping_add = (fun (self: u32) (rhs: u32) -> Core.Num.impl_u32__wrapping_add self rhs);
    f_wrapping_sub_pre = (fun (self: u32) (rhs: u32) -> true);
    f_wrapping_sub_post = (fun (self: u32) (rhs: u32) (out: u32) -> true);
    f_wrapping_sub = (fun (self: u32) (rhs: u32) -> Core.Num.impl_u32__wrapping_sub self rhs);
    f_overflowing_mul_pre = (fun (self: u32) (rhs: u32) -> true);
    f_overflowing_mul_post = (fun (self: u32) (rhs: u32) (out: u32) -> true);
    f_overflowing_mul
    =
    (fun (self: u32) (rhs: u32) -> (Core.Num.impl_u32__overflowing_mul self rhs)._1);
    f_saturating_add_pre = (fun (self: u32) (rhs: u32) -> true);
    f_saturating_add_post = (fun (self: u32) (rhs: u32) (out: u32) -> true);
    f_saturating_add = (fun (self: u32) (rhs: u32) -> Core.Num.impl_u32__saturating_add self rhs);
    f_saturating_sub_pre = (fun (self: u32) (rhs: u32) -> true);
    f_saturating_sub_post = (fun (self: u32) (rhs: u32) (out: u32) -> true);
    f_saturating_sub = (fun (self: u32) (rhs: u32) -> Core.Num.impl_u32__saturating_sub self rhs);
    f_absolute_diff_pre = (fun (self: u32) (rhs: u32) -> true);
    f_absolute_diff_post = (fun (self: u32) (rhs: u32) (out: u32) -> true);
    f_absolute_diff
    =
    (fun (self: u32) (rhs: u32) -> if self >. rhs then self -! rhs else rhs -! self);
    f_absolute_val_pre = (fun (self: u32) -> true);
    f_absolute_val_post = (fun (self: u32) (out: u32) -> true);
    f_absolute_val = fun (self: u32) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_MachineInteger_for_u64: t_MachineInteger u64 =
  {
    f_SIGNED = false;
    f_ZEROS = mk_u64 0;
    f_ONE = mk_u64 1;
    f_ONES = Core.Num.impl_u64__MAX;
    f_MIN = Core.Num.impl_u64__MIN;
    f_MAX = Core.Num.impl_u64__MAX;
    f_bits_pre = (fun (_: Prims.unit) -> true);
    f_bits_post = (fun (_: Prims.unit) (out: u32) -> true);
    f_bits = (fun (_: Prims.unit) -> Core.Num.impl_u64__BITS);
    f_wrapping_add_pre = (fun (self: u64) (rhs: u64) -> true);
    f_wrapping_add_post = (fun (self: u64) (rhs: u64) (out: u64) -> true);
    f_wrapping_add = (fun (self: u64) (rhs: u64) -> Core.Num.impl_u64__wrapping_add self rhs);
    f_wrapping_sub_pre = (fun (self: u64) (rhs: u64) -> true);
    f_wrapping_sub_post = (fun (self: u64) (rhs: u64) (out: u64) -> true);
    f_wrapping_sub = (fun (self: u64) (rhs: u64) -> Core.Num.impl_u64__wrapping_sub self rhs);
    f_overflowing_mul_pre = (fun (self: u64) (rhs: u64) -> true);
    f_overflowing_mul_post = (fun (self: u64) (rhs: u64) (out: u64) -> true);
    f_overflowing_mul
    =
    (fun (self: u64) (rhs: u64) -> (Core.Num.impl_u64__overflowing_mul self rhs)._1);
    f_saturating_add_pre = (fun (self: u64) (rhs: u64) -> true);
    f_saturating_add_post = (fun (self: u64) (rhs: u64) (out: u64) -> true);
    f_saturating_add = (fun (self: u64) (rhs: u64) -> Core.Num.impl_u64__saturating_add self rhs);
    f_saturating_sub_pre = (fun (self: u64) (rhs: u64) -> true);
    f_saturating_sub_post = (fun (self: u64) (rhs: u64) (out: u64) -> true);
    f_saturating_sub = (fun (self: u64) (rhs: u64) -> Core.Num.impl_u64__saturating_sub self rhs);
    f_absolute_diff_pre = (fun (self: u64) (rhs: u64) -> true);
    f_absolute_diff_post = (fun (self: u64) (rhs: u64) (out: u64) -> true);
    f_absolute_diff
    =
    (fun (self: u64) (rhs: u64) -> if self >. rhs then self -! rhs else rhs -! self);
    f_absolute_val_pre = (fun (self: u64) -> true);
    f_absolute_val_post = (fun (self: u64) (out: u64) -> true);
    f_absolute_val = fun (self: u64) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_MachineInteger_for_u128: t_MachineInteger u128 =
  {
    f_SIGNED = false;
    f_ZEROS = mk_u128 0;
    f_ONE = mk_u128 1;
    f_ONES = Core.Num.impl_u128__MAX;
    f_MIN = Core.Num.impl_u128__MIN;
    f_MAX = Core.Num.impl_u128__MAX;
    f_bits_pre = (fun (_: Prims.unit) -> true);
    f_bits_post = (fun (_: Prims.unit) (out: u32) -> true);
    f_bits = (fun (_: Prims.unit) -> Core.Num.impl_u128__BITS);
    f_wrapping_add_pre = (fun (self: u128) (rhs: u128) -> true);
    f_wrapping_add_post = (fun (self: u128) (rhs: u128) (out: u128) -> true);
    f_wrapping_add = (fun (self: u128) (rhs: u128) -> Core.Num.impl_u128__wrapping_add self rhs);
    f_wrapping_sub_pre = (fun (self: u128) (rhs: u128) -> true);
    f_wrapping_sub_post = (fun (self: u128) (rhs: u128) (out: u128) -> true);
    f_wrapping_sub = (fun (self: u128) (rhs: u128) -> Core.Num.impl_u128__wrapping_sub self rhs);
    f_overflowing_mul_pre = (fun (self: u128) (rhs: u128) -> true);
    f_overflowing_mul_post = (fun (self: u128) (rhs: u128) (out: u128) -> true);
    f_overflowing_mul
    =
    (fun (self: u128) (rhs: u128) -> (Core.Num.impl_u128__overflowing_mul self rhs)._1);
    f_saturating_add_pre = (fun (self: u128) (rhs: u128) -> true);
    f_saturating_add_post = (fun (self: u128) (rhs: u128) (out: u128) -> true);
    f_saturating_add = (fun (self: u128) (rhs: u128) -> Core.Num.impl_u128__saturating_add self rhs);
    f_saturating_sub_pre = (fun (self: u128) (rhs: u128) -> true);
    f_saturating_sub_post = (fun (self: u128) (rhs: u128) (out: u128) -> true);
    f_saturating_sub = (fun (self: u128) (rhs: u128) -> Core.Num.impl_u128__saturating_sub self rhs);
    f_absolute_diff_pre = (fun (self: u128) (rhs: u128) -> true);
    f_absolute_diff_post = (fun (self: u128) (rhs: u128) (out: u128) -> true);
    f_absolute_diff
    =
    (fun (self: u128) (rhs: u128) -> if self >. rhs then self -! rhs else rhs -! self);
    f_absolute_val_pre = (fun (self: u128) -> true);
    f_absolute_val_post = (fun (self: u128) (out: u128) -> true);
    f_absolute_val = fun (self: u128) -> self
  }
