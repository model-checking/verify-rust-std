module Core_models.Abstractions.Funarr
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

open FStar.FunctionalExtensionality    
type t_FunArray (n: u64) (t: Type0) = i:u64 {v i < v n} ^-> t

let impl_5__get (v_N: u64) (#v_T: Type0) (self: t_FunArray v_N v_T) (i: u64 {v i < v v_N}) : v_T = 
    self i

let impl_5__from_fn
    (v_N: u64)
    (#v_T: Type0)
    (f: (i: u64 {v i < v v_N}) -> v_T)
    : t_FunArray v_N v_T = on (i: u64 {v i < v v_N}) f

let impl_5__as_vec n #t (self: t_FunArray n t) = FStar.Seq.init (v n) (fun i -> self (mk_u64 i))

let rec impl_5__fold n #t #a (arr: t_FunArray n t) (init: a) (f: a -> t -> a): Tot a (decreases (v n)) = 
    match n with
    | MkInt 0 -> init
    | MkInt n -> 
        let acc: a = f init (arr (mk_u64 0)) in 
        let n = MkInt (n - 1) in
        impl_5__fold  n #t #a
                      (impl_5__from_fn n (fun i -> arr (i +. mk_u64 1)))
                      acc f

let impl_1
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Clone.t_Clone (t_FunArray v_N v_T) = { f_clone = (fun x -> x) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': v_N: u64 -> #v_T: Type0 -> {| i1: Core.Marker.t_Copy v_T |}
  -> Core.Marker.t_Copy (t_FunArray v_N v_T)

unfold
let impl
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Marker.t_Copy v_T)
     = impl' v_N #v_T #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': v_N: u64 -> #v_T: Type0 -> Core.Marker.t_StructuralPartialEq (t_FunArray v_N v_T)

unfold
let impl_3 (v_N: u64) (#v_T: Type0) = impl_3' v_N #v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': v_N: u64 -> #v_T: Type0 -> {| i1: Core.Cmp.t_PartialEq v_T v_T |}
  -> Core.Cmp.t_PartialEq (t_FunArray v_N v_T) (t_FunArray v_N v_T)

unfold
let impl_4
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Cmp.t_PartialEq v_T v_T)
     = impl_4' v_N #v_T #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': v_N: u64 -> #v_T: Type0 -> {| i1: Core.Cmp.t_Eq v_T |}
  -> Core.Cmp.t_Eq (t_FunArray v_N v_T)

unfold
let impl_2
      (v_N: u64)
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Cmp.t_Eq v_T)
     = impl_2' v_N #v_T #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11 (v_N: u64) (#v_T: Type0) : Core.Ops.Index.t_Index (t_FunArray v_N v_T) u64 =
  {
    f_Output = v_T;
    f_index_pre = (fun (self_: t_FunArray v_N v_T) (index: u64) -> index <. v_N);
    f_index_post = (fun (self: t_FunArray v_N v_T) (index: u64) (out: v_T) -> true);
    f_index = fun (self: t_FunArray v_N v_T) (index: u64) -> impl_5__get v_N #v_T self index
  }

let impl_6__pointwise
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Marker.t_Copy v_T)
      (self: t_FunArray (mk_u64 4) v_T)
    : t_FunArray (mk_u64 4) v_T =
  impl_5__from_fn (mk_u64 4)
    #v_T
    (fun i ->
        let i:u64 = i in
        match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 -> self.[ mk_u64 0 ] <: v_T
        | Rust_primitives.Integers.MkInt 1 -> self.[ mk_u64 1 ] <: v_T
        | Rust_primitives.Integers.MkInt 2 -> self.[ mk_u64 2 ] <: v_T
        | Rust_primitives.Integers.MkInt 3 -> self.[ mk_u64 3 ] <: v_T
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          v_T)

let impl_7__pointwise
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Marker.t_Copy v_T)
      (self: t_FunArray (mk_u64 8) v_T)
    : t_FunArray (mk_u64 8) v_T =
  impl_5__from_fn (mk_u64 8)
    #v_T
    (fun i ->
        let i:u64 = i in
        match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 -> self.[ mk_u64 0 ] <: v_T
        | Rust_primitives.Integers.MkInt 1 -> self.[ mk_u64 1 ] <: v_T
        | Rust_primitives.Integers.MkInt 2 -> self.[ mk_u64 2 ] <: v_T
        | Rust_primitives.Integers.MkInt 3 -> self.[ mk_u64 3 ] <: v_T
        | Rust_primitives.Integers.MkInt 4 -> self.[ mk_u64 4 ] <: v_T
        | Rust_primitives.Integers.MkInt 5 -> self.[ mk_u64 5 ] <: v_T
        | Rust_primitives.Integers.MkInt 6 -> self.[ mk_u64 6 ] <: v_T
        | Rust_primitives.Integers.MkInt 7 -> self.[ mk_u64 7 ] <: v_T
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          v_T)

let impl_8__pointwise
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Marker.t_Copy v_T)
      (self: t_FunArray (mk_u64 16) v_T)
    : t_FunArray (mk_u64 16) v_T =
  impl_5__from_fn (mk_u64 16)
    #v_T
    (fun i ->
        let i:u64 = i in
        match i <: u64 with
        | Rust_primitives.Integers.MkInt 0 -> self.[ mk_u64 0 ] <: v_T
        | Rust_primitives.Integers.MkInt 1 -> self.[ mk_u64 1 ] <: v_T
        | Rust_primitives.Integers.MkInt 2 -> self.[ mk_u64 2 ] <: v_T
        | Rust_primitives.Integers.MkInt 3 -> self.[ mk_u64 3 ] <: v_T
        | Rust_primitives.Integers.MkInt 4 -> self.[ mk_u64 4 ] <: v_T
        | Rust_primitives.Integers.MkInt 5 -> self.[ mk_u64 5 ] <: v_T
        | Rust_primitives.Integers.MkInt 6 -> self.[ mk_u64 6 ] <: v_T
        | Rust_primitives.Integers.MkInt 7 -> self.[ mk_u64 7 ] <: v_T
        | Rust_primitives.Integers.MkInt 8 -> self.[ mk_u64 8 ] <: v_T
        | Rust_primitives.Integers.MkInt 9 -> self.[ mk_u64 9 ] <: v_T
        | Rust_primitives.Integers.MkInt 10 -> self.[ mk_u64 10 ] <: v_T
        | Rust_primitives.Integers.MkInt 11 -> self.[ mk_u64 11 ] <: v_T
        | Rust_primitives.Integers.MkInt 12 -> self.[ mk_u64 12 ] <: v_T
        | Rust_primitives.Integers.MkInt 13 -> self.[ mk_u64 13 ] <: v_T
        | Rust_primitives.Integers.MkInt 14 -> self.[ mk_u64 14 ] <: v_T
        | Rust_primitives.Integers.MkInt 15 -> self.[ mk_u64 15 ] <: v_T
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
          <:
          v_T)
