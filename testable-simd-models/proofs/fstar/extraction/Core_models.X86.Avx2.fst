module Core_models.X86.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Core_models.Abstractions.Bit in
  let open Core_models.Abstractions.Bitvec in
  let open Core_models.Abstractions.Bitvec.Int_vec_interp in
  let open Core_models.Abstractions.Funarr in
  let open Core_models.Abstractions.Simd in
  ()

let phaddw (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 4 <: bool
        then
          Core.Num.impl_i16__wrapping_add (a.[ mk_u64 2 *! i <: u64 ] <: i16)
            (a.[ (mk_u64 2 *! i <: u64) +! mk_u64 1 <: u64 ] <: i16)
          <:
          i16
        else
          if i <. mk_u64 8 <: bool
          then
            Core.Num.impl_i16__wrapping_add (b.[ mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64 ] <: i16)
              (b.[ (mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i16)
            <:
            i16
          else
            if i <. mk_u64 12 <: bool
            then
              Core.Num.impl_i16__wrapping_add (a.[ mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64 ]
                  <:
                  i16)
                (a.[ (mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i16)
              <:
              i16
            else
              Core.Num.impl_i16__wrapping_add (b.[ mk_u64 2 *! (i -! mk_u64 8 <: u64) <: u64 ]
                  <:
                  i16)
                (b.[ (mk_u64 2 *! (i -! mk_u64 8 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i16)
              <:
              i16)

let phaddd (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 2 <: bool
        then
          Core.Num.impl_i32__wrapping_add (a.[ mk_u64 2 *! i <: u64 ] <: i32)
            (a.[ (mk_u64 2 *! i <: u64) +! mk_u64 1 <: u64 ] <: i32)
          <:
          i32
        else
          if i <. mk_u64 4 <: bool
          then
            Core.Num.impl_i32__wrapping_add (b.[ mk_u64 2 *! (i -! mk_u64 2 <: u64) <: u64 ] <: i32)
              (b.[ (mk_u64 2 *! (i -! mk_u64 2 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i32)
            <:
            i32
          else
            if i <. mk_u64 6 <: bool
            then
              Core.Num.impl_i32__wrapping_add (a.[ mk_u64 2 *! (i -! mk_u64 2 <: u64) <: u64 ]
                  <:
                  i32)
                (a.[ (mk_u64 2 *! (i -! mk_u64 2 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i32)
              <:
              i32
            else
              Core.Num.impl_i32__wrapping_add (b.[ mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64 ]
                  <:
                  i32)
                (b.[ (mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i32)
              <:
              i32)

let phaddsw (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 4 <: bool
        then
          Core.Num.impl_i16__saturating_add (a.[ mk_u64 2 *! i <: u64 ] <: i16)
            (a.[ (mk_u64 2 *! i <: u64) +! mk_u64 1 <: u64 ] <: i16)
          <:
          i16
        else
          if i <. mk_u64 8 <: bool
          then
            Core.Num.impl_i16__saturating_add (b.[ mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64 ]
                <:
                i16)
              (b.[ (mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i16)
            <:
            i16
          else
            if i <. mk_u64 12 <: bool
            then
              Core.Num.impl_i16__saturating_add (a.[ mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64 ]
                  <:
                  i16)
                (a.[ (mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i16)
              <:
              i16
            else
              Core.Num.impl_i16__saturating_add (b.[ mk_u64 2 *! (i -! mk_u64 8 <: u64) <: u64 ]
                  <:
                  i16)
                (b.[ (mk_u64 2 *! (i -! mk_u64 8 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i16)
              <:
              i16)

let phsubw (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 4 <: bool
        then
          Core.Num.impl_i16__wrapping_sub (a.[ mk_u64 2 *! i <: u64 ] <: i16)
            (a.[ (mk_u64 2 *! i <: u64) +! mk_u64 1 <: u64 ] <: i16)
          <:
          i16
        else
          if i <. mk_u64 8 <: bool
          then
            Core.Num.impl_i16__wrapping_sub (b.[ mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64 ] <: i16)
              (b.[ (mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i16)
            <:
            i16
          else
            if i <. mk_u64 12 <: bool
            then
              Core.Num.impl_i16__wrapping_sub (a.[ mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64 ]
                  <:
                  i16)
                (a.[ (mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i16)
              <:
              i16
            else
              Core.Num.impl_i16__wrapping_sub (b.[ mk_u64 2 *! (i -! mk_u64 8 <: u64) <: u64 ]
                  <:
                  i16)
                (b.[ (mk_u64 2 *! (i -! mk_u64 8 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i16)
              <:
              i16)

let phsubd (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 2 <: bool
        then
          Core.Num.impl_i32__wrapping_sub (a.[ mk_u64 2 *! i <: u64 ] <: i32)
            (a.[ (mk_u64 2 *! i <: u64) +! mk_u64 1 <: u64 ] <: i32)
          <:
          i32
        else
          if i <. mk_u64 4 <: bool
          then
            Core.Num.impl_i32__wrapping_sub (b.[ mk_u64 2 *! (i -! mk_u64 2 <: u64) <: u64 ] <: i32)
              (b.[ (mk_u64 2 *! (i -! mk_u64 2 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i32)
            <:
            i32
          else
            if i <. mk_u64 6 <: bool
            then
              Core.Num.impl_i32__wrapping_sub (a.[ mk_u64 2 *! (i -! mk_u64 2 <: u64) <: u64 ]
                  <:
                  i32)
                (a.[ (mk_u64 2 *! (i -! mk_u64 2 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i32)
              <:
              i32
            else
              Core.Num.impl_i32__wrapping_sub (b.[ mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64 ]
                  <:
                  i32)
                (b.[ (mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i32)
              <:
              i32)

let phsubsw (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 4 <: bool
        then
          Core.Num.impl_i16__saturating_sub (a.[ mk_u64 2 *! i <: u64 ] <: i16)
            (a.[ (mk_u64 2 *! i <: u64) +! mk_u64 1 <: u64 ] <: i16)
          <:
          i16
        else
          if i <. mk_u64 8 <: bool
          then
            Core.Num.impl_i16__saturating_sub (b.[ mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64 ]
                <:
                i16)
              (b.[ (mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i16)
            <:
            i16
          else
            if i <. mk_u64 12 <: bool
            then
              Core.Num.impl_i16__saturating_sub (a.[ mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64 ]
                  <:
                  i16)
                (a.[ (mk_u64 2 *! (i -! mk_u64 4 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i16)
              <:
              i16
            else
              Core.Num.impl_i16__saturating_sub (b.[ mk_u64 2 *! (i -! mk_u64 8 <: u64) <: u64 ]
                  <:
                  i16)
                (b.[ (mk_u64 2 *! (i -! mk_u64 8 <: u64) <: u64) +! mk_u64 1 <: u64 ] <: i16)
              <:
              i16)

let pmaddwd (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        ((cast (a.[ mk_u64 2 *! i <: u64 ] <: i16) <: i32) *!
          (cast (b.[ mk_u64 2 *! i <: u64 ] <: i16) <: i32)
          <:
          i32) +!
        ((cast (a.[ (mk_u64 2 *! i <: u64) +! mk_u64 1 <: u64 ] <: i16) <: i32) *!
          (cast (b.[ (mk_u64 2 *! i <: u64) +! mk_u64 1 <: u64 ] <: i16) <: i32)
          <:
          i32)
        <:
        i32)

let pmaddubsw (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        Core.Num.impl_i16__saturating_add ((cast (cast (a.[ mk_u64 2 *! i <: u64 ] <: u8) <: u16)
              <:
              i16) *!
            (cast (cast (b.[ mk_u64 2 *! i <: u64 ] <: u8) <: i8) <: i16)
            <:
            i16)
          ((cast (cast (a.[ (mk_u64 2 *! i <: u64) +! mk_u64 1 <: u64 ] <: u8) <: u16) <: i16) *!
            (cast (cast (b.[ (mk_u64 2 *! i <: u64) +! mk_u64 1 <: u64 ] <: u8) <: i8) <: i16)
            <:
            i16)
        <:
        i16)

let packsswb (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 32)
    #i8
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 8 <: bool
        then
          if (a.[ i ] <: i16) >. (cast (Core.Num.impl_i8__MAX <: i8) <: i16) <: bool
          then Core.Num.impl_i8__MAX
          else
            if (a.[ i ] <: i16) <. (cast (Core.Num.impl_i8__MIN <: i8) <: i16) <: bool
            then Core.Num.impl_i8__MIN
            else cast (a.[ i ] <: i16) <: i8
        else
          if i <. mk_u64 16 <: bool
          then
            if
              (b.[ i -! mk_u64 8 <: u64 ] <: i16) >. (cast (Core.Num.impl_i8__MAX <: i8) <: i16)
              <:
              bool
            then Core.Num.impl_i8__MAX
            else
              if
                (b.[ i -! mk_u64 8 <: u64 ] <: i16) <. (cast (Core.Num.impl_i8__MIN <: i8) <: i16)
                <:
                bool
              then Core.Num.impl_i8__MIN
              else cast (b.[ i -! mk_u64 8 <: u64 ] <: i16) <: i8
          else
            if i <. mk_u64 24 <: bool
            then
              if
                (a.[ i -! mk_u64 8 <: u64 ] <: i16) >. (cast (Core.Num.impl_i8__MAX <: i8) <: i16)
                <:
                bool
              then Core.Num.impl_i8__MAX
              else
                if
                  (a.[ i -! mk_u64 8 <: u64 ] <: i16) <. (cast (Core.Num.impl_i8__MIN <: i8) <: i16)
                  <:
                  bool
                then Core.Num.impl_i8__MIN
                else cast (a.[ i -! mk_u64 8 <: u64 ] <: i16) <: i8
            else
              if
                (b.[ i -! mk_u64 16 <: u64 ] <: i16) >. (cast (Core.Num.impl_i8__MAX <: i8) <: i16)
                <:
                bool
              then Core.Num.impl_i8__MAX
              else
                if
                  (b.[ i -! mk_u64 16 <: u64 ] <: i16) <.
                  (cast (Core.Num.impl_i8__MIN <: i8) <: i16)
                  <:
                  bool
                then Core.Num.impl_i8__MIN
                else cast (b.[ i -! mk_u64 16 <: u64 ] <: i16) <: i8)

let packssdw (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 4 <: bool
        then
          if (a.[ i ] <: i32) >. (cast (Core.Num.impl_i16__MAX <: i16) <: i32) <: bool
          then Core.Num.impl_i16__MAX
          else
            if (a.[ i ] <: i32) <. (cast (Core.Num.impl_i16__MIN <: i16) <: i32) <: bool
            then Core.Num.impl_i16__MIN
            else cast (a.[ i ] <: i32) <: i16
        else
          if i <. mk_u64 8 <: bool
          then
            if
              (b.[ i -! mk_u64 4 <: u64 ] <: i32) >. (cast (Core.Num.impl_i16__MAX <: i16) <: i32)
              <:
              bool
            then Core.Num.impl_i16__MAX
            else
              if
                (b.[ i -! mk_u64 4 <: u64 ] <: i32) <. (cast (Core.Num.impl_i16__MIN <: i16) <: i32)
                <:
                bool
              then Core.Num.impl_i16__MIN
              else cast (b.[ i -! mk_u64 4 <: u64 ] <: i32) <: i16
          else
            if i <. mk_u64 12 <: bool
            then
              if
                (a.[ i -! mk_u64 4 <: u64 ] <: i32) >. (cast (Core.Num.impl_i16__MAX <: i16) <: i32)
                <:
                bool
              then Core.Num.impl_i16__MAX
              else
                if
                  (a.[ i -! mk_u64 4 <: u64 ] <: i32) <.
                  (cast (Core.Num.impl_i16__MIN <: i16) <: i32)
                  <:
                  bool
                then Core.Num.impl_i16__MIN
                else cast (a.[ i -! mk_u64 4 <: u64 ] <: i32) <: i16
            else
              if
                (b.[ i -! mk_u64 8 <: u64 ] <: i32) >. (cast (Core.Num.impl_i16__MAX <: i16) <: i32)
                <:
                bool
              then Core.Num.impl_i16__MAX
              else
                if
                  (b.[ i -! mk_u64 8 <: u64 ] <: i32) <.
                  (cast (Core.Num.impl_i16__MIN <: i16) <: i32)
                  <:
                  bool
                then Core.Num.impl_i16__MIN
                else cast (b.[ i -! mk_u64 8 <: u64 ] <: i32) <: i16)

let packuswb (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 32)
    #u8
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 8 <: bool
        then
          if (a.[ i ] <: i16) >. (cast (Core.Num.impl_u8__MAX <: u8) <: i16) <: bool
          then Core.Num.impl_u8__MAX
          else
            if (a.[ i ] <: i16) <. (cast (Core.Num.impl_u8__MIN <: u8) <: i16) <: bool
            then Core.Num.impl_u8__MIN
            else cast (a.[ i ] <: i16) <: u8
        else
          if i <. mk_u64 16 <: bool
          then
            if
              (b.[ i -! mk_u64 8 <: u64 ] <: i16) >. (cast (Core.Num.impl_u8__MAX <: u8) <: i16)
              <:
              bool
            then Core.Num.impl_u8__MAX
            else
              if
                (b.[ i -! mk_u64 8 <: u64 ] <: i16) <. (cast (Core.Num.impl_u8__MIN <: u8) <: i16)
                <:
                bool
              then Core.Num.impl_u8__MIN
              else cast (b.[ i -! mk_u64 8 <: u64 ] <: i16) <: u8
          else
            if i <. mk_u64 24 <: bool
            then
              if
                (a.[ i -! mk_u64 8 <: u64 ] <: i16) >. (cast (Core.Num.impl_u8__MAX <: u8) <: i16)
                <:
                bool
              then Core.Num.impl_u8__MAX
              else
                if
                  (a.[ i -! mk_u64 8 <: u64 ] <: i16) <. (cast (Core.Num.impl_u8__MIN <: u8) <: i16)
                  <:
                  bool
                then Core.Num.impl_u8__MIN
                else cast (a.[ i -! mk_u64 8 <: u64 ] <: i16) <: u8
            else
              if
                (b.[ i -! mk_u64 16 <: u64 ] <: i16) >. (cast (Core.Num.impl_u8__MAX <: u8) <: i16)
                <:
                bool
              then Core.Num.impl_u8__MAX
              else
                if
                  (b.[ i -! mk_u64 16 <: u64 ] <: i16) <.
                  (cast (Core.Num.impl_u8__MIN <: u8) <: i16)
                  <:
                  bool
                then Core.Num.impl_u8__MIN
                else cast (b.[ i -! mk_u64 16 <: u64 ] <: i16) <: u8)

let packusdw (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #u16
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 4 <: bool
        then
          if (a.[ i ] <: i32) >. (cast (Core.Num.impl_u16__MAX <: u16) <: i32) <: bool
          then Core.Num.impl_u16__MAX
          else
            if (a.[ i ] <: i32) <. (cast (Core.Num.impl_u16__MIN <: u16) <: i32) <: bool
            then Core.Num.impl_u16__MIN
            else cast (a.[ i ] <: i32) <: u16
        else
          if i <. mk_u64 8 <: bool
          then
            if
              (b.[ i -! mk_u64 4 <: u64 ] <: i32) >. (cast (Core.Num.impl_u16__MAX <: u16) <: i32)
              <:
              bool
            then Core.Num.impl_u16__MAX
            else
              if
                (b.[ i -! mk_u64 4 <: u64 ] <: i32) <. (cast (Core.Num.impl_u16__MIN <: u16) <: i32)
                <:
                bool
              then Core.Num.impl_u16__MIN
              else cast (b.[ i -! mk_u64 4 <: u64 ] <: i32) <: u16
          else
            if i <. mk_u64 12 <: bool
            then
              if
                (a.[ i -! mk_u64 4 <: u64 ] <: i32) >. (cast (Core.Num.impl_u16__MAX <: u16) <: i32)
                <:
                bool
              then Core.Num.impl_u16__MAX
              else
                if
                  (a.[ i -! mk_u64 4 <: u64 ] <: i32) <.
                  (cast (Core.Num.impl_u16__MIN <: u16) <: i32)
                  <:
                  bool
                then Core.Num.impl_u16__MIN
                else cast (a.[ i -! mk_u64 4 <: u64 ] <: i32) <: u16
            else
              if
                (b.[ i -! mk_u64 8 <: u64 ] <: i32) >. (cast (Core.Num.impl_u16__MAX <: u16) <: i32)
                <:
                bool
              then Core.Num.impl_u16__MAX
              else
                if
                  (b.[ i -! mk_u64 8 <: u64 ] <: i32) <.
                  (cast (Core.Num.impl_u16__MIN <: u16) <: i32)
                  <:
                  bool
                then Core.Num.impl_u16__MIN
                else cast (b.[ i -! mk_u64 8 <: u64 ] <: i32) <: u16)

let psignb (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 32)
    #i8
    (fun i ->
        let i:u64 = i in
        if (b.[ i ] <: i8) <. mk_i8 0 <: bool
        then
          if (a.[ i ] <: i8) =. Core.Num.impl_i8__MIN <: bool
          then a.[ i ] <: i8
          else Core.Ops.Arith.f_neg (a.[ i ] <: i8) <: i8
        else if (b.[ i ] <: i8) >. mk_i8 0 <: bool then a.[ i ] <: i8 else mk_i8 0)

let psignw (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        if (b.[ i ] <: i16) <. mk_i16 0 <: bool
        then
          if (a.[ i ] <: i16) =. Core.Num.impl_i16__MIN <: bool
          then a.[ i ] <: i16
          else Core.Ops.Arith.f_neg (a.[ i ] <: i16) <: i16
        else if (b.[ i ] <: i16) >. mk_i16 0 <: bool then a.[ i ] <: i16 else mk_i16 0)

let psignd (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if (b.[ i ] <: i32) <. mk_i32 0 <: bool
        then
          if (a.[ i ] <: i32) =. Core.Num.impl_i32__MIN <: bool
          then a.[ i ] <: i32
          else Core.Ops.Arith.f_neg (a.[ i ] <: i32) <: i32
        else if (b.[ i ] <: i32) >. mk_i32 0 <: bool then a.[ i ] <: i32 else mk_i32 0)

let psllw
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      (count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  let (count4: u64):u64 = cast (cast (count.[ mk_u64 0 ] <: i16) <: u16) <: u64 in
  let (count3: u64):u64 = (cast (cast (count.[ mk_u64 1 ] <: i16) <: u16) <: u64) *! mk_u64 65536 in
  let (count2: u64):u64 =
    (cast (cast (count.[ mk_u64 2 ] <: i16) <: u16) <: u64) *! mk_u64 4294967296
  in
  let (count1: u64):u64 =
    (cast (cast (count.[ mk_u64 3 ] <: i16) <: u16) <: u64) *! mk_u64 281474976710656
  in
  let count:u64 = ((count1 +! count2 <: u64) +! count3 <: u64) +! count4 in
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        if count >. mk_u64 15 <: bool
        then mk_i16 0
        else cast ((cast (a.[ i ] <: i16) <: u16) <<! count <: u16) <: i16)

let pslld
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      (count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  let (count: u64):u64 =
    ((cast (cast (count.[ mk_u64 1 ] <: i32) <: u32) <: u64) *! mk_u64 4294967296 <: u64) +!
    (cast (cast (count.[ mk_u64 0 ] <: i32) <: u32) <: u64)
  in
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if count >. mk_u64 31 <: bool
        then mk_i32 0
        else cast ((cast (a.[ i ] <: i32) <: u32) <<! count <: u32) <: i32)

let psllq
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      (count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  let (count: u64):u64 = cast (count.[ mk_u64 0 ] <: i64) <: u64 in
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        if count >. mk_u64 63 <: bool
        then mk_i64 0
        else cast ((cast (a.[ i ] <: i64) <: u64) <<! count <: u64) <: i64)

let psllvd (a count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i32
    (fun i ->
        let i:u64 = i in
        if ((count.[ i ] <: i32) >. mk_i32 31 <: bool) || ((count.[ i ] <: i32) <. mk_i32 0 <: bool)
        then mk_i32 0
        else cast ((cast (a.[ i ] <: i32) <: u32) <<! (count.[ i ] <: i32) <: u32) <: i32)

let psllvd256 (a count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if ((count.[ i ] <: i32) >. mk_i32 31 <: bool) || ((count.[ i ] <: i32) <. mk_i32 0 <: bool)
        then mk_i32 0
        else cast ((cast (a.[ i ] <: i32) <: u32) <<! (count.[ i ] <: i32) <: u32) <: i32)

let psllvq (a count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
    #i64
    (fun i ->
        let i:u64 = i in
        if ((count.[ i ] <: i64) >. mk_i64 63 <: bool) || ((count.[ i ] <: i64) <. mk_i64 0 <: bool)
        then mk_i64 0
        else cast ((cast (a.[ i ] <: i64) <: u64) <<! (count.[ i ] <: i64) <: u64) <: i64)

let psllvq256 (a count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        if ((count.[ i ] <: i64) >. mk_i64 63 <: bool) || ((count.[ i ] <: i64) <. mk_i64 0 <: bool)
        then mk_i64 0
        else cast ((cast (a.[ i ] <: i64) <: u64) <<! (count.[ i ] <: i64) <: u64) <: i64)

let psraw
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      (count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  let (count: u64):u64 =
    ((((cast (cast (count.[ mk_u64 3 ] <: i16) <: u16) <: u64) *! mk_u64 281474976710656 <: u64) +!
        ((cast (cast (count.[ mk_u64 2 ] <: i16) <: u16) <: u64) *! mk_u64 4294967296 <: u64)
        <:
        u64) +!
      ((cast (cast (count.[ mk_u64 1 ] <: i16) <: u16) <: u64) *! mk_u64 65536 <: u64)
      <:
      u64) +!
    (cast (cast (count.[ mk_u64 0 ] <: i16) <: u16) <: u64)
  in
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        if count >. mk_u64 15 <: bool
        then if (a.[ i ] <: i16) <. mk_i16 0 <: bool then mk_i16 (-1) else mk_i16 0
        else (a.[ i ] <: i16) >>! count <: i16)

let psrad
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      (count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  let (count: u64):u64 =
    ((cast (cast (count.[ mk_u64 1 ] <: i32) <: u32) <: u64) *! mk_u64 4294967296 <: u64) +!
    (cast (cast (count.[ mk_u64 0 ] <: i32) <: u32) <: u64)
  in
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if count >. mk_u64 31 <: bool
        then if (a.[ i ] <: i32) <. mk_i32 0 <: bool then mk_i32 (-1) else mk_i32 0
        else (a.[ i ] <: i32) <<! count <: i32)

let psravd (a count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i32
    (fun i ->
        let i:u64 = i in
        if ((count.[ i ] <: i32) >. mk_i32 31 <: bool) || ((count.[ i ] <: i32) <. mk_i32 0 <: bool)
        then if (a.[ i ] <: i32) <. mk_i32 0 <: bool then mk_i32 (-1) else mk_i32 0
        else (a.[ i ] <: i32) >>! (count.[ i ] <: i32) <: i32)

let psravd256 (a count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  let _:(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 &
    Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32) =
    (match a <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 with
      | tmp ->
        let _:Prims.unit =
          Std.Io.Stdio.e_eprint (Core.Fmt.impl_4__new_v1_formatted ((let list =
                      ["[src/x86/avx2.rs:446:5] a = "; "\n"]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                    Rust_primitives.Hax.array_of_list 2 list)
                  <:
                  t_Slice string)
                ((let list =
                      [
                        Core.Fmt.Rt.impl_1__new_debug #(Core_models.Abstractions.Funarr.t_FunArray
                              (mk_u64 8) i32)
                          tmp
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list)
                  <:
                  t_Slice Core.Fmt.Rt.t_Argument)
                ((let list =
                      [
                        Core.Fmt.Rt.impl_Placeholder__new (mk_usize 0)
                          (mk_u32 3766485024)
                          (Core.Fmt.Rt.Count_Implied <: Core.Fmt.Rt.t_Count)
                          (Core.Fmt.Rt.Count_Implied <: Core.Fmt.Rt.t_Count)
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list)
                  <:
                  t_Slice Core.Fmt.Rt.t_Placeholder)
                (Core.Fmt.Rt.impl_UnsafeArg__new () <: Core.Fmt.Rt.t_UnsafeArg)
              <:
              Core.Fmt.t_Arguments)
        in
        let _:Prims.unit = () in
        tmp),
    (match count <: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 with
      | tmp ->
        let _:Prims.unit =
          Std.Io.Stdio.e_eprint (Core.Fmt.impl_4__new_v1_formatted ((let list =
                      ["[src/x86/avx2.rs:446:5] count = "; "\n"]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                    Rust_primitives.Hax.array_of_list 2 list)
                  <:
                  t_Slice string)
                ((let list =
                      [
                        Core.Fmt.Rt.impl_1__new_debug #(Core_models.Abstractions.Funarr.t_FunArray
                              (mk_u64 8) i32)
                          tmp
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list)
                  <:
                  t_Slice Core.Fmt.Rt.t_Argument)
                ((let list =
                      [
                        Core.Fmt.Rt.impl_Placeholder__new (mk_usize 0)
                          (mk_u32 3766485024)
                          (Core.Fmt.Rt.Count_Implied <: Core.Fmt.Rt.t_Count)
                          (Core.Fmt.Rt.Count_Implied <: Core.Fmt.Rt.t_Count)
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list)
                  <:
                  t_Slice Core.Fmt.Rt.t_Placeholder)
                (Core.Fmt.Rt.impl_UnsafeArg__new () <: Core.Fmt.Rt.t_UnsafeArg)
              <:
              Core.Fmt.t_Arguments)
        in
        let _:Prims.unit = () in
        tmp)
    <:
    (Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 &
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
  in
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if ((count.[ i ] <: i32) >. mk_i32 31 <: bool) || ((count.[ i ] <: i32) <. mk_i32 0 <: bool)
        then if (a.[ i ] <: i32) <. mk_i32 0 <: bool then mk_i32 (-1) else mk_i32 0
        else (a.[ i ] <: i32) >>! (count.[ i ] <: i32) <: i32)

let psrlw
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      (count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
  let (count: u64):u64 =
    ((((cast (cast (count.[ mk_u64 3 ] <: i16) <: u16) <: u64) *! mk_u64 281474976710656 <: u64) +!
        ((cast (cast (count.[ mk_u64 2 ] <: i16) <: u16) <: u64) *! mk_u64 4294967296 <: u64)
        <:
        u64) +!
      ((cast (cast (count.[ mk_u64 1 ] <: i16) <: u16) <: u64) *! mk_u64 65536 <: u64)
      <:
      u64) +!
    (cast (cast (count.[ mk_u64 0 ] <: i16) <: u16) <: u64)
  in
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
    #i16
    (fun i ->
        let i:u64 = i in
        if count >. mk_u64 15 <: bool
        then mk_i16 0
        else cast ((cast (a.[ i ] <: i16) <: u16) >>! count <: u16) <: i16)

let psrld
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      (count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  let (count: u64):u64 =
    ((cast (cast (count.[ mk_u64 1 ] <: i32) <: u32) <: u64) *! mk_u64 4294967296 <: u64) +!
    (cast (cast (count.[ mk_u64 0 ] <: i32) <: u32) <: u64)
  in
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if count >. mk_u64 31 <: bool
        then mk_i32 0
        else cast ((cast (a.[ i ] <: i32) <: u32) >>! count <: u32) <: i32)

let psrlq
      (a: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      (count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  let (count: u64):u64 = cast (count.[ mk_u64 0 ] <: i64) <: u64 in
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        if count >. mk_u64 63 <: bool
        then mk_i64 0
        else cast ((cast (a.[ i ] <: i64) <: u64) >>! count <: u64) <: i64)

let psrlvd (a count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i32
    (fun i ->
        let i:u64 = i in
        if ((count.[ i ] <: i32) >. mk_i32 31 <: bool) || ((count.[ i ] <: i32) <. mk_i32 0 <: bool)
        then mk_i32 0
        else cast ((cast (a.[ i ] <: i32) <: u32) >>! (count.[ i ] <: i32) <: u32) <: i32)

let psrlvd256 (a count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #i32
    (fun i ->
        let i:u64 = i in
        if ((count.[ i ] <: i32) >. mk_i32 31 <: bool) || ((count.[ i ] <: i32) <. mk_i32 0 <: bool)
        then mk_i32 0
        else cast ((cast (a.[ i ] <: i32) <: u32) >>! (count.[ i ] <: i32) <: u32) <: i32)

let psrlvq (a count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
    #i64
    (fun i ->
        let i:u64 = i in
        if ((count.[ i ] <: i64) >. mk_i64 63 <: bool) || ((count.[ i ] <: i64) <. mk_i64 0 <: bool)
        then mk_i64 0
        else cast ((cast (a.[ i ] <: i64) <: u64) >>! (count.[ i ] <: i64) <: u64) <: i64)

let psrlvq256 (a count: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        if ((count.[ i ] <: i64) >. mk_i64 63 <: bool) || ((count.[ i ] <: i64) <. mk_i64 0 <: bool)
        then mk_i64 0
        else cast ((cast (a.[ i ] <: i64) <: u64) >>! (count.[ i ] <: i64) <: u64) <: i64)

let pshufb (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 32)
    #u8
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 16 <: bool
        then
          if (b.[ i ] <: u8) >. mk_u8 127 <: bool
          then mk_u8 0
          else
            let (index: u64):u64 = cast ((b.[ i ] <: u8) %! mk_u8 16 <: u8) <: u64 in
            a.[ index ]
        else
          if (b.[ i ] <: u8) >. mk_u8 127 <: bool
          then mk_u8 0
          else
            let (index: u64):u64 = cast ((b.[ i ] <: u8) %! mk_u8 16 <: u8) <: u64 in
            a.[ index +! mk_u64 16 <: u64 ])

let permd (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32 =
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
    #u32
    (fun i ->
        let i:u64 = i in
        let id:u32 = (b.[ i ] <: u32) %! mk_u32 8 in
        a.[ cast (id <: u32) <: u64 ])

let vperm2i128 (a b: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64) (imm8: i8)
    : Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
      #i128
      (fun i ->
          let i:u64 = i in
          cast ((cast (cast (a.[ mk_u64 2 *! i <: u64 ] <: i64) <: u64) <: u128) +!
              ((cast (cast (a.[ (mk_u64 2 *! i <: u64) +! mk_u64 1 <: u64 ] <: i64) <: u64) <: u128) <<!
                mk_i32 64
                <:
                u128)
              <:
              u128)
          <:
          i128)
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
      #i128
      (fun i ->
          let i:u64 = i in
          cast ((cast (cast (b.[ mk_u64 2 *! i <: u64 ] <: i64) <: u64) <: u128) +!
              ((cast (cast (b.[ (mk_u64 2 *! i <: u64) +! mk_u64 1 <: u64 ] <: i64) <: u64) <: u128) <<!
                mk_i32 64
                <:
                u128)
              <:
              u128)
          <:
          i128)
  in
  let imm8:i32 = cast (cast (cast (imm8 <: i8) <: u8) <: u32) <: i32 in
  let r:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i128 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
      #i128
      (fun i ->
          let i:u64 = i in
          let control:i32 = imm8 >>! (i *! mk_u64 4 <: u64) in
          if ((control >>! mk_i32 3 <: i32) %! mk_i32 2 <: i32) =. mk_i32 1
          then mk_i128 0
          else
            match control %! mk_i32 4 <: i32 with
            | Rust_primitives.Integers.MkInt 0 -> a.[ mk_u64 0 ]
            | Rust_primitives.Integers.MkInt 1 -> a.[ mk_u64 1 ]
            | Rust_primitives.Integers.MkInt 2 -> b.[ mk_u64 0 ]
            | Rust_primitives.Integers.MkInt 3 -> b.[ mk_u64 1 ]
            | _ ->
              Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

                  <:
                  Rust_primitives.Hax.t_Never))
  in
  Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
    #i64
    (fun i ->
        let i:u64 = i in
        let index:u64 = i >>! mk_i32 1 in
        let hilo:u64 = Core.Num.impl_u64__rem_euclid i (mk_u64 2) in
        let v_val:i128 = r.[ index ] in
        if hilo =. mk_u64 0
        then Core_models.Abstractions.Simd.f_cast #i64 #i128 #FStar.Tactics.Typeclasses.solve v_val
        else
          Core_models.Abstractions.Simd.f_cast #i64
            #i128
            #FStar.Tactics.Typeclasses.solve
            (v_val >>! mk_i32 64 <: i128))

/// Computes the absolute values of packed 32-bit integers in `a`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_abs_epi32)
let e_mm256_abs_epi32 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
  in
  let r:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
    Core_models.Abstractions.Simd.simd_select (mk_u64 8)
      #i32
      #i32
      (Core_models.Abstractions.Simd.simd_lt (mk_u64 8)
          #i32
          a
          (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
              #i32
              (fun temp_0_ ->
                  let _:u64 = temp_0_ in
                  mk_i32 0)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      (Core_models.Abstractions.Simd.simd_neg (mk_u64 8) #i32 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      a
  in
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 r

/// Computes the absolute values of packed 16-bit integers in `a`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_abs_epi16)
let e_mm256_abs_epi16 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
  in
  let r:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
    Core_models.Abstractions.Simd.simd_select (mk_u64 16)
      #i16
      #i16
      (Core_models.Abstractions.Simd.simd_lt (mk_u64 16)
          #i16
          a
          (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
              #i16
              (fun temp_0_ ->
                  let _:u64 = temp_0_ in
                  mk_i16 0)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      (Core_models.Abstractions.Simd.simd_neg (mk_u64 16) #i16 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      a
  in
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__from_i16x16 r

/// Computes the absolute values of packed 8-bit integers in `a`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_abs_epi8)
let e_mm256_abs_epi8 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
  in
  let r:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
    Core_models.Abstractions.Simd.simd_select (mk_u64 32)
      #i8
      #i8
      (Core_models.Abstractions.Simd.simd_lt (mk_u64 32)
          #i8
          a
          (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 32)
              #i8
              (fun temp_0_ ->
                  let _:u64 = temp_0_ in
                  mk_i8 0)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      (Core_models.Abstractions.Simd.simd_neg (mk_u64 32) #i8 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      a
  in
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__from_i8x32 r

/// Adds packed 64-bit integers in `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi64)
let e_mm256_add_epi64 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__from_i64x4 (Core_models.Abstractions.Simd.simd_add
        (mk_u64 4)
        #i64
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Adds packed 32-bit integers in `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi32)
let e_mm256_add_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__from_i32x8 (Core_models.Abstractions.Simd.simd_add
        (mk_u64 8)
        #i32
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Adds packed 16-bit integers in `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi16)
let e_mm256_add_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__from_i16x16 (Core_models.Abstractions.Simd.simd_add
        (mk_u64 16)
        #i16
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Adds packed 8-bit integers in `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi8)
let e_mm256_add_epi8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__from_i8x32 (Core_models.Abstractions.Simd.simd_add
        (mk_u64 32)
        #i8
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)

/// Adds packed 8-bit integers in `a` and `b` using saturation.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_adds_epi8)
let e_mm256_adds_epi8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__from_i8x32 (Core_models.Abstractions.Simd.simd_saturating_add
        #i8
        (mk_u64 32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)

/// Adds packed 16-bit integers in `a` and `b` using saturation.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_adds_epi16)
let e_mm256_adds_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__from_i16x16 (Core_models.Abstractions.Simd.simd_saturating_add
        #i16
        (mk_u64 16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Adds packed unsigned 8-bit integers in `a` and `b` using saturation.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_adds_epu8)
let e_mm256_adds_epu8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_saturating_add #u8
        (mk_u64 32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_9__impl_2__to_u8x32 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_9__impl_2__to_u8x32 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)

/// Adds packed unsigned 16-bit integers in `a` and `b` using saturation.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_adds_epu16)
let e_mm256_adds_epu16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_saturating_add #u16
        (mk_u64 16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_2__to_u16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_2__to_u16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)

let e_mm256_setzero_si256 (_: Prims.unit) : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 256)
    (fun temp_0_ ->
        let _:u64 = temp_0_ in
        Core_models.Abstractions.Bit.Bit_Zero <: Core_models.Abstractions.Bit.t_Bit)

/// Concatenates pairs of 16-byte blocks in `a` and `b` into a 32-byte temporary
/// result, shifts the result right by `n` bytes, and returns the low 16 bytes.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_alignr_epi8)
let e_mm256_alignr_epi8 (v_IMM8: i32) (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  if v_IMM8 >=. mk_i32 32
  then e_mm256_setzero_si256 ()
  else
    let a, b:(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
      Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) =
      if v_IMM8 >. mk_i32 16
      then
        e_mm256_setzero_si256 (), a
        <:
        (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
          Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      else
        a, b
        <:
        (Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) &
          Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    in
    let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
      Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
    in
    let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
      Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 b
    in
    if v_IMM8 =. mk_i32 16
    then
      Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
        #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        #FStar.Tactics.Typeclasses.solve
        a
    else
      let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8):Core_models.Abstractions.Funarr.t_FunArray
        (mk_u64 32) i8 =
        match v_IMM8 %! mk_i32 16 <: i32 with
        | Rust_primitives.Integers.MkInt 0 ->
          Core_models.Abstractions.Simd.simd_shuffle #i8
            (mk_u64 32)
            (mk_usize 32)
            (mk_u64 32)
            b
            a
            (let list =
                [
                  mk_u64 0; mk_u64 1; mk_u64 2; mk_u64 3; mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7;
                  mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14;
                  mk_u64 15; mk_u64 16; mk_u64 17; mk_u64 18; mk_u64 19; mk_u64 20; mk_u64 21;
                  mk_u64 22; mk_u64 23; mk_u64 24; mk_u64 25; mk_u64 26; mk_u64 27; mk_u64 28;
                  mk_u64 29; mk_u64 30; mk_u64 31
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
              Rust_primitives.Hax.array_of_list 32 list)
        | Rust_primitives.Integers.MkInt 1 ->
          Core_models.Abstractions.Simd.simd_shuffle #i8
            (mk_u64 32)
            (mk_usize 32)
            (mk_u64 32)
            b
            a
            (let list =
                [
                  mk_u64 1; mk_u64 2; mk_u64 3; mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7; mk_u64 8;
                  mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15;
                  mk_u64 32; mk_u64 17; mk_u64 18; mk_u64 19; mk_u64 20; mk_u64 21; mk_u64 22;
                  mk_u64 23; mk_u64 24; mk_u64 25; mk_u64 26; mk_u64 27; mk_u64 28; mk_u64 29;
                  mk_u64 30; mk_u64 31; mk_u64 48
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
              Rust_primitives.Hax.array_of_list 32 list)
        | Rust_primitives.Integers.MkInt 2 ->
          Core_models.Abstractions.Simd.simd_shuffle #i8
            (mk_u64 32)
            (mk_usize 32)
            (mk_u64 32)
            b
            a
            (let list =
                [
                  mk_u64 2; mk_u64 3; mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7; mk_u64 8; mk_u64 9;
                  mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32;
                  mk_u64 33; mk_u64 18; mk_u64 19; mk_u64 20; mk_u64 21; mk_u64 22; mk_u64 23;
                  mk_u64 24; mk_u64 25; mk_u64 26; mk_u64 27; mk_u64 28; mk_u64 29; mk_u64 30;
                  mk_u64 31; mk_u64 48; mk_u64 49
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
              Rust_primitives.Hax.array_of_list 32 list)
        | Rust_primitives.Integers.MkInt 3 ->
          Core_models.Abstractions.Simd.simd_shuffle #i8
            (mk_u64 32)
            (mk_usize 32)
            (mk_u64 32)
            b
            a
            (let list =
                [
                  mk_u64 3; mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7; mk_u64 8; mk_u64 9; mk_u64 10;
                  mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 33;
                  mk_u64 34; mk_u64 19; mk_u64 20; mk_u64 21; mk_u64 22; mk_u64 23; mk_u64 24;
                  mk_u64 25; mk_u64 26; mk_u64 27; mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31;
                  mk_u64 48; mk_u64 49; mk_u64 50
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
              Rust_primitives.Hax.array_of_list 32 list)
        | Rust_primitives.Integers.MkInt 4 ->
          Core_models.Abstractions.Simd.simd_shuffle #i8
            (mk_u64 32)
            (mk_usize 32)
            (mk_u64 32)
            b
            a
            (let list =
                [
                  mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7; mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11;
                  mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 33; mk_u64 34;
                  mk_u64 35; mk_u64 20; mk_u64 21; mk_u64 22; mk_u64 23; mk_u64 24; mk_u64 25;
                  mk_u64 26; mk_u64 27; mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 48;
                  mk_u64 49; mk_u64 50; mk_u64 51
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
              Rust_primitives.Hax.array_of_list 32 list)
        | Rust_primitives.Integers.MkInt 5 ->
          Core_models.Abstractions.Simd.simd_shuffle #i8
            (mk_u64 32)
            (mk_usize 32)
            (mk_u64 32)
            b
            a
            (let list =
                [
                  mk_u64 5; mk_u64 6; mk_u64 7; mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12;
                  mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 33; mk_u64 34; mk_u64 35;
                  mk_u64 36; mk_u64 21; mk_u64 22; mk_u64 23; mk_u64 24; mk_u64 25; mk_u64 26;
                  mk_u64 27; mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 48; mk_u64 49;
                  mk_u64 50; mk_u64 51; mk_u64 52
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
              Rust_primitives.Hax.array_of_list 32 list)
        | Rust_primitives.Integers.MkInt 6 ->
          Core_models.Abstractions.Simd.simd_shuffle #i8
            (mk_u64 32)
            (mk_usize 32)
            (mk_u64 32)
            b
            a
            (let list =
                [
                  mk_u64 6; mk_u64 7; mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13;
                  mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 33; mk_u64 34; mk_u64 35; mk_u64 36;
                  mk_u64 37; mk_u64 22; mk_u64 23; mk_u64 24; mk_u64 25; mk_u64 26; mk_u64 27;
                  mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 48; mk_u64 49; mk_u64 50;
                  mk_u64 51; mk_u64 52; mk_u64 53
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
              Rust_primitives.Hax.array_of_list 32 list)
        | Rust_primitives.Integers.MkInt 7 ->
          Core_models.Abstractions.Simd.simd_shuffle #i8
            (mk_u64 32)
            (mk_usize 32)
            (mk_u64 32)
            b
            a
            (let list =
                [
                  mk_u64 7; mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13;
                  mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 33; mk_u64 34; mk_u64 35; mk_u64 36;
                  mk_u64 37; mk_u64 38; mk_u64 23; mk_u64 24; mk_u64 25; mk_u64 26; mk_u64 27;
                  mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 48; mk_u64 49; mk_u64 50;
                  mk_u64 51; mk_u64 52; mk_u64 53; mk_u64 54
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
              Rust_primitives.Hax.array_of_list 32 list)
        | Rust_primitives.Integers.MkInt 8 ->
          Core_models.Abstractions.Simd.simd_shuffle #i8
            (mk_u64 32)
            (mk_usize 32)
            (mk_u64 32)
            b
            a
            (let list =
                [
                  mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14;
                  mk_u64 15; mk_u64 32; mk_u64 33; mk_u64 34; mk_u64 35; mk_u64 36; mk_u64 37;
                  mk_u64 38; mk_u64 39; mk_u64 24; mk_u64 25; mk_u64 26; mk_u64 27; mk_u64 28;
                  mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 48; mk_u64 49; mk_u64 50; mk_u64 51;
                  mk_u64 52; mk_u64 53; mk_u64 54; mk_u64 55
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
              Rust_primitives.Hax.array_of_list 32 list)
        | Rust_primitives.Integers.MkInt 9 ->
          Core_models.Abstractions.Simd.simd_shuffle #i8
            (mk_u64 32)
            (mk_usize 32)
            (mk_u64 32)
            b
            a
            (let list =
                [
                  mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15;
                  mk_u64 32; mk_u64 33; mk_u64 34; mk_u64 35; mk_u64 36; mk_u64 37; mk_u64 38;
                  mk_u64 39; mk_u64 40; mk_u64 25; mk_u64 26; mk_u64 27; mk_u64 28; mk_u64 29;
                  mk_u64 30; mk_u64 31; mk_u64 48; mk_u64 49; mk_u64 50; mk_u64 51; mk_u64 52;
                  mk_u64 53; mk_u64 54; mk_u64 55; mk_u64 56
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
              Rust_primitives.Hax.array_of_list 32 list)
        | Rust_primitives.Integers.MkInt 10 ->
          Core_models.Abstractions.Simd.simd_shuffle #i8
            (mk_u64 32)
            (mk_usize 32)
            (mk_u64 32)
            b
            a
            (let list =
                [
                  mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32;
                  mk_u64 33; mk_u64 34; mk_u64 35; mk_u64 36; mk_u64 37; mk_u64 38; mk_u64 39;
                  mk_u64 40; mk_u64 41; mk_u64 26; mk_u64 27; mk_u64 28; mk_u64 29; mk_u64 30;
                  mk_u64 31; mk_u64 48; mk_u64 49; mk_u64 50; mk_u64 51; mk_u64 52; mk_u64 53;
                  mk_u64 54; mk_u64 55; mk_u64 56; mk_u64 57
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
              Rust_primitives.Hax.array_of_list 32 list)
        | Rust_primitives.Integers.MkInt 11 ->
          Core_models.Abstractions.Simd.simd_shuffle #i8
            (mk_u64 32)
            (mk_usize 32)
            (mk_u64 32)
            b
            a
            (let list =
                [
                  mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 33;
                  mk_u64 34; mk_u64 35; mk_u64 36; mk_u64 37; mk_u64 38; mk_u64 39; mk_u64 40;
                  mk_u64 41; mk_u64 42; mk_u64 27; mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31;
                  mk_u64 48; mk_u64 49; mk_u64 50; mk_u64 51; mk_u64 52; mk_u64 53; mk_u64 54;
                  mk_u64 55; mk_u64 56; mk_u64 57; mk_u64 58
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
              Rust_primitives.Hax.array_of_list 32 list)
        | Rust_primitives.Integers.MkInt 12 ->
          Core_models.Abstractions.Simd.simd_shuffle #i8
            (mk_u64 32)
            (mk_usize 32)
            (mk_u64 32)
            b
            a
            (let list =
                [
                  mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 33; mk_u64 34;
                  mk_u64 35; mk_u64 36; mk_u64 37; mk_u64 38; mk_u64 39; mk_u64 40; mk_u64 41;
                  mk_u64 42; mk_u64 43; mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 48;
                  mk_u64 49; mk_u64 50; mk_u64 51; mk_u64 52; mk_u64 53; mk_u64 54; mk_u64 55;
                  mk_u64 56; mk_u64 57; mk_u64 58; mk_u64 59
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
              Rust_primitives.Hax.array_of_list 32 list)
        | Rust_primitives.Integers.MkInt 13 ->
          Core_models.Abstractions.Simd.simd_shuffle #i8
            (mk_u64 32)
            (mk_usize 32)
            (mk_u64 32)
            b
            a
            (let list =
                [
                  mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 33; mk_u64 34; mk_u64 35;
                  mk_u64 36; mk_u64 37; mk_u64 38; mk_u64 39; mk_u64 40; mk_u64 41; mk_u64 42;
                  mk_u64 43; mk_u64 44; mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 48; mk_u64 49;
                  mk_u64 50; mk_u64 51; mk_u64 52; mk_u64 53; mk_u64 54; mk_u64 55; mk_u64 56;
                  mk_u64 57; mk_u64 58; mk_u64 59; mk_u64 60
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
              Rust_primitives.Hax.array_of_list 32 list)
        | Rust_primitives.Integers.MkInt 14 ->
          Core_models.Abstractions.Simd.simd_shuffle #i8
            (mk_u64 32)
            (mk_usize 32)
            (mk_u64 32)
            b
            a
            (let list =
                [
                  mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 33; mk_u64 34; mk_u64 35; mk_u64 36;
                  mk_u64 37; mk_u64 38; mk_u64 39; mk_u64 40; mk_u64 41; mk_u64 42; mk_u64 43;
                  mk_u64 44; mk_u64 45; mk_u64 30; mk_u64 31; mk_u64 48; mk_u64 49; mk_u64 50;
                  mk_u64 51; mk_u64 52; mk_u64 53; mk_u64 54; mk_u64 55; mk_u64 56; mk_u64 57;
                  mk_u64 58; mk_u64 59; mk_u64 60; mk_u64 61
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
              Rust_primitives.Hax.array_of_list 32 list)
        | Rust_primitives.Integers.MkInt 15 ->
          Core_models.Abstractions.Simd.simd_shuffle #i8
            (mk_u64 32)
            (mk_usize 32)
            (mk_u64 32)
            b
            a
            (let list =
                [
                  mk_u64 15; mk_u64 32; mk_u64 33; mk_u64 34; mk_u64 35; mk_u64 36; mk_u64 37;
                  mk_u64 38; mk_u64 39; mk_u64 40; mk_u64 41; mk_u64 42; mk_u64 43; mk_u64 44;
                  mk_u64 45; mk_u64 46; mk_u64 31; mk_u64 48; mk_u64 49; mk_u64 50; mk_u64 51;
                  mk_u64 52; mk_u64 53; mk_u64 54; mk_u64 55; mk_u64 56; mk_u64 57; mk_u64 58;
                  mk_u64 59; mk_u64 60; mk_u64 61; mk_u64 62
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
              Rust_primitives.Hax.array_of_list 32 list)
        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

              <:
              Rust_primitives.Hax.t_Never)
      in
      Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
        #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
        #FStar.Tactics.Typeclasses.solve
        r

/// Computes the bitwise AND of 256 bits (representing integer data)
/// in `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_and_si256)
let e_mm256_and_si256 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_and (mk_u64 4)
        #i64
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

let e_mm256_set1_epi8 (v_val: i8) : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__from_i8x32 (Core_models.Abstractions.Funarr.impl_5__from_fn
        (mk_u64 32)
        #i8
        (fun temp_0_ ->
            let _:u64 = temp_0_ in
            v_val)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)

/// Computes the bitwise NOT of 256 bits (representing integer data)
/// in `a` and then AND with `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_andnot_si256)
let e_mm256_andnot_si256 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let all_ones:Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
    e_mm256_set1_epi8 (mk_i8 (-1))
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_and (mk_u64 4)
        #i64
        (Core_models.Abstractions.Simd.simd_xor (mk_u64 4)
            #i64
            (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
            (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 all_ones
              <:
              Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Averages packed unsigned 16-bit integers in `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_avg_epu16)
let e_mm256_avg_epu16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 16)
      #u16
      #u32
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_2__to_u16x16 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 16)
      #u16
      #u32
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_2__to_u16x16 b
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
  in
  let r:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32 =
    Core_models.Abstractions.Simd.simd_shr (mk_u64 16)
      #u32
      (Core_models.Abstractions.Simd.simd_add (mk_u64 16)
          #u32
          (Core_models.Abstractions.Simd.simd_add (mk_u64 16) #u32 a b
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32)
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_19__impl_1__splat (mk_u32 1)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_19__impl_1__splat (mk_u32 1)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 16) #u32 #u16 r
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)

/// Averages packed unsigned 8-bit integers in `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_avg_epu8)
let e_mm256_avg_epu8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 32)
      #u8
      #u16
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_9__impl_2__to_u8x32 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 32)
      #u8
      #u16
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_9__impl_2__to_u8x32 b
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
  in
  let r:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16 =
    Core_models.Abstractions.Simd.simd_shr (mk_u64 32)
      #u16
      (Core_models.Abstractions.Simd.simd_add (mk_u64 32)
          #u16
          (Core_models.Abstractions.Simd.simd_add (mk_u64 32) #u16 a b
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16)
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_20__impl_1__splat (mk_u16 1)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_20__impl_1__splat (mk_u16 1)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u16)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 32) #u16 #u8 r
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)

/// Blends packed 32-bit integers from `a` and `b` using control mask `IMM4`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_blend_epi32)
let e_mm_blend_epi32 (v_IMM4: i32) (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 b
  in
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i32 =
    Core_models.Abstractions.Simd.simd_shuffle #i32
      (mk_u64 4)
      (mk_usize 4)
      (mk_u64 4)
      a
      b
      (let list =
          [
            (let list = [mk_u64 0; mk_u64 4; mk_u64 0; mk_u64 4] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ (cast (v_IMM4 <: i32) <: usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 1; mk_u64 1; mk_u64 5; mk_u64 5] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ (cast (v_IMM4 <: i32) <: usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 2; mk_u64 6; mk_u64 2; mk_u64 6] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM4 <: i32) <: usize) >>!
                mk_i32 2
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 3; mk_u64 3; mk_u64 7; mk_u64 7] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM4 <: i32) <: usize) >>!
                mk_i32 2
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    #FStar.Tactics.Typeclasses.solve
    r

/// Blends packed 32-bit integers from `a` and `b` using control mask `IMM8`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blend_epi32)
let e_mm256_blend_epi32 (v_IMM8: i32) (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
  in
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) i32 =
    Core_models.Abstractions.Simd.simd_shuffle #i32
      (mk_u64 8)
      (mk_usize 8)
      (mk_u64 8)
      a
      b
      (let list =
          [
            (let list = [mk_u64 0; mk_u64 8; mk_u64 0; mk_u64 8] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ (cast (v_IMM8 <: i32) <: usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 1; mk_u64 1; mk_u64 9; mk_u64 9] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ (cast (v_IMM8 <: i32) <: usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 2; mk_u64 10; mk_u64 2; mk_u64 10] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 2
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 3; mk_u64 3; mk_u64 11; mk_u64 11] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 2
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 4; mk_u64 12; mk_u64 4; mk_u64 12] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 4
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 5; mk_u64 5; mk_u64 13; mk_u64 13] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 4
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 6; mk_u64 14; mk_u64 6; mk_u64 14] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 6
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 7; mk_u64 7; mk_u64 15; mk_u64 15] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 6
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
        Rust_primitives.Hax.array_of_list 8 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    r

/// Blends packed 16-bit integers from `a` and `b` using control mask `IMM8`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blend_epi16)
let e_mm256_blend_epi16 (v_IMM8: i32) (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
  in
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 16) i16 =
    Core_models.Abstractions.Simd.simd_shuffle #i16
      (mk_u64 16)
      (mk_usize 16)
      (mk_u64 16)
      a
      b
      (let list =
          [
            (let list = [mk_u64 0; mk_u64 16; mk_u64 0; mk_u64 16] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ (cast (v_IMM8 <: i32) <: usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 1; mk_u64 1; mk_u64 17; mk_u64 17] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ (cast (v_IMM8 <: i32) <: usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 2; mk_u64 18; mk_u64 2; mk_u64 18] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 2
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 3; mk_u64 3; mk_u64 19; mk_u64 19] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 2
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 4; mk_u64 20; mk_u64 4; mk_u64 20] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 4
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 5; mk_u64 5; mk_u64 21; mk_u64 21] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 4
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 6; mk_u64 22; mk_u64 6; mk_u64 22] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 6
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 7; mk_u64 7; mk_u64 23; mk_u64 23] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 6
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 8; mk_u64 24; mk_u64 8; mk_u64 24] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ (cast (v_IMM8 <: i32) <: usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 9; mk_u64 9; mk_u64 25; mk_u64 25] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ (cast (v_IMM8 <: i32) <: usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 10; mk_u64 26; mk_u64 10; mk_u64 26] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 2
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 11; mk_u64 11; mk_u64 27; mk_u64 27] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 2
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 12; mk_u64 28; mk_u64 12; mk_u64 28] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 4
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 13; mk_u64 13; mk_u64 29; mk_u64 29] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 4
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 14; mk_u64 30; mk_u64 14; mk_u64 30] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 6
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64;
            (let list = [mk_u64 15; mk_u64 15; mk_u64 31; mk_u64 31] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list).[ ((cast (v_IMM8 <: i32) <: usize) >>!
                mk_i32 6
                <:
                usize) &.
              mk_usize 3
              <:
              usize ]
            <:
            u64
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    r

/// Blends packed 8-bit integers from `a` and `b` using `mask`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blendv_epi8)
let e_mm256_blendv_epi8 (a b mask: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let (mask: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 32) i8 =
    Core_models.Abstractions.Simd.simd_lt (mk_u64 32)
      #i8
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 mask
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 32)
          #i8
          (fun temp_0_ ->
              let _:u64 = temp_0_ in
              mk_i8 0)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_select (mk_u64 32)
        #i8
        #i8
        mask
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)

/// Broadcasts the low packed 8-bit integer from `a` to all elements of
/// the 128-bit returned value.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastb_epi8)
let e_mm_broadcastb_epi8 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let ret:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
    Core_models.Abstractions.Simd.simd_shuffle #i8
      (mk_u64 16)
      (mk_usize 16)
      (mk_u64 16)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_2__to_i8x16 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
      (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
          #i8
          (fun temp_0_ ->
              let _:u64 = temp_0_ in
              mk_i8 0)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
      (Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 16) <: t_Array u64 (mk_usize 16))
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    #FStar.Tactics.Typeclasses.solve
    ret

/// Broadcasts the low packed 8-bit integer from `a` to all elements of
/// the 256-bit returned value.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastb_epi8)
let e_mm256_broadcastb_epi8 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let ret:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
    Core_models.Abstractions.Simd.simd_shuffle #i8
      (mk_u64 16)
      (mk_usize 32)
      (mk_u64 32)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_2__to_i8x16 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
      (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 16)
          #i8
          (fun temp_0_ ->
              let _:u64 = temp_0_ in
              mk_i8 0)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
      (Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 32) <: t_Array u64 (mk_usize 32))
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    ret

/// Broadcasts the low packed 32-bit integer from `a` to all elements of
/// the 128-bit returned value.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastd_epi32)
let e_mm_broadcastd_epi32 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let ret:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32 =
    Core_models.Abstractions.Simd.simd_shuffle #i32
      (mk_u64 4)
      (mk_usize 4)
      (mk_u64 4)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
      (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
          #i32
          (fun temp_0_ ->
              let _:u64 = temp_0_ in
              mk_i32 0)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
      (Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 4) <: t_Array u64 (mk_usize 4))
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    #FStar.Tactics.Typeclasses.solve
    ret

/// Broadcasts the low packed 32-bit integer from `a` to all elements of
/// the 256-bit returned value.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastd_epi32)
let e_mm256_broadcastd_epi32 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let ret:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
    Core_models.Abstractions.Simd.simd_shuffle #i32
      (mk_u64 4)
      (mk_usize 8)
      (mk_u64 8)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
      (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
          #i32
          (fun temp_0_ ->
              let _:u64 = temp_0_ in
              mk_i32 0)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
      (Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 8) <: t_Array u64 (mk_usize 8))
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    ret

/// Broadcasts the low packed 64-bit integer from `a` to all elements of
/// the 128-bit returned value.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastq_epi64)
let e_mm_broadcastq_epi64 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let ret:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64 =
    Core_models.Abstractions.Simd.simd_shuffle #i64
      (mk_u64 2)
      (mk_usize 2)
      (mk_u64 2)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_2__to_i64x2 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_2__to_i64x2 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
      (Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 2) <: t_Array u64 (mk_usize 2))
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    #FStar.Tactics.Typeclasses.solve
    ret

/// Broadcasts the low packed 64-bit integer from `a` to all elements of
/// the 256-bit returned value.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastq_epi64)
let e_mm256_broadcastq_epi64 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let ret:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
    Core_models.Abstractions.Simd.simd_shuffle #i64
      (mk_u64 2)
      (mk_usize 4)
      (mk_u64 4)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_2__to_i64x2 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_2__to_i64x2 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
      (Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 4) <: t_Array u64 (mk_usize 4))
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    ret

/// Broadcasts 128 bits of integer data from a to all 128-bit lanes in
/// the 256-bit returned value.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastsi128_si256)
let e_mm_broadcastsi128_si256 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let ret:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
    Core_models.Abstractions.Simd.simd_shuffle #i64
      (mk_u64 2)
      (mk_usize 4)
      (mk_u64 4)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_2__to_i64x2 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
      (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
          #i64
          (fun temp_0_ ->
              let _:u64 = temp_0_ in
              mk_i64 0)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
      (let list = [mk_u64 0; mk_u64 1; mk_u64 0; mk_u64 1] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    ret

/// Broadcasts 128 bits of integer data from a to all 128-bit lanes in
/// the 256-bit returned value.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastsi128_si256)
let e_mm256_broadcastsi128_si256 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let ret:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
    Core_models.Abstractions.Simd.simd_shuffle #i64
      (mk_u64 2)
      (mk_usize 4)
      (mk_u64 4)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_2__to_i64x2 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
      (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 2)
          #i64
          (fun temp_0_ ->
              let _:u64 = temp_0_ in
              mk_i64 0)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
      (let list = [mk_u64 0; mk_u64 1; mk_u64 0; mk_u64 1] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    ret

/// Broadcasts the low packed 16-bit integer from a to all elements of
/// the 128-bit returned value
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_broadcastw_epi16)
let e_mm_broadcastw_epi16 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let ret:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
    Core_models.Abstractions.Simd.simd_shuffle #i16
      (mk_u64 8)
      (mk_usize 8)
      (mk_u64 8)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
      (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
          #i16
          (fun temp_0_ ->
              let _:u64 = temp_0_ in
              mk_i16 0)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
      (Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 8) <: t_Array u64 (mk_usize 8))
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    #FStar.Tactics.Typeclasses.solve
    ret

/// Broadcasts the low packed 16-bit integer from a to all elements of
/// the 256-bit returned value
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_broadcastw_epi16)
let e_mm256_broadcastw_epi16 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let ret:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
    Core_models.Abstractions.Simd.simd_shuffle #i16
      (mk_u64 8)
      (mk_usize 16)
      (mk_u64 16)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
      (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 8)
          #i16
          (fun temp_0_ ->
              let _:u64 = temp_0_ in
              mk_i16 0)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
      (Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 16) <: t_Array u64 (mk_usize 16))
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    ret

/// Compares packed 64-bit integers in `a` and `b` for equality.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpeq_epi64)
let e_mm256_cmpeq_epi64 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_eq (mk_u64 4)
        #i64
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Compares packed 32-bit integers in `a` and `b` for equality.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpeq_epi32)
let e_mm256_cmpeq_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_eq (mk_u64 8)
        #i32
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Compares packed 16-bit integers in `a` and `b` for equality.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpeq_epi16)
let e_mm256_cmpeq_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_eq (mk_u64 16)
        #i16
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Compares packed 8-bit integers in `a` and `b` for equality.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpeq_epi8)
let e_mm256_cmpeq_epi8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_eq (mk_u64 32)
        #i8
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)

/// Compares packed 64-bit integers in `a` and `b` for greater-than.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi64)
let e_mm256_cmpgt_epi64 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_gt (mk_u64 4)
        #i64
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Compares packed 32-bit integers in `a` and `b` for greater-than.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi32)
let e_mm256_cmpgt_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_gt (mk_u64 8)
        #i32
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Compares packed 16-bit integers in `a` and `b` for greater-than.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi16)
let e_mm256_cmpgt_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_gt (mk_u64 16)
        #i16
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Compares packed 8-bit integers in `a` and `b` for greater-than.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi8)
let e_mm256_cmpgt_epi8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_gt (mk_u64 32)
        #i8
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)

/// Sign-extend 16-bit integers to 32-bit integers.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi16_epi32)
let e_mm256_cvtepi16_epi32 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
        #i16
        #i32
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Sign-extend 16-bit integers to 64-bit integers.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi16_epi64)
let e_mm256_cvtepi16_epi64 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 a
  in
  let (v64: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i16 =
    Core_models.Abstractions.Simd.simd_shuffle #i16
      (mk_u64 8)
      (mk_usize 4)
      (mk_u64 4)
      a
      a
      (let list = [mk_u64 0; mk_u64 1; mk_u64 2; mk_u64 3] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i16 #i64 v64
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Sign-extend 32-bit integers to 64-bit integers.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi32_epi64)
let e_mm256_cvtepi32_epi64 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
        #i32
        #i64
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Sign-extend 8-bit integers to 16-bit integers.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi8_epi16)
let e_mm256_cvtepi8_epi16 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 16)
        #i8
        #i16
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_2__to_i8x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Sign-extend 8-bit integers to 32-bit integers.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi8_epi32)
let e_mm256_cvtepi8_epi32 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_2__to_i8x16 a
  in
  let (v64: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) i8 =
    Core_models.Abstractions.Simd.simd_shuffle #i8
      (mk_u64 16)
      (mk_usize 8)
      (mk_u64 8)
      a
      a
      (let list =
          [mk_u64 0; mk_u64 1; mk_u64 2; mk_u64 3; mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
        Rust_primitives.Hax.array_of_list 8 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #i8 #i32 v64
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Sign-extend 8-bit integers to 64-bit integers.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi8_epi64)
let e_mm256_cvtepi8_epi64 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_14__impl_2__to_i8x16 a
  in
  let (v32: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i8 =
    Core_models.Abstractions.Simd.simd_shuffle #i8
      (mk_u64 16)
      (mk_usize 4)
      (mk_u64 4)
      a
      a
      (let list = [mk_u64 0; mk_u64 1; mk_u64 2; mk_u64 3] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #i8 #i64 v32
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Zeroes extend packed unsigned 16-bit integers in `a` to packed 32-bit
/// integers, and stores the results in `dst`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu16_epi32)
let e_mm256_cvtepu16_epi32 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 8)
        #u16
        #u32
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_17__impl_2__to_u16x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)

/// Zero-extend the lower four unsigned 16-bit integers in `a` to 64-bit
/// integers. The upper four elements of `a` are unused.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu16_epi64)
let e_mm256_cvtepu16_epi64 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_17__impl_2__to_u16x8 a
  in
  let (v64: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) u16 =
    Core_models.Abstractions.Simd.simd_shuffle #u16
      (mk_u64 8)
      (mk_usize 4)
      (mk_u64 4)
      a
      a
      (let list = [mk_u64 0; mk_u64 1; mk_u64 2; mk_u64 3] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #u16 #u64 v64
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)

/// Zero-extend unsigned 32-bit integers in `a` to 64-bit integers.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu32_epi64)
let e_mm256_cvtepu32_epi64 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
        #u32
        #u64
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_15__impl_2__to_u32x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)

/// Zero-extend unsigned 8-bit integers in `a` to 16-bit integers.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu8_epi16)
let e_mm256_cvtepu8_epi16 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 16)
        #u8
        #u16
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_18__impl_2__to_u8x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)

/// Zero-extend the lower eight unsigned 8-bit integers in `a` to 32-bit
/// integers. The upper eight elements of `a` are unused.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu8_epi32)
let e_mm256_cvtepu8_epi32 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_18__impl_2__to_u8x16 a
  in
  let (v64: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) u8 =
    Core_models.Abstractions.Simd.simd_shuffle #u8
      (mk_u64 16)
      (mk_usize 8)
      (mk_u64 8)
      a
      a
      (let list =
          [mk_u64 0; mk_u64 1; mk_u64 2; mk_u64 3; mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
        Rust_primitives.Hax.array_of_list 8 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 8) #u8 #u32 v64
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)

/// Zero-extend the lower four unsigned 8-bit integers in `a` to 64-bit
/// integers. The upper twelve elements of `a` are unused.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepu8_epi64)
let e_mm256_cvtepu8_epi64 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_18__impl_2__to_u8x16 a
  in
  let (v32: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) u8 =
    Core_models.Abstractions.Simd.simd_shuffle #u8
      (mk_u64 16)
      (mk_usize 4)
      (mk_u64 4)
      a
      a
      (let list = [mk_u64 0; mk_u64 1; mk_u64 2; mk_u64 3] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 4) #u8 #u64 v32
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)

/// Extracts 128 bits (of integer data) from `a` selected with `IMM1`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_extracti128_si256)
let e_mm256_extracti128_si256
      (v_IMM1: i32)
      (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
      #i64
      (fun temp_0_ ->
          let _:u64 = temp_0_ in
          mk_i64 0)
  in
  let (dst: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 2) i64 =
    Core_models.Abstractions.Simd.simd_shuffle #i64
      (mk_u64 4)
      (mk_usize 2)
      (mk_u64 2)
      a
      b
      ((let list =
            [
              (let list = [mk_u64 0; mk_u64 1] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list 2 list);
              let list = [mk_u64 2; mk_u64 3] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
              Rust_primitives.Hax.array_of_list 2 list
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list).[ cast (v_IMM1 <: i32) <: usize ]
        <:
        t_Array u64 (mk_usize 2))
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    #FStar.Tactics.Typeclasses.solve
    dst

/// Horizontally adds adjacent pairs of 16-bit integers in `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hadd_epi16)
let e_mm256_hadd_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (phaddw (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Horizontally adds adjacent pairs of 32-bit integers in `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hadd_epi32)
let e_mm256_hadd_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (phaddd (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Horizontally adds adjacent pairs of 16-bit integers in `a` and `b`
/// using saturation.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hadds_epi16)
let e_mm256_hadds_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (phaddsw (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Horizontally subtract adjacent pairs of 16-bit integers in `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hsub_epi16)
let e_mm256_hsub_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (phsubw (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Horizontally subtract adjacent pairs of 32-bit integers in `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hsub_epi32)
let e_mm256_hsub_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (phsubd (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Horizontally subtract adjacent pairs of 16-bit integers in `a` and `b`
/// using saturation.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_hsubs_epi16)
let e_mm256_hsubs_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (phsubsw (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Copies `a` to `dst`, then insert 128 bits (of integer data) from `b` at the
/// location specified by `IMM1`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_inserti128_si256)
let e_mm256_castsi128_si256 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core_models.Abstractions.Bitvec.impl_9__from_fn (mk_u64 256)
    (fun i ->
        let i:u64 = i in
        if i <. mk_u64 128 <: bool
        then a.[ i ] <: Core_models.Abstractions.Bit.t_Bit
        else Core_models.Abstractions.Bit.Bit_Zero <: Core_models.Abstractions.Bit.t_Bit)

let e_mm256_inserti128_si256
      (v_IMM1: i32)
      (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 (e_mm256_castsi128_si256
          b
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
  in
  let (dst: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i64 =
    Core_models.Abstractions.Simd.simd_shuffle #i64
      (mk_u64 4)
      (mk_usize 4)
      (mk_u64 4)
      a
      b
      ((let list =
            [
              (let list = [mk_u64 4; mk_u64 5; mk_u64 2; mk_u64 3] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
                Rust_primitives.Hax.array_of_list 4 list);
              let list = [mk_u64 0; mk_u64 1; mk_u64 4; mk_u64 5] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
              Rust_primitives.Hax.array_of_list 4 list
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list).[ cast (v_IMM1 <: i32) <: usize ]
        <:
        t_Array u64 (mk_usize 4))
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    dst

/// Multiplies packed signed 16-bit integers in `a` and `b`, producing
/// intermediate signed 32-bit integers. Horizontally add adjacent pairs
/// of intermediate 32-bit integers.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_madd_epi16)
let e_mm256_madd_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (pmaddwd (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Vertically multiplies each unsigned 8-bit integer from `a` with the
/// corresponding signed 8-bit integer from `b`, producing intermediate
/// signed 16-bit integers. Horizontally add adjacent pairs of intermediate
/// signed 16-bit integers
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_maddubs_epi16)
let e_mm256_maddubs_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (pmaddubsw (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_9__impl_2__to_u8x32 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_9__impl_2__to_u8x32 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Compares packed 16-bit integers in `a` and `b`, and returns the packed
/// maximum values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epi16)
let e_mm256_max_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_select (mk_u64 16)
        #i16
        #i16
        (Core_models.Abstractions.Simd.simd_gt (mk_u64 16) #i16 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        a
        b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Compares packed 32-bit integers in `a` and `b`, and returns the packed
/// maximum values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epi32)
let e_mm256_max_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_select (mk_u64 8)
        #i32
        #i32
        (Core_models.Abstractions.Simd.simd_gt (mk_u64 8) #i32 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        a
        b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Compares packed 8-bit integers in `a` and `b`, and returns the packed
/// maximum values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epi8)
let e_mm256_max_epi8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 b
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_select (mk_u64 32)
        #i8
        #i8
        (Core_models.Abstractions.Simd.simd_gt (mk_u64 32) #i8 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
        a
        b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)

/// Compares packed unsigned 16-bit integers in `a` and `b`, and returns
/// the packed maximum values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epu16)
let e_mm256_max_epu16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_2__to_u16x16 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_2__to_u16x16 b
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_select (mk_u64 16)
        #u16
        #u16
        (Core_models.Abstractions.Simd.simd_gt (mk_u64 16) #u16 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
        a
        b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)

/// Compares packed unsigned 32-bit integers in `a` and `b`, and returns
/// the packed maximum values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epu32)
let e_mm256_max_epu32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_6__impl_2__to_u32x8 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_6__impl_2__to_u32x8 b
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_select (mk_u64 8)
        #u32
        #u32
        (Core_models.Abstractions.Simd.simd_gt (mk_u64 8) #u32 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
        a
        b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)

/// Compares packed unsigned 8-bit integers in `a` and `b`, and returns
/// the packed maximum values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_max_epu8)
let e_mm256_max_epu8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_9__impl_2__to_u8x32 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_9__impl_2__to_u8x32 b
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_select (mk_u64 32)
        #u8
        #u8
        (Core_models.Abstractions.Simd.simd_gt (mk_u64 32) #u8 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
        a
        b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)

/// Compares packed 16-bit integers in `a` and `b`, and returns the packed
/// minimum values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epi16)
let e_mm256_min_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_select (mk_u64 16)
        #i16
        #i16
        (Core_models.Abstractions.Simd.simd_lt (mk_u64 16) #i16 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        a
        b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Compares packed 32-bit integers in `a` and `b`, and returns the packed
/// minimum values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epi32)
let e_mm256_min_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_select (mk_u64 8)
        #i32
        #i32
        (Core_models.Abstractions.Simd.simd_lt (mk_u64 8) #i32 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        a
        b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Compares packed 8-bit integers in `a` and `b`, and returns the packed
/// minimum values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epi8)
let e_mm256_min_epi8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 b
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_select (mk_u64 32)
        #i8
        #i8
        (Core_models.Abstractions.Simd.simd_lt (mk_u64 32) #i8 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
        a
        b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)

/// Compares packed unsigned 16-bit integers in `a` and `b`, and returns
/// the packed minimum values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epu16)
let e_mm256_min_epu16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_2__to_u16x16 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_2__to_u16x16 b
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_select (mk_u64 16)
        #u16
        #u16
        (Core_models.Abstractions.Simd.simd_lt (mk_u64 16) #u16 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
        a
        b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)

/// Compares packed unsigned 32-bit integers in `a` and `b`, and returns
/// the packed minimum values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epu32)
let e_mm256_min_epu32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_6__impl_2__to_u32x8 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_6__impl_2__to_u32x8 b
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_select (mk_u64 8)
        #u32
        #u32
        (Core_models.Abstractions.Simd.simd_lt (mk_u64 8) #u32 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
        a
        b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)

/// Compares packed unsigned 8-bit integers in `a` and `b`, and returns
/// the packed minimum values.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_min_epu8)
let e_mm256_min_epu8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_9__impl_2__to_u8x32 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_9__impl_2__to_u8x32 b
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_select (mk_u64 32)
        #u8
        #u8
        (Core_models.Abstractions.Simd.simd_lt (mk_u64 32) #u8 a b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
        a
        b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)

/// Creates mask from the most significant bit of each 8-bit element in `a`,
/// return the result.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_movemask_epi8)
let e_mm256_movemask_epi8 (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) : i32 =
  let z:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 32)
      #i8
      (fun temp_0_ ->
          let _:u64 = temp_0_ in
          mk_i8 0)
  in
  let (m: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 32) i8 =
    Core_models.Abstractions.Simd.simd_lt (mk_u64 32)
      #i8
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      z
  in
  let r:u32 =
    (mk_u32 2147483648 *!
      (cast ((if (m.[ mk_u64 31 ] <: i8) <. mk_i8 0 <: bool then mk_i32 1 else mk_i32 0) <: i32)
        <:
        u32)
      <:
      u32) +!
    ((mk_u32 1073741824 *!
        (cast ((if (m.[ mk_u64 30 ] <: i8) <. mk_i8 0 <: bool then mk_i32 1 else mk_i32 0) <: i32)
          <:
          u32)
        <:
        u32) +!
      ((mk_u32 536870912 *!
          (cast ((if (m.[ mk_u64 29 ] <: i8) <. mk_i8 0 <: bool then mk_i32 1 else mk_i32 0) <: i32)
            <:
            u32)
          <:
          u32) +!
        ((mk_u32 268435456 *!
            (cast ((if (m.[ mk_u64 28 ] <: i8) <. mk_i8 0 <: bool then mk_i32 1 else mk_i32 0)
                  <:
                  i32)
              <:
              u32)
            <:
            u32) +!
          ((mk_u32 134217728 *!
              (cast ((if (m.[ mk_u64 27 ] <: i8) <. mk_i8 0 <: bool then mk_i32 1 else mk_i32 0)
                    <:
                    i32)
                <:
                u32)
              <:
              u32) +!
            ((mk_u32 67108864 *!
                (cast ((if (m.[ mk_u64 26 ] <: i8) <. mk_i8 0 <: bool then mk_i32 1 else mk_i32 0)
                      <:
                      i32)
                  <:
                  u32)
                <:
                u32) +!
              ((mk_u32 33554432 *!
                  (cast ((if (m.[ mk_u64 25 ] <: i8) <. mk_i8 0 <: bool then mk_i32 1 else mk_i32 0)
                        <:
                        i32)
                    <:
                    u32)
                  <:
                  u32) +!
                ((mk_u32 16777216 *!
                    (cast ((if (m.[ mk_u64 24 ] <: i8) <. mk_i8 0 <: bool
                            then mk_i32 1
                            else mk_i32 0)
                          <:
                          i32)
                      <:
                      u32)
                    <:
                    u32) +!
                  ((mk_u32 8388608 *!
                      (cast ((if (m.[ mk_u64 23 ] <: i8) <. mk_i8 0 <: bool
                              then mk_i32 1
                              else mk_i32 0)
                            <:
                            i32)
                        <:
                        u32)
                      <:
                      u32) +!
                    ((mk_u32 4194304 *!
                        (cast ((if (m.[ mk_u64 22 ] <: i8) <. mk_i8 0 <: bool
                                then mk_i32 1
                                else mk_i32 0)
                              <:
                              i32)
                          <:
                          u32)
                        <:
                        u32) +!
                      ((mk_u32 2097152 *!
                          (cast ((if (m.[ mk_u64 21 ] <: i8) <. mk_i8 0 <: bool
                                  then mk_i32 1
                                  else mk_i32 0)
                                <:
                                i32)
                            <:
                            u32)
                          <:
                          u32) +!
                        ((mk_u32 1048576 *!
                            (cast ((if (m.[ mk_u64 20 ] <: i8) <. mk_i8 0 <: bool
                                    then mk_i32 1
                                    else mk_i32 0)
                                  <:
                                  i32)
                              <:
                              u32)
                            <:
                            u32) +!
                          ((mk_u32 524288 *!
                              (cast ((if (m.[ mk_u64 19 ] <: i8) <. mk_i8 0 <: bool
                                      then mk_i32 1
                                      else mk_i32 0)
                                    <:
                                    i32)
                                <:
                                u32)
                              <:
                              u32) +!
                            ((mk_u32 262144 *!
                                (cast ((if (m.[ mk_u64 18 ] <: i8) <. mk_i8 0 <: bool
                                        then mk_i32 1
                                        else mk_i32 0)
                                      <:
                                      i32)
                                  <:
                                  u32)
                                <:
                                u32) +!
                              ((mk_u32 131072 *!
                                  (cast ((if (m.[ mk_u64 17 ] <: i8) <. mk_i8 0 <: bool
                                          then mk_i32 1
                                          else mk_i32 0)
                                        <:
                                        i32)
                                    <:
                                    u32)
                                  <:
                                  u32) +!
                                ((mk_u32 65536 *!
                                    (cast ((if (m.[ mk_u64 16 ] <: i8) <. mk_i8 0 <: bool
                                            then mk_i32 1
                                            else mk_i32 0)
                                          <:
                                          i32)
                                      <:
                                      u32)
                                    <:
                                    u32) +!
                                  ((mk_u32 32768 *!
                                      (cast ((if (m.[ mk_u64 15 ] <: i8) <. mk_i8 0 <: bool
                                              then mk_i32 1
                                              else mk_i32 0)
                                            <:
                                            i32)
                                        <:
                                        u32)
                                      <:
                                      u32) +!
                                    ((mk_u32 16384 *!
                                        (cast ((if (m.[ mk_u64 14 ] <: i8) <. mk_i8 0 <: bool
                                                then mk_i32 1
                                                else mk_i32 0)
                                              <:
                                              i32)
                                          <:
                                          u32)
                                        <:
                                        u32) +!
                                      ((mk_u32 8192 *!
                                          (cast ((if (m.[ mk_u64 13 ] <: i8) <. mk_i8 0 <: bool
                                                  then mk_i32 1
                                                  else mk_i32 0)
                                                <:
                                                i32)
                                            <:
                                            u32)
                                          <:
                                          u32) +!
                                        ((mk_u32 4096 *!
                                            (cast ((if (m.[ mk_u64 12 ] <: i8) <. mk_i8 0 <: bool
                                                    then mk_i32 1
                                                    else mk_i32 0)
                                                  <:
                                                  i32)
                                              <:
                                              u32)
                                            <:
                                            u32) +!
                                          ((mk_u32 2048 *!
                                              (cast ((if (m.[ mk_u64 11 ] <: i8) <. mk_i8 0 <: bool
                                                      then mk_i32 1
                                                      else mk_i32 0)
                                                    <:
                                                    i32)
                                                <:
                                                u32)
                                              <:
                                              u32) +!
                                            ((mk_u32 1024 *!
                                                (cast ((if
                                                          (m.[ mk_u64 10 ] <: i8) <. mk_i8 0 <: bool
                                                        then mk_i32 1
                                                        else mk_i32 0)
                                                      <:
                                                      i32)
                                                  <:
                                                  u32)
                                                <:
                                                u32) +!
                                              ((mk_u32 512 *!
                                                  (cast ((if
                                                            (m.[ mk_u64 9 ] <: i8) <. mk_i8 0
                                                            <:
                                                            bool
                                                          then mk_i32 1
                                                          else mk_i32 0)
                                                        <:
                                                        i32)
                                                    <:
                                                    u32)
                                                  <:
                                                  u32) +!
                                                ((mk_u32 256 *!
                                                    (cast ((if
                                                              (m.[ mk_u64 8 ] <: i8) <. mk_i8 0
                                                              <:
                                                              bool
                                                            then mk_i32 1
                                                            else mk_i32 0)
                                                          <:
                                                          i32)
                                                      <:
                                                      u32)
                                                    <:
                                                    u32) +!
                                                  ((mk_u32 128 *!
                                                      (cast ((if
                                                                (m.[ mk_u64 7 ] <: i8) <. mk_i8 0
                                                                <:
                                                                bool
                                                              then mk_i32 1
                                                              else mk_i32 0)
                                                            <:
                                                            i32)
                                                        <:
                                                        u32)
                                                      <:
                                                      u32) +!
                                                    ((mk_u32 64 *!
                                                        (cast ((if
                                                                  (m.[ mk_u64 6 ] <: i8) <. mk_i8 0
                                                                  <:
                                                                  bool
                                                                then mk_i32 1
                                                                else mk_i32 0)
                                                              <:
                                                              i32)
                                                          <:
                                                          u32)
                                                        <:
                                                        u32) +!
                                                      ((mk_u32 32 *!
                                                          (cast ((if
                                                                    (m.[ mk_u64 5 ] <: i8) <.
                                                                    mk_i8 0
                                                                    <:
                                                                    bool
                                                                  then mk_i32 1
                                                                  else mk_i32 0)
                                                                <:
                                                                i32)
                                                            <:
                                                            u32)
                                                          <:
                                                          u32) +!
                                                        ((mk_u32 16 *!
                                                            (cast ((if
                                                                      (m.[ mk_u64 4 ] <: i8) <.
                                                                      mk_i8 0
                                                                      <:
                                                                      bool
                                                                    then mk_i32 1
                                                                    else mk_i32 0)
                                                                  <:
                                                                  i32)
                                                              <:
                                                              u32)
                                                            <:
                                                            u32) +!
                                                          ((mk_u32 8 *!
                                                              (cast ((if
                                                                        (m.[ mk_u64 3 ] <: i8) <.
                                                                        mk_i8 0
                                                                        <:
                                                                        bool
                                                                      then mk_i32 1
                                                                      else mk_i32 0)
                                                                    <:
                                                                    i32)
                                                                <:
                                                                u32)
                                                              <:
                                                              u32) +!
                                                            ((mk_u32 4 *!
                                                                (cast ((if
                                                                          (m.[ mk_u64 2 ] <: i8) <.
                                                                          mk_i8 0
                                                                          <:
                                                                          bool
                                                                        then mk_i32 1
                                                                        else mk_i32 0)
                                                                      <:
                                                                      i32)
                                                                  <:
                                                                  u32)
                                                                <:
                                                                u32) +!
                                                              ((mk_u32 2 *!
                                                                  (cast ((if
                                                                            (m.[ mk_u64 1 ] <: i8) <.
                                                                            mk_i8 0
                                                                            <:
                                                                            bool
                                                                          then mk_i32 1
                                                                          else mk_i32 0)
                                                                        <:
                                                                        i32)
                                                                    <:
                                                                    u32)
                                                                  <:
                                                                  u32) +!
                                                                (cast ((if
                                                                          (m.[ mk_u64 0 ] <: i8) <.
                                                                          mk_i8 0
                                                                          <:
                                                                          bool
                                                                        then mk_i32 1
                                                                        else mk_i32 0)
                                                                      <:
                                                                      i32)
                                                                  <:
                                                                  u32)
                                                                <:
                                                                u32)
                                                              <:
                                                              u32)
                                                            <:
                                                            u32)
                                                          <:
                                                          u32)
                                                        <:
                                                        u32)
                                                      <:
                                                      u32)
                                                    <:
                                                    u32)
                                                  <:
                                                  u32)
                                                <:
                                                u32)
                                              <:
                                              u32)
                                            <:
                                            u32)
                                          <:
                                          u32)
                                        <:
                                        u32)
                                      <:
                                      u32)
                                    <:
                                    u32)
                                  <:
                                  u32)
                                <:
                                u32)
                              <:
                              u32)
                            <:
                            u32)
                          <:
                          u32)
                        <:
                        u32)
                      <:
                      u32)
                    <:
                    u32)
                  <:
                  u32)
                <:
                u32)
              <:
              u32)
            <:
            u32)
          <:
          u32)
        <:
        u32)
      <:
      u32)
  in
  cast (r <: u32) <: i32

/// Multiplies the low 32-bit integers from each packed 64-bit element in
/// `a` and `b`
/// Returns the 64-bit results.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mul_epi32)
let e_mm256_mul_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
      #i32
      #i64
      (Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
          #i64
          #i32
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
      #i32
      #i64
      (Core_models.Abstractions.Simd.simd_cast (mk_u64 4)
          #i64
          #i32
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_mul (mk_u64 4) #i64 a b
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Multiplies the low unsigned 32-bit integers from each packed 64-bit
/// element in `a` and `b`
/// Returns the unsigned 64-bit results.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mul_epu32)
let e_mm256_mul_epu32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_7__impl_2__to_u64x4 a
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_7__impl_2__to_u64x4 b
  in
  let mask:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_7__impl_1__splat (Core.Convert.f_into #u32
          #u64
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_u32__MAX
        <:
        u64)
  in
  Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_7__impl_2__from_u64x4 (Core_models.Abstractions.Simd.simd_mul
        (mk_u64 4)
        #u64
        (Core_models.Abstractions.Simd.simd_and (mk_u64 4) #u64 a mask
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)
        (Core_models.Abstractions.Simd.simd_and (mk_u64 4) #u64 b mask
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)

/// Multiplies the packed 16-bit integers in `a` and `b`, producing
/// intermediate 32-bit integers and returning the high 16 bits of the
/// intermediate integers.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mulhi_epi16)
let e_mm256_mulhi_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 16)
      #i16
      #i32
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 16)
      #i16
      #i32
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
  in
  let r:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i32 =
    Core_models.Abstractions.Simd.simd_shr (mk_u64 16)
      #i32
      (Core_models.Abstractions.Simd.simd_mul (mk_u64 16) #i32 a b
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i32)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_21__impl_1__splat (mk_i32 16)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i32)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 16) #i32 #i16 r
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Multiplies the packed unsigned 16-bit integers in `a` and `b`, producing
/// intermediate 32-bit integers and returning the high 16 bits of the
/// intermediate integers.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mulhi_epu16)
let e_mm256_mulhi_epu16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 16)
      #u16
      #u32
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_2__to_u16x16 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
  in
  let b:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32 =
    Core_models.Abstractions.Simd.simd_cast (mk_u64 16)
      #u16
      #u32
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_2__to_u16x16 b
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
  in
  let r:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32 =
    Core_models.Abstractions.Simd.simd_shr (mk_u64 16)
      #u32
      (Core_models.Abstractions.Simd.simd_mul (mk_u64 16) #u32 a b
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_19__impl_1__splat (mk_u32 16)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u32)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_cast (mk_u64 16) #u32 #u16 r
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)

/// Multiplies the packed 16-bit integers in `a` and `b`, producing
/// intermediate 32-bit integers, and returns the low 16 bits of the
/// intermediate integers
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mullo_epi16)
let e_mm256_mullo_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_mul (mk_u64 16)
        #i16
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Multiplies the packed 32-bit integers in `a` and `b`, producing
/// intermediate 64-bit integers, and returns the low 32 bits of the
/// intermediate integers
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mullo_epi32)
let e_mm256_mullo_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_mul (mk_u64 8)
        #i32
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Computes the bitwise OR of 256 bits (representing integer data) in `a`
/// and `b`
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_or_si256)
let e_mm256_or_si256 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_or (mk_u64 8)
        #i32
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Converts packed 16-bit integers from `a` and `b` to packed 8-bit integers
/// using signed saturation
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_packs_epi16)
let e_mm256_packs_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (packsswb (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)

/// Converts packed 32-bit integers from `a` and `b` to packed 16-bit integers
/// using signed saturation
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_packs_epi32)
let e_mm256_packs_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (packssdw (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Converts packed 16-bit integers from `a` and `b` to packed 8-bit integers
/// using unsigned saturation
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_packus_epi16)
let e_mm256_packus_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (packuswb (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)

/// Converts packed 32-bit integers from `a` and `b` to packed 16-bit integers
/// using unsigned saturation
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_packus_epi32)
let e_mm256_packus_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (packusdw (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)

/// Permutes packed 32-bit integers from `a` according to the content of `b`.
/// The last 3 bits of each integer of `b` are used as addresses into the 8
/// integers of `a`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permutevar8x32_epi32)
let e_mm256_permutevar8x32_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (permd (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_6__impl_2__to_u32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_6__impl_2__to_u32x8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)

/// Permutes 64-bit integers from `a` using control mask `imm8`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permute4x64_epi64)
let e_mm256_permute4x64_epi64
      (v_IMM8: i32)
      (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let zero:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 4)
      #i64
      (fun temp_0_ ->
          let _:u64 = temp_0_ in
          mk_i64 0)
  in
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i64 =
    Core_models.Abstractions.Simd.simd_shuffle #i64
      (mk_u64 4)
      (mk_usize 4)
      (mk_u64 4)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      zero
      (let list =
          [
            (cast (v_IMM8 <: i32) <: u64) &. mk_u64 3 <: u64;
            ((cast (v_IMM8 <: i32) <: u64) >>! mk_i32 2 <: u64) &. mk_u64 3 <: u64;
            ((cast (v_IMM8 <: i32) <: u64) >>! mk_i32 4 <: u64) &. mk_u64 3 <: u64;
            ((cast (v_IMM8 <: i32) <: u64) >>! mk_i32 6 <: u64) &. mk_u64 3 <: u64
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    r

/// Shuffles 128-bits of integer data selected by `imm8` from `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permute2x128_si256)
let e_mm256_permute2x128_si256
      (v_IMM8: i32)
      (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (vperm2i128 (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (cast (v_IMM8 <: i32) <: i8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Shuffles bytes from `a` according to the content of `b`.
/// For each of the 128-bit low and high halves of the vectors, the last
/// 4 bits of each byte of `b` are used as addresses into the respective
/// low or high 16 bytes of `a`. That is, the halves are shuffled separately.
/// In addition, if the highest significant bit of a byte of `b` is set, the
/// respective destination byte is set to 0.
/// Picturing `a` and `b` as `[u8; 32]`, `_mm256_shuffle_epi8` is logically
/// equivalent to:
/// ```
/// fn mm256_shuffle_epi8(a: [u8; 32], b: [u8; 32]) -> [u8; 32] {
///     let mut r = [0; 32];
///     for i in 0..16 {
///         // if the most significant bit of b is set,
///         // then the destination byte is set to 0.
///         if b[i] & 0x80 == 0u8 {
///             r[i] = a[(b[i] % 16) as usize];
///         }
///         if b[i + 16] & 0x80 == 0u8 {
///             r[i + 16] = a[(b[i + 16] % 16 + 16) as usize];
///         }
///     }
///     r
/// }
/// ```
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shuffle_epi8)
let e_mm256_shuffle_epi8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (pshufb (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_9__impl_2__to_u8x32 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_9__impl_2__to_u8x32 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)

/// Shuffles 32-bit integers in 128-bit lanes of `a` using the control in
/// `imm8`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shuffle_epi32)
let e_mm256_shuffle_epi32 (v_MASK: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) i32 =
    Core_models.Abstractions.Simd.simd_shuffle #i32
      (mk_u64 8)
      (mk_usize 8)
      (mk_u64 8)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      (let list =
          [
            (cast (v_MASK <: i32) <: u64) &. mk_u64 3 <: u64;
            ((cast (v_MASK <: i32) <: u64) >>! mk_i32 2 <: u64) &. mk_u64 3 <: u64;
            ((cast (v_MASK <: i32) <: u64) >>! mk_i32 4 <: u64) &. mk_u64 3 <: u64;
            ((cast (v_MASK <: i32) <: u64) >>! mk_i32 6 <: u64) &. mk_u64 3 <: u64;
            ((cast (v_MASK <: i32) <: u64) &. mk_u64 3 <: u64) +! mk_u64 4 <: u64;
            (((cast (v_MASK <: i32) <: u64) >>! mk_i32 2 <: u64) &. mk_u64 3 <: u64) +! mk_u64 4
            <:
            u64;
            (((cast (v_MASK <: i32) <: u64) >>! mk_i32 4 <: u64) &. mk_u64 3 <: u64) +! mk_u64 4
            <:
            u64;
            (((cast (v_MASK <: i32) <: u64) >>! mk_i32 6 <: u64) &. mk_u64 3 <: u64) +! mk_u64 4
            <:
            u64
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
        Rust_primitives.Hax.array_of_list 8 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    r

/// Shuffles 16-bit integers in the high 64 bits of 128-bit lanes of `a` using
/// the control in `imm8`. The low 64 bits of 128-bit lanes of `a` are copied
/// to the output.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shufflehi_epi16)
let e_mm256_shufflehi_epi16 (v_IMM8: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
  in
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 16) i16 =
    Core_models.Abstractions.Simd.simd_shuffle #i16
      (mk_u64 16)
      (mk_usize 16)
      (mk_u64 16)
      a
      a
      (let list =
          [
            mk_u64 0; mk_u64 1; mk_u64 2; mk_u64 3;
            mk_u64 4 +! ((cast (v_IMM8 <: i32) <: u64) &. mk_u64 3 <: u64) <: u64;
            mk_u64 4 +! (((cast (v_IMM8 <: i32) <: u64) >>! mk_i32 2 <: u64) &. mk_u64 3 <: u64)
            <:
            u64;
            mk_u64 4 +! (((cast (v_IMM8 <: i32) <: u64) >>! mk_i32 4 <: u64) &. mk_u64 3 <: u64)
            <:
            u64;
            mk_u64 4 +! (((cast (v_IMM8 <: i32) <: u64) >>! mk_i32 6 <: u64) &. mk_u64 3 <: u64)
            <:
            u64; mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11;
            mk_u64 12 +! ((cast (v_IMM8 <: i32) <: u64) &. mk_u64 3 <: u64) <: u64;
            mk_u64 12 +! (((cast (v_IMM8 <: i32) <: u64) >>! mk_i32 2 <: u64) &. mk_u64 3 <: u64)
            <:
            u64;
            mk_u64 12 +! (((cast (v_IMM8 <: i32) <: u64) >>! mk_i32 4 <: u64) &. mk_u64 3 <: u64)
            <:
            u64;
            mk_u64 12 +! (((cast (v_IMM8 <: i32) <: u64) >>! mk_i32 6 <: u64) &. mk_u64 3 <: u64)
            <:
            u64
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    r

/// Shuffles 16-bit integers in the low 64 bits of 128-bit lanes of `a` using
/// the control in `imm8`. The high 64 bits of 128-bit lanes of `a` are copied
/// to the output.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shufflelo_epi16)
let e_mm256_shufflelo_epi16 (v_IMM8: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
  in
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 16) i16 =
    Core_models.Abstractions.Simd.simd_shuffle #i16
      (mk_u64 16)
      (mk_usize 16)
      (mk_u64 16)
      a
      a
      (let list =
          [
            mk_u64 0 +! ((cast (v_IMM8 <: i32) <: u64) &. mk_u64 3 <: u64) <: u64;
            mk_u64 0 +! (((cast (v_IMM8 <: i32) <: u64) >>! mk_i32 2 <: u64) &. mk_u64 3 <: u64)
            <:
            u64;
            mk_u64 0 +! (((cast (v_IMM8 <: i32) <: u64) >>! mk_i32 4 <: u64) &. mk_u64 3 <: u64)
            <:
            u64;
            mk_u64 0 +! (((cast (v_IMM8 <: i32) <: u64) >>! mk_i32 6 <: u64) &. mk_u64 3 <: u64)
            <:
            u64; mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7;
            mk_u64 8 +! ((cast (v_IMM8 <: i32) <: u64) &. mk_u64 3 <: u64) <: u64;
            mk_u64 8 +! (((cast (v_IMM8 <: i32) <: u64) >>! mk_i32 2 <: u64) &. mk_u64 3 <: u64)
            <:
            u64;
            mk_u64 8 +! (((cast (v_IMM8 <: i32) <: u64) >>! mk_i32 4 <: u64) &. mk_u64 3 <: u64)
            <:
            u64;
            mk_u64 8 +! (((cast (v_IMM8 <: i32) <: u64) >>! mk_i32 6 <: u64) &. mk_u64 3 <: u64)
            <:
            u64; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    r

/// Negates packed 16-bit integers in `a` when the corresponding signed
/// 16-bit integer in `b` is negative, and returns the results.
/// Results are zeroed out when the corresponding element in `b` is zero.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sign_epi16)
let e_mm256_sign_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (psignw (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Negates packed 32-bit integers in `a` when the corresponding signed
/// 32-bit integer in `b` is negative, and returns the results.
/// Results are zeroed out when the corresponding element in `b` is zero.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sign_epi32)
let e_mm256_sign_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (psignd (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Negates packed 8-bit integers in `a` when the corresponding signed
/// 8-bit integer in `b` is negative, and returns the results.
/// Results are zeroed out when the corresponding element in `b` is zero.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sign_epi8)
let e_mm256_sign_epi8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (psignb (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)

/// Shifts packed 16-bit integers in `a` left by `count` while
/// shifting in zeros, and returns the result
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sll_epi16)
let e_mm256_sll_epi16
      (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (psllw (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Shifts packed 32-bit integers in `a` left by `count` while
/// shifting in zeros, and returns the result
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sll_epi32)
let e_mm256_sll_epi32
      (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (pslld (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Shifts packed 64-bit integers in `a` left by `count` while
/// shifting in zeros, and returns the result
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sll_epi64)
let e_mm256_sll_epi64
      (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (psllq (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_2__to_i64x2 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Shifts packed 16-bit integers in `a` left by `IMM8` while
/// shifting in zeros, return the results;
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi16)
let e_mm256_slli_epi16 (v_IMM8: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  if v_IMM8 >=. mk_i32 16
  then e_mm256_setzero_si256 ()
  else
    Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
      #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Abstractions.Simd.simd_shl (mk_u64 16)
          #u16
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_2__to_u16x16 a
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_1__splat (cast (v_IMM8 <: i32
                  )
                <:
                u16)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)

/// Shifts packed 32-bit integers in `a` left by `IMM8` while
/// shifting in zeros, return the results;
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi32)
let e_mm256_slli_epi32 (v_IMM8: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  if v_IMM8 >=. mk_i32 32
  then e_mm256_setzero_si256 ()
  else
    Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
      #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Abstractions.Simd.simd_shl (mk_u64 8)
          #u32
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_6__impl_2__to_u32x8 a
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_6__impl_1__splat (cast (v_IMM8 <: i32
                  )
                <:
                u32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)

/// Shifts packed 64-bit integers in `a` left by `IMM8` while
/// shifting in zeros, return the results;
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi64)
let e_mm256_slli_epi64 (v_IMM8: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  if v_IMM8 >=. mk_i32 64
  then e_mm256_setzero_si256 ()
  else
    Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)
      #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Abstractions.Simd.simd_shl (mk_u64 4)
          #u64
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_7__impl_2__to_u64x4 a
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_7__impl_1__splat (cast (v_IMM8 <: i32
                  )
                <:
                u64)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)

let e_mm256_bslli_epi128__mask (shift: i32) (i: u32) : u32 =
  let shift:u32 = (cast (shift <: i32) <: u32) &. mk_u32 255 in
  if shift >. mk_u32 15 || (i %! mk_u32 16 <: u32) <. shift
  then mk_u32 0
  else mk_u32 32 +! (i -! shift <: u32)

/// Shifts 128-bit lanes in `a` left by `imm8` bytes while shifting in zeros.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_bslli_epi128)
let e_mm256_bslli_epi128 (v_IMM8: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
  in
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 32) i8 =
    Core_models.Abstractions.Simd.simd_shuffle #i8
      (mk_u64 32)
      (mk_usize 32)
      (mk_u64 32)
      (Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 32)
          #i8
          (fun temp_0_ ->
              let _:u64 = temp_0_ in
              mk_i8 0)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      a
      (let list =
          [
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 0) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 1) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 2) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 3) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 4) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 5) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 6) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 7) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 8) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 9) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 10) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 11) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 12) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 13) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 14) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 15) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 16) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 17) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 18) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 19) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 20) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 21) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 22) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 23) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 24) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 25) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 26) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 27) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 28) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 29) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 30) <: u32) <: u64;
            cast (e_mm256_bslli_epi128__mask v_IMM8 (mk_u32 31) <: u32) <: u64
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
        Rust_primitives.Hax.array_of_list 32 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    r

/// Shifts 128-bit lanes in `a` left by `imm8` bytes while shifting in zeros.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_si256)
let e_mm256_slli_si256 (v_IMM8: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = e_mm256_bslli_epi128 v_IMM8 a

/// Shifts packed 32-bit integers in `a` left by the amount
/// specified by the corresponding element in `count` while
/// shifting in zeros, and returns the result.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sllv_epi32)
let e_mm_sllv_epi32 (a count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    #FStar.Tactics.Typeclasses.solve
    (psllvd (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)

/// Shifts packed 32-bit integers in `a` left by the amount
/// specified by the corresponding element in `count` while
/// shifting in zeros, and returns the result.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sllv_epi32)
let e_mm256_sllv_epi32 (a count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (psllvd256 (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Shifts packed 64-bit integers in `a` left by the amount
/// specified by the corresponding element in `count` while
/// shifting in zeros, and returns the result.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sllv_epi64)
let e_mm_sllv_epi64 (a count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    #FStar.Tactics.Typeclasses.solve
    (psllvq (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_2__to_i64x2 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_2__to_i64x2 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)

/// Shifts packed 64-bit integers in `a` left by the amount
/// specified by the corresponding element in `count` while
/// shifting in zeros, and returns the result.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sllv_epi64)
let e_mm256_sllv_epi64 (a count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (psllvq256 (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Shifts packed 16-bit integers in `a` right by `count` while
/// shifting in sign bits.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sra_epi16)
let e_mm256_sra_epi16
      (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (psraw (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Shifts packed 32-bit integers in `a` right by `count` while
/// shifting in sign bits.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sra_epi32)
let e_mm256_sra_epi32
      (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (psrad (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Shifts packed 16-bit integers in `a` right by `IMM8` while
/// shifting in sign bits.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srai_epi16)
let e_mm256_srai_epi16 (v_IMM8: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_shr (mk_u64 16)
        #i16
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_1__splat (cast (Core.Cmp.f_min #i32
                    #FStar.Tactics.Typeclasses.solve
                    v_IMM8
                    (mk_i32 15)
                  <:
                  i32)
              <:
              i16)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Shifts packed 32-bit integers in `a` right by `IMM8` while
/// shifting in sign bits.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srai_epi32)
let e_mm256_srai_epi32 (v_IMM8: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_shr (mk_u64 8)
        #i32
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_1__splat (Core.Cmp.f_min #i32
                #FStar.Tactics.Typeclasses.solve
                v_IMM8
                (mk_i32 31)
              <:
              i32)
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Shifts packed 32-bit integers in `a` right by the amount specified by the
/// corresponding element in `count` while shifting in sign bits.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srav_epi32)
let e_mm_srav_epi32 (a count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    #FStar.Tactics.Typeclasses.solve
    (psravd (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)

/// Shifts packed 32-bit integers in `a` right by the amount specified by the
/// corresponding element in `count` while shifting in sign bits.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srav_epi32)
let e_mm256_srav_epi32 (a count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (psravd256 (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Shifts 128-bit lanes in `a` right by `imm8` bytes while shifting in zeros.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_bsrli_epi128)
let e_mm256_bsrli_epi128 (v_IMM8: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let a:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
    Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
  in
  let zero:Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8 =
    Core_models.Abstractions.Funarr.impl_5__from_fn (mk_u64 32)
      #i8
      (fun temp_0_ ->
          let _:u64 = temp_0_ in
          mk_i8 0)
  in
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 32) i8 =
    match v_IMM8 %! mk_i32 16 <: i32 with
    | Rust_primitives.Integers.MkInt 0 ->
      Core_models.Abstractions.Simd.simd_shuffle #i8
        (mk_u64 32)
        (mk_usize 32)
        (mk_u64 32)
        a
        zero
        (let list =
            [
              mk_u64 0; mk_u64 1; mk_u64 2; mk_u64 3; mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7;
              mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15;
              mk_u64 16; mk_u64 17; mk_u64 18; mk_u64 19; mk_u64 20; mk_u64 21; mk_u64 22; mk_u64 23;
              mk_u64 24; mk_u64 25; mk_u64 26; mk_u64 27; mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
          Rust_primitives.Hax.array_of_list 32 list)
    | Rust_primitives.Integers.MkInt 1 ->
      Core_models.Abstractions.Simd.simd_shuffle #i8
        (mk_u64 32)
        (mk_usize 32)
        (mk_u64 32)
        a
        zero
        (let list =
            [
              mk_u64 1; mk_u64 2; mk_u64 3; mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7; mk_u64 8;
              mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32;
              mk_u64 17; mk_u64 18; mk_u64 19; mk_u64 20; mk_u64 21; mk_u64 22; mk_u64 23; mk_u64 24;
              mk_u64 25; mk_u64 26; mk_u64 27; mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 32
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
          Rust_primitives.Hax.array_of_list 32 list)
    | Rust_primitives.Integers.MkInt 2 ->
      Core_models.Abstractions.Simd.simd_shuffle #i8
        (mk_u64 32)
        (mk_usize 32)
        (mk_u64 32)
        a
        zero
        (let list =
            [
              mk_u64 2; mk_u64 3; mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7; mk_u64 8; mk_u64 9;
              mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 32;
              mk_u64 18; mk_u64 19; mk_u64 20; mk_u64 21; mk_u64 22; mk_u64 23; mk_u64 24; mk_u64 25;
              mk_u64 26; mk_u64 27; mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 32; mk_u64 32
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
          Rust_primitives.Hax.array_of_list 32 list)
    | Rust_primitives.Integers.MkInt 3 ->
      Core_models.Abstractions.Simd.simd_shuffle #i8
        (mk_u64 32)
        (mk_usize 32)
        (mk_u64 32)
        a
        zero
        (let list =
            [
              mk_u64 3; mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7; mk_u64 8; mk_u64 9; mk_u64 10;
              mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 19; mk_u64 20; mk_u64 21; mk_u64 22; mk_u64 23; mk_u64 24; mk_u64 25; mk_u64 26;
              mk_u64 27; mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 32; mk_u64 32; mk_u64 32
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
          Rust_primitives.Hax.array_of_list 32 list)
    | Rust_primitives.Integers.MkInt 4 ->
      Core_models.Abstractions.Simd.simd_shuffle #i8
        (mk_u64 32)
        (mk_usize 32)
        (mk_u64 32)
        a
        zero
        (let list =
            [
              mk_u64 4; mk_u64 5; mk_u64 6; mk_u64 7; mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11;
              mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 20; mk_u64 21; mk_u64 22; mk_u64 23; mk_u64 24; mk_u64 25; mk_u64 26; mk_u64 27;
              mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
          Rust_primitives.Hax.array_of_list 32 list)
    | Rust_primitives.Integers.MkInt 5 ->
      Core_models.Abstractions.Simd.simd_shuffle #i8
        (mk_u64 32)
        (mk_usize 32)
        (mk_u64 32)
        a
        zero
        (let list =
            [
              mk_u64 5; mk_u64 6; mk_u64 7; mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12;
              mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 21; mk_u64 22; mk_u64 23; mk_u64 24; mk_u64 25; mk_u64 26; mk_u64 27; mk_u64 28;
              mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
          Rust_primitives.Hax.array_of_list 32 list)
    | Rust_primitives.Integers.MkInt 6 ->
      Core_models.Abstractions.Simd.simd_shuffle #i8
        (mk_u64 32)
        (mk_usize 32)
        (mk_u64 32)
        a
        zero
        (let list =
            [
              mk_u64 6; mk_u64 7; mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13;
              mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 22; mk_u64 23; mk_u64 24; mk_u64 25; mk_u64 26; mk_u64 27; mk_u64 28; mk_u64 29;
              mk_u64 30; mk_u64 31; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
          Rust_primitives.Hax.array_of_list 32 list)
    | Rust_primitives.Integers.MkInt 7 ->
      Core_models.Abstractions.Simd.simd_shuffle #i8
        (mk_u64 32)
        (mk_usize 32)
        (mk_u64 32)
        a
        zero
        (let list =
            [
              mk_u64 7; mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14;
              mk_u64 15; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 23; mk_u64 24; mk_u64 25; mk_u64 26; mk_u64 27; mk_u64 28; mk_u64 29; mk_u64 30;
              mk_u64 31; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
          Rust_primitives.Hax.array_of_list 32 list)
    | Rust_primitives.Integers.MkInt 8 ->
      Core_models.Abstractions.Simd.simd_shuffle #i8
        (mk_u64 32)
        (mk_usize 32)
        (mk_u64 32)
        a
        zero
        (let list =
            [
              mk_u64 8; mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15;
              mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 24; mk_u64 25; mk_u64 26; mk_u64 27; mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31;
              mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
          Rust_primitives.Hax.array_of_list 32 list)
    | Rust_primitives.Integers.MkInt 9 ->
      Core_models.Abstractions.Simd.simd_shuffle #i8
        (mk_u64 32)
        (mk_usize 32)
        (mk_u64 32)
        a
        zero
        (let list =
            [
              mk_u64 9; mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32;
              mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 25; mk_u64 26; mk_u64 27; mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 32;
              mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
          Rust_primitives.Hax.array_of_list 32 list)
    | Rust_primitives.Integers.MkInt 10 ->
      Core_models.Abstractions.Simd.simd_shuffle #i8
        (mk_u64 32)
        (mk_usize 32)
        (mk_u64 32)
        a
        zero
        (let list =
            [
              mk_u64 10; mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 32;
              mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 26; mk_u64 27; mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 32; mk_u64 32;
              mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
          Rust_primitives.Hax.array_of_list 32 list)
    | Rust_primitives.Integers.MkInt 11 ->
      Core_models.Abstractions.Simd.simd_shuffle #i8
        (mk_u64 32)
        (mk_usize 32)
        (mk_u64 32)
        a
        zero
        (let list =
            [
              mk_u64 11; mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 27; mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
          Rust_primitives.Hax.array_of_list 32 list)
    | Rust_primitives.Integers.MkInt 12 ->
      Core_models.Abstractions.Simd.simd_shuffle #i8
        (mk_u64 32)
        (mk_usize 32)
        (mk_u64 32)
        a
        zero
        (let list =
            [
              mk_u64 12; mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 28; mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
          Rust_primitives.Hax.array_of_list 32 list)
    | Rust_primitives.Integers.MkInt 13 ->
      Core_models.Abstractions.Simd.simd_shuffle #i8
        (mk_u64 32)
        (mk_usize 32)
        (mk_u64 32)
        a
        zero
        (let list =
            [
              mk_u64 13; mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 29; mk_u64 30; mk_u64 31; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
          Rust_primitives.Hax.array_of_list 32 list)
    | Rust_primitives.Integers.MkInt 14 ->
      Core_models.Abstractions.Simd.simd_shuffle #i8
        (mk_u64 32)
        (mk_usize 32)
        (mk_u64 32)
        a
        zero
        (let list =
            [
              mk_u64 14; mk_u64 15; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 30; mk_u64 31; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
          Rust_primitives.Hax.array_of_list 32 list)
    | Rust_primitives.Integers.MkInt 15 ->
      Core_models.Abstractions.Simd.simd_shuffle #i8
        (mk_u64 32)
        (mk_usize 32)
        (mk_u64 32)
        a
        zero
        (let list =
            [
              mk_u64 15; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 31; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32;
              mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32; mk_u64 32
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
          Rust_primitives.Hax.array_of_list 32 list)
    | _ -> zero
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    r

/// Shifts 128-bit lanes in `a` right by `imm8` bytes while shifting in zeros.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_si256)
let e_mm256_srli_si256 (v_IMM8: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) = e_mm256_bsrli_epi128 v_IMM8 a

/// Shifts packed 16-bit integers in `a` right by `count` while shifting in
/// zeros.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srl_epi16)
let e_mm256_srl_epi16
      (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (psrlw (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_12__impl_2__to_i16x8 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Shifts packed 32-bit integers in `a` right by `count` while shifting in
/// zeros.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srl_epi32)
let e_mm256_srl_epi32
      (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (psrld (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Shifts packed 64-bit integers in `a` right by `count` while shifting in
/// zeros.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srl_epi64)
let e_mm256_srl_epi64
      (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      (count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (psrlq (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_2__to_i64x2 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Shifts packed 16-bit integers in `a` right by `IMM8` while shifting in
/// zeros
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi16)
let e_mm256_srli_epi16 (v_IMM8: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  if v_IMM8 >=. mk_i32 16
  then e_mm256_setzero_si256 ()
  else
    Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
      #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Abstractions.Simd.simd_shr (mk_u64 16)
          #u16
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_2__to_u16x16 a
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_1__splat (cast (v_IMM8 <: i32
                  )
                <:
                u16)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)

/// Shifts packed 32-bit integers in `a` right by `IMM8` while shifting in
/// zeros
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi32)
let e_mm256_srli_epi32 (v_IMM8: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  if v_IMM8 >=. mk_i32 32
  then e_mm256_setzero_si256 ()
  else
    Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
      #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Abstractions.Simd.simd_shr (mk_u64 8)
          #u32
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_6__impl_2__to_u32x8 a
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_6__impl_1__splat (cast (v_IMM8 <: i32
                  )
                <:
                u32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) u32)

/// Shifts packed 64-bit integers in `a` right by `IMM8` while shifting in
/// zeros
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi64)
let e_mm256_srli_epi64 (v_IMM8: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  if v_IMM8 >=. mk_i32 64
  then e_mm256_setzero_si256 ()
  else
    Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)
      #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
      #FStar.Tactics.Typeclasses.solve
      (Core_models.Abstractions.Simd.simd_shr (mk_u64 4)
          #u64
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_7__impl_2__to_u64x4 a
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)
          (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_7__impl_1__splat (cast (v_IMM8 <: i32
                  )
                <:
                u64)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) u64)

/// Shifts packed 32-bit integers in `a` right by the amount specified by
/// the corresponding element in `count` while shifting in zeros,
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srlv_epi32)
let e_mm_srlv_epi32 (a count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    #FStar.Tactics.Typeclasses.solve
    (psrlvd (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_10__impl_2__to_i32x4 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i32)

/// Shifts packed 32-bit integers in `a` right by the amount specified by
/// the corresponding element in `count` while shifting in zeros,
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srlv_epi32)
let e_mm256_srlv_epi32 (a count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (psrlvd256 (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Shifts packed 64-bit integers in `a` right by the amount specified by
/// the corresponding element in `count` while shifting in zeros,
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srlv_epi64)
let e_mm_srlv_epi64 (a count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 128))
    #FStar.Tactics.Typeclasses.solve
    (psrlvq (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_2__to_i64x2 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_11__impl_2__to_i64x2 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 2) i64)

/// Shifts packed 64-bit integers in `a` right by the amount specified by
/// the corresponding element in `count` while shifting in zeros,
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srlv_epi64)
let e_mm256_srlv_epi64 (a count: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (psrlvq256 (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 count
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Subtract packed 16-bit integers in `b` from packed 16-bit integers in `a`
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi16)
let e_mm256_sub_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_sub (mk_u64 16)
        #i16
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Subtract packed 32-bit integers in `b` from packed 32-bit integers in `a`
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi32)
let e_mm256_sub_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_sub (mk_u64 8)
        #i32
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)

/// Subtract packed 64-bit integers in `b` from packed 64-bit integers in `a`
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi64)
let e_mm256_sub_epi64 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_sub (mk_u64 4)
        #i64
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Subtract packed 8-bit integers in `b` from packed 8-bit integers in `a`
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi8)
let e_mm256_sub_epi8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_sub (mk_u64 32)
        #i8
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)

/// Subtract packed 16-bit integers in `b` from packed 16-bit integers in
/// `a` using saturation.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_subs_epi16)
let e_mm256_subs_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_saturating_sub #i16
        (mk_u64 16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)

/// Subtract packed 8-bit integers in `b` from packed 8-bit integers in
/// `a` using saturation.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_subs_epi8)
let e_mm256_subs_epi8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_saturating_sub #i8
        (mk_u64 32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)

/// Subtract packed unsigned 16-bit integers in `b` from packed 16-bit
/// integers in `a` using saturation.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_subs_epu16)
let e_mm256_subs_epu16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_saturating_sub #u16
        (mk_u64 16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_2__to_u16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_2__to_u16x16 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)

/// Subtract packed unsigned 8-bit integers in `b` from packed 8-bit
/// integers in `a` using saturation.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_subs_epu8)
let e_mm256_subs_epu8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_saturating_sub #u8
        (mk_u64 32)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_9__impl_2__to_u8x32 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_9__impl_2__to_u8x32 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)

/// Unpacks and interleave 8-bit integers from the high half of each
/// 128-bit lane in `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi8)
let e_mm256_unpackhi_epi8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 32) i8 =
    Core_models.Abstractions.Simd.simd_shuffle #i8
      (mk_u64 32)
      (mk_usize 32)
      (mk_u64 32)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 b
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      (let list =
          [
            mk_u64 8; mk_u64 40; mk_u64 9; mk_u64 41; mk_u64 10; mk_u64 42; mk_u64 11; mk_u64 43;
            mk_u64 12; mk_u64 44; mk_u64 13; mk_u64 45; mk_u64 14; mk_u64 46; mk_u64 15; mk_u64 47;
            mk_u64 24; mk_u64 56; mk_u64 25; mk_u64 57; mk_u64 26; mk_u64 58; mk_u64 27; mk_u64 59;
            mk_u64 28; mk_u64 60; mk_u64 29; mk_u64 61; mk_u64 30; mk_u64 62; mk_u64 31; mk_u64 63
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
        Rust_primitives.Hax.array_of_list 32 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    r

/// Unpacks and interleave 8-bit integers from the low half of each
/// 128-bit lane of `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi8)
let e_mm256_unpacklo_epi8 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 32) i8 =
    Core_models.Abstractions.Simd.simd_shuffle #i8
      (mk_u64 32)
      (mk_usize 32)
      (mk_u64 32)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_5__impl_2__to_i8x32 b
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
      (let list =
          [
            mk_u64 0; mk_u64 32; mk_u64 1; mk_u64 33; mk_u64 2; mk_u64 34; mk_u64 3; mk_u64 35;
            mk_u64 4; mk_u64 36; mk_u64 5; mk_u64 37; mk_u64 6; mk_u64 38; mk_u64 7; mk_u64 39;
            mk_u64 16; mk_u64 48; mk_u64 17; mk_u64 49; mk_u64 18; mk_u64 50; mk_u64 19; mk_u64 51;
            mk_u64 20; mk_u64 52; mk_u64 21; mk_u64 53; mk_u64 22; mk_u64 54; mk_u64 23; mk_u64 55
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
        Rust_primitives.Hax.array_of_list 32 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) i8)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    r

/// Unpacks and interleave 16-bit integers from the high half of each
/// 128-bit lane of `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi16)
let e_mm256_unpackhi_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 16) i16 =
    Core_models.Abstractions.Simd.simd_shuffle #i16
      (mk_u64 16)
      (mk_usize 16)
      (mk_u64 16)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      (let list =
          [
            mk_u64 4; mk_u64 20; mk_u64 5; mk_u64 21; mk_u64 6; mk_u64 22; mk_u64 7; mk_u64 23;
            mk_u64 12; mk_u64 28; mk_u64 13; mk_u64 29; mk_u64 14; mk_u64 30; mk_u64 15; mk_u64 31
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    r

/// Unpacks and interleave 16-bit integers from the low half of each
/// 128-bit lane of `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi16)
let e_mm256_unpacklo_epi16 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 16) i16 =
    Core_models.Abstractions.Simd.simd_shuffle #i16
      (mk_u64 16)
      (mk_usize 16)
      (mk_u64 16)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_3__impl_2__to_i16x16 b
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
      (let list =
          [
            mk_u64 0; mk_u64 16; mk_u64 1; mk_u64 17; mk_u64 2; mk_u64 18; mk_u64 3; mk_u64 19;
            mk_u64 8; mk_u64 24; mk_u64 9; mk_u64 25; mk_u64 10; mk_u64 26; mk_u64 11; mk_u64 27
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) i16)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    r

/// Unpacks and interleave 32-bit integers from the high half of each
/// 128-bit lane of `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi32)
let e_mm256_unpackhi_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) i32 =
    Core_models.Abstractions.Simd.simd_shuffle #i32
      (mk_u64 8)
      (mk_usize 8)
      (mk_u64 8)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      (let list =
          [mk_u64 2; mk_u64 10; mk_u64 3; mk_u64 11; mk_u64 6; mk_u64 14; mk_u64 7; mk_u64 15]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
        Rust_primitives.Hax.array_of_list 8 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    r

/// Unpacks and interleave 32-bit integers from the low half of each
/// 128-bit lane of `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi32)
let e_mm256_unpacklo_epi32 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 8) i32 =
    Core_models.Abstractions.Simd.simd_shuffle #i32
      (mk_u64 8)
      (mk_usize 8)
      (mk_u64 8)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_1__impl_2__to_i32x8 b
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
      (let list =
          [mk_u64 0; mk_u64 8; mk_u64 1; mk_u64 9; mk_u64 4; mk_u64 12; mk_u64 5; mk_u64 13]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
        Rust_primitives.Hax.array_of_list 8 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    r

/// Unpacks and interleave 64-bit integers from the high half of each
/// 128-bit lane of `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi64)
let e_mm256_unpackhi_epi64 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i64 =
    Core_models.Abstractions.Simd.simd_shuffle #i64
      (mk_u64 4)
      (mk_usize 4)
      (mk_u64 4)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      (let list = [mk_u64 1; mk_u64 5; mk_u64 3; mk_u64 7] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    r

/// Unpacks and interleave 64-bit integers from the low half of each
/// 128-bit lane of `a` and `b`.
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi64)
let e_mm256_unpacklo_epi64 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  let (r: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64):Core_models.Abstractions.Funarr.t_FunArray
    (mk_u64 4) i64 =
    Core_models.Abstractions.Simd.simd_shuffle #i64
      (mk_u64 4)
      (mk_usize 4)
      (mk_u64 4)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      (let list = [mk_u64 0; mk_u64 4; mk_u64 2; mk_u64 6] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
  in
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    r

/// Computes the bitwise XOR of 256 bits (representing integer data)
/// in `a` and `b`
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_xor_si256)
let e_mm256_xor_si256 (a b: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) =
  Core.Convert.f_into #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
    #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    #FStar.Tactics.Typeclasses.solve
    (Core_models.Abstractions.Simd.simd_xor (mk_u64 4)
        #i64
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_2__impl_2__to_i64x4 b
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
      <:
      Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)

/// Extracts an 8-bit integer from `a`, selected with `INDEX`. Returns a 32-bit
/// integer containing the zero-extended integer data.
/// See [LLVM commit D20468](https://reviews.llvm.org/D20468).
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_extract_epi8)
let e_mm256_extract_epi8 (v_INDEX: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : i32 =
  cast (Core_models.Abstractions.Simd.simd_extract (mk_u64 32)
        #u8
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_9__impl_2__to_u8x32 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 32) u8)
        (cast (v_INDEX <: i32) <: u64)
      <:
      u8)
  <:
  i32

/// Extracts a 16-bit integer from `a`, selected with `INDEX`. Returns a 32-bit
/// integer containing the zero-extended integer data.
/// See [LLVM commit D20468](https://reviews.llvm.org/D20468).
/// [Intel's documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_extract_epi16)
let e_mm256_extract_epi16 (v_INDEX: i32) (a: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : i32 =
  cast (Core_models.Abstractions.Simd.simd_extract (mk_u64 16)
        #u16
        (Core_models.Abstractions.Bitvec.Int_vec_interp.e_ee_8__impl_2__to_u16x16 a
          <:
          Core_models.Abstractions.Funarr.t_FunArray (mk_u64 16) u16)
        (cast (v_INDEX <: i32) <: u64)
      <:
      u16)
  <:
  i32
