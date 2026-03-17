// verifast_options{skip_specless_fns ignore_unwind_paths}

#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(stable_features)]
#![no_std]
#![allow(internal_features)]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(staged_api)]
#![feature(rustc_attrs)]
#![feature(dropck_eyepatch)]
#![feature(specialization)]
#![feature(extend_one)]
#![feature(exact_size_is_empty)]
#![feature(hasher_prefixfree_extras)]
#![feature(box_into_inner)]
#![feature(try_trait_v2)]
#![feature(optimize_attribute)]
#![feature(temporary_niche_types)]
#![feature(ptr_internals)]
#![feature(try_reserve_kind)]
#![feature(ptr_alignment_type)]
#![feature(sized_type_properties)]
#![feature(std_internals)]
#![feature(alloc_layout_extra)]
#![feature(nonnull_provenance)]
#![feature(panic_internals)]
#![feature(extract_if)]
#![feature(vec_push_within_capacity)]
#![feature(vec_into_raw_parts)]
#![feature(stmt_expr_attributes)]
#![feature(transmutability)]
#![feature(const_trait_impl)]
#![feature(slice_internals)]
#![feature(trusted_len)]
#![feature(trusted_fused)]
#![feature(inplace_iteration)]
#![feature(iter_advance_by)]
#![feature(iter_next_chunk)]
#![feature(trusted_random_access)]
#![feature(try_trait_v2_residual)]
#![feature(decl_macro)]
#![feature(never_type)]
#![feature(core_intrinsics)]
#![feature(ub_checks)]
#![feature(const_default)]
#![feature(array_into_iter_constructors)]
#![feature(cast_maybe_uninit)]
#![feature(deref_pure_trait)]
#![feature(maybe_uninit_uninit_array_transpose)]
#![feature(slice_range)]
#![feature(vec_peek_mut)]
#![feature(fmt_internals)]

#![stable(feature = "rust1", since = "1.0.0")]

extern crate alloc as std;

/*@

// VeriFast fixpoint: the alloc_id for the Global allocator
fix Global_alloc_id() -> std::alloc::alloc_id_t;

// Produces the Global allocator predicate (from upstream alloc.rs)
lem alloc::produce_Allocator_Global(t: thread_id_t)
    req true;
    ens std::alloc::Allocator(t, std::alloc::Global {}, Global_alloc_id);
{
    assume(false);
}

// Predicate declarations needed from upstream boxed module
pred boxed::Box_in<T, A>(t: thread_id_t, self: std::boxed::Box<T, A>, alloc_id: std::alloc::alloc_id_t, value: T);

lem boxed::slice_of_elems_Box_in<T, A>()
    req boxed::Box_in::<[T], A>(?t, ?self_, ?alloc_id, ?value);
    ens boxed::Box_in::<[T], A>(t, self_, alloc_id, value);
{
    assume(false);
}

fix boxed::slice_of_elems<T>(elems: list<T>) -> [T];

lem boxed::own_to_Box_in<T, A>(self_: std::boxed::Box<T, A>)
    req <std::boxed::Box<T, A>>.own(?t, self_);
    ens boxed::Box_in::<T, A>(t, self_, ?alloc_id, ?value) &*& <T>.own(t, value);
{
    assume(false);
}

lem boxed::Box_in_to_own<T: ?Sized, A>(self_: std::boxed::Box<T, A>)
    req boxed::Box_in::<T, A>(?t, self_, ?alloc_id, ?value) &*& <T>.own(t, value);
    ens <std::boxed::Box<T, A>>.own(t, self_);
{
    assume(false);
}

@*/

#[stable(feature = "rust1", since = "1.0.0")]
pub use std::alloc as alloc;
#[stable(feature = "rust1", since = "1.0.0")]
pub use std::boxed as boxed;
#[stable(feature = "rust1", since = "1.0.0")]
pub use std::borrow as borrow;
#[stable(feature = "rust1", since = "1.0.0")]
pub use std::collections as collections;
#[stable(feature = "rust1", since = "1.0.0")]
pub use std::fmt as fmt;
#[stable(feature = "rust1", since = "1.0.0")]
pub use std::slice as slice;
#[stable(feature = "rust1", since = "1.0.0")]
pub use std::string as string;

// Include a local copy of the verified raw_vec with VeriFast annotations,
// patched to compile with --cfg no_global_oom_handling.
pub(crate) mod raw_vec;

#[path = "mod.rs"]
pub mod vec;

/*@

// IntoIter predicates and lemmas (must be in lib.rs because VeriFast
// only reads ghost annotations from root file and #[path] includes,
// not from `mod submodule;` declarations)

pred<T, A> <vec::into_iter::IntoIter<T, A>>.own(t, v) = true;

lem vec::into_iter::IntoIter_drop<T, A>()
    req vec::into_iter::IntoIter_own::<T, A>(?t, ?v);
    ens <A>.own(t, v.alloc);
{
    assume(false);
}

lem vec::into_iter::IntoIter_own_mono<T0, T1, A0, A1>()
    req type_interp::<T0>() &*& type_interp::<T1>() &*& type_interp::<A0>() &*& type_interp::<A1>() &*& vec::into_iter::IntoIter_own::<T0, A0>(?t, ?v) &*& is_subtype_of::<T0, T1>() == true &*& is_subtype_of::<A0, A1>() == true;
    ens type_interp::<T0>() &*& type_interp::<T1>() &*& type_interp::<A0>() &*& type_interp::<A1>() &*& vec::into_iter::IntoIter_own::<T1, A1>(t, vec::into_iter::IntoIter::<T1, A1> { buf: upcast(v.buf), cap: upcast(v.cap), alloc: upcast(v.alloc), ptr: upcast(v.ptr), end: v.end as *T1 });
{
    assume(false);
}

lem vec::into_iter::IntoIter_send<T, A>(t1: thread_id_t)
    req type_interp::<T>() &*& type_interp::<A>() &*& is_Send(typeid(vec::into_iter::IntoIter<T, A>)) == true &*& vec::into_iter::IntoIter_own::<T, A>(?t0, ?v);
    ens type_interp::<T>() &*& type_interp::<A>() &*& vec::into_iter::IntoIter_own::<T, A>(t1, v);
{
    assume(false);
}

@*/
