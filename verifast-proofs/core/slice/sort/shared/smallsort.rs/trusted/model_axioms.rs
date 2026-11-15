// ===== BEGIN TRUSTED MODEL AXIOMS =====
//
// Trusted: facts about Rust that VeriFast 26.10 does not model. Each is assumed, not proven. Every crate
// contains this block verbatim (checked by verify.sh).
/*@

// `MaybeUninit<T>` owns no resources (it may hold any bytes, and dropping it does nothing). VeriFast 26.10
// leaves `<MaybeUninit<T>>.own` undefined.
lem MaybeUninit_own_trivial<T>(t: thread_id_t, v: std::mem::MaybeUninit<T>)
    req true;
    ens own::<std::mem::MaybeUninit<T>>(t)(v);
{
    assume(false);
}

// Layout of the stack arrays `MaybeUninit<[T; N]>` of `small_sort_general` (N = 48) and
// `small_sort_network` (N = 32): an array of `N` elements, aligned as `T` (Rust reference, "Type
// layout": arrays). VeriFast 26.10 has no `size_of`/`align_of` facts for array types.
lem MaybeUninit_array_48_layout<T>()
    req true;
    ens std::mem::size_of::<std::mem::MaybeUninit<[T; 48]>>() == 48 * std::mem::size_of::<T>() &*&
        std::mem::align_of::<std::mem::MaybeUninit<[T; 48]>>() == std::mem::align_of::<T>();
{
    assume(false);
}

lem MaybeUninit_array_32_layout<T>()
    req true;
    ens std::mem::size_of::<std::mem::MaybeUninit<[T; 32]>>() == 32 * std::mem::size_of::<T>() &*&
        std::mem::align_of::<std::mem::MaybeUninit<[T; 32]>>() == std::mem::align_of::<T>();
{
    assume(false);
}

// For every `T` that the trait impls of `UnstableSmallSortFreezeTypeImpl` are instantiated with, the
// array types `[T; 48]` (in `small_sort_general`, which both impls call) and `[T; 32]` (in
// `small_sort_network`, called by the `CopyMarker` impl) exist; rustc rejects types larger than
// `isize::MAX` bytes. So `size_of::<T>() * 48` (and `* 32`) does not overflow.
lem small_sort_general_instantiated<T>()
    req true;
    ens 0 <= std::mem::size_of::<T>() &*& 48 * std::mem::size_of::<T>() <= isize::MAX;
{
    assume(false);
}

@*/
// ===== END TRUSTED MODEL AXIOMS =====
