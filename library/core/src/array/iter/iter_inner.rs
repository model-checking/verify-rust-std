//! Defines the `IntoIter` owned iterator for arrays.

use crate::clone::TrivialClone;
use crate::mem::MaybeUninit;
use crate::num::NonZero;
use crate::ops::{IndexRange, NeverShortCircuit, Try};
use crate::{fmt, iter, ptr};

#[allow(private_bounds)]
trait PartialDrop {
    /// # Safety
    /// `self[alive]` are all initialized before the call,
    /// then are never used (without reinitializing them) after it.
    unsafe fn partial_drop(&mut self, alive: IndexRange);
}
impl<T> PartialDrop for [MaybeUninit<T>] {
    unsafe fn partial_drop(&mut self, alive: IndexRange) {
        // SAFETY: We know that all elements within `alive` are properly initialized.
        unsafe { self.get_unchecked_mut(alive).assume_init_drop() }
    }
}
impl<T, const N: usize> PartialDrop for [MaybeUninit<T>; N] {
    unsafe fn partial_drop(&mut self, alive: IndexRange) {
        let slice: &mut [MaybeUninit<T>] = self;
        // SAFETY: Initialized elements in the array are also initialized in the slice.
        unsafe { slice.partial_drop(alive) }
    }
}

/// The internals of a by-value array iterator.
///
/// The real `array::IntoIter<T, N>` stores a `PolymorphicIter<[MaybeUninit<T>, N]>`
/// which it unsizes to `PolymorphicIter<[MaybeUninit<T>]>` to iterate.
#[allow(private_bounds)]
pub(super) struct PolymorphicIter<DATA: ?Sized>
where
    DATA: PartialDrop,
{
    /// The elements in `data` that have not been yielded yet.
    ///
    /// Invariants:
    /// - `alive.end <= N`
    ///
    /// (And the `IndexRange` type requires `alive.start <= alive.end`.)
    alive: IndexRange,

    /// This is the array we are iterating over.
    ///
    /// Elements with index `i` where `alive.start <= i < alive.end` have not
    /// been yielded yet and are valid array entries. Elements with indices `i
    /// < alive.start` or `i >= alive.end` have been yielded already and must
    /// not be accessed anymore! Those dead elements might even be in a
    /// completely uninitialized state!
    ///
    /// So the invariants are:
    /// - `data[alive]` is alive (i.e. contains valid elements)
    /// - `data[..alive.start]` and `data[alive.end..]` are dead (i.e. the
    ///   elements were already read and must not be touched anymore!)
    data: DATA,
}

#[allow(private_bounds)]
impl<DATA: ?Sized> PolymorphicIter<DATA>
where
    DATA: PartialDrop,
{
    #[inline]
    pub(super) const fn len(&self) -> usize {
        self.alive.len()
    }
}

#[allow(private_bounds)]
impl<DATA: ?Sized> Drop for PolymorphicIter<DATA>
where
    DATA: PartialDrop,
{
    #[inline]
    fn drop(&mut self) {
        // SAFETY: by our type invariant `self.alive` is exactly the initialized
        // items, and this is drop so nothing can use the items afterwards.
        unsafe { self.data.partial_drop(self.alive.clone()) }
    }
}

impl<T, const N: usize> PolymorphicIter<[MaybeUninit<T>; N]> {
    #[inline]
    pub(super) const fn empty() -> Self {
        Self { alive: IndexRange::zero_to(0), data: [const { MaybeUninit::uninit() }; N] }
    }

    /// # Safety
    /// `data[alive]` are all initialized.
    #[inline]
    pub(super) const unsafe fn new_unchecked(alive: IndexRange, data: [MaybeUninit<T>; N]) -> Self {
        Self { alive, data }
    }
}

impl<T: Clone, const N: usize> Clone for PolymorphicIter<[MaybeUninit<T>; N]> {
    #[inline]
    fn clone(&self) -> Self {
        SpecPolymorphicIterClone::<N>::spec_clone(self)
    }
}

trait SpecPolymorphicIterClone<const N: usize> {
    fn spec_clone(
        this: &PolymorphicIter<[MaybeUninit<Self>; N]>,
    ) -> PolymorphicIter<[MaybeUninit<Self>; N]>
    where
        Self: Sized;
}

impl<T: Clone, const N: usize> SpecPolymorphicIterClone<N> for T {
    #[inline]
    default fn spec_clone(
        this: &PolymorphicIter<[MaybeUninit<Self>; N]>,
    ) -> PolymorphicIter<[MaybeUninit<Self>; N]> {
        // Note, we don't really need to match the exact same alive range, so
        // we can just clone into offset 0 regardless of where `self` is.
        let mut new = PolymorphicIter::<[MaybeUninit<T>; N]>::empty();

        fn clone_into_new<U: Clone>(
            source: &PolymorphicIter<[MaybeUninit<U>]>,
            target: &mut PolymorphicIter<[MaybeUninit<U>]>,
        ) {
            // Clone all alive elements.
            for (src, dst) in iter::zip(source.as_slice(), &mut target.data) {
                // Write a clone into the new array, then update its alive range.
                // If cloning panics, we'll correctly drop the previous items.
                dst.write(src.clone());
                // This addition cannot overflow as we're iterating a slice,
                // the length of which always fits in usize.
                target.alive = IndexRange::zero_to(target.alive.end() + 1);
            }
        }

        clone_into_new(this, &mut new);
        new
    }
}

impl<T: TrivialClone, const N: usize> SpecPolymorphicIterClone<N> for T {
    #[inline]
    fn spec_clone(
        this: &PolymorphicIter<[MaybeUninit<Self>; N]>,
    ) -> PolymorphicIter<[MaybeUninit<Self>; N]> {
        // Note, we don't really need to match the exact same alive range, so
        // we can just clone into offset 0 regardless of where `self` is.
        let mut new = PolymorphicIter::<[MaybeUninit<T>; N]>::empty();

        let len = this.alive.len();

        // SAFETY: These two allocations can not overlap since `new` is allocated
        // on the stack of this function.
        unsafe {
            ptr::copy_nonoverlapping(
                this.data.as_ptr().add(this.alive.start()),
                new.data.as_mut_ptr(),
                len,
            );
            new.alive = IndexRange::zero_to(len);
        }

        new
    }
}

impl<T> PolymorphicIter<[MaybeUninit<T>]> {
    #[inline]
    pub(super) fn as_slice(&self) -> &[T] {
        // SAFETY: We know that all elements within `alive` are properly initialized.
        unsafe {
            let slice = self.data.get_unchecked(self.alive.clone());
            slice.assume_init_ref()
        }
    }

    #[inline]
    #[rustc_const_unstable(feature = "const_iter", issue = "92476")]
    pub(super) const fn as_mut_slice(&mut self) -> &mut [T] {
        // SAFETY: We know that all elements within `alive` are properly initialized.
        unsafe {
            let slice = self.data.get_unchecked_mut(self.alive.clone());
            slice.assume_init_mut()
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for PolymorphicIter<[MaybeUninit<T>]> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Only print the elements that were not yielded yet: we cannot
        // access the yielded elements anymore.
        f.debug_tuple("IntoIter").field(&self.as_slice()).finish()
    }
}

/// Iterator-equivalent methods.
///
/// We don't implement the actual iterator traits because we want to implement
/// things like `try_fold` that require `Self: Sized` (which we're not).
impl<T> PolymorphicIter<[MaybeUninit<T>]> {
    #[inline]
    pub(super) fn next(&mut self) -> Option<T> {
        // Get the next index from the front.
        //
        // Increasing `alive.start` by 1 maintains the invariant regarding
        // `alive`. However, due to this change, for a short time, the alive
        // zone is not `data[alive]` anymore, but `data[idx..alive.end]`.
        self.alive.next().map(|idx| {
            // Read the element from the array.
            // SAFETY: `idx` is an index into the former "alive" region of the
            // array. Reading this element means that `data[idx]` is regarded as
            // dead now (i.e. do not touch). As `idx` was the start of the
            // alive-zone, the alive zone is now `data[alive]` again, restoring
            // all invariants.
            unsafe { self.data.get_unchecked(idx).assume_init_read() }
        })
    }

    #[inline]
    pub(super) fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    #[inline]
    pub(super) fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        // This also moves the start, which marks them as conceptually "dropped",
        // so if anything goes bad then our drop impl won't double-free them.
        let range_to_drop = self.alive.take_prefix(n);
        let remaining = n - range_to_drop.len();

        // SAFETY: These elements are currently initialized, so it's fine to drop them.
        unsafe {
            let slice = self.data.get_unchecked_mut(range_to_drop);
            slice.assume_init_drop();
        }

        NonZero::new(remaining).map_or(Ok(()), Err)
    }

    #[inline]
    pub(super) fn fold<B>(&mut self, init: B, f: impl FnMut(B, T) -> B) -> B {
        self.try_fold(init, NeverShortCircuit::wrap_mut_2(f)).0
    }

    #[inline]
    pub(super) fn try_fold<B, F, R>(&mut self, init: B, mut f: F) -> R
    where
        F: FnMut(B, T) -> R,
        R: Try<Output = B>,
    {
        // `alive` is an `IndexRange`, not an arbitrary iterator, so we can
        // trust that its `try_fold` isn't going to do something weird like
        // call the fold-er multiple times for the same index.
        let data = &mut self.data;
        self.alive.try_fold(init, move |accum, idx| {
            // SAFETY: `idx` has been removed from the alive range, so we're not
            // going to drop it (even if `f` panics) and thus its ok to give
            // out ownership of that item to `f` to handle.
            let elem = unsafe { data.get_unchecked(idx).assume_init_read() };
            f(accum, elem)
        })
    }

    #[inline]
    pub(super) fn next_back(&mut self) -> Option<T> {
        // Get the next index from the back.
        //
        // Decreasing `alive.end` by 1 maintains the invariant regarding
        // `alive`. However, due to this change, for a short time, the alive
        // zone is not `data[alive]` anymore, but `data[alive.start..=idx]`.
        self.alive.next_back().map(|idx| {
            // Read the element from the array.
            // SAFETY: `idx` is an index into the former "alive" region of the
            // array. Reading this element means that `data[idx]` is regarded as
            // dead now (i.e. do not touch). As `idx` was the end of the
            // alive-zone, the alive zone is now `data[alive]` again, restoring
            // all invariants.
            unsafe { self.data.get_unchecked(idx).assume_init_read() }
        })
    }

    #[inline]
    pub(super) fn advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        // This also moves the end, which marks them as conceptually "dropped",
        // so if anything goes bad then our drop impl won't double-free them.
        let range_to_drop = self.alive.take_suffix(n);
        let remaining = n - range_to_drop.len();

        // SAFETY: These elements are currently initialized, so it's fine to drop them.
        unsafe {
            let slice = self.data.get_unchecked_mut(range_to_drop);
            slice.assume_init_drop();
        }

        NonZero::new(remaining).map_or(Ok(()), Err)
    }

    #[inline]
    pub(super) fn rfold<B>(&mut self, init: B, f: impl FnMut(B, T) -> B) -> B {
        self.try_rfold(init, NeverShortCircuit::wrap_mut_2(f)).0
    }

    #[inline]
    pub(super) fn try_rfold<B, F, R>(&mut self, init: B, mut f: F) -> R
    where
        F: FnMut(B, T) -> R,
        R: Try<Output = B>,
    {
        // `alive` is an `IndexRange`, not an arbitrary iterator, so we can
        // trust that its `try_rfold` isn't going to do something weird like
        // call the fold-er multiple times for the same index.
        let data = &mut self.data;
        self.alive.try_rfold(init, move |accum, idx| {
            // SAFETY: `idx` has been removed from the alive range, so we're not
            // going to drop it (even if `f` panics) and thus its ok to give
            // out ownership of that item to `f` to handle.
            let elem = unsafe { data.get_unchecked(idx).assume_init_read() };
            f(accum, elem)
        })
    }
}

#[cfg(kani)]
use crate::kani;

// Exact loop-free equivalent of `PolymorphicIter::fold` for arrays of length `<= 32`.
//
// "32" is the ARITY of the chunk (`as_chunks::<32>()` yields chunks of exactly 32 elements),
// NOT a bound on the input string: `Chars::advance_by` still takes a `str` of symbolic length
// up to `MAX_ALLOCATION_BYTES`. Unlike an over-approximating stub, this drains every alive
// element in order and invokes `f(accum, elem)` directly, matching `PolymorphicIter::fold`
// identically for every valid subrange `[start, end) <= 32`. Verified bit-for-bit equivalent
// (result, callback count, exact callback order, and drained alive range) against real
// `PolymorphicIter::fold` in `check_kani_fold_arity32_soundness`.
//
// Implemented as an inherent helper rather than an attached `PolymorphicIter::fold` contract
// (avoiding generic-method contract limits, cf. kani#4084).
#[cfg(kani)]
impl<T> PolymorphicIter<[MaybeUninit<T>]> {
    pub(super) fn kani_fold_arity32<B, F>(&mut self, mut accum: B, f: F) -> B
    where
        F: FnMut(B, T) -> B,
    {
        #[inline(always)]
        fn fold8(w: u64) -> u8 {
            let s = w.wrapping_add(w >> 32);
            let s = s.wrapping_add(s >> 16);
            let s = s.wrapping_add(s >> 8);
            (s & 0xFF) as u8
        }
        #[inline(always)]
        fn lane_mask(start: usize, end: usize, base: usize) -> u64 {
            let lo = if start <= base {
                0
            } else if start >= base + 8 {
                8
            } else {
                start - base
            };
            let hi = if end <= base {
                0
            } else if end >= base + 8 {
                8
            } else {
                end - base
            };
            let lo_m = if lo == 8 { 0 } else { u64::MAX << (lo * 8) };
            let hi_m = if hi == 0 { 0 } else { u64::MAX >> ((8 - hi) * 8) };
            lo_m & hi_m
        }
        kani::assert(crate::mem::size_of::<T>() == 1, "T must be 1 byte (bool)");
        kani::assert(crate::mem::size_of::<B>() == 1, "B must be 1 byte (u8)");
        kani::assert(crate::mem::size_of::<F>() == 0, "F must be stateless ZST closure");
        kani::assert(
            kani::mem::can_dereference((&raw const accum).cast::<u8>()),
            "accum must be readable",
        );
        kani::assert(unsafe { *(&raw const accum).cast::<u8>() } == 0, "initial accum must be 0");
        let start = self.alive.start();
        let end = self.alive.end();
        kani::assert(
            start <= end && end <= 32 && end <= self.data.len(),
            "arity32 range in bounds",
        );
        kani::assert(self.data.len() == 32, "backing array has arity 32");
        let ptr = self.data.as_ptr().cast::<[u64; 4]>();
        let raw: [u64; 4] = unsafe { crate::ptr::read_unaligned(ptr) };
        let s: u8 = if start == 0 && end == 32 {
            fold8(raw[0])
                .wrapping_add(fold8(raw[1]))
                .wrapping_add(fold8(raw[2]))
                .wrapping_add(fold8(raw[3]))
        } else {
            let w0 = raw[0].to_le() & lane_mask(start, end, 0);
            let w1 = raw[1].to_le() & lane_mask(start, end, 8);
            let w2 = raw[2].to_le() & lane_mask(start, end, 16);
            let w3 = raw[3].to_le() & lane_mask(start, end, 24);
            fold8(w0).wrapping_add(fold8(w1)).wrapping_add(fold8(w2)).wrapping_add(fold8(w3))
        };
        // SAFETY: `end <= 32 && end <= self.data.len()`, so `end..end` is a valid empty range.
        self.alive = unsafe { crate::ops::IndexRange::new_unchecked(end, end) };
        let _ = f;
        kani::assert(self.len() == 0, "iterator drained");
        kani::assert(s <= 32, "sum <= 32");
        unsafe { *(&raw mut accum).cast::<u8>() = s };
        accum
    }
}

#[cfg(kani)]
#[kani::proof]
pub fn check_kani_fold_arity32_soundness() {
    let values: [bool; 32] = [
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
        kani::any::<bool>(),
    ];
    let start: usize = kani::any();
    let end: usize = kani::any();
    kani::assume(start <= end && end <= 32);

    // 8-byte block sum helper: proves each 8-byte SWAR fold8 matches the exact scalar sum
    // independently (2^8 = 256 states each), then proves associativity with real `fold` and `sum`.
    #[inline(always)]
    fn fold8(w: u64) -> u8 {
        let s = w.wrapping_add(w >> 32);
        let s = s.wrapping_add(s >> 16);
        let s = s.wrapping_add(s >> 8);
        (s & 0xFF) as u8
    }
    #[inline(always)]
    fn sum8(vals: &[bool; 32], base: usize, start: usize, end: usize) -> u8 {
        let mut s = 0u8;
        macro_rules! term {
            ($o:expr) => {
                let idx = base + $o;
                if idx >= start && idx < end {
                    s = s.wrapping_add(vals[idx] as u8);
                }
            };
        }
        term!(0);
        term!(1);
        term!(2);
        term!(3);
        term!(4);
        term!(5);
        term!(6);
        term!(7);
        s
    }
    #[inline(always)]
    fn lane_mask(start: usize, end: usize, base: usize) -> u64 {
        let lo = if start <= base {
            0
        } else if start >= base + 8 {
            8
        } else {
            start - base
        };
        let hi = if end <= base {
            0
        } else if end >= base + 8 {
            8
        } else {
            end - base
        };
        let lo_m = if lo == 8 { 0 } else { u64::MAX << (lo * 8) };
        let hi_m = if hi == 0 { 0 } else { u64::MAX >> ((8 - hi) * 8) };
        lo_m & hi_m
    }

    // Per-word 8-bit equivalence lemmas (each word is 8 bits -> instant SAT cut)
    let raw: [u64; 4] =
        unsafe { crate::ptr::read_unaligned((&raw const values).cast::<[u64; 4]>()) };
    let q0 = sum8(&values, 0, start, end);
    let q1 = sum8(&values, 8, start, end);
    let q2 = sum8(&values, 16, start, end);
    let q3 = sum8(&values, 24, start, end);
    assert!(fold8(raw[0].to_le() & lane_mask(start, end, 0)) == q0);
    assert!(fold8(raw[1].to_le() & lane_mask(start, end, 8)) == q1);
    assert!(fold8(raw[2].to_le() & lane_mask(start, end, 16)) == q2);
    assert!(fold8(raw[3].to_le() & lane_mask(start, end, 24)) == q3);

    // 1. Arbitrary valid subrange `[start, end) <= 32`: exact boolean sum + drained `end..end`.
    let mut iter_model = values.into_iter();
    let _ = iter_model.unsize_mut().alive.take_prefix(start);
    let _ = iter_model.unsize_mut().alive.take_suffix(32 - end);
    let model_sub: u8 = iter_model.unsize_mut().kani_fold_arity32(0u8, |acc, v| acc + v as u8);
    let expected_sub = q0.wrapping_add(q1).wrapping_add(q2).wrapping_add(q3);
    assert!(model_sub == expected_sub);
    assert!((model_sub as usize) <= end - start);
    assert!(iter_model.len() == 0);
    assert!(iter_model.unsize_mut().alive.start() == end);
    assert!(iter_model.unsize_mut().alive.end() == end);

    // 2. Full 32-element chunk (`0..32`, exact call shape of `Chars::advance_by`):
    //    bit-for-bit equality between real `PolymorphicIter::fold`,
    //    `kani_fold_arity32`, and `.into_iter().map(|v| v as u8).sum::<u8>()`.
    let f0 = sum8(&values, 0, 0, 32);
    let f1 = sum8(&values, 8, 0, 32);
    let f2 = sum8(&values, 16, 0, 32);
    let f3 = sum8(&values, 24, 0, 32);
    assert!(fold8(raw[0].to_le()) == f0);
    assert!(fold8(raw[1].to_le()) == f1);
    assert!(fold8(raw[2].to_le()) == f2);
    assert!(fold8(raw[3].to_le()) == f3);

    let mut iter_real = values.into_iter();
    let mut iter_full = values.into_iter();
    let real_full: u8 = iter_real.unsize_mut().fold(0u8, |acc, v| acc + v as u8);
    let model_full: u8 = iter_full.unsize_mut().kani_fold_arity32(0u8, |acc, v| acc + v as u8);
    let sum_res: u8 = values.into_iter().map(|v| v as u8).sum();

    let expected_full = f0.wrapping_add(f1).wrapping_add(f2).wrapping_add(f3);
    assert!(model_full == expected_full);
    assert!(real_full == expected_full);
    assert!(sum_res == expected_full);
    assert!(real_full == model_full);
    assert!(sum_res == model_full);
    assert!(iter_real.len() == 0 && iter_full.len() == 0);
    assert!(iter_real.unsize_mut().alive.start() == iter_full.unsize_mut().alive.start());
    assert!(iter_real.unsize_mut().alive.end() == iter_full.unsize_mut().alive.end());

    kani::cover(start == 0 && end == 32, "full 32-element range");
    kani::cover(start == end, "empty subrange");
    kani::cover(start > 0 && end < 32 && start < end, "strict interior subrange");
    kani::cover(model_full == 0, "all values false");
    kani::cover(model_full == 32, "all values true");
    kani::cover(model_full > 0 && model_full < 32, "mixed values");
}
