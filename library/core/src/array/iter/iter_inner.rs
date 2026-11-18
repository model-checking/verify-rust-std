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

// Fail closed if the harness-wide fold stub reaches an unproved element
// instantiation. The actual advance_by pipeline and refinement proofs use bool.
#[cfg(kani)]
trait Challenge22FoldElement {
    fn admitted() -> bool;
}

#[cfg(kani)]
impl<T> Challenge22FoldElement for T {
    default fn admitted() -> bool {
        false
    }
}

#[cfg(kani)]
impl Challenge22FoldElement for bool {
    fn admitted() -> bool {
        true
    }
}

impl<T> PolymorphicIter<[MaybeUninit<T>]> {
    /// Loop-free replacement used only by the Challenge 22 harnesses.
    ///
    /// Unlike a non-consuming sum oracle, this advances `alive` before each
    /// callback, just as `try_fold` does. Ordinary drop therefore sees exactly
    /// the same remaining elements, including if a callback panics.
    /// The assertions make uses outside the proved, fixed-size domain fail.
    #[cfg(kani)]
    pub(crate) fn kani_fold_at_most_32<B>(&mut self, init: B, mut f: impl FnMut(B, T) -> B) -> B {
        assert!(<T as Challenge22FoldElement>::admitted());
        assert!(self.alive.start() <= self.alive.end());
        assert!(self.alive.end() <= self.data.len());
        assert!(self.data.len() == 32);
        let start = self.alive.start();
        let end = self.alive.end();
        let data = self.data.as_ptr().cast::<T>();
        let mut accum = init;
        macro_rules! step {
            ($k:expr) => {
                if start + $k < end {
                    let idx = start + $k;
                    // A direct range assignment keeps the model's write target
                    // visible to CBMC's loop-frame inference.
                    self.alive = IndexRange::kani_from_bounds(idx + 1, end);
                    // SAFETY: The range update transfers the initialized
                    // element's ownership to the callback.
                    let ptr = data.wrapping_add(idx);
                    let elem = unsafe { crate::intrinsics::read_via_copy(ptr) };
                    accum = f(accum, elem);
                }
            };
        }
        step!(0);
        step!(1);
        step!(2);
        step!(3);
        step!(4);
        step!(5);
        step!(6);
        step!(7);
        step!(8);
        step!(9);
        step!(10);
        step!(11);
        step!(12);
        step!(13);
        step!(14);
        step!(15);
        step!(16);
        step!(17);
        step!(18);
        step!(19);
        step!(20);
        step!(21);
        step!(22);
        step!(23);
        step!(24);
        step!(25);
        step!(26);
        step!(27);
        step!(28);
        step!(29);
        step!(30);
        step!(31);
        accum
    }

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
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use super::*;
    use crate::kani;

    // In addition to the sum used by advance_by, record the entire sequence
    // (at most 32 bits) and the callback count. Compare the actual implementation
    // directly with the model; neither implementation is stubbed in this proof.
    #[kani::proof]
    #[kani::unwind(33)]
    fn check_consuming_fold_model() {
        let flags: [bool; 32] = kani::any();
        let start: usize = kani::any();
        let end: usize = kani::any();
        kani::assume(start <= end && end <= 32);
        // Same representation conversion as IntoIterator for arrays, without
        // array::map's unrelated construction and draining machinery.
        let data: [MaybeUninit<bool>; 32] = unsafe { crate::mem::transmute(flags) };
        let mut actual =
            unsafe { PolymorphicIter::new_unchecked(IndexRange::new_unchecked(start, end), data) };
        let mut model =
            unsafe { PolymorphicIter::new_unchecked(IndexRange::new_unchecked(start, end), data) };
        let actual: &mut PolymorphicIter<[MaybeUninit<bool>]> = &mut actual;
        let model: &mut PolymorphicIter<[MaybeUninit<bool>]> = &mut model;
        let observe = |(sum, trace, calls): (u8, u64, u8), flag: bool| {
            (sum + flag as u8, (trace << 1) | flag as u64, calls + 1)
        };
        let expected = actual.fold((0, 0, 0), observe);
        let result = model.kani_fold_at_most_32((0, 0, 0), observe);
        assert!(result == expected);
        assert!(actual.alive == model.alive);
        assert!(model.alive.start() == end && model.alive.end() == end);
        assert!(result.2 as usize == end - start);
        assert!(model.next().is_none() && actual.next().is_none());
        kani::cover(start == 0 && end == 32, "all 32 independent flags consumed");
        kani::cover(start == end, "empty alive range");
        kani::cover(0 < start && start < end && end < 32, "interior alive range");
        // Both ordinary destructors run; bool has no destructor of its own.
    }
}
