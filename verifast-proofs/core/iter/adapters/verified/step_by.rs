// Generic contract proof. See ../README.md for validation evidence and scope.

use crate::intrinsics;
use crate::num::NonZero;

#[must_use = "iterators are lazy and do nothing unless consumed"]
#[stable(feature = "iterator_step_by", since = "1.28.0")]
#[derive(Clone, Debug)]
pub struct StepBy<I> {
    /// This field is guaranteed to be preprocessed by the specialized `SpecRangeSetup::setup`
    /// in the constructor.
    /// For most iterators that processing is a no-op, but for Range<{integer}> types it is lossy
    /// which means the inner iterator cannot be returned to user code.
    /// Additionally this type-dependent preprocessing means specialized implementations
    /// cannot be used interchangeably.
    iter: I,
    /// This field is `step - 1`, aka the correct amount to pass to `nth` when iterating.
    /// It MUST NOT be `usize::MAX`, as `unsafe` code depends on being able to add one
    /// without the risk of overflow.  (This is important so that length calculations
    /// don't need to check for division-by-zero, for example.)
    step_minus_one: usize,
    first_take: bool,
}

impl<I> StepBy<I> {
    /// The `step` that was originally passed to `Iterator::step_by(step)`,
    /// aka `self.step_minus_one + 1`.
    #[inline]
    unsafe fn original_step(&self) -> NonZero<usize>
//@ req [?f](*self).step_minus_one |-> ?step &*& step < usize::MAX;
    //@ ens [f](*self).step_minus_one |-> step &*& result.get() == step + 1 &*& 0 < result.get();
    //@ on_unwind_ens false;
    {
        // SAFETY: By type invariant, `step_minus_one` cannot be `MAX`, which
        // means the addition cannot overflow and the result cannot be zero.
        unsafe { NonZero::new_unchecked(intrinsics::unchecked_add(self.step_minus_one, 1)) }
    }
}
