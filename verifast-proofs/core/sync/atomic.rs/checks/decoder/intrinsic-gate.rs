#![feature(core_intrinsics)]

// Exact current-Rust intrinsic shape used by the atomic_store wrapper.
unsafe fn store_relaxed(dst: *mut u8, val: u8)
//@ req *dst |-> _;
//@ ens *dst |-> val;
//@ on_unwind_ens false;
{
    unsafe {
        std::intrinsics::atomic_store::<u8, { std::intrinsics::AtomicOrdering::Relaxed }>(dst, val)
    }
}
