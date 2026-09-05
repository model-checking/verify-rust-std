#![feature(core_intrinsics)]
#![allow(non_snake_case, internal_features)]

mod bridge {
    pub unsafe fn exchange_relaxed__VeriFast_wrapper(dst: *mut u8, val: u8) -> u8 {
        unsafe { std::intrinsics::atomic_xchg::<u8, { std::intrinsics::AtomicOrdering::Relaxed }>(dst, val) }
    }
    pub unsafe fn exchange_release__VeriFast_wrapper(dst: *mut u8, val: u8) -> u8 {
        unsafe { std::intrinsics::atomic_xchg::<u8, { std::intrinsics::AtomicOrdering::Release }>(dst, val) }
    }
    pub unsafe fn exchange_acquire__VeriFast_wrapper(dst: *mut u8, val: u8) -> u8 {
        unsafe { std::intrinsics::atomic_xchg::<u8, { std::intrinsics::AtomicOrdering::Acquire }>(dst, val) }
    }
    pub unsafe fn exchange_acqrel__VeriFast_wrapper(dst: *mut u8, val: u8) -> u8 {
        unsafe { std::intrinsics::atomic_xchg::<u8, { std::intrinsics::AtomicOrdering::AcqRel }>(dst, val) }
    }
    pub unsafe fn exchange_seqcst__VeriFast_wrapper(dst: *mut u8, val: u8) -> u8 {
        unsafe { std::intrinsics::atomic_xchg::<u8, { std::intrinsics::AtomicOrdering::SeqCst }>(dst, val) }
    }
}

pub unsafe fn exchange_relaxed(dst: *mut u8, val: u8) -> u8 {
    unsafe { bridge::exchange_relaxed__VeriFast_wrapper(dst, val) }
}

pub unsafe fn exchange_release(dst: *mut u8, val: u8) -> u8 {
    unsafe { bridge::exchange_release__VeriFast_wrapper(dst, val) }
}

pub unsafe fn exchange_acquire(dst: *mut u8, val: u8) -> u8 {
    unsafe { bridge::exchange_acquire__VeriFast_wrapper(dst, val) }
}

pub unsafe fn exchange_acqrel(dst: *mut u8, val: u8) -> u8 {
    unsafe { bridge::exchange_acqrel__VeriFast_wrapper(dst, val) }
}

pub unsafe fn exchange_seqcst(dst: *mut u8, val: u8) -> u8 {
    unsafe { bridge::exchange_seqcst__VeriFast_wrapper(dst, val) }
}
