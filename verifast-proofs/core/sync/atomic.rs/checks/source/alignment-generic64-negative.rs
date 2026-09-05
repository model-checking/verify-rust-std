#[repr(C, align(64))]
struct WideAlignment { value: u8 }
#[repr(C, align(8))]
struct Generic<T> { value: T }
unsafe fn minimum_alignment_is_not_exact_alignment()
//@ req true;
//@ ens std::mem::align_of::<Generic<WideAlignment>>() == 8;
//@ on_unwind_ens false;
{}
