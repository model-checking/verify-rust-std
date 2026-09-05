#[repr(C, align(8))]
struct Generic<T> { value: T }
unsafe fn no_single_alignment_for_every_instantiation<T>()
//@ req true;
//@ ens std::mem::align_of::<Generic<T>>() == 8;
//@ on_unwind_ens false;
{}
