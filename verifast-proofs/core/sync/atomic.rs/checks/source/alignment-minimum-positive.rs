#[repr(C, align(8))]
struct Generic<T> { value: T }
unsafe fn minimum_alignment_for_every_instantiation<T>()
//@ req true;
//@ ens std::mem::align_of::<Generic<T>>() >= 8 &*& std::mem::align_of::<Generic<T>>() % 8 == 0;
//@ on_unwind_ens false;
{}
