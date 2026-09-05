#[repr(C, align(1))]
struct AlignedWide { value: u64 }
unsafe fn alignment_attribute_is_not_exact_alignment()
//@ req true;
//@ ens std::mem::align_of::<AlignedWide>() == 1;
//@ on_unwind_ens false;
{}
