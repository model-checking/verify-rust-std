#[repr(C, align(32))]
struct AlignedByte { value: u8 }
#[repr(C, align(1))]
struct AlignedWide { value: u64 }
unsafe fn check_layouts()
//@ req true;
//@ ens std::mem::align_of::<AlignedByte>() == 32 &*& std::mem::align_of::<AlignedWide>() == 8;
//@ on_unwind_ens false;
{}
