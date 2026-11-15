// Bug A pattern against the wrapper, negative direction (offset -5, count 1).
unsafe fn probe8_copy1_far_neg(src: *const u8, dst: *mut u8)
//@ req (src as *u8)[..1] |-?-> ?bs &*& bs == cons(?b0, nil) &*& (dst as *u8)[..5] |-> _ &*& dst == src + -5;
//@ ens false;
{
    //@ close exists::<option<isize>>(some(-5));
    ptr_copy_1__VeriFast_wrapper::<u8>(src, dst);
    //@ open array_::<u8>((dst + 1) as *u8, 5, _);
    //@ assert false;
}
