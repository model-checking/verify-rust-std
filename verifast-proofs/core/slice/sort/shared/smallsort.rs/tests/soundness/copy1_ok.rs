// Usability of the wrapper: forward adjacent move (offset 1), in place (offset 0), backward (offset -1),
// and disjoint regions (none).
unsafe fn probe8_copy1_pos(src: *const u8, dst: *mut u8)
//@ req (src as *u8)[..1] |-?-> ?bs &*& ((src + 1) as *u8)[..1] |-> _ &*& dst == src + 1;
//@ ens (src as *u8)[..1] |-?-> take(1, bs) &*& (dst as *u8)[..1] |-?-> bs;
{
    //@ close exists::<option<isize>>(some(1));
    ptr_copy_1__VeriFast_wrapper::<u8>(src, dst);
}
unsafe fn probe8_copy1_zero(src: *const u8, dst: *mut u8)
//@ req (dst as *u8)[..1] |-?-> ?bs &*& dst == src;
//@ ens (dst as *u8)[..1] |-?-> bs;
{
    //@ close exists::<option<isize>>(some(0));
    ptr_copy_1__VeriFast_wrapper::<u8>(src, dst);
}
unsafe fn probe8_copy1_neg(src: *const u8, dst: *mut u8)
//@ req (src as *u8)[..1] |-?-> ?bs &*& (dst as *u8)[..1] |-> _ &*& dst == src + -1;
//@ ens ((dst + 1) as *u8)[..1] |-?-> bs &*& (dst as *u8)[..1] |-?-> bs;
{
    //@ close exists::<option<isize>>(some(-1));
    ptr_copy_1__VeriFast_wrapper::<u8>(src, dst);
}
unsafe fn probe8_copy1_none(src: *const u8, dst: *mut u8)
//@ req [?f](src as *u8)[..1] |-?-> ?bs &*& (dst as *u8)[..1] |-> _;
//@ ens [f](src as *u8)[..1] |-?-> bs &*& (dst as *u8)[..1] |-?-> bs;
{
    //@ close exists::<option<isize>>(none);
    ptr_copy_1__VeriFast_wrapper::<u8>(src, dst);
}
