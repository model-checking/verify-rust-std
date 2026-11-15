// Control: the same pattern against the prelude spec of ptr::copy derives false (Bug A).
unsafe fn probe8_copy1_raw_far(src: *const u8, dst: *mut u8)
//@ req (src as *u8)[..1] |-?-> ?bs &*& bs == cons(?b0, nil) &*& ((src + 1) as *u8)[..5] |-> _ &*& dst == src + 5;
//@ ens false;
{
    //@ close exists::<option<isize>>(some(5));
    ptr::copy::<u8>(src, dst, 1);
    //@ open array_::<u8>(src as *u8, 5, _);
    //@ assert false;
}
