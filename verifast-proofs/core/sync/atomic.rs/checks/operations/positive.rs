#![feature(core_intrinsics)]

/*@
fix accepts<T>(value: T) -> bool { true }
fix bool_byte(value: u8) -> bool { value == 0 || value == 1 }
@*/

// A generic caller can construct an actual invariant-closure witness. The
// operand domain remains a requirement, since Copy is insufficient by itself.
unsafe fn generic_add<T: Copy, U: Copy>(dst: *mut T, val: U) -> T
//@ req std::intrinsics::atomic_rmw_types::<T, U>() == true &*& [?f]std::intrinsics::atomic_points_to(dst, 1, accepts);
//@ ens [f]std::intrinsics::atomic_points_to(dst, 1, accepts);
//@ on_unwind_ens false;
{
    /*@
    produce_lem_ptr_chunk std::intrinsics::atomic_rmw_preserves<T, U>(typeid(T), typeid(U), std::intrinsics::RmwAdd, accepts, val)(old) {
    };
    @*/
    //@ leak std::intrinsics::is_atomic_rmw_preserves::<T, U>(_, typeid(T), typeid(U), std::intrinsics::RmwAdd, accepts, val);
    let result = unsafe { std::intrinsics::atomic_xadd::<T, U, {std::intrinsics::AtomicOrdering::Relaxed}>(dst, val) };
    result
}

unsafe fn bool_and(dst: *mut u8, val: u8) -> u8
//@ req [?f]std::intrinsics::atomic_points_to(dst, 1, bool_byte) &*& bool_byte(val) == true;
//@ ens [f]std::intrinsics::atomic_points_to(dst, 1, bool_byte) &*& bool_byte(result) == true;
//@ on_unwind_ens false;
{
    /*@
    produce_lem_ptr_chunk std::intrinsics::atomic_rmw_preserves<u8, u8>(typeid(u8), typeid(u8), std::intrinsics::RmwAnd, bool_byte, val)(old) {
        assert bool_byte(old) == true;
        assert bool_byte(val) == true;
        std::intrinsics::atomic_rmw_bool_bytes_and(old, val);
        if old == 0 {} else {}
        if val == 0 {} else {}
    };
    @*/
    //@ leak std::intrinsics::is_atomic_rmw_preserves::<u8, u8>(_, typeid(u8), typeid(u8), std::intrinsics::RmwAnd, bool_byte, val);
    let result = unsafe { std::intrinsics::atomic_and::<u8, u8, {std::intrinsics::AtomicOrdering::Relaxed}>(dst, val) };
    result
}

unsafe fn bool_or(dst: *mut u8, val: u8) -> u8
//@ req [?f]std::intrinsics::atomic_points_to(dst, 1, bool_byte) &*& bool_byte(val) == true;
//@ ens [f]std::intrinsics::atomic_points_to(dst, 1, bool_byte) &*& bool_byte(result) == true;
//@ on_unwind_ens false;
{
    /*@
    produce_lem_ptr_chunk std::intrinsics::atomic_rmw_preserves<u8, u8>(typeid(u8), typeid(u8), std::intrinsics::RmwOr, bool_byte, val)(old) {
        assert bool_byte(old) == true;
        assert bool_byte(val) == true;
        std::intrinsics::atomic_rmw_bool_bytes_or(old, val);
        if old == 0 {} else {}
        if val == 0 {} else {}
    };
    @*/
    //@ leak std::intrinsics::is_atomic_rmw_preserves::<u8, u8>(_, typeid(u8), typeid(u8), std::intrinsics::RmwOr, bool_byte, val);
    let result = unsafe { std::intrinsics::atomic_or::<u8, u8, {std::intrinsics::AtomicOrdering::Relaxed}>(dst, val) };
    result
}

unsafe fn bool_xor(dst: *mut u8, val: u8) -> u8
//@ req [?f]std::intrinsics::atomic_points_to(dst, 1, bool_byte) &*& bool_byte(val) == true;
//@ ens [f]std::intrinsics::atomic_points_to(dst, 1, bool_byte) &*& bool_byte(result) == true;
//@ on_unwind_ens false;
{
    /*@
    produce_lem_ptr_chunk std::intrinsics::atomic_rmw_preserves<u8, u8>(typeid(u8), typeid(u8), std::intrinsics::RmwXor, bool_byte, val)(old) {
        assert bool_byte(old) == true;
        assert bool_byte(val) == true;
        std::intrinsics::atomic_rmw_bool_bytes_xor(old, val);
        if old == 0 {} else {}
        if val == 0 {} else {}
    };
    @*/
    //@ leak std::intrinsics::is_atomic_rmw_preserves::<u8, u8>(_, typeid(u8), typeid(u8), std::intrinsics::RmwXor, bool_byte, val);
    let result = unsafe { std::intrinsics::atomic_xor::<u8, u8, {std::intrinsics::AtomicOrdering::Relaxed}>(dst, val) };
    result
}
