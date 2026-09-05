#![feature(core_intrinsics)]
#![allow(internal_features)]
use std::cell::UnsafeCell;

#[repr(C, align(1))]
pub struct AtomicU8 {
    v: UnsafeCell<u8>,
}

unsafe impl Sync for AtomicU8 {}

/*@
fix accepts_u8(value: u8) -> bool { true }
pred_ctor own_atomic_contents(p: *u8)(;) = std::intrinsics::atomic_points_to(p, 1, accepts_u8);
pred <AtomicU8>.own(t, value) = true;
pred <AtomicU8>.share(k, t, l) = [_]frac_borrow(k, own_atomic_contents(ref_origin(l) as *u8));

lem AtomicU8_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *AtomicU8)
    req lifetime_inclusion(k1, k) == true &*& [_]AtomicU8_share(k, t, l);
    ens [_]AtomicU8_share(k1, t, l);
{
    open AtomicU8_share(k, t, l);
    frac_borrow_mono(k, k1, own_atomic_contents(ref_origin(l) as *u8));
    close AtomicU8_share(k1, t, l);
    leak AtomicU8_share(k1, t, l);
}

lem AtomicU8_sync(t1: thread_id_t)
    req is_Sync(typeid(AtomicU8)) == true &*& [_]AtomicU8_share(?k, ?t0, ?l);
    ens [_]AtomicU8_share(k, t1, l);
{
    open AtomicU8_share(k, t0, l);
    close AtomicU8_share(k, t1, l);
    leak AtomicU8_share(k, t1, l);
}

lem AtomicU8_share_full(k: lifetime_t, t: thread_id_t, l: *AtomicU8)
    req atomic_mask(MaskTop) &*& full_borrow(k, AtomicU8_full_borrow_content(t, l)) &*& [?q]lifetime_token(k) &*& ref_origin(l) == l;
    ens atomic_mask(MaskTop) &*& [_]AtomicU8_share(k, t, l) &*& [q]lifetime_token(k);
{
    open_full_borrow_strong_m_(k, AtomicU8_full_borrow_content(t, l));
    open AtomicU8_full_borrow_content(t, l)();
    open AtomicU8_own(t, _);
    div_rem(l as usize, 1);
    std::intrinsics::atomic_align_of_u8();
    std::intrinsics::close_atomic_points_to_m(l as *u8, accepts_u8);
    close own_atomic_contents(l as *u8)();
    close True();
    produce_lem_ptr_chunk restore_full_borrow_(True, own_atomic_contents(l as *u8), AtomicU8_full_borrow_content(t, l))() {
        open True();
        open own_atomic_contents(l as *u8)();
        std::intrinsics::open_atomic_points_to(l as *u8);
        close_points_to(l);
        assert *l |-> ?value;
        close AtomicU8_own(t, value);
        open_points_to(l);
        close AtomicU8_full_borrow_content(t, l)();
    } {
        close_full_borrow_strong_m_();
    }
    full_borrow_into_frac_m(k, own_atomic_contents(l as *u8));
    close AtomicU8_share(k, t, l);
    leak AtomicU8_share(k, t, l);
}

lem init_ref_AtomicU8(p: *AtomicU8)
    req atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]AtomicU8_share(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]AtomicU8_share(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    open AtomicU8_share(k, t, x);
    open_ref_init_perm_AtomicU8(p);
    close_ref_initialized_AtomicU8(p, 1);
    close ref_initialized_::<AtomicU8>(p)();
    borrow_m(k, ref_initialized_(p));
    leak borrow_end_token(k, ref_initialized_(p));
    full_borrow_into_frac_m(k, ref_initialized_(p));
    close AtomicU8_share(k, t, p);
    leak AtomicU8_share(k, t, p);
}
@*/

impl AtomicU8 {
    pub const unsafe fn from_ptr<'a>(ptr: *mut u8) -> &'a AtomicU8
    //@ req type_interp::<AtomicU8>() &*& atomic_mask(MaskTop) &*& [?q]lifetime_token('a) &*& *ptr |-> ?value;
    //@ ens type_interp::<AtomicU8>() &*& atomic_mask(MaskTop) &*& [q]lifetime_token('a) &*& [_]AtomicU8_share('a, currentThread, result) &*& [_]ref_initialized(result) &*& [_]frac_borrow('a, ref_initialized_(result)) &*& ref_origin(result) == ref_origin(ptr as *AtomicU8) &*& borrow_end_token('a, AtomicU8_full_borrow_content(currentThread, ptr as *AtomicU8));
    //@ on_unwind_ens false;
    {
        //@ close_points_to(ptr as *AtomicU8);
        //@ assert *(ptr as *AtomicU8) |-> ?atomic;
        //@ close AtomicU8_own(currentThread, atomic);
        //@ open_points_to(ptr as *AtomicU8);
        //@ close AtomicU8_full_borrow_content(currentThread, ptr as *AtomicU8)();
        //@ borrow('a, AtomicU8_full_borrow_content(currentThread, ptr as *AtomicU8));
        //@ share_full_borrow::<AtomicU8>('a, currentThread, ptr as *AtomicU8);
        //@ let p = precreate_ref(ptr as *AtomicU8);
        //@ init_ref_share::<AtomicU8>('a, currentThread, p);
        //@ open_frac_borrow('a, ref_initialized_(p), q);
        //@ open [?f]ref_initialized_::<AtomicU8>(p)();
        let result = unsafe { &*ptr.cast() };
        //@ close [f]ref_initialized_::<AtomicU8>(p)();
        //@ close_frac_borrow(f, ref_initialized_(p));
        //@ close_ref_initialized_AtomicU8(p, 1);
        //@ leak ref_initialized(p);
        result
    }

    pub fn store_relaxed<'a>(&'a self, value: u8)
    //@ req [_]AtomicU8_share('a, currentThread, self) &*& [?q]lifetime_token('a);
    //@ ens [q]lifetime_token('a);
    //@ on_unwind_ens false;
    {
        //@ open AtomicU8_share('a, currentThread, self);
        //@ let f = open_frac_borrow('a, own_atomic_contents(ref_origin(self) as *u8), q);
        //@ open [f]own_atomic_contents(ref_origin(self) as *u8)();
        unsafe { std::intrinsics::atomic_store::<u8, {std::intrinsics::AtomicOrdering::Relaxed}>(self.v.get(), value) }
        //@ close [f]own_atomic_contents(ref_origin(self) as *u8)();
        //@ close_frac_borrow(f, own_atomic_contents(ref_origin(self) as *u8));
    }
}

unsafe fn recover_plain_storage(ptr: *mut u8)
//@ req [_]lifetime_dead_token(?k) &*& borrow_end_token(k, AtomicU8_full_borrow_content(currentThread, ptr as *AtomicU8));
//@ ens *ptr |-> ?stored_value;
//@ on_unwind_ens false;
{
    //@ borrow_end(k, AtomicU8_full_borrow_content(currentThread, ptr as *AtomicU8));
    //@ open AtomicU8_full_borrow_content(currentThread, ptr as *AtomicU8)();
    //@ open AtomicU8_own(currentThread, _);
}

unsafe fn creation_store_recovery<'a>(ptr: *mut u8, value: u8)
//@ req type_interp::<AtomicU8>() &*& atomic_mask(MaskTop) &*& lifetime_token('a) &*& *ptr |-> ?initial_value;
//@ ens type_interp::<AtomicU8>() &*& atomic_mask(MaskTop) &*& [_]lifetime_dead_token('a) &*& *ptr |-> ?stored_value;
//@ on_unwind_ens false;
{
    let atomic: &'a AtomicU8 = unsafe { AtomicU8::from_ptr/*@::<'a>@*/(ptr) };
    let second: &'a AtomicU8 = unsafe { AtomicU8::from_ptr/*@::<'a>@*/(ptr) };
    atomic.store_relaxed/*@::<'a>@*/(value);
    //@ end_lifetime('a);
    unsafe { recover_plain_storage(ptr) };
}
