#![feature(core_intrinsics)]
#![allow(internal_features)]
use std::cell::UnsafeCell;

#[repr(C, align(8))]
pub struct AtomicUsize {
    v: UnsafeCell<usize>,
}

unsafe impl Sync for AtomicUsize {}

/*@
fix accepts_usize(value: usize) -> bool { true }
pred_ctor own_atomic_contents(p: *usize)(;) = std::intrinsics::atomic_points_to(p, 1, accepts_usize);
pred <AtomicUsize>.own(t, value) = true;
pred <AtomicUsize>.share(k, t, l) = [_]frac_borrow(k, own_atomic_contents(ref_origin(l) as *usize));

lem AtomicUsize_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *AtomicUsize)
    req lifetime_inclusion(k1, k) == true &*& [_]AtomicUsize_share(k, t, l);
    ens [_]AtomicUsize_share(k1, t, l);
{
    open AtomicUsize_share(k, t, l);
    frac_borrow_mono(k, k1, own_atomic_contents(ref_origin(l) as *usize));
    close AtomicUsize_share(k1, t, l);
    leak AtomicUsize_share(k1, t, l);
}

lem AtomicUsize_sync(t1: thread_id_t)
    req is_Sync(typeid(AtomicUsize)) == true &*& [_]AtomicUsize_share(?k, ?t0, ?l);
    ens [_]AtomicUsize_share(k, t1, l);
{
    open AtomicUsize_share(k, t0, l);
    close AtomicUsize_share(k, t1, l);
    leak AtomicUsize_share(k, t1, l);
}

lem AtomicUsize_share_full(k: lifetime_t, t: thread_id_t, l: *AtomicUsize)
    req atomic_mask(MaskTop) &*& full_borrow(k, AtomicUsize_full_borrow_content(t, l)) &*& [?q]lifetime_token(k) &*& ref_origin(l) == l;
    ens atomic_mask(MaskTop) &*& [_]AtomicUsize_share(k, t, l) &*& [q]lifetime_token(k);
{
    open_full_borrow_strong_m_(k, AtomicUsize_full_borrow_content(t, l));
    open AtomicUsize_full_borrow_content(t, l)();
    open AtomicUsize_own(t, _);
    close_points_to(l);
    to_u8s_(l);
    from_u8s_(l);
    assert (l as usize) % std::mem::align_of::<AtomicUsize>() == 0;
    assert std::mem::align_of::<AtomicUsize>() == 8;
    open_points_to(l);
    std::intrinsics::atomic_align_of_usize();
    std::intrinsics::close_atomic_points_to_m(l as *usize, accepts_usize);
    close own_atomic_contents(l as *usize)();
    close True();
    produce_lem_ptr_chunk restore_full_borrow_(True, own_atomic_contents(l as *usize), AtomicUsize_full_borrow_content(t, l))() {
        open True();
        open own_atomic_contents(l as *usize)();
        std::intrinsics::open_atomic_points_to(l as *usize);
        close_points_to(l);
        assert *l |-> ?value;
        close AtomicUsize_own(t, value);
        open_points_to(l);
        close AtomicUsize_full_borrow_content(t, l)();
    } {
        close_full_borrow_strong_m_();
    }
    full_borrow_into_frac_m(k, own_atomic_contents(l as *usize));
    close AtomicUsize_share(k, t, l);
    leak AtomicUsize_share(k, t, l);
}

lem init_ref_AtomicUsize(p: *AtomicUsize)
    req atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]AtomicUsize_share(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]AtomicUsize_share(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    open AtomicUsize_share(k, t, x);
    open_ref_init_perm_AtomicUsize(p);
    close_ref_initialized_AtomicUsize(p, 1);
    close ref_initialized_::<AtomicUsize>(p)();
    borrow_m(k, ref_initialized_(p));
    leak borrow_end_token(k, ref_initialized_(p));
    full_borrow_into_frac_m(k, ref_initialized_(p));
    close AtomicUsize_share(k, t, p);
    leak AtomicUsize_share(k, t, p);
}
@*/

impl AtomicUsize {
    pub const unsafe fn from_ptr<'a>(ptr: *mut usize) -> &'a AtomicUsize
    //@ req type_interp::<AtomicUsize>() &*& atomic_mask(MaskTop) &*& [?q]lifetime_token('a) &*& *ptr |-> ?value &*& ptr as usize % std::mem::align_of::<AtomicUsize>() == 0;
    //@ ens type_interp::<AtomicUsize>() &*& atomic_mask(MaskTop) &*& [q]lifetime_token('a) &*& [_]AtomicUsize_share('a, currentThread, result) &*& [_]ref_initialized(result) &*& [_]frac_borrow('a, ref_initialized_(result)) &*& ref_origin(result) == ref_origin(ptr as *AtomicUsize) &*& borrow_end_token('a, AtomicUsize_full_borrow_content(currentThread, ptr as *AtomicUsize));
    //@ on_unwind_ens false;
    {
        //@ close_points_to(ptr as *AtomicUsize);
        //@ assert *(ptr as *AtomicUsize) |-> ?atomic;
        //@ close AtomicUsize_own(currentThread, atomic);
        //@ open_points_to(ptr as *AtomicUsize);
        //@ close AtomicUsize_full_borrow_content(currentThread, ptr as *AtomicUsize)();
        //@ borrow('a, AtomicUsize_full_borrow_content(currentThread, ptr as *AtomicUsize));
        //@ share_full_borrow::<AtomicUsize>('a, currentThread, ptr as *AtomicUsize);
        //@ let p = precreate_ref(ptr as *AtomicUsize);
        //@ init_ref_share::<AtomicUsize>('a, currentThread, p);
        //@ open_frac_borrow('a, ref_initialized_(p), q);
        //@ open [?f]ref_initialized_::<AtomicUsize>(p)();
        let result = unsafe { &*ptr.cast() };
        //@ close [f]ref_initialized_::<AtomicUsize>(p)();
        //@ close_frac_borrow(f, ref_initialized_(p));
        //@ close_ref_initialized_AtomicUsize(p, 1);
        //@ leak ref_initialized(p);
        result
    }

    pub fn store_relaxed<'a>(&'a self, value: usize)
    //@ req [_]AtomicUsize_share('a, currentThread, self) &*& [?q]lifetime_token('a);
    //@ ens [q]lifetime_token('a);
    //@ on_unwind_ens false;
    {
        //@ open AtomicUsize_share('a, currentThread, self);
        //@ let f = open_frac_borrow('a, own_atomic_contents(ref_origin(self) as *usize), q);
        //@ open [f]own_atomic_contents(ref_origin(self) as *usize)();
        unsafe { std::intrinsics::atomic_store::<usize, {std::intrinsics::AtomicOrdering::Relaxed}>(self.v.get(), value) }
        //@ close [f]own_atomic_contents(ref_origin(self) as *usize)();
        //@ close_frac_borrow(f, own_atomic_contents(ref_origin(self) as *usize));
    }
}

unsafe fn recover_plain_storage(ptr: *mut usize)
//@ req [_]lifetime_dead_token(?k) &*& borrow_end_token(k, AtomicUsize_full_borrow_content(currentThread, ptr as *AtomicUsize));
//@ ens *ptr |-> ?stored_value;
//@ on_unwind_ens false;
{
    //@ borrow_end(k, AtomicUsize_full_borrow_content(currentThread, ptr as *AtomicUsize));
    //@ open AtomicUsize_full_borrow_content(currentThread, ptr as *AtomicUsize)();
    //@ open AtomicUsize_own(currentThread, _);
}
