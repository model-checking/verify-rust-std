/*@
lem ptr_alignment_product(x: i32, y: i32)
    req true;
    ens x * (std::mem::size_of::<usize>() * y) == std::mem::size_of::<usize>() * (x * y);
{}

fix accepts_ptr<T>(value: *T) -> bool { true }
pred_ctor own_atomic_ptr_contents<T>(p: **T)(;) = std::intrinsics::atomic_points_to(p, 1, accepts_ptr);
pred<T> <AtomicPtr<T>>.own(t, value) = true;
pred<T> <AtomicPtr<T>>.share(k, t, l) = [_]frac_borrow(k, own_atomic_ptr_contents::<T>(ref_origin(l) as **T));

lem AtomicPtr_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *AtomicPtr<T>)
    req type_interp::<T>() &*& lifetime_inclusion(k1, k) == true &*& [_]AtomicPtr_share::<T>(k, t, l);
    ens type_interp::<T>() &*& [_]AtomicPtr_share::<T>(k1, t, l);
{
    open AtomicPtr_share::<T>(k, t, l);
    frac_borrow_mono(k, k1, own_atomic_ptr_contents::<T>(ref_origin(l) as **T));
    close AtomicPtr_share::<T>(k1, t, l);
    leak AtomicPtr_share::<T>(k1, t, l);
}

lem AtomicPtr_sync<T>(t1: thread_id_t)
    req type_interp::<T>() &*& is_Sync(typeid(AtomicPtr<T>)) == true &*& [_]AtomicPtr_share::<T>(?k, ?t0, ?l);
    ens type_interp::<T>() &*& [_]AtomicPtr_share::<T>(k, t1, l);
{
    open AtomicPtr_share::<T>(k, t0, l);
    close AtomicPtr_share::<T>(k, t1, l);
    leak AtomicPtr_share::<T>(k, t1, l);
}

lem AtomicPtr_send<T>(t1: thread_id_t)
    req type_interp::<T>() &*& is_Send(typeid(AtomicPtr<T>)) == true &*& AtomicPtr_own::<T>(?t0, ?value);
    ens type_interp::<T>() &*& AtomicPtr_own::<T>(t1, value);
{
    open AtomicPtr_own::<T>(t0, value);
    close AtomicPtr_own::<T>(t1, value);
}

lem AtomicPtr_share_full<T>(k: lifetime_t, t: thread_id_t, l: *AtomicPtr<T>)
    req type_interp::<T>() &*& atomic_mask(MaskTop) &*& full_borrow(k, AtomicPtr_full_borrow_content::<T>(t, l)) &*& [?q]lifetime_token(k) &*& ref_origin(l) == l;
    ens type_interp::<T>() &*& atomic_mask(MaskTop) &*& [_]AtomicPtr_share::<T>(k, t, l) &*& [q]lifetime_token(k);
{
    open_full_borrow_strong_m_(k, AtomicPtr_full_borrow_content::<T>(t, l));
    open AtomicPtr_full_borrow_content::<T>(t, l)();
    open AtomicPtr_own::<T>(t, _);
    close_points_to(l);
    to_u8s_(l);
    from_u8s_(l);
    open_points_to(l);
    let a = std::mem::align_of::<AtomicPtr<T>>();
    let n = std::mem::size_of::<usize>();
    assert (l as usize) % a == 0;
    assert a % n == 0;
    assert a >= n;
    div_rem_nonneg(l as usize, a);
    div_rem_nonneg(a, n);
    ptr_alignment_product((l as usize) / a, a / n);
    div_rem_nonneg_unique(l as usize, n, (l as usize) / a * (a / n), 0);
    std::intrinsics::atomic_align_of_ptr::<T>();
    std::intrinsics::close_atomic_points_to_m(l as **T, accepts_ptr);
    close own_atomic_ptr_contents::<T>(l as **T)();
    close True();
    produce_lem_ptr_chunk restore_full_borrow_(True, own_atomic_ptr_contents::<T>(l as **T), AtomicPtr_full_borrow_content::<T>(t, l))() {
        open True();
        open own_atomic_ptr_contents::<T>(l as **T)();
        std::intrinsics::open_atomic_points_to(l as **T);
        close_points_to(l);
        assert *l |-> ?value;
        close AtomicPtr_own::<T>(t, value);
        open_points_to(l);
        close AtomicPtr_full_borrow_content::<T>(t, l)();
    } {
        close_full_borrow_strong_m_();
    }
    full_borrow_into_frac_m(k, own_atomic_ptr_contents::<T>(l as **T));
    close AtomicPtr_share::<T>(k, t, l);
    leak AtomicPtr_share::<T>(k, t, l);
}

lem init_ref_AtomicPtr<T>(p: *AtomicPtr<T>)
    req type_interp::<T>() &*& atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]AtomicPtr_share::<T>(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]AtomicPtr_share::<T>(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    open AtomicPtr_share::<T>(k, t, x);
    open_ref_init_perm_AtomicPtr(p);
    close_ref_initialized_AtomicPtr(p, 1);
    close ref_initialized_::<AtomicPtr<T>>(p)();
    borrow_m(k, ref_initialized_(p));
    leak borrow_end_token(k, ref_initialized_(p));
    full_borrow_into_frac_m(k, ref_initialized_(p));
    close AtomicPtr_share::<T>(k, t, p);
    leak AtomicPtr_share::<T>(k, t, p);
}
@*/
