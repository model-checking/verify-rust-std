            pub const unsafe fn from_ptr<'a>(ptr: *mut $int_type) -> &'a $atomic_type
            //@ req type_interp::<Self>() &*& atomic_mask(MaskTop) &*& [?q]lifetime_token('a) &*& exists::<bool>(?fresh) &*& (if fresh { *ptr |-> ?value } else { [_](<Self>.share)('a, currentThread, ptr as *Self) }) &*& ptr as usize % std::mem::align_of::<Self>() == 0;
            //@ ens type_interp::<Self>() &*& atomic_mask(MaskTop) &*& [q]lifetime_token('a) &*& [_](<Self>.share)('a, currentThread, result) &*& [_](<Self>.share)('a, currentThread, ptr as *Self) &*& [_]frac_borrow('a, ref_initialized_(result)) &*& ref_origin(result) == ref_origin(ptr as *Self) &*& (if fresh { borrow_end_token('a, (<Self>.full_borrow_content)(currentThread, ptr as *Self)) } else { true });
            //@ on_unwind_ens false;
            {
                //@ open exists::<bool>(fresh);
                /*@ if fresh {
                    close_points_to(ptr as *Self);
                    assert *(ptr as *Self) |-> ?atomic;
                    close <Self>.own(currentThread, atomic);
                    close_full_borrow_content::<Self>(currentThread, ptr as *Self);
                    borrow('a, (<Self>.full_borrow_content)(currentThread, ptr as *Self));
                    share_full_borrow::<Self>('a, currentThread, ptr as *Self);
                } @*/
                //@ let p = precreate_ref(ptr as *Self);
                //@ init_ref_share::<Self>('a, currentThread, p);
                //@ open_frac_borrow('a, ref_initialized_(p), q);
                //@ open [?f]ref_initialized_::<Self>(p)();
                let result = unsafe { &*ptr.cast() };
                //@ close [f]ref_initialized_::<Self>(p)();
                //@ close_frac_borrow(f, ref_initialized_(p));
                result
            }