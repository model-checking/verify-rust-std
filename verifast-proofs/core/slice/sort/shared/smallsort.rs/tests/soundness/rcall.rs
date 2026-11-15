unsafe fn probe8_rcall<'a, T, F: FnMut(&T, &T) -> bool>(f: &mut F, a: &'a T, b: &'a T)
//@ req thread_token(?t) &*& *f |-> ?f0 &*& <F>.own(t, f0) &*& [1/2](*a |-> ?a0) &*& [1/2](*b |-> ?b0) &*& is_less_models::<T, F>(f0) == true &*& [_]frac_borrow('a, ref_initialized_(a)) &*& [_]frac_borrow('a, ref_initialized_(b)) &*& [?q]lifetime_token('a);
//@ ens false;
{
    let r1 = is_less__VeriFast_wrapper(f, a, b);
    let r2 = is_less__VeriFast_wrapper(f, a, b);
    let r3 = is_less__VeriFast_wrapper(f, b, a);
    //@ is_less_irreflexive::<T, F>(f0, a0);
    //@ assert r1 == r2;
    //@ if r1 && r3 { is_less_transitive::<T, F>(f0, a0, b0, a0); }
    //@ assert false;
}
