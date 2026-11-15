// without is_less_models: the results are unconstrained; no contradiction.
unsafe fn probe8_rcall_nm<'a, T, F: FnMut(&T, &T) -> bool>(f: &mut F, a: &'a T, b: &'a T)
//@ req thread_token(?t) &*& *f |-> ?f0 &*& <F>.own(t, f0) &*& [1/2](*a |-> ?a0) &*& [1/2](*b |-> ?b0) &*& [_]frac_borrow('a, ref_initialized_(a)) &*& [_]frac_borrow('a, ref_initialized_(b)) &*& [?q]lifetime_token('a);
//@ ens false;
//@ on_unwind_ens thread_token(t) &*& *f |-> ?f1 &*& <F>.own(t, f1) &*& [1/2](*a |-> _) &*& [1/2](*b |-> _) &*& [q]lifetime_token('a);
{
    let r1 = is_less__VeriFast_wrapper(f, a, b);
    let r2 = is_less__VeriFast_wrapper(f, b, a);
    //@ assert false;
}
