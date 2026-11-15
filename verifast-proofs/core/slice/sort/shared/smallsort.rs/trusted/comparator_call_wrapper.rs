// ===== BEGIN TRUSTED COMPARATOR CALL WRAPPER =====
//
// Trusted link between a comparator call and the comparator model (block TRUSTED COMPARATOR MODEL).
// Every call `is_less(&x, &y)` in this file goes through this wrapper; its body is exactly the
// original call (refinement-checker inlines it and checks the code against original/). Its spec is
// assumed (`assume_correct`), not proven: when the comparator value `f0` is well-behaved
// (`is_less_models`), the call does not unwind, leaves the comparator and both values unchanged, and
// returns the model order applied to the two values; otherwise it only returns the ownership it took.
// Every crate contains this block verbatim (checked by verify.sh).
unsafe fn is_less__VeriFast_wrapper<T, F: FnMut(&T, &T) -> bool>(f: &mut F, a: &T, b: &T) -> bool
//@ req thread_token(?t) &*& *f |-> ?f0 &*& <F>.own(t, f0) &*& [?qa](*a |-> ?a0) &*& [?qb](*b |-> ?b0);
/*@
ens thread_token(t) &*& *f |-> ?f1 &*& <F>.own(t, f1) &*& [qa](*a |-> ?a1) &*& [qb](*b |-> ?b1) &*&
    if is_less_models::<T, F>(f0) {
        f1 == f0 && a1 == a0 && b1 == b0 && result == apply_lt(is_less_model_of::<T, F>(f0), a0, b0)
    } else {
        true
    };
@*/
//@ on_unwind_ens thread_token(t) &*& *f |-> ?f1 &*& <F>.own(t, f1) &*& [qa](*a |-> _) &*& [qb](*b |-> _) &*& !is_less_models::<T, F>(f0);
//@ assume_correct
{
    f(a, b)
}
// ===== END TRUSTED COMPARATOR CALL WRAPPER =====
