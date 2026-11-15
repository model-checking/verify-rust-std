/*@
// is_less_call applied outside its audit rule: two applications with the same arguments, different r.
lem probe8_call<T, F>(f0: F, a: T)
    req is_less_models::<T, F>(f0) == true;
    ens false;
{
    is_less_call::<T, F>(f0, f0, a, a, a, a, true);
    is_less_call::<T, F>(f0, f0, a, a, a, a, false);
}
// one application suffices when the "after" values are free: r = true contradicts irreflexivity.
lem probe8_call1<T, F>(f0: F, a: T)
    req is_less_models::<T, F>(f0) == true;
    ens false;
{
    is_less_call::<T, F>(f0, f0, a, a, a, a, true);
    is_less_irreflexive::<T, F>(f0, a);
}
@*/
