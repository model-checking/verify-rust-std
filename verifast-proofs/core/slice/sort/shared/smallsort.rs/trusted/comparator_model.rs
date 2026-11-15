// ===== BEGIN TRUSTED COMPARATOR MODEL =====
//
// The only trusted part of the specifications. Everything in this block is assumed, not proven.
// Every target crate contains this block verbatim (checked by verify.sh); `assume` may appear
// nowhere else.
//
// `is_less_models::<T, F>(f)`: the comparator value `f` is well-behaved. A call `f(&a, &b)`
// terminates without panicking, leaves `f`, `a` and `b` unchanged, and returns
// `is_less_model_of::<T, F>(f)(a, b)`.
// `is_less_model_of::<T, F>(f)`: the order `f` computes. It is left uninterpreted so that the
// specifications hold for every such order; the lemmas below only fix it to be a strict weak order.
// The link between a real call `is_less(&x, &y)` and the model is the trusted wrapper
// `is_less__VeriFast_wrapper` (block TRUSTED COMPARATOR CALL WRAPPER at the end of smallsort.rs), which
// every such call goes through; there is no free-argument lemma for it, so each use of the link is
// tied to one real call.
fix is_less_models<T, F>(f: F) -> bool;
fix is_less_model_of<T, F>(f: F) -> fix(T, T, bool);

// `lt(a, b)`.
fix apply_lt<T>(lt: fix(T, T, bool), a: T, b: T) -> bool { lt(a, b) }

// Axiom (strict weak order, 1/3): irreflexive.
lem is_less_irreflexive<T, F>(f: F, a: T)
    req is_less_models::<T, F>(f) == true;
    ens !apply_lt(is_less_model_of::<T, F>(f), a, a);
{
    assume(false);
}

// Axiom (strict weak order, 2/3): transitive.
lem is_less_transitive<T, F>(f: F, a: T, b: T, c: T)
    req is_less_models::<T, F>(f) == true &*&
        apply_lt(is_less_model_of::<T, F>(f), a, b) && apply_lt(is_less_model_of::<T, F>(f), b, c);
    ens apply_lt(is_less_model_of::<T, F>(f), a, c) == true;
{
    assume(false);
}

// Axiom (strict weak order, 3/3): incomparability is transitive.
lem is_less_incomparable_transitive<T, F>(f: F, a: T, b: T, c: T)
    req is_less_models::<T, F>(f) == true &*&
        !apply_lt(is_less_model_of::<T, F>(f), a, b) && !apply_lt(is_less_model_of::<T, F>(f), b, a) &*&
        !apply_lt(is_less_model_of::<T, F>(f), b, c) && !apply_lt(is_less_model_of::<T, F>(f), c, b);
    ens !apply_lt(is_less_model_of::<T, F>(f), a, c) && !apply_lt(is_less_model_of::<T, F>(f), c, a);
{
    assume(false);
}

// ===== END TRUSTED COMPARATOR MODEL =====
