//! This module contains a variety of sort implementations that are optimized for small lengths.

use crate::mem::{self, ManuallyDrop, MaybeUninit};
use crate::slice::sort::shared::FreezeMarker;
use crate::{hint, intrinsics, ptr, slice};

/*@

// ===== Ghost vocabulary for the Challenge 8 target specifications =====

// `x` occurs in `xs`.
fix contains<T>(xs: list<T>, x: T) -> bool {
    match xs {
        nil => false,
        cons(x0, xs0) => x0 == x || contains(xs0, x)
    }
}

// `xs` is a permutation of `ys` (same elements, same multiplicities).
fix is_perm<T>(xs: list<T>, ys: list<T>) -> bool {
    match xs {
        nil => ys == nil,
        cons(x, xs0) => contains(ys, x) && is_perm(xs0, remove(x, ys))
    }
}

// No element of `xs` is less than its predecessor according to `lt`.
// (Clause-by-clause equivalent to the nested form `cons(x, xs0) => match xs0 { nil => true,
// cons(y, xs1) => !lt(y, x) && sorted_by(lt, xs0) }`, which VeriFast 26.10 cannot unfold: any proof step
// that unfolds a fixpoint with a nested `match` on a pattern variable aborts with
// `Fatal error: exception Not_found`.)
fix sorted_by<T>(lt: fix(T, T, bool), xs: list<T>) -> bool {
    match xs {
        nil => true,
        cons(x, xs0) => (xs0 == nil || !lt(head(xs0), x)) && sorted_by(lt, xs0)
    }
}

// `xs` with the element at index `i` replaced by `x`.
fix update_nth<T>(i: i32, x: T, xs: list<T>) -> list<T> {
    match xs {
        nil => nil,
        cons(x0, xs0) => if i == 0 { cons(x, xs0) } else { cons(x0, update_nth(i - 1, x, xs0)) }
    }
}

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

@*/

// ===== BEGIN TRUSTED MODEL AXIOMS =====
//
// Trusted: facts about Rust that VeriFast 26.10 does not model. Each is assumed, not proven. Every crate
// contains this block verbatim (checked by verify.sh).
/*@

// `MaybeUninit<T>` owns no resources (it may hold any bytes, and dropping it does nothing). VeriFast 26.10
// leaves `<MaybeUninit<T>>.own` undefined.
lem MaybeUninit_own_trivial<T>(t: thread_id_t, v: std::mem::MaybeUninit<T>)
    req true;
    ens own::<std::mem::MaybeUninit<T>>(t)(v);
{
    assume(false);
}

// Layout of the stack arrays `MaybeUninit<[T; N]>` of `small_sort_general` (N = 48) and
// `small_sort_network` (N = 32): an array of `N` elements, aligned as `T` (Rust reference, "Type
// layout": arrays). VeriFast 26.10 has no `size_of`/`align_of` facts for array types.
lem MaybeUninit_array_48_layout<T>()
    req true;
    ens std::mem::size_of::<std::mem::MaybeUninit<[T; 48]>>() == 48 * std::mem::size_of::<T>() &*&
        std::mem::align_of::<std::mem::MaybeUninit<[T; 48]>>() == std::mem::align_of::<T>();
{
    assume(false);
}

lem MaybeUninit_array_32_layout<T>()
    req true;
    ens std::mem::size_of::<std::mem::MaybeUninit<[T; 32]>>() == 32 * std::mem::size_of::<T>() &*&
        std::mem::align_of::<std::mem::MaybeUninit<[T; 32]>>() == std::mem::align_of::<T>();
{
    assume(false);
}

// For every `T` that the trait impls of `UnstableSmallSortFreezeTypeImpl` are instantiated with, the
// array types `[T; 48]` (in `small_sort_general`, which both impls call) and `[T; 32]` (in
// `small_sort_network`, called by the `CopyMarker` impl) exist; rustc rejects types larger than
// `isize::MAX` bytes. So `size_of::<T>() * 48` (and `* 32`) does not overflow.
lem small_sort_general_instantiated<T>()
    req true;
    ens 0 <= std::mem::size_of::<T>() &*& 48 * std::mem::size_of::<T>() <= isize::MAX;
{
    assume(false);
}

@*/
// ===== END TRUSTED MODEL AXIOMS =====

/*@

// ===== Proof library (not trusted: every lemma below is proven) =====

// Splits a points-to chunk into two chunks of different predicate symbols, so that VeriFast does not
// merge them again (needed when two shared references to the same place are passed to one call).
lem points_to_split_half<T>(p: *T)
    req [?f](*p |-> ?v);
    ens [f/2](*p |-> v) &*& [f/2]points_to_(p, some(v));
{
    open points_to(p, v);
    close [f/2]points_to(p, v);
}

// A fraction of a points-to chunk kept out of reach of a call (so that the call sees only the rest).
pred hidden_pt<T>(p: *T, v: T) = *p |-> v;

lem pt_hide_half<T>(p: *T)
    req [?f](*p |-> ?v);
    ens [f/2](*p |-> v) &*& [f/2]hidden_pt(p, v);
{
    close [f/2]hidden_pt(p, v);
}

lem pt_unhide<T>(p: *T)
    req [?f1](*p |-> ?v1) &*& [?f2]hidden_pt(p, ?v2);
    ens [f1 + f2](*p |-> v2) &*& v1 == v2;
{
    open [f2]hidden_pt(p, v2);
}

// ----- lists -----

lem nth_take_lt<T>(i: i32, n: i32, xs: list<T>)
    req 0 <= i &*& i < n;
    ens nth(i, take(n, xs)) == nth(i, xs);
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if i != 0 { nth_take_lt(i - 1, n - 1, xs0); } }
    }
}

lem update_nth_length<T>(i: i32, x: T, xs: list<T>)
    req true;
    ens length(update_nth(i, x, xs)) == length(xs);
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if i != 0 { update_nth_length(i - 1, x, xs0); } }
    }
}

lem update_nth_def<T>(i: i32, x: T, xs: list<T>)
    req 0 <= i &*& i < length(xs);
    ens update_nth(i, x, xs) == append(take(i, xs), cons(x, drop(i + 1, xs)));
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if i != 0 { update_nth_def(i - 1, x, xs0); } }
    }
}

lem nth_update_nth_same<T>(i: i32, x: T, xs: list<T>)
    req 0 <= i &*& i < length(xs);
    ens nth(i, update_nth(i, x, xs)) == x;
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if i != 0 { nth_update_nth_same(i - 1, x, xs0); } }
    }
}

lem nth_update_nth_other<T>(i: i32, j: i32, x: T, xs: list<T>)
    req i != j;
    ens nth(j, update_nth(i, x, xs)) == nth(j, xs);
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if i != 0 && j != 0 { nth_update_nth_other(i - 1, j - 1, x, xs0); } }
    }
}

lem update_nth_nth<T>(i: i32, xs: list<T>)
    req true;
    ens update_nth(i, nth(i, xs), xs) == xs;
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if i != 0 { update_nth_nth(i - 1, xs0); } }
    }
}

lem update_nth_update_nth_same<T>(i: i32, x: T, y: T, xs: list<T>)
    req true;
    ens update_nth(i, x, update_nth(i, y, xs)) == update_nth(i, x, xs);
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if i != 0 { update_nth_update_nth_same(i - 1, x, y, xs0); } }
    }
}

// ----- arrays -----

lem array_join_n0<T>(p: *T, c1: i32, c2: i32)
    req [?f]array::<T>(p, c1, ?vs1) &*& [f]array::<T>(p + c1, c2, ?vs2);
    ens [f]array::<T>(p, c1 + c2, append(vs1, vs2));
{
    open array::<T>(p, c1, vs1);
    if c1 == 0 {
    } else {
        array_join_n0(p + 1, c1 - 1, c2);
        close [f]array::<T>(p, c1 + c2, append(vs1, vs2));
    }
}

pred array_hole<T>(p: *T, n: i32, vs: list<T>, i: i32) =
    0 <= i &*& i < n &*& length(vs) == n &*&
    array::<T>(p, i, take(i, vs)) &*& array::<T>(p + i + 1, n - i - 1, drop(i + 1, vs));

lem array_open_at<T>(p: *T, i: i32)
    req [?f]array::<T>(p, ?n, ?vs) &*& 0 <= i &*& i < n;
    ens [f](*(p + i) |-> nth(i, vs)) &*& [f]array_hole::<T>(p, n, vs, i);
{
    array_split(p, i);
    drop_n_plus_one(i, vs);
    open array::<T>(p + i, n - i, drop(i, vs));
    close [f]array_hole::<T>(p, n, vs, i);
}

lem array_close_at<T>(p: *T, i: i32, x: T)
    req [?f](*(p + i) |-> x) &*& [f]array_hole::<T>(p, ?n, ?vs, i);
    ens [f]array::<T>(p, n, update_nth(i, x, vs));
{
    open array_hole::<T>(p, n, vs, i);
    close [f]array::<T>(p + i, n - i, cons(x, drop(i + 1, vs)));
    array_join_n0(p, i, n - i);
    update_nth_def(i, x, vs);
}

lem take_update_nth<T>(n: i32, j: i32, y: T, xs: list<T>)
    req 0 <= n &*& 0 <= j;
    ens take(n, update_nth(j, y, xs)) == if j < n { update_nth(j, y, take(n, xs)) } else { take(n, xs) };
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if n != 0 && j != 0 { take_update_nth(n - 1, j - 1, y, xs0); } }
    }
}

lem drop_update_nth<T>(n: i32, j: i32, y: T, xs: list<T>)
    req 0 <= n &*& 0 <= j;
    ens drop(n, update_nth(j, y, xs)) == if j < n { drop(n, xs) } else { update_nth(j - n, y, drop(n, xs)) };
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if n != 0 { if j != 0 { drop_update_nth(n - 1, j - 1, y, xs0); } else { } } }
    }
}

pred array_hole2<T>(p: *T, n: i32, vs: list<T>, i: i32, j: i32) =
    0 <= i &*& i < n &*& 0 <= j &*& j < n &*& i != j &*& length(vs) == n &*&
    if j < i {
        array_hole::<T>(p, i, take(i, vs), j) &*& array::<T>(p + i + 1, n - i - 1, drop(i + 1, vs))
    } else {
        array::<T>(p, i, take(i, vs)) &*& array_hole::<T>(p + i + 1, n - i - 1, drop(i + 1, vs), j - i - 1)
    };

lem array_open_at2<T>(p: *T, i: i32, j: i32)
    req [?f]array::<T>(p, ?n, ?vs) &*& 0 <= i &*& i < n &*& 0 <= j &*& j < n &*& i != j;
    ens [f](*(p + i) |-> nth(i, vs)) &*& [f](*(p + j) |-> nth(j, vs)) &*& [f]array_hole2::<T>(p, n, vs, i, j);
{
    array_open_at(p, i);
    open array_hole::<T>(p, n, vs, i);
    if j < i {
        array_open_at(p, j);
    } else {
        array_open_at(p + i + 1, j - i - 1);
        nth_drop(j - i - 1, i + 1, vs);
    }
    close [f]array_hole2::<T>(p, n, vs, i, j);
}

lem array_close_at2<T>(p: *T, i: i32, j: i32, x: T, y: T)
    req [?f](*(p + i) |-> x) &*& [f](*(p + j) |-> y) &*& [f]array_hole2::<T>(p, ?n, ?vs, i, j);
    ens [f]array::<T>(p, n, update_nth(i, x, update_nth(j, y, vs)));
{
    open array_hole2::<T>(p, n, vs, i, j);
    let ws = update_nth(j, y, vs);
    update_nth_length(j, y, vs);
    take_update_nth(i, j, y, vs);
    drop_update_nth(i + 1, j, y, vs);
    if j < i {
        array_close_at(p, j, y);
    } else {
        array_close_at(p + i + 1, j - i - 1, y);
    }
    close [f]array_hole::<T>(p, n, ws, i);
    array_close_at(p, i, x);
}

// Reading two elements leaves the array unchanged.
lem array_close_at2_same<T>(p: *T, i: i32, j: i32)
    req [?f](*(p + i) |-> ?x) &*& [f](*(p + j) |-> ?y) &*& [f]array_hole2::<T>(p, ?n, ?vs, i, j) &*& x == nth(i, vs) &*& y == nth(j, vs);
    ens [f]array::<T>(p, n, vs);
{
    array_close_at2(p, i, j, x, y);
    update_nth_nth(j, vs);
    update_nth_nth(i, vs);
}

lem array_close_at_same<T>(p: *T, i: i32)
    req [?f](*(p + i) |-> ?x) &*& [f]array_hole::<T>(p, ?n, ?vs, i) &*& x == nth(i, vs);
    ens [f]array::<T>(p, n, vs);
{
    array_close_at(p, i, x);
    update_nth_nth(i, vs);
}

// ----- permutations -----

lem contains_remove<T>(x: T, y: T, xs: list<T>)
    req contains(xs, x) == true &*& x != y;
    ens contains(remove(y, xs), x) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if x0 != x && x0 != y { contains_remove(x, y, xs0); } }
    }
}

lem contains_remove_inv<T>(x: T, y: T, xs: list<T>)
    req contains(remove(y, xs), x) == true;
    ens contains(xs, x) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if x0 != y && x0 != x { contains_remove_inv(x, y, xs0); } }
    }
}

lem remove_remove_comm<T>(x: T, y: T, xs: list<T>)
    req true;
    ens remove(x, remove(y, xs)) == remove(y, remove(x, xs));
{
    match xs {
        nil => {}
        cons(x0, xs0) => { remove_remove_comm(x, y, xs0); }
    }
}

lem is_perm_refl<T>(xs: list<T>)
    req true;
    ens is_perm(xs, xs) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => { is_perm_refl(xs0); }
    }
}

lem length_remove<T>(x: T, xs: list<T>)
    req contains(xs, x) == true;
    ens length(remove(x, xs)) == length(xs) - 1;
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if x0 != x { length_remove(x, xs0); } }
    }
}

lem is_perm_length<T>(xs: list<T>, ys: list<T>)
    req is_perm(xs, ys) == true;
    ens length(xs) == length(ys);
{
    match xs {
        nil => {}
        cons(x0, xs0) => { is_perm_length(xs0, remove(x0, ys)); length_remove(x0, ys); }
    }
}

lem is_perm_contains<T>(xs: list<T>, ys: list<T>, z: T)
    req is_perm(xs, ys) == true &*& contains(xs, z) == true;
    ens contains(ys, z) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            if x0 != z {
                is_perm_contains(xs0, remove(x0, ys), z);
                contains_remove_inv(z, x0, ys);
            }
        }
    }
}

lem is_perm_remove<T>(xs: list<T>, ys: list<T>, z: T)
    req is_perm(xs, ys) == true &*& contains(xs, z) == true;
    ens contains(ys, z) == true &*& is_perm(remove(z, xs), remove(z, ys)) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            if x0 == z {
            } else {
                is_perm_remove(xs0, remove(x0, ys), z);
                contains_remove_inv(z, x0, ys);
                contains_remove(x0, z, ys);
                remove_remove_comm(x0, z, ys);
            }
        }
    }
}

lem is_perm_trans<T>(xs: list<T>, ys: list<T>, zs: list<T>)
    req is_perm(xs, ys) == true &*& is_perm(ys, zs) == true;
    ens is_perm(xs, zs) == true;
{
    match xs {
        nil => { is_perm_length(ys, zs); match zs { nil => {} cons(z0, zs0) => {} } }
        cons(x0, xs0) => {
            is_perm_remove(ys, zs, x0);
            is_perm_trans(xs0, remove(x0, ys), remove(x0, zs));
        }
    }
}

lem is_perm_cons_r<T>(ys: list<T>, x: T, ws: list<T>)
    req is_perm(remove(x, ys), ws) == true &*& contains(ys, x) == true;
    ens is_perm(ys, cons(x, ws)) == true;
{
    match ys {
        nil => {}
        cons(y0, ys0) => {
            if y0 == x {
            } else {
                is_perm_cons_r(ys0, x, remove(y0, ws));
            }
        }
    }
}

lem is_perm_sym<T>(xs: list<T>, ys: list<T>)
    req is_perm(xs, ys) == true;
    ens is_perm(ys, xs) == true;
{
    match xs {
        nil => { match ys { nil => {} cons(y0, ys0) => {} } }
        cons(x0, xs0) => {
            is_perm_sym(xs0, remove(x0, ys));
            is_perm_cons_r(ys, x0, xs0);
        }
    }
}

lem is_perm_cons<T>(x: T, xs: list<T>, ys: list<T>)
    req is_perm(xs, ys) == true;
    ens is_perm(cons(x, xs), cons(x, ys)) == true;
{
}

lem is_perm_swap_head<T>(a: T, b: T, l: list<T>)
    req true;
    ens is_perm(cons(a, cons(b, l)), cons(b, cons(a, l))) == true;
{
    is_perm_refl(cons(b, l));
    is_perm_refl(l);
}

lem is_perm_update_nth<T>(i: i32, x: T, ws: list<T>)
    req 0 <= i &*& i < length(ws);
    ens is_perm(cons(nth(i, ws), update_nth(i, x, ws)), cons(x, ws)) == true;
{
    match ws {
        nil => {}
        cons(w, ws0) => {
            if i == 0 {
                is_perm_swap_head(w, x, ws0);
            } else {
                is_perm_update_nth(i - 1, x, ws0);
                let a = nth(i - 1, ws0);
                let u = update_nth(i - 1, x, ws0);
                is_perm_swap_head(a, w, u);
                is_perm_cons(w, cons(a, u), cons(x, ws0));
                is_perm_trans(cons(a, cons(w, u)), cons(w, cons(a, u)), cons(w, cons(x, ws0)));
                is_perm_swap_head(w, x, ws0);
                is_perm_trans(cons(a, cons(w, u)), cons(w, cons(x, ws0)), cons(x, cons(w, ws0)));
            }
        }
    }
}

// Swapping two positions is a permutation.
lem is_perm_swap<T>(i: i32, j: i32, vs: list<T>)
    req 0 <= i &*& i < length(vs) &*& 0 <= j &*& j < length(vs);
    ens is_perm(update_nth(i, nth(j, vs), update_nth(j, nth(i, vs), vs)), vs) == true;
{
    if i == j {
        update_nth_nth(i, vs);
        update_nth_update_nth_same(i, nth(i, vs), nth(i, vs), vs);
        is_perm_refl(vs);
    } else {
        let ws = update_nth(j, nth(i, vs), vs);
        update_nth_length(j, nth(i, vs), vs);
        nth_update_nth_other(j, i, nth(i, vs), vs);
        is_perm_update_nth(i, nth(j, vs), ws);
        // cons(vi, final) ~ cons(vj, ws)
        is_perm_update_nth(j, nth(i, vs), vs);
        // cons(vj, ws) ~ cons(vi, vs)
        is_perm_trans(cons(nth(i, vs), update_nth(i, nth(j, vs), ws)), cons(nth(j, vs), ws), cons(nth(i, vs), vs));
    }
}

// One more swap on top of a permutation of `vs0`.
lem perm_step<T>(i: i32, j: i32, l: list<T>, vs0: list<T>)
    req is_perm(l, vs0) == true &*& 0 <= i &*& i < length(l) &*& 0 <= j &*& j < length(l);
    ens is_perm(update_nth(i, nth(j, l), update_nth(j, nth(i, l), l)), vs0) == true;
{
    is_perm_swap(i, j, l);
    is_perm_trans(update_nth(i, nth(j, l), update_nth(j, nth(i, l), l)), l, vs0);
}

lem foreach_unremove<T>(x: T, xs: list<T>, p: pred(T))
    req foreach(remove(x, xs), p) &*& p(x) &*& contains(xs, x) == true;
    ens foreach(xs, p);
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            if x0 == x {
                close foreach(xs, p);
            } else {
                open foreach(remove(x, xs), p);
                foreach_unremove(x, xs0, p);
                close foreach(xs, p);
            }
        }
    }
}

lem foreach_perm<T>(xs: list<T>, ys: list<T>)
    req foreach(xs, ?p) &*& is_perm(xs, ys) == true;
    ens foreach(ys, p);
{
    match xs {
        nil => { open foreach(xs, p); match ys { nil => { close foreach(ys, p); } cons(y0, ys0) => {} } }
        cons(x0, xs0) => {
            open foreach(xs, p);
            foreach_perm(xs0, remove(x0, ys));
            foreach_unremove(x0, ys, p);
        }
    }
}

// ----- arithmetic -----

lem mul_pos(a: i32, b: i32)
    req 0 < a &*& 0 < b;
    ens 0 < a * b &*& b <= a * b;
{
    mul_mono_l(1, a, b);
}

// `p + i == p` (as element pointers) with `i != 0`: the element type is zero-sized.
lem ptr_add_eq_zst<T>(p: *T, i: i32, q: *T)
    req p + i == p &*& i != 0 &*& [?f](*q |-> ?v);
    ens std::mem::size_of::<T>() == 0 &*& [f](*q |-> v);
{
    points_to_limits(q);
    let s = std::mem::size_of::<T>();
    if s != 0 {
        assert (p as pointer).address + i * s == (p as pointer).address;
        if i > 0 { mul_pos(i, s); } else { mul_pos(-i, s); }
    }
}

lem array_size_nonneg<T>(p: *T)
    req [?f]array::<T>(p, ?n, ?vs) &*& 0 < n;
    ens [f]array::<T>(p, n, vs) &*& 0 <= std::mem::size_of::<T>();
{
    open array::<T>(p, n, vs);
    points_to_limits(p);
    close [f]array::<T>(p, n, vs);
}

lem ptr_add_inj<T>(p: *T, i: i32, j: i32)
    req p + i == p + j &*& std::mem::size_of::<T>() > 0;
    ens i == j;
{
    let s = std::mem::size_of::<T>();
    if i != j {
        assert (p as pointer).address + i * s == (p as pointer).address + j * s;
        if i > j { mul_pos(i - j, s); } else { mul_pos(j - i, s); }
    }
}

// ----- small arrays -----

lem array4_open<T>(p: *T)
    req [?f]array::<T>(p, 4, ?vs);
    ens [f](*p |-> nth(0, vs)) &*& [f](*(p + 1) |-> nth(1, vs)) &*& [f](*(p + 2) |-> nth(2, vs)) &*& [f](*(p + 3) |-> nth(3, vs)) &*&
        [f]array::<T>(p + 4, 0, nil) &*& vs == [nth(0, vs), nth(1, vs), nth(2, vs), nth(3, vs)];
{
    open array::<T>(p, 4, vs);
    open array::<T>(p + 1, 3, _);
    open array::<T>(p + 2, 2, _);
    open array::<T>(p + 3, 1, _);
    open array::<T>(p + 4, 0, _);
    close [f]array::<T>(p + 4, 0, nil);
}

lem array4_close<T>(p: *T)
    req [?f](*p |-> ?v0) &*& [f](*(p + 1) |-> ?v1) &*& [f](*(p + 2) |-> ?v2) &*& [f](*(p + 3) |-> ?v3) &*& [f]array::<T>(p + 4, 0, nil);
    ens [f]array::<T>(p, 4, [v0, v1, v2, v3]);
{
    points_to_limits(p);
    points_to_limits(p + 1);
    points_to_limits(p + 2);
    points_to_limits(p + 3);
    close [f]array::<T>(p + 3, 1, [v3]);
    close [f]array::<T>(p + 2, 2, [v2, v3]);
    close [f]array::<T>(p + 1, 3, [v1, v2, v3]);
    close [f]array::<T>(p, 4, [v0, v1, v2, v3]);
}

lem array__4_open<T>(p: *T)
    req array_::<T>(p, 4, ?vs);
    ens (*p |-> _) &*& (*(p + 1) |-> _) &*& (*(p + 2) |-> _) &*& (*(p + 3) |-> _) &*& array_::<T>(p + 4, 0, nil);
{
    open array_::<T>(p, 4, vs);
    open array_::<T>(p + 1, 3, _);
    open array_::<T>(p + 2, 2, _);
    open array_::<T>(p + 3, 1, _);
    open array_::<T>(p + 4, 0, _);
    close array_::<T>(p + 4, 0, nil);
}

// A one-element array at `p` from its points-to chunk, and back.
lem array1_close<T>(p: *T)
    req [?f](*p |-> ?v);
    ens [f]array::<T>(p, 1, [v]);
{
    points_to_limits(p);
    close [f]array::<T>(p + 1, 0, nil);
    close [f]array::<T>(p, 1, [v]);
}

lem array1_open<T>(p: *T)
    req [?f]array::<T>(p, 1, ?vs);
    ens [f](*p |-> head(vs)) &*& vs == [head(vs)];
{
    open array::<T>(p, 1, vs);
    open array::<T>(p + 1, 0, _);
}

lem array_1_close<T>(p: *T)
    req *p |-> _;
    ens array_::<T>(p, 1, _);
{
    points_to__limits(p);
    close array_::<T>(p + 1, 0, nil);
    close array_::<T>(p, 1, _);
}

// ----- zero-sized types -----

// Any two values of a zero-sized type are equal (both are `of_u8s_` of the empty byte list).
lem zst_values_equal<T>(p: *T, q: *T)
    req [?f1](*p |-> ?v1) &*& [?f2](*q |-> ?v2) &*& std::mem::size_of::<T>() == 0;
    ens [f1](*p |-> v1) &*& [f2](*q |-> v2) &*& v1 == v2;
{
    to_u8s_(p);
    to_u8s_(q);
    assert [f1](p as *u8)[..0] |-?-> ?bs1;
    assert [f2](q as *u8)[..0] |-?-> ?bs2;
    match bs1 { nil => {} cons(b1, bs10) => {} }
    match bs2 { nil => {} cons(b2, bs20) => {} }
    from_u8s_(p);
    from_u8s_(q);
    close [f1]points_to::<T>(p, v1);
    close [f2]points_to::<T>(q, v2);
}

// ----- array helpers, part 2 -----

// `array_join` with explicit counts (so that the right chunks are picked when `T` is zero-sized and
// several arrays start at the same address).
lem array_join_n<T>(p: *T, c1: i32, c2: i32)
    req [?f]array::<T>(p, c1, ?vs1) &*& [f]array::<T>(p + c1, c2, ?vs2);
    ens [f]array::<T>(p, c1 + c2, append(vs1, vs2));
{
    open array::<T>(p, c1, vs1);
    if c1 == 0 {
    } else {
        array_join_n(p + 1, c1 - 1, c2);
        close [f]array::<T>(p, c1 + c2, append(vs1, vs2));
    }
}

lem take_take<T>(m: i32, n: i32, xs: list<T>)
    req 0 <= m &*& m <= n;
    ens take(m, take(n, xs)) == take(m, xs);
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if m != 0 { take_take(m - 1, n - 1, xs0); } }
    }
}

lem array_split_last<T>(p: *T, m: i32)
    req [?f]array::<T>(p, m + 1, ?vs) &*& 0 <= m;
    ens [f]array::<T>(p, m, take(m, vs)) &*& [f](*(p + m) |-> nth(m, vs)) &*& [f]array::<T>(p + m + 1, 0, nil) &*& vs == append(take(m, vs), [nth(m, vs)]);
{
    array_split(p, m);
    drop_n_plus_one(m, vs);
    open array::<T>(p + m, 1, _);
}

lem array_join_last<T>(p: *T, m: i32)
    req [?f]array::<T>(p, m, ?xs) &*& [f](*(p + m) |-> ?x) &*& [f]array::<T>(p + m + 1, 0, nil);
    ens [f]array::<T>(p, m + 1, append(xs, [x]));
{
    close [f]array::<T>(p + m, 1, [x]);
    array_join(p);
}
// ----- pointer limits inside arrays -----

lem array_ptr_within_limits<T>(p: *T, k: i32)
    req [?f]array::<T>(p, ?n, ?vs) &*& 0 <= k &*& k <= n;
    ens [f]array::<T>(p, n, vs) &*& pointer_within_limits(p + k) == true;
{
    array_split(p, k);
    array_join_n(p, k, n - k);
}

lem array__split_n<T>(p: *T, k: i32)
    req [?f]array_::<T>(p, ?n, ?vs) &*& 0 <= k &*& k <= n;
    ens [f]array_::<T>(p, k, take(k, vs)) &*& [f]array_::<T>(p + k, n - k, drop(k, vs));
{
    array__split(p, k);
}

lem array__join_n<T>(p: *T, c1: i32, c2: i32)
    req [?f]array_::<T>(p, c1, ?vs1) &*& [f]array_::<T>(p + c1, c2, ?vs2);
    ens [f]array_::<T>(p, c1 + c2, append(vs1, vs2));
{
    open array_::<T>(p, c1, vs1);
    if c1 == 0 {
    } else {
        array__join_n(p + 1, c1 - 1, c2);
        close [f]array_::<T>(p, c1 + c2, append(vs1, vs2));
    }
}

lem array__ptr_within_limits<T>(p: *T, k: i32)
    req [?f]array_::<T>(p, ?n, ?vs) &*& 0 <= k &*& k <= n;
    ens [f]array_::<T>(p, n, vs) &*& pointer_within_limits(p + k) == true;
{
    array__split(p, k);
    array__join_n(p, k, n - k);
}

// `p + i < p + j` (by address): the element type is not zero-sized and `i < j`.
lem ptr_lt_index<T>(p: *T, i: i32, j: i32)
    req (p + i) < (p + j) &*& 0 <= std::mem::size_of::<T>();
    ens 0 < std::mem::size_of::<T>() &*& i < j;
{
    let s = std::mem::size_of::<T>();
    if s == 0 {
    } else if i >= j {
        mul_mono_l(j, i, s);
    }
}

// ----- wrapping pointer arithmetic (see `ptr_wrapping_offset` in the STD WRAPPERS block) -----

lem pwo_no_wrap<T>(p: *T, n: i32)
    req 0 <= (p as pointer).address + n * std::mem::size_of::<T>() &*& (p as pointer).address + n * std::mem::size_of::<T>() <= usize::MAX;
    ens ptr_wrapping_offset(p, n) == p + n;
{
}

lem pwo_roundtrip<T>(p: *T)
    req 0 <= (p as pointer).address &*& (p as pointer).address <= usize::MAX &*&
        0 <= std::mem::size_of::<T>() &*& std::mem::size_of::<T>() <= isize::MAX;
    ens ptr_wrapping_offset(ptr_wrapping_offset(p, -1), 1) == p;
{
}

@*/

/*@

// ===== Proof library: sorting (not trusted: every lemma below is proven) =====

// Facts about the insertion position `j` of `x` into `xs` found by `insert_tail` (under a well-behaved comparator).
pred ins_facts<T>(m: bool, order: fix(T, T, bool), x: T, xs: list<T>, j: i32) =
    0 <= j &*& j < length(xs) &*&
    (!m || ((j == 0 || !apply_lt(order, x, nth(j - 1, xs))) && apply_lt(order, x, nth(j, xs)))) == true;

// ----- derived order facts (from the three comparator-model axioms) -----

lem lt_asym<T, F>(f0: F, a: T, b: T)
    req is_less_models::<T, F>(f0) == true &*& apply_lt(is_less_model_of::<T, F>(f0), a, b) == true;
    ens !apply_lt(is_less_model_of::<T, F>(f0), b, a);
{
    if apply_lt(is_less_model_of::<T, F>(f0), b, a) {
        is_less_transitive::<T, F>(f0, a, b, a);
        is_less_irreflexive::<T, F>(f0, a);
    }
}

// Negative transitivity: `x <= y` and `y <= z` (as `!lt(y, x)`, `!lt(z, y)`) give `x <= z`.
lem lt_neg_trans<T, F>(f0: F, x: T, y: T, z: T)
    req is_less_models::<T, F>(f0) == true &*&
        !apply_lt(is_less_model_of::<T, F>(f0), y, x) && !apply_lt(is_less_model_of::<T, F>(f0), z, y);
    ens !apply_lt(is_less_model_of::<T, F>(f0), z, x);
{
    let lt = is_less_model_of::<T, F>(f0);
    if apply_lt(lt, z, x) {
        if apply_lt(lt, y, z) {
            is_less_transitive::<T, F>(f0, y, z, x);
        } else if apply_lt(lt, x, y) {
            is_less_transitive::<T, F>(f0, z, x, y);
        } else {
            is_less_incomparable_transitive::<T, F>(f0, x, y, z);
        }
    }
}

fix all_eq<T>(xs: list<T>, v: T) -> bool {
    match xs { nil => true, cons(x, xs0) => x == v && all_eq(xs0, v) }
}

lem zst_array_all_eq<T>(p: *T, n: i32, w: *T)
    req [?q]array::<T>(p, n, ?vs) &*& [?r](*w |-> ?v) &*& std::mem::size_of::<T>() == 0;
    ens [q]array::<T>(p, n, vs) &*& [r](*w |-> v) &*& all_eq(vs, v) == true;
{
    open array::<T>(p, n, vs);
    if n != 0 {
        zst_values_equal(p, w);
        zst_array_all_eq(p + 1, n - 1, w);
    }
    close [q]array::<T>(p, n, vs);
}

lem all_eq_sorted<T, F>(f0: F, xs: list<T>, v: T)
    req all_eq(xs, v) == true &*& is_less_models::<T, F>(f0) == true;
    ens sorted_by(is_less_model_of::<T, F>(f0), xs) == true;
{
    match xs {
        nil => {}
        cons(x, xs0) => {
            is_less_irreflexive::<T, F>(f0, v);
            all_eq_sorted::<T, F>(f0, xs0, v);
            match xs0 { nil => {} cons(y, ys) => {} }
        }
    }
}

// Under a well-behaved comparator, any list of values of a zero-sized type is sorted (all its values are
// equal, and the order is irreflexive).
lem zst_array_sorted<T, F>(f0: F, p: *T, n: i32)
    req [?q]array::<T>(p, n, ?vs) &*& std::mem::size_of::<T>() == 0 &*& is_less_models::<T, F>(f0) == true;
    ens [q]array::<T>(p, n, vs) &*& sorted_by(is_less_model_of::<T, F>(f0), vs) == true;
{
    open array::<T>(p, n, vs);
    if n != 0 {
        zst_array_all_eq(p + 1, n - 1, p);
        all_eq_sorted::<T, F>(f0, vs, head(vs));
    }
    close [q]array::<T>(p, n, vs);
}

fix insert_at<T>(j: i32, x: T, xs: list<T>) -> list<T> { append(take(j, xs), cons(x, drop(j, xs))) }

lem insert_at_length<T>(j: i32, x: T, xs: list<T>)
    req 0 <= j &*& j <= length(xs);
    ens length(insert_at(j, x, xs)) == length(xs) + 1;
{
}

lem is_perm_insert_at_cons<T>(j: i32, x: T, xs: list<T>)
    req 0 <= j &*& j <= length(xs);
    ens is_perm(insert_at(j, x, xs), cons(x, xs)) == true;
{
    match xs {
        nil => { is_perm_refl(cons(x, xs)); }
        cons(x0, xs0) => {
            if j == 0 {
                is_perm_refl(cons(x, xs));
            } else {
                is_perm_insert_at_cons(j - 1, x, xs0);
                // insert_at(j, x, xs) == cons(x0, insert_at(j - 1, x, xs0))
                is_perm_cons(x0, insert_at(j - 1, x, xs0), cons(x, xs0));
                is_perm_swap_head(x0, x, xs0);
                is_perm_trans(cons(x0, insert_at(j - 1, x, xs0)), cons(x0, cons(x, xs0)), cons(x, xs));
            }
        }
    }
}

lem is_perm_cons_snoc<T>(x: T, xs: list<T>)
    req true;
    ens is_perm(cons(x, xs), append(xs, [x])) == true;
{
    match xs {
        nil => { is_perm_refl([x]); }
        cons(x0, xs0) => {
            is_perm_cons_snoc(x, xs0);
            is_perm_swap_head(x, x0, xs0);
            is_perm_cons(x0, cons(x, xs0), append(xs0, [x]));
            is_perm_trans(cons(x, xs), cons(x0, cons(x, xs0)), append(xs, [x]));
        }
    }
}

lem contains_append_l<T>(x: T, xs: list<T>, ys: list<T>)
    req contains(xs, x) == true;
    ens contains(append(xs, ys), x) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if x0 != x { contains_append_l(x, xs0, ys); } }
    }
}

lem remove_append_l<T>(x: T, xs: list<T>, ys: list<T>)
    req contains(xs, x) == true;
    ens remove(x, append(xs, ys)) == append(remove(x, xs), ys);
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if x0 != x { remove_append_l(x, xs0, ys); } }
    }
}

lem is_perm_append_l<T>(xs: list<T>, xs1: list<T>, ys: list<T>)
    req is_perm(xs1, xs) == true;
    ens is_perm(append(xs1, ys), append(xs, ys)) == true;
{
    match xs1 {
        nil => { match xs { nil => {} cons(x0, xs0) => {} } is_perm_refl(ys); }
        cons(x0, xs10) => {
            // contains(xs, x0), is_perm(xs10, remove(x0, xs))
            is_perm_append_l(remove(x0, xs), xs10, ys);
            contains_append_l(x0, xs, ys);
            remove_append_l(x0, xs, ys);
        }
    }
}

lem sorted_insert_at<T>(order: fix(T, T, bool), j: i32, x: T, xs: list<T>)
    req sorted_by(order, xs) == true &*& 0 <= j &*& j <= length(xs) &*&
        (j == 0 || !apply_lt(order, x, nth(j - 1, xs))) &*& (j == length(xs) || !apply_lt(order, nth(j, xs), x));
    ens sorted_by(order, insert_at(j, x, xs)) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            if j == 0 {
            } else {
                sorted_insert_at(order, j - 1, x, xs0);
                if j == 1 {
                } else {
                    match xs0 { nil => {} cons(x1, xs1) => {} }
                }
            }
        }
    }
}

@*/

/*@

// ===== Proof library: merging (not trusted: every lemma below is proven) =====

// ----- order facts on sorted lists -----

lem le_lt_trans<T, F>(f0: F, a: T, b: T, c: T)
    req is_less_models::<T, F>(f0) == true &*&
        !apply_lt(is_less_model_of::<T, F>(f0), b, a) && apply_lt(is_less_model_of::<T, F>(f0), b, c);
    ens apply_lt(is_less_model_of::<T, F>(f0), a, c) == true;
{
    if !apply_lt(is_less_model_of::<T, F>(f0), a, c) {
        lt_neg_trans::<T, F>(f0, c, a, b);
    }
}

lem lt_le_trans<T, F>(f0: F, a: T, b: T, c: T)
    req is_less_models::<T, F>(f0) == true &*&
        apply_lt(is_less_model_of::<T, F>(f0), a, b) && !apply_lt(is_less_model_of::<T, F>(f0), c, b);
    ens apply_lt(is_less_model_of::<T, F>(f0), a, c) == true;
{
    if !apply_lt(is_less_model_of::<T, F>(f0), a, c) {
        lt_neg_trans::<T, F>(f0, b, c, a);
    }
}

lem sorted_tail<T>(order: fix(T, T, bool), x: T, xs: list<T>)
    req sorted_by(order, cons(x, xs)) == true;
    ens sorted_by(order, xs) == true;
{
}

lem sorted_adj<T>(order: fix(T, T, bool), xs: list<T>, k: i32)
    req sorted_by(order, xs) == true &*& 0 <= k &*& k + 1 < length(xs);
    ens !apply_lt(order, nth(k + 1, xs), nth(k, xs));
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            match xs0 { nil => {} cons(x1, xs1) => {} }
            if k != 0 { sorted_adj(order, xs0, k - 1); }
        }
    }
}

// In a sorted list, a later element is not less than an earlier one.
lem sorted_nth_le<T, F>(f0: F, xs: list<T>, a: i32, b: i32)
    req is_less_models::<T, F>(f0) == true &*& sorted_by(is_less_model_of::<T, F>(f0), xs) == true &*&
        0 <= a &*& a <= b &*& b < length(xs);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(b, xs), nth(a, xs));
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            if a == 0 {
                if b == 0 {
                    is_less_irreflexive::<T, F>(f0, x0);
                } else {
                    sorted_nth_le::<T, F>(f0, xs0, 0, b - 1);
                    match xs0 { nil => {} cons(x1, xs1) => {} }
                    lt_neg_trans::<T, F>(f0, x0, nth(0, xs0), nth(b - 1, xs0));
                }
            } else {
                sorted_nth_le::<T, F>(f0, xs0, a - 1, b - 1);
            }
        }
    }
}

// ----- cuts of a stable merge of `l` and `r` -----

// `(i, j)`: the first `i` elements of `l` and the first `j` of `r` are exactly the first `i + j` elements
// of the stable merge of `l` and `r` (ties: elements of `l` first).
fix valid_cut<T>(order: fix(T, T, bool), l: list<T>, r: list<T>, i: i32, j: i32) -> bool {
    0 <= i && i <= length(l) && 0 <= j && j <= length(r) &&
    (i == 0 || j == length(r) || !apply_lt(order, nth(j, r), nth(i - 1, l))) &&
    (j == 0 || i == length(l) || apply_lt(order, nth(j - 1, r), nth(i, l)))
}

// A forward step (`merge_up`) from a valid cut gives a valid cut.
lem cut_step_fwd<T, F>(f0: F, l: list<T>, r: list<T>, i: i32, j: i32)
    req is_less_models::<T, F>(f0) == true &*& sorted_by(is_less_model_of::<T, F>(f0), l) == true &*&
        sorted_by(is_less_model_of::<T, F>(f0), r) == true &*&
        valid_cut(is_less_model_of::<T, F>(f0), l, r, i, j) == true &*& i < length(l) &*& j < length(r);
    ens if !apply_lt(is_less_model_of::<T, F>(f0), nth(j, r), nth(i, l)) {
            valid_cut(is_less_model_of::<T, F>(f0), l, r, i + 1, j) == true
        } else {
            valid_cut(is_less_model_of::<T, F>(f0), l, r, i, j + 1) == true
        };
{
    let lt = is_less_model_of::<T, F>(f0);
    if !apply_lt(lt, nth(j, r), nth(i, l)) {
        if j != 0 && i + 1 != length(l) {
            sorted_adj(lt, l, i);
            lt_le_trans::<T, F>(f0, nth(j - 1, r), nth(i, l), nth(i + 1, l));
        }
    } else {
        if i != 0 && j + 1 != length(r) {
            sorted_adj(lt, r, j);
            lt_neg_trans::<T, F>(f0, nth(i - 1, l), nth(j, r), nth(j + 1, r));
        }
    }
}

// A backward step (`merge_down`) from a valid cut with both sides nonempty gives a valid cut.
lem cut_step_bwd<T, F>(f0: F, l: list<T>, r: list<T>, i: i32, j: i32)
    req is_less_models::<T, F>(f0) == true &*& sorted_by(is_less_model_of::<T, F>(f0), l) == true &*&
        sorted_by(is_less_model_of::<T, F>(f0), r) == true &*&
        valid_cut(is_less_model_of::<T, F>(f0), l, r, i, j) == true &*& 1 <= i &*& 1 <= j;
    ens if !apply_lt(is_less_model_of::<T, F>(f0), nth(j - 1, r), nth(i - 1, l)) {
            valid_cut(is_less_model_of::<T, F>(f0), l, r, i, j - 1) == true
        } else {
            valid_cut(is_less_model_of::<T, F>(f0), l, r, i - 1, j) == true
        };
{
    let lt = is_less_model_of::<T, F>(f0);
    if !apply_lt(lt, nth(j - 1, r), nth(i - 1, l)) {
        if j - 1 != 0 && i != length(l) {
            sorted_adj(lt, r, j - 2);
            le_lt_trans::<T, F>(f0, nth(j - 2, r), nth(j - 1, r), nth(i, l));
        }
    } else {
        if i - 1 != 0 && j != length(r) {
            sorted_adj(lt, l, i - 2);
            lt_neg_trans::<T, F>(f0, nth(i - 2, l), nth(i - 1, l), nth(j, r));
        }
    }
}

// Valid cuts are ordered by their sizes.
lem cut_mono<T, F>(f0: F, l: list<T>, r: list<T>, i: i32, j: i32, i2: i32, j2: i32)
    req is_less_models::<T, F>(f0) == true &*& sorted_by(is_less_model_of::<T, F>(f0), l) == true &*&
        sorted_by(is_less_model_of::<T, F>(f0), r) == true &*&
        valid_cut(is_less_model_of::<T, F>(f0), l, r, i, j) == true &*&
        valid_cut(is_less_model_of::<T, F>(f0), l, r, i2, j2) == true &*& i + j <= i2 + j2;
    ens i <= i2 &*& j <= j2;
{
    let lt = is_less_model_of::<T, F>(f0);
    if i > i2 {
        // j < j2: R[j2-1] < L[i2] <= L[i-1] <= R[j] <= R[j2-1]
        sorted_nth_le::<T, F>(f0, l, i2, i - 1);
        sorted_nth_le::<T, F>(f0, r, j, j2 - 1);
        lt_le_trans::<T, F>(f0, nth(j2 - 1, r), nth(i2, l), nth(i - 1, l));
        lt_le_trans::<T, F>(f0, nth(j2 - 1, r), nth(i - 1, l), nth(j, r));
        lt_le_trans::<T, F>(f0, nth(j2 - 1, r), nth(j, r), nth(j2 - 1, r));
        is_less_irreflexive::<T, F>(f0, nth(j2 - 1, r));
    } else if j > j2 {
        // i < i2: R[j-1] < L[i] <= L[i2-1] <= R[j2] <= R[j-1]
        sorted_nth_le::<T, F>(f0, l, i, i2 - 1);
        sorted_nth_le::<T, F>(f0, r, j2, j - 1);
        lt_le_trans::<T, F>(f0, nth(j - 1, r), nth(i, l), nth(i2 - 1, l));
        lt_le_trans::<T, F>(f0, nth(j - 1, r), nth(i2 - 1, l), nth(j2, r));
        lt_le_trans::<T, F>(f0, nth(j - 1, r), nth(j2, r), nth(j - 1, r));
        is_less_irreflexive::<T, F>(f0, nth(j - 1, r));
    }
}

// ----- runs written by the merge -----

fix last<T>(xs: list<T>) -> T {
    match xs { nil => default_value, cons(x, xs0) => if xs0 == nil { x } else { last(xs0) } }
}

lem last_snoc<T>(xs: list<T>, x: T)
    req true;
    ens last(append(xs, [x])) == x;
{
    match xs { nil => {} cons(x0, xs0) => { last_snoc(xs0, x); match xs0 { nil => {} cons(y, ys) => {} } } }
}

lem sorted_snoc<T>(order: fix(T, T, bool), xs: list<T>, x: T)
    req sorted_by(order, xs) == true &*& (xs == nil || !apply_lt(order, x, last(xs)));
    ens sorted_by(order, append(xs, [x])) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            sorted_snoc(order, xs0, x);
            match xs0 { nil => {} cons(x1, xs1) => {} }
        }
    }
}

lem sorted_append<T>(order: fix(T, T, bool), xs: list<T>, ys: list<T>)
    req sorted_by(order, xs) == true &*& sorted_by(order, ys) == true &*&
        (xs == nil || ys == nil || !apply_lt(order, head(ys), last(xs)));
    ens sorted_by(order, append(xs, ys)) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            sorted_append(order, xs0, ys);
            match xs0 { nil => { match ys { nil => {} cons(y0, ys0) => {} } } cons(x1, xs1) => {} }
        }
    }
}

// ----- permutation algebra -----

lem is_perm_cons_middle<T>(y: T, c: list<T>, d: list<T>)
    req true;
    ens is_perm(cons(y, append(c, d)), append(c, cons(y, d))) == true;
{
    match c {
        nil => { is_perm_refl(cons(y, d)); }
        cons(c0, c1) => {
            is_perm_cons_middle(y, c1, d);
            is_perm_swap_head(y, c0, append(c1, d));
            is_perm_cons(c0, cons(y, append(c1, d)), append(c1, cons(y, d)));
            is_perm_trans(cons(y, append(c, d)), cons(c0, cons(y, append(c1, d))), append(c, cons(y, d)));
        }
    }
}

lem is_perm_append_r<T>(xs: list<T>, ys: list<T>, ys1: list<T>)
    req is_perm(ys1, ys) == true;
    ens is_perm(append(xs, ys1), append(xs, ys)) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            is_perm_append_r(xs0, ys, ys1);
            is_perm_cons(x0, append(xs0, ys1), append(xs0, ys));
        }
    }
}

lem is_perm_append_both<T>(a1: list<T>, a: list<T>, b1: list<T>, b: list<T>)
    req is_perm(a1, a) == true &*& is_perm(b1, b) == true;
    ens is_perm(append(a1, b1), append(a, b)) == true;
{
    is_perm_append_l(a, a1, b1);
    is_perm_append_r(a, b, b1);
    is_perm_trans(append(a1, b1), append(a, b1), append(a, b));
}

lem is_perm_append_comm<T>(xs: list<T>, ys: list<T>)
    req true;
    ens is_perm(append(xs, ys), append(ys, xs)) == true;
{
    match xs {
        nil => { is_perm_refl(ys); }
        cons(x0, xs0) => {
            is_perm_append_comm(xs0, ys);
            is_perm_cons(x0, append(xs0, ys), append(ys, xs0));
            is_perm_cons_middle(x0, ys, xs0);
            is_perm_trans(append(xs, ys), cons(x0, append(ys, xs0)), append(ys, xs));
        }
    }
}

// (a ++ b) ++ (c ++ d)  ~  (a ++ c) ++ (b ++ d)
lem is_perm_middle_swap<T>(a: list<T>, b: list<T>, c: list<T>, d: list<T>)
    req true;
    ens is_perm(append(append(a, b), append(c, d)), append(append(a, c), append(b, d))) == true;
{
    append_assoc(a, b, append(c, d));
    append_assoc(b, c, d);
    is_perm_append_comm(b, c);
    is_perm_refl(d);
    is_perm_append_both(append(b, c), append(c, b), d, d);
    append_assoc(c, b, d);
    is_perm_append_r(a, append(c, append(b, d)), append(b, append(c, d)));
    append_assoc(a, c, append(b, d));
}

lem is_perm_snoc_middle<T>(f: list<T>, a: list<T>, b: list<T>, x: T)
    req is_perm(f, append(a, b)) == true;
    ens is_perm(append(f, [x]), append(append(a, [x]), b)) == true;
{
    is_perm_refl([x]);
    is_perm_append_both(f, append(a, b), [x], [x]);
    append_assoc(a, b, [x]);
    is_perm_append_comm(b, [x]);
    is_perm_append_r(a, cons(x, b), append(b, [x]));
    is_perm_trans(append(f, [x]), append(a, append(b, [x])), append(a, cons(x, b)));
    append_assoc(a, [x], b);
}

lem is_perm_snoc_right<T>(f: list<T>, a: list<T>, b: list<T>, y: T)
    req is_perm(f, append(a, b)) == true;
    ens is_perm(append(f, [y]), append(a, append(b, [y]))) == true;
{
    is_perm_refl([y]);
    is_perm_append_both(f, append(a, b), [y], [y]);
    append_assoc(a, b, [y]);
}

lem is_perm_cons_right<T>(bw: list<T>, c: list<T>, d: list<T>, y: T)
    req is_perm(bw, append(c, d)) == true;
    ens is_perm(cons(y, bw), append(c, cons(y, d))) == true;
{
    is_perm_cons(y, bw, append(c, d));
    is_perm_cons_middle(y, c, d);
    is_perm_trans(cons(y, bw), cons(y, append(c, d)), append(c, cons(y, d)));
}

lem take_plus_one<T>(n: i32, xs: list<T>)
    req 0 <= n &*& n < length(xs);
    ens take(n + 1, xs) == append(take(n, xs), [nth(n, xs)]);
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if n != 0 { take_plus_one(n - 1, xs0); } }
    }
}

lem all_eq_perm<T>(xs: list<T>, ys: list<T>, v: T)
    req all_eq(xs, v) == true &*& all_eq(ys, v) == true &*& length(xs) == length(ys);
    ens is_perm(xs, ys) == true;
{
    match xs {
        nil => { match ys { nil => {} cons(y0, ys0) => {} } }
        cons(x0, xs0) => {
            match ys { nil => {} cons(y0, ys0) => { all_eq_perm(xs0, ys0, v); } }
        }
    }
}

lem all_eq_append<T>(xs: list<T>, ys: list<T>, v: T)
    req all_eq(xs, v) == true &*& all_eq(ys, v) == true;
    ens all_eq(append(xs, ys), v) == true;
{
    match xs { nil => {} cons(x0, xs0) => { all_eq_append(xs0, ys, v); } }
}

// With a zero-sized `T`, the elements of `p[..n]` all equal the first element of `w[..m]`.
lem zst_arrays_all_eq<T>(p: *T, w: *T)
    req [?q]array::<T>(p, ?n, ?xs) &*& [?r]array::<T>(w, ?m, ?ys) &*& 0 < m &*& std::mem::size_of::<T>() == 0;
    ens [q]array::<T>(p, n, xs) &*& [r]array::<T>(w, m, ys) &*& all_eq(xs, head(ys)) == true;
{
    open array::<T>(w, m, ys);
    zst_array_all_eq(p, n, w);
    close [r]array::<T>(w, m, ys);
}

lem zst_array_all_eq_self<T>(p: *T)
    req [?q]array::<T>(p, ?n, ?xs) &*& 0 < n &*& std::mem::size_of::<T>() == 0;
    ens [q]array::<T>(p, n, xs) &*& all_eq(xs, head(xs)) == true;
{
    open array::<T>(p, n, xs);
    zst_array_all_eq(p + 1, n - 1, p);
    close [q]array::<T>(p, n, xs);
}

lem array_nonnull_aligned<T>(p: *T)
    req [?f]array::<T>(p, ?n, ?vs) &*& 0 < n;
    ens [f]array::<T>(p, n, vs) &*& p != 0 &*& p as usize % std::mem::align_of::<T>() == 0;
{
    open array::<T>(p, n, vs);
    points_to_limits(p);
    to_u8s_(p);
    from_u8s_(p);
    close [f]points_to::<T>(p, head(vs));
    close [f]array::<T>(p, n, vs);
}

lem sorted_take1<T>(order: fix(T, T, bool), xs: list<T>)
    req true;
    ens sorted_by(order, take(1, xs)) == true;
{
    match xs { nil => {} cons(x0, xs0) => {} }
}

// ----- the scratch regions of `small_sort_general_with_scratch` -----

// `p[..d]`: the first `n` elements are initialized with a permutation `ss` of `take(n, xs)` (sorted if
// `srt`), the rest is uninitialized.
pred sregion<T>(p: *T, d: i32, n: i32, xs: list<T>, srt: bool, order: fix(T, T, bool); ss: list<T>) =
    0 <= n &*& n <= d &*& array::<T>(p, n, ss) &*& array_::<T>(p + n, d - n, _) &*&
    is_perm(ss, take(n, xs)) == true &*& (!srt || sorted_by(order, ss));

lem foreach_MaybeUninit_own<T>(t: thread_id_t, xs: list<std::mem::MaybeUninit<T>>)
    req true;
    ens foreach(xs, own::<std::mem::MaybeUninit<T>>(t));
{
    match xs {
        nil => { close foreach(xs, own::<std::mem::MaybeUninit<T>>(t)); }
        cons(x0, xs0) => {
            foreach_MaybeUninit_own(t, xs0);
            MaybeUninit_own_trivial(t, x0);
            close foreach(xs, own::<std::mem::MaybeUninit<T>>(t));
        }
    }
}

lem array_MaybeUninit_to_array_<T>(p: *std::mem::MaybeUninit<T>)
    req array::<std::mem::MaybeUninit<T>>(p, ?n, ?ms);
    ens array_::<T>(p as *T, n, _);
{
    open array::<std::mem::MaybeUninit<T>>(p, n, ms);
    if n != 0 {
        std::mem::open_MaybeUninit(p);
        array_MaybeUninit_to_array_(p + 1);
        assert (p + 1) as *T == (p as *T) + 1;
        close array_::<T>(p as *T, n, _);
    } else {
        close array_::<T>(p as *T, 0, nil);
    }
}
@*/

// It's important to differentiate between SMALL_SORT_THRESHOLD performance for
// small slices and small-sort performance sorting small sub-slices as part of
// the main quicksort loop. For the former, testing showed that the
// representative benchmarks for real-world performance are cold CPU state and
// not single-size hot benchmarks. For the latter the CPU will call them many
// times, so hot benchmarks are fine and more realistic. And it's worth it to
// optimize sorting small sub-slices with more sophisticated solutions than
// insertion sort.

/// Using a trait allows us to specialize on `Freeze` which in turn allows us to make safe
/// abstractions.
pub(crate) trait StableSmallSortTypeImpl: Sized {
    /// For which input length <= return value of this function, is it valid to call `small_sort`.
    fn small_sort_threshold() -> usize;

    /// Sorts `v` using strategies optimized for small sizes.
    fn small_sort<F: FnMut(&Self, &Self) -> bool>(
        v: &mut [Self],
        scratch: &mut [MaybeUninit<Self>],
        is_less: &mut F,
    );
}

impl<T> StableSmallSortTypeImpl for T {
    #[inline(always)]
    default fn small_sort_threshold() -> usize {
        // Optimal number of comparisons, and good perf.
        SMALL_SORT_FALLBACK_THRESHOLD
    }

    #[inline(always)]
    default fn small_sort<F: FnMut(&T, &T) -> bool>(
        v: &mut [T],
        _scratch: &mut [MaybeUninit<T>],
        is_less: &mut F,
    )
    {
        if v.len() >= 2 {
            insertion_sort_shift_left(v, 1, is_less);
        }
    }
}

impl<T: FreezeMarker> StableSmallSortTypeImpl for T {
    #[inline(always)]
    fn small_sort_threshold() -> usize {
        SMALL_SORT_GENERAL_THRESHOLD
    }

    #[inline(always)]
    fn small_sort<F: FnMut(&T, &T) -> bool>(
        v: &mut [T],
        scratch: &mut [MaybeUninit<T>],
        is_less: &mut F,
    )
    {
        small_sort_general_with_scratch(v, scratch, is_less);
    }
}

/// Using a trait allows us to specialize on `Freeze` which in turn allows us to make safe
/// abstractions.
pub(crate) trait UnstableSmallSortTypeImpl: Sized {
    /// For which input length <= return value of this function, is it valid to call `small_sort`.
    fn small_sort_threshold() -> usize;

    /// Sorts `v` using strategies optimized for small sizes.
    fn small_sort<F: FnMut(&Self, &Self) -> bool>(v: &mut [Self], is_less: &mut F);
}

impl<T> UnstableSmallSortTypeImpl for T {
    #[inline(always)]
    default fn small_sort_threshold() -> usize {
        SMALL_SORT_FALLBACK_THRESHOLD
    }

    #[inline(always)]
    default fn small_sort<F>(v: &mut [T], is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        small_sort_fallback(v, is_less);
    }
}

impl<T: FreezeMarker> UnstableSmallSortTypeImpl for T {
    #[inline(always)]
    fn small_sort_threshold() -> usize {
        <T as UnstableSmallSortFreezeTypeImpl>::small_sort_threshold()
    }

    #[inline(always)]
    fn small_sort<F>(v: &mut [T], is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        <T as UnstableSmallSortFreezeTypeImpl>::small_sort(v, is_less);
    }
}

/// FIXME(const_trait_impl) use original ipnsort approach with choose_unstable_small_sort,
/// as found here <https://github.com/Voultapher/sort-research-rs/blob/438fad5d0495f65d4b72aa87f0b62fc96611dff3/ipnsort/src/smallsort.rs#L83C10-L83C36>.
pub(crate) trait UnstableSmallSortFreezeTypeImpl: Sized + FreezeMarker {
    fn small_sort_threshold() -> usize;

    fn small_sort<F: FnMut(&Self, &Self) -> bool>(v: &mut [Self], is_less: &mut F);
}

impl<T: FreezeMarker> UnstableSmallSortFreezeTypeImpl for T {
    #[inline(always)]
    default fn small_sort_threshold() -> usize {
        if (size_of::<T>() * SMALL_SORT_GENERAL_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE {
            SMALL_SORT_GENERAL_THRESHOLD
        } else {
            SMALL_SORT_FALLBACK_THRESHOLD
        }
    }

    #[inline(always)]
    default fn small_sort<F>(v: &mut [T], is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        if (size_of::<T>() * SMALL_SORT_GENERAL_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE {
            small_sort_general(v, is_less);
        } else {
            small_sort_fallback(v, is_less);
        }
    }
}

/// SAFETY: Only used for run-time optimization heuristic.
#[unsafe(rustc_allow_lifetime_dependent_specialization)]
trait CopyMarker {}

impl<T: Copy> CopyMarker for T {}

impl<T: FreezeMarker + CopyMarker> UnstableSmallSortFreezeTypeImpl for T {
    #[inline(always)]
    fn small_sort_threshold() -> usize {
        if has_efficient_in_place_swap::<T>()
            && (size_of::<T>() * SMALL_SORT_NETWORK_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE
        {
            SMALL_SORT_NETWORK_THRESHOLD
        } else if (size_of::<T>() * SMALL_SORT_GENERAL_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE {
            SMALL_SORT_GENERAL_THRESHOLD
        } else {
            SMALL_SORT_FALLBACK_THRESHOLD
        }
    }

    #[inline(always)]
    fn small_sort<F>(v: &mut [T], is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        if has_efficient_in_place_swap::<T>()
            && (size_of::<T>() * SMALL_SORT_NETWORK_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE
        {
            small_sort_network(v, is_less);
        } else if (size_of::<T>() * SMALL_SORT_GENERAL_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE {
            small_sort_general(v, is_less);
        } else {
            small_sort_fallback(v, is_less);
        }
    }
}

/// Optimal number of comparisons, and good perf.
const SMALL_SORT_FALLBACK_THRESHOLD: usize = 16;

/// From a comparison perspective 20 was ~2% more efficient for fully random input, but for
/// wall-clock performance choosing 32 yielded better performance overall.
///
/// SAFETY: If you change this value, you have to adjust [`small_sort_general`] !
const SMALL_SORT_GENERAL_THRESHOLD: usize = 32;

/// [`small_sort_general`] uses [`sort8_stable`] as primitive and does a kind of ping-pong merge,
/// where the output of the first two [`sort8_stable`] calls is stored at the end of the scratch
/// buffer. This simplifies panic handling and avoids additional copies. This affects the required
/// scratch buffer size.
///
/// SAFETY: If you change this value, you have to adjust [`small_sort_general`] !
pub(crate) const SMALL_SORT_GENERAL_SCRATCH_LEN: usize = SMALL_SORT_GENERAL_THRESHOLD + 16;

/// SAFETY: If you change this value, you have to adjust [`small_sort_network`] !
const SMALL_SORT_NETWORK_THRESHOLD: usize = 32;
const SMALL_SORT_NETWORK_SCRATCH_LEN: usize = SMALL_SORT_NETWORK_THRESHOLD;

/// Using a stack array, could cause a stack overflow if the type `T` is very large. To be
/// conservative we limit the usage of small-sorts that require a stack array to types that fit
/// within this limit.
const MAX_STACK_ARRAY_SIZE: usize = 4096;

fn small_sort_fallback<T, F: FnMut(&T, &T) -> bool>(v: &mut [T], is_less: &mut F) {
    if v.len() >= 2 {
        insertion_sort_shift_left(v, 1, is_less);
    }
}

fn small_sort_general<T: FreezeMarker, F: FnMut(&T, &T) -> bool>(v: &mut [T], is_less: &mut F) {
    let mut stack_array = MaybeUninit::<[T; SMALL_SORT_GENERAL_SCRATCH_LEN]>::uninit();

    // SAFETY: The memory is backed by `stack_array`, and the operation is safe as long as the len
    // is the same.
    let scratch = unsafe {
        slice::from_raw_parts_mut(
            maybe_uninit_as_mut_ptr__VeriFast_wrapper(&mut stack_array) as *mut MaybeUninit<T>,
            SMALL_SORT_GENERAL_SCRATCH_LEN,
        )
    };

    small_sort_general_with_scratch(v, scratch, is_less);
}

fn small_sort_general_with_scratch<T: FreezeMarker, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    scratch: &mut [MaybeUninit<T>],
    is_less: &mut F,
) {
    let len = v.len();
    if len < 2 {
        return;
    }

    if scratch.len() < len + 16 {
        intrinsics::abort_immediate();
    }

    let v_base = slice_as_mut_ptr__VeriFast_wrapper(v);
    let len_div_2 = len / 2;

    // SAFETY: See individual comments.
    unsafe {
        let scratch_base = slice_as_mut_ptr__VeriFast_wrapper(scratch) as *mut T;

        let presorted_len = if const { size_of::<T>() <= 16 } && len >= 16 {
            // SAFETY: scratch_base is valid and has enough space.
            sort8_stable(v_base, scratch_base, scratch_base.add(len), is_less);
            sort8_stable(
                v_base.add(len_div_2),
                scratch_base.add(len_div_2),
                scratch_base.add(len + 8),
                is_less,
            );

            8
        } else if len >= 8 {
            // SAFETY: scratch_base is valid and has enough space.
            sort4_stable(v_base, scratch_base, is_less);
            sort4_stable(v_base.add(len_div_2), scratch_base.add(len_div_2), is_less);

            4
        } else {
            ptr::copy_nonoverlapping(v_base, scratch_base, 1);
            ptr::copy_nonoverlapping(v_base.add(len_div_2), scratch_base.add(len_div_2), 1);

            1
        };

        {
        let mut offsets = array_0_and_into_iter__VeriFast_wrapper(len_div_2);
        loop {
            let offset = match array_usize_2_into_iter_next__VeriFast_wrapper(&mut offsets) {
                None => break,
                Some(offset) => offset,
            };
            // SAFETY: at this point dst is initialized with presorted_len elements.
            // We extend this to desired_len, src is valid for desired_len elements.
            let src = v_base.add(offset);
            let dst = scratch_base.add(offset);
            let desired_len = if offset == 0 { len_div_2 } else { len - len_div_2 };

            for i in presorted_len..desired_len {
                ptr::copy_nonoverlapping(src.add(i), dst.add(i), 1);
                insert_tail(dst, dst.add(i), is_less);
            }
        }
        }

        // SAFETY: see comment in `CopyOnDrop::drop`.
        let drop_guard = CopyOnDrop { src: scratch_base, dst: v_base, len };

        // SAFETY: at this point scratch_base is fully initialized, allowing us
        // to use it as the source of our merge back into the original array.
        // If a panic occurs we ensure the original array is restored to a valid
        // permutation of the input through drop_guard. This technique is similar
        // to ping-pong merging.
        bidirectional_merge(
            slice::from_raw_parts(drop_guard.src, drop_guard.len),
            drop_guard.dst,
            is_less,
        );
        mem::forget(drop_guard);
    }
}

struct CopyOnDrop<T> {
    src: *const T,
    dst: *mut T,
    len: usize,
}

/*@
// `CopyOnDrop<T>` holds raw pointers only; it owns nothing. (Its `drop` runs only while unwinding: on the
// normal paths the module forgets every guard, after rewrite 001 also in `insert_tail`.)
pred<T> <CopyOnDrop<T>>.own(t, v) = true;
@*/

impl<T> Drop for CopyOnDrop<T> {
    fn drop(&mut self) {
        // SAFETY: `src` must contain `len` initialized elements, and dst must
        // be valid to write `len` elements.
        unsafe {
            ptr::copy_nonoverlapping(self.src, self.dst, self.len);
        }
    }
}

fn small_sort_network<T, F>(v: &mut [T], is_less: &mut F)
where
    T: FreezeMarker,
    F: FnMut(&T, &T) -> bool,
{
    // This implementation is tuned to be efficient for integer types.

    let len = v.len();
    if len < 2 {
        return;
    }

    if len > SMALL_SORT_NETWORK_SCRATCH_LEN {
        intrinsics::abort_immediate();
    }

    let mut stack_array = MaybeUninit::<[T; SMALL_SORT_NETWORK_SCRATCH_LEN]>::uninit();

    let len_div_2 = len / 2;
    let no_merge = len < 18;

    let v_base = slice_as_mut_ptr__VeriFast_wrapper(v);
    let initial_region_len = if no_merge { len } else { len_div_2 };
    // SAFETY: Both possible values of `initial_region_len` are in-bounds.
    let mut region = unsafe { slice::from_raw_parts_mut(v_base, initial_region_len) };

    // Avoid compiler unrolling, we *really* don't want that to happen here for binary-size reasons.
    loop {
        let presorted_len = if region.len() >= 13 {
            sort13_optimal(region, is_less);
            13
        } else if region.len() >= 9 {
            sort9_optimal(region, is_less);
            9
        } else {
            1
        };

        insertion_sort_shift_left(region, presorted_len, is_less);

        if no_merge {
            return;
        }

        if region.as_ptr() != v_base {
            break;
        }

        // SAFETY: The right side of `v` based on `len_div_2` is guaranteed in-bounds.
        unsafe { region = slice::from_raw_parts_mut(v_base.add(len_div_2), len - len_div_2) };
    }

    // SAFETY: We checked that T is Freeze and thus observation safe.
    // Should is_less panic v was not modified in parity_merge and retains it's original input.
    // scratch and v must not alias and scratch has v.len() space.
    unsafe {
        let scratch_base = maybe_uninit_as_mut_ptr__VeriFast_wrapper(&mut stack_array) as *mut T;
        bidirectional_merge(slice::from_raw_parts_mut(v_base, len), scratch_base, is_less);
        ptr::copy_nonoverlapping(scratch_base, v_base, len);
    }
}

/// Swap two values in the slice pointed to by `v_base` at the position `a_pos` and `b_pos` if the
/// value at position `b_pos` is less than the one at position `a_pos`.
///
/// Purposefully not marked `#[inline]`, despite us wanting it to be inlined for integers like
/// types. `is_less` could be a huge function and we want to give the compiler an option to
/// not inline this function. For the same reasons that this function is very perf critical
/// it should be in the same module as the functions that use it.
unsafe fn swap_if_less<T, F>(v_base: *mut T, a_pos: usize, b_pos: usize, is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    // SAFETY: the caller must guarantee that `a_pos` and `b_pos` each added to `v_base` yield valid
    // pointers into `v_base`, and are properly aligned, and part of the same allocation.
    unsafe {
        let v_a = v_base.add(a_pos);
        let v_b = v_base.add(b_pos);

        // PANIC SAFETY: if is_less panics, no scratch memory was created and the slice should still be
        // in a well defined state, without duplicates.

        // Important to only swap if it is more and not if it is equal. is_less should return false for
        // equal, so we don't swap.
        let should_swap = is_less__VeriFast_wrapper(is_less, &*v_b, &*v_a);

        // This is a branchless version of swap if.
        // The equivalent code with a branch would be:
        //
        // if should_swap {
        //     ptr::swap(v_a, v_b, 1);
        // }

        // The goal is to generate cmov instructions here.
        let v_a_swap = hint::select_unpredictable(should_swap, v_b, v_a);
        let v_b_swap = hint::select_unpredictable(should_swap, v_a, v_b);

        let v_b_swap_tmp = ManuallyDrop::new(ptr::read(v_b_swap));
        ptr_copy_1__VeriFast_wrapper(v_a_swap, v_a);
        ptr::copy_nonoverlapping(&*v_b_swap_tmp, v_b, 1);
    }
}

/// Sorts the first 9 elements of `v` with a fast fixed function.
///
/// Should `is_less` generate substantial amounts of code the compiler can choose to not inline
/// `swap_if_less`. If the code of a sort impl changes so as to call this function in multiple
/// places, `#[inline(never)]` is recommended to keep binary-size in check. The current design of
/// `small_sort_network` makes sure to only call this once.
fn sort9_optimal<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    if v.len() < 9 {
        intrinsics::abort_immediate();
    }

    let v_base = slice_as_mut_ptr__VeriFast_wrapper(v);

    // Optimal sorting network see:
    // https://bertdobbelaere.github.io/sorting_networks.html.

    // SAFETY: We checked the len.
    unsafe {
        swap_if_less(v_base, 0, 3, is_less);
        swap_if_less(v_base, 1, 7, is_less);
        swap_if_less(v_base, 2, 5, is_less);
        swap_if_less(v_base, 4, 8, is_less);
        swap_if_less(v_base, 0, 7, is_less);
        swap_if_less(v_base, 2, 4, is_less);
        swap_if_less(v_base, 3, 8, is_less);
        swap_if_less(v_base, 5, 6, is_less);
        swap_if_less(v_base, 0, 2, is_less);
        swap_if_less(v_base, 1, 3, is_less);
        swap_if_less(v_base, 4, 5, is_less);
        swap_if_less(v_base, 7, 8, is_less);
        swap_if_less(v_base, 1, 4, is_less);
        swap_if_less(v_base, 3, 6, is_less);
        swap_if_less(v_base, 5, 7, is_less);
        swap_if_less(v_base, 0, 1, is_less);
        swap_if_less(v_base, 2, 4, is_less);
        swap_if_less(v_base, 3, 5, is_less);
        swap_if_less(v_base, 6, 8, is_less);
        swap_if_less(v_base, 2, 3, is_less);
        swap_if_less(v_base, 4, 5, is_less);
        swap_if_less(v_base, 6, 7, is_less);
        swap_if_less(v_base, 1, 2, is_less);
        swap_if_less(v_base, 3, 4, is_less);
        swap_if_less(v_base, 5, 6, is_less);
    }
}

/// Sorts the first 13 elements of `v` with a fast fixed function.
///
/// Should `is_less` generate substantial amounts of code the compiler can choose to not inline
/// `swap_if_less`. If the code of a sort impl changes so as to call this function in multiple
/// places, `#[inline(never)]` is recommended to keep binary-size in check. The current design of
/// `small_sort_network` makes sure to only call this once.
fn sort13_optimal<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    if v.len() < 13 {
        intrinsics::abort_immediate();
    }

    let v_base = slice_as_mut_ptr__VeriFast_wrapper(v);

    // Optimal sorting network see:
    // https://bertdobbelaere.github.io/sorting_networks.html.

    // SAFETY: We checked the len.
    unsafe {
        swap_if_less(v_base, 0, 12, is_less);
        swap_if_less(v_base, 1, 10, is_less);
        swap_if_less(v_base, 2, 9, is_less);
        swap_if_less(v_base, 3, 7, is_less);
        swap_if_less(v_base, 5, 11, is_less);
        swap_if_less(v_base, 6, 8, is_less);
        swap_if_less(v_base, 1, 6, is_less);
        swap_if_less(v_base, 2, 3, is_less);
        swap_if_less(v_base, 4, 11, is_less);
        swap_if_less(v_base, 7, 9, is_less);
        swap_if_less(v_base, 8, 10, is_less);
        swap_if_less(v_base, 0, 4, is_less);
        swap_if_less(v_base, 1, 2, is_less);
        swap_if_less(v_base, 3, 6, is_less);
        swap_if_less(v_base, 7, 8, is_less);
        swap_if_less(v_base, 9, 10, is_less);
        swap_if_less(v_base, 11, 12, is_less);
        swap_if_less(v_base, 4, 6, is_less);
        swap_if_less(v_base, 5, 9, is_less);
        swap_if_less(v_base, 8, 11, is_less);
        swap_if_less(v_base, 10, 12, is_less);
        swap_if_less(v_base, 0, 5, is_less);
        swap_if_less(v_base, 3, 8, is_less);
        swap_if_less(v_base, 4, 7, is_less);
        swap_if_less(v_base, 6, 11, is_less);
        swap_if_less(v_base, 9, 10, is_less);
        swap_if_less(v_base, 0, 1, is_less);
        swap_if_less(v_base, 2, 5, is_less);
        swap_if_less(v_base, 6, 9, is_less);
        swap_if_less(v_base, 7, 8, is_less);
        swap_if_less(v_base, 10, 11, is_less);
        swap_if_less(v_base, 1, 3, is_less);
        swap_if_less(v_base, 2, 4, is_less);
        swap_if_less(v_base, 5, 6, is_less);
        swap_if_less(v_base, 9, 10, is_less);
        swap_if_less(v_base, 1, 2, is_less);
        swap_if_less(v_base, 3, 4, is_less);
        swap_if_less(v_base, 5, 7, is_less);
        swap_if_less(v_base, 6, 8, is_less);
        swap_if_less(v_base, 2, 3, is_less);
        swap_if_less(v_base, 4, 5, is_less);
        swap_if_less(v_base, 6, 7, is_less);
        swap_if_less(v_base, 8, 9, is_less);
        swap_if_less(v_base, 3, 4, is_less);
        swap_if_less(v_base, 5, 6, is_less);
    }
}

/// Sorts range [begin, tail] assuming [begin, tail) is already sorted.
///
/// # Safety
/// begin < tail and p must be valid and initialized for all begin <= p <= tail.
unsafe fn insert_tail<T, F: FnMut(&T, &T) -> bool>(begin: *mut T, tail: *mut T, is_less: &mut F) {
    // SAFETY: see individual comments.
    unsafe {
        // SAFETY: in-bounds as tail > begin.
        let mut sift = tail.sub(1);
        if !is_less__VeriFast_wrapper(is_less, &*tail, &*sift) {
            return;
        }

        // SAFETY: after this read tail is never read from again, as we only ever
        // read from sift, sift < tail and we only ever decrease sift. Thus this is
        // effectively a move, not a copy. Should a panic occur, or we have found
        // the correct insertion position, gap_guard ensures the element is moved
        // back into the array.
        let tmp = ManuallyDrop::new(tail.read());
        let mut gap_guard = CopyOnDrop { src: &*tmp, dst: tail, len: 1 };

        loop {
            // SAFETY: we move sift into the gap (which is valid), and point the
            // gap guard destination at sift, ensuring that if a panic occurs the
            // gap is once again filled.
            ptr::copy_nonoverlapping(sift, gap_guard.dst, 1);
            gap_guard.dst = sift;

            if sift == begin {
                break;
            }

            // SAFETY: we checked that sift != begin, thus this is in-bounds.
            sift = sift.sub(1);
            if !is_less__VeriFast_wrapper(is_less, &tmp, &*sift) {
                break;
            }
        }
        // VeriFast rewrite (rewrites/001): the drop of `gap_guard` at the end of this block, written out:
        // `CopyOnDrop::drop`'s body followed by `mem::forget`. Runtime-equivalent; see rewrites/LOG.md.
        ptr::copy_nonoverlapping(gap_guard.src, gap_guard.dst, gap_guard.len);
        mem::forget(gap_guard);
    }
}

/// Sort `v` assuming `v[..offset]` is already sorted.
pub fn insertion_sort_shift_left<T, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    offset: usize,
    is_less: &mut F,
)
{
    let len = v.len();
    if offset == 0 || offset > len {
        intrinsics::abort_immediate();
    }

    // SAFETY: see individual comments.
    unsafe {
        // We write this basic loop directly using pointers, as when we use a
        // for loop LLVM likes to unroll this loop which we do not want.
        // SAFETY: v_end is the one-past-end pointer, and we checked that
        // offset <= len, thus tail is also in-bounds.
        let v_base = slice_as_mut_ptr__VeriFast_wrapper(v);
        let v_end = v_base.add(len);
        let mut tail = v_base.add(offset);
        while tail != v_end {
            // SAFETY: v_base and tail are both valid pointers to elements, and
            // v_base < tail since we checked offset != 0.
            insert_tail(v_base, tail, is_less);

            // SAFETY: we checked that tail is not yet the one-past-end pointer.
            tail = tail.add(1);
        }
    }
}

/// SAFETY: The caller MUST guarantee that `v_base` is valid for 4 reads and
/// `dst` is valid for 4 writes. The result will be stored in `dst[0..4]`.
pub unsafe fn sort4_stable<T, F: FnMut(&T, &T) -> bool>(
    v_base: *const T,
    dst: *mut T,
    is_less: &mut F,
)
/*@
req thread_token(?t) &*& t == currentThread &*&
    array::<T>(v_base, 4, ?vs) &*& foreach(vs, own::<T>(t)) &*&
    array_::<T>(dst, 4, _) &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0);
@*/
/*@
ens thread_token(t) &*&
    array::<T>(v_base, 4, ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
    array::<T>(dst, 4, ?ds) &*& is_perm(ds, vs1) == true &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1) &*&
    if is_less_models::<T, F>(f0) {
        vs1 == vs && sorted_by(is_less_model_of::<T, F>(f0), ds)
    } else {
        true
    };
@*/
/*@
on_unwind_ens thread_token(t) &*&
    array::<T>(v_base, 4, ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
    array_::<T>(dst, 4, _) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1);
@*/
{
    // By limiting select to picking pointers, we are guaranteed good cmov code-gen
    // regardless of type T's size. Further this only does 5 instead of 6
    // comparisons compared to a stable transposition 4 element sorting-network,
    // and always copies each element exactly once.

    // SAFETY: all pointers have offset at most 3 from v_base and dst, and are
    // thus in-bounds by the precondition.
    unsafe {
        //@ array4_open(v_base);
        //@ array__4_open(dst);
        //@ let v0 = nth(0, vs);
        //@ let v1 = nth(1, vs);
        //@ let v2 = nth(2, vs);
        //@ let v3 = nth(3, vs);
        //@ points_to_limits(v_base + 1);
        //@ points_to_limits(v_base + 2);
        //@ points_to_limits(v_base + 3);
        //@ points_to__limits(dst + 1);
        //@ points_to__limits(dst + 2);
        //@ points_to__limits(dst + 3);
        //@ let m = is_less_models::<T, F>(f0);
        //@ let lt = is_less_model_of::<T, F>(f0);
        // Stably create two pairs a <= b and c <= d.
        //@ pt_hide_half(v_base + 1);
        //@ pt_hide_half(v_base);
        let c1 = is_less__VeriFast_wrapper(is_less, &*v_base.add(1), &*v_base);
        //@ pt_unhide(v_base + 1);
        //@ pt_unhide(v_base);
        //@ if c1 {} else {}
        //@ pt_hide_half(v_base + 3);
        //@ pt_hide_half(v_base + 2);
        let c2 = is_less__VeriFast_wrapper(is_less, &*v_base.add(3), &*v_base.add(2));
        //@ pt_unhide(v_base + 3);
        //@ pt_unhide(v_base + 2);
        //@ if c2 {} else {}
        let a = v_base.add(c1 as usize);
        let b = v_base.add(!c1 as usize);
        let c = v_base.add(2 + c2 as usize);
        let d = v_base.add(2 + (!c2 as usize));
        //@ let va = *a;
        //@ let vb = *b;
        //@ let vc = *c;
        //@ let vd = *d;

        // Compare (a, c) and (b, d) to identify max/min. We're left with two
        // unknown elements, but because we are a stable sort we must know which
        // one is leftmost and which one is rightmost.
        // c3, c4 | min max unknown_left unknown_right
        //  0,  0 |  a   d    b         c
        //  0,  1 |  a   b    c         d
        //  1,  0 |  c   d    a         b
        //  1,  1 |  c   b    a         d
        //@ pt_hide_half(c);
        //@ pt_hide_half(a);
        let c3 = is_less__VeriFast_wrapper(is_less, &*c, &*a);
        //@ pt_unhide(c);
        //@ pt_unhide(a);
        //@ pt_hide_half(d);
        //@ pt_hide_half(b);
        let c4 = is_less__VeriFast_wrapper(is_less, &*d, &*b);
        //@ pt_unhide(d);
        //@ pt_unhide(b);
        //@ if c3 {} else {}
        //@ if c4 {} else {}
        //@ close raw_ptr_own::<T>()(t, c);
        //@ close raw_ptr_own::<T>()(t, a);
        let min = hint::select_unpredictable(c3, c, a);
        //@ open raw_ptr_own::<T>()(t, min);
        //@ close raw_ptr_own::<T>()(t, b);
        //@ close raw_ptr_own::<T>()(t, d);
        let max = hint::select_unpredictable(c4, b, d);
        //@ open raw_ptr_own::<T>()(t, max);
        //@ close raw_ptr_own::<T>()(t, a);
        //@ close raw_ptr_own::<T>()(t, c);
        //@ close raw_ptr_own::<T>()(t, b);
        let unknown_left = hint::select_unpredictable(c3, a, hint::select_unpredictable(c4, c, b));
        //@ open raw_ptr_own::<T>()(t, unknown_left);
        //@ close raw_ptr_own::<T>()(t, d);
        //@ close raw_ptr_own::<T>()(t, b);
        //@ close raw_ptr_own::<T>()(t, c);
        let unknown_right = hint::select_unpredictable(c4, d, hint::select_unpredictable(c3, b, c));
        //@ open raw_ptr_own::<T>()(t, unknown_right);
        //@ let vul = *unknown_left;
        //@ let vur = *unknown_right;

        // Sort the last two unknown elements.
        //@ pt_hide_half(unknown_right);
        //@ pt_hide_half(unknown_left);
        let c5 = is_less__VeriFast_wrapper(is_less, &*unknown_right, &*unknown_left);
        //@ pt_unhide(unknown_right);
        //@ pt_unhide(unknown_left);
        //@ if c5 {} else {}
        //@ close raw_ptr_own::<T>()(t, unknown_right);
        //@ close raw_ptr_own::<T>()(t, unknown_left);
        let lo = hint::select_unpredictable(c5, unknown_right, unknown_left);
        //@ open raw_ptr_own::<T>()(t, lo);
        //@ close raw_ptr_own::<T>()(t, unknown_left);
        //@ close raw_ptr_own::<T>()(t, unknown_right);
        let hi = hint::select_unpredictable(c5, unknown_left, unknown_right);
        //@ open raw_ptr_own::<T>()(t, hi);
        //@ let vmin = *min;
        //@ let vlo = *lo;
        //@ let vhi = *hi;
        //@ let vmax = *max;

        //@ array1_close(min);
        //@ array_1_close(dst);
        ptr::copy_nonoverlapping(min, dst, 1);
        //@ array1_open(min);
        //@ array1_open(dst);
        //@ array1_close(lo);
        //@ array_1_close(dst + 1);
        ptr::copy_nonoverlapping(lo, dst.add(1), 1);
        //@ array1_open(lo);
        //@ array1_open(dst + 1);
        //@ array1_close(hi);
        //@ array_1_close(dst + 2);
        ptr::copy_nonoverlapping(hi, dst.add(2), 1);
        //@ array1_open(hi);
        //@ array1_open(dst + 2);
        //@ array1_close(max);
        //@ array_1_close(dst + 3);
        ptr::copy_nonoverlapping(max, dst.add(3), 1);
        //@ array1_open(max);
        //@ array1_open(dst + 3);
        //@ array4_close(v_base);
        //@ open array_::<T>(dst + 4, 0, _);
        //@ close array::<T>(dst + 4, 0, nil);
        //@ array4_close(dst);
        /*@
        {
            let L0 = [v0, v1, v2, v3];
            is_perm_refl(L0);
            if c1 { perm_step(0, 1, L0, L0); }
            let L0b = if c1 { [v1, v0, v2, v3] } else { L0 };
            if c2 { perm_step(2, 3, L0b, L0); }
            let L1 = [va, vb, vc, vd];
            assert is_perm(L1, L0) == true;
            if !c3 && c4 {
                perm_step(1, 2, L1, L0);
                perm_step(2, 3, [va, vc, vb, vd], L0);
            } else if c3 && !c4 {
                perm_step(0, 2, L1, L0);
                perm_step(1, 2, [vc, vb, va, vd], L0);
            } else if c3 && c4 {
                perm_step(0, 2, L1, L0);
                perm_step(1, 2, [vc, vb, va, vd], L0);
                perm_step(2, 3, [vc, va, vb, vd], L0);
            }
            let L2 = [vmin, vul, vur, vmax];
            assert is_perm(L2, L0) == true;
            if c5 { perm_step(1, 2, L2, L0); }
            assert is_perm([vmin, vlo, vhi, vmax], L0) == true;
            if m {
                // !lt(b, a) and !lt(d, c)
                if c1 { lt_asym::<T, F>(f0, v1, v0); }
                if c2 { lt_asym::<T, F>(f0, v3, v2); }
                if c5 { lt_asym::<T, F>(f0, vur, vul); }
                if !c3 && !c4 {
                } else if !c3 && c4 {
                    lt_neg_trans::<T, F>(f0, va, vc, vd);
                    if !apply_lt(lt, vc, vb) { lt_neg_trans::<T, F>(f0, vb, vc, vd); }
                    lt_asym::<T, F>(f0, vc, vb);
                    lt_asym::<T, F>(f0, vd, vb);
                } else if c3 && !c4 {
                    lt_asym::<T, F>(f0, vc, va);
                    lt_neg_trans::<T, F>(f0, vc, va, vb);
                    lt_neg_trans::<T, F>(f0, va, vb, vd);
                } else {
                    lt_asym::<T, F>(f0, vc, va);
                    lt_asym::<T, F>(f0, vd, vb);
                }
            }
        }
        @*/
    }
}

/// SAFETY: The caller MUST guarantee that `v_base` is valid for 8 reads and
/// writes, `scratch_base` and `dst` MUST be valid for 8 writes. The result will
/// be stored in `dst[0..8]`.
unsafe fn sort8_stable<T: FreezeMarker, F: FnMut(&T, &T) -> bool>(
    v_base: *mut T,
    dst: *mut T,
    scratch_base: *mut T,
    is_less: &mut F,
) {
    // SAFETY: these pointers are all in-bounds by the precondition of our function.
    unsafe {
        sort4_stable(v_base, scratch_base, is_less);
        sort4_stable(v_base.add(4), scratch_base.add(4), is_less);
    }

    // SAFETY: scratch_base[0..8] is now initialized, allowing us to merge back
    // into dst.
    unsafe {
        bidirectional_merge(slice::from_raw_parts(scratch_base, 8), dst, is_less);
    }
}

#[inline(always)]
unsafe fn merge_up<T, F: FnMut(&T, &T) -> bool>(
    mut left_src: *const T,
    mut right_src: *const T,
    mut dst: *mut T,
    is_less: &mut F,
) -> (*const T, *const T, *mut T) {
    // This is a branchless merge utility function.
    // The equivalent code with a branch would be:
    //
    // if !is_less(&*right_src, &*left_src) {
    //     ptr::copy_nonoverlapping(left_src, dst, 1);
    //     left_src = left_src.add(1);
    // } else {
    //     ptr::copy_nonoverlapping(right_src, dst, 1);
    //     right_src = right_src.add(1);
    // }
    // dst = dst.add(1);

    // SAFETY: The caller must guarantee that `left_src`, `right_src` are valid
    // to read and `dst` is valid to write, while not aliasing.
    unsafe {
        let is_l = !is_less__VeriFast_wrapper(is_less, &*right_src, &*left_src);
        let src = if is_l { left_src } else { right_src };
        ptr::copy_nonoverlapping(src, dst, 1);
        right_src = right_src.add(!is_l as usize);
        left_src = left_src.add(is_l as usize);
        dst = dst.add(1);
    }

    (left_src, right_src, dst)
}

#[inline(always)]
unsafe fn merge_down<T, F: FnMut(&T, &T) -> bool>(
    mut left_src: *const T,
    mut right_src: *const T,
    mut dst: *mut T,
    is_less: &mut F,
) -> (*const T, *const T, *mut T) {
    // This is a branchless merge utility function.
    // The equivalent code with a branch would be:
    //
    // if !is_less(&*right_src, &*left_src) {
    //     ptr::copy_nonoverlapping(right_src, dst, 1);
    //     right_src = right_src.wrapping_sub(1);
    // } else {
    //     ptr::copy_nonoverlapping(left_src, dst, 1);
    //     left_src = left_src.wrapping_sub(1);
    // }
    // dst = dst.sub(1);

    // SAFETY: The caller must guarantee that `left_src`, `right_src` are valid
    // to read and `dst` is valid to write, while not aliasing.
    unsafe {
        let is_l = !is_less__VeriFast_wrapper(is_less, &*right_src, &*left_src);
        let src = if is_l { right_src } else { left_src };
        ptr::copy_nonoverlapping(src, dst, 1);
        right_src = const_ptr_wrapping_sub__VeriFast_wrapper(right_src, is_l as usize);
        left_src = const_ptr_wrapping_sub__VeriFast_wrapper(left_src, !is_l as usize);
        dst = dst.sub(1);
    }

    (left_src, right_src, dst)
}

/// Merge v assuming v[..len / 2] and v[len / 2..] are sorted.
///
/// Original idea for bi-directional merging by Igor van den Hoven (quadsort),
/// adapted to only use merge up and down. In contrast to the original
/// parity_merge function, it performs 2 writes instead of 4 per iteration.
///
/// # Safety
/// The caller must guarantee that `dst` is valid for v.len() writes.
/// Also `v.as_ptr()` and `dst` must not alias and v.len() must be >= 2.
///
/// Note that T must be Freeze, the comparison function is evaluated on outdated
/// temporary 'copies' that may not end up in the final array.
unsafe fn bidirectional_merge<T: FreezeMarker, F: FnMut(&T, &T) -> bool>(
    v: &[T],
    dst: *mut T,
    is_less: &mut F,
) {
    // It helps to visualize the merge:
    //
    // Initial:
    //
    //  |dst (in dst)
    //  |left               |right
    //  v                   v
    // [xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx]
    //                     ^                   ^
    //                     |left_rev           |right_rev
    //                                         |dst_rev (in dst)
    //
    // After:
    //
    //                      |dst (in dst)
    //        |left         |           |right
    //        v             v           v
    // [xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx]
    //       ^             ^           ^
    //       |left_rev     |           |right_rev
    //                     |dst_rev (in dst)
    //
    // In each iteration one of left or right moves up one position, and one of
    // left_rev or right_rev moves down one position, whereas dst always moves
    // up one position and dst_rev always moves down one position. Assuming
    // the input was sorted and the comparison function is correctly implemented
    // at the end we will have left == left_rev + 1, and right == right_rev + 1,
    // fully consuming the input having written it to dst.

    let len = v.len();
    let src = v.as_ptr();

    let len_div_2 = len / 2;

    // SAFETY: The caller has to ensure that len >= 2.
    unsafe {
        intrinsics::assume(len_div_2 != 0); // This can avoid useless code-gen.
    }

    // SAFETY: no matter what the result of the user-provided comparison function
    // is, all 4 read pointers will always be in-bounds. Writing `dst` and `dst_rev`
    // will always be in bounds if the caller guarantees that `dst` is valid for
    // `v.len()` writes.
    unsafe {
        let mut left = src;
        let mut right = src.add(len_div_2);
        let mut dst = dst;

        let mut left_rev = src.add(len_div_2 - 1);
        let mut right_rev = src.add(len - 1);
        let mut dst_rev = dst.add(len - 1);

        for _ in 0..len_div_2 {
            (left, right, dst) = merge_up(left, right, dst, is_less);
            (left_rev, right_rev, dst_rev) = merge_down(left_rev, right_rev, dst_rev, is_less);
        }

        let left_end = const_ptr_wrapping_add_1__VeriFast_wrapper(left_rev);
        let right_end = const_ptr_wrapping_add_1__VeriFast_wrapper(right_rev);

        // Odd length, so one element is left unconsumed in the input.
        if !len.is_multiple_of(2) {
            let left_nonempty = left < left_end;
            let last_src = if left_nonempty { left } else { right };
            ptr::copy_nonoverlapping(last_src, dst, 1);
            left = left.add(left_nonempty as usize);
            right = right.add((!left_nonempty) as usize);
        }

        // We now should have consumed the full input exactly once. This can only fail if the
        // user-provided comparison function fails to implement a strict weak ordering. In that case
        // we panic and never access the inconsistent state in dst.
        if left != left_end || right != right_end {
            panic_on_ord_violation();
        }
    }
}

#[cfg_attr(not(panic = "immediate-abort"), inline(never), cold)]
#[cfg_attr(panic = "immediate-abort", inline)]
fn panic_on_ord_violation() -> ! {
    // This is indicative of a logic bug in the user-provided comparison function or Ord
    // implementation. They are expected to implement a total order as explained in the Ord
    // documentation.
    //
    // By panicking we inform the user, that they have a logic bug in their program. If a strict
    // weak ordering is not given, the concept of comparison based sorting cannot yield a sorted
    // result. E.g.: a < b < c < a
    //
    // The Ord documentation requires users to implement a total order. Arguably that's
    // unnecessarily strict in the context of sorting. Issues only arise if the weaker requirement
    // of a strict weak ordering is violated.
    //
    // The panic message talks about a total order because that's what the Ord documentation talks
    // about and requires, so as to not confuse users.
    panic!("user-provided comparison function does not correctly implement a total order");
}

#[must_use]
pub(crate) const fn has_efficient_in_place_swap<T>() -> bool
{
    // Heuristic that holds true on all tested 64-bit capable architectures.
    size_of::<T>() <= 8 // size_of::<u64>()
}

// ===== BEGIN TRUSTED STD WRAPPERS =====
//
// Trusted part of the specifications, following the verify-rust-std LinkedList proof. VeriFast 26.10
// cannot attach a spec to these std calls (see README.md), so each call site in this file calls a
// wrapper instead. Each wrapper's body is exactly the original call, and refinement-checker checks
// that the code with wrappers refines the original code. Each spec is assumed (`assume_correct`),
// not proven, and follows the function's documentation in core.
// Every target crate contains this block verbatim (checked by verify.sh).

/*@

// The elements an array iterator has yet to yield.
fix array_IntoIter_remaining<T, N>(it: core::array::IntoIter<T, N>) -> list<T>;

// An address computed with wrapping `usize` arithmetic, for offsets of magnitude at most `usize::MAX + 1`.
fix wrap_usize(a: i32) -> i32 {
    if a < 0 { a + usize::MAX + 1 } else if a > usize::MAX { a - usize::MAX - 1 } else { a }
}

// `p.wrapping_offset(n)`: the same provenance and metadata, address `p + n * size_of::<T>()` modulo
// `usize::MAX + 1`.
fix ptr_wrapping_offset<T>(p: *T, n: i32) -> *T {
    pointer_ctor((p as pointer).provenance, wrap_usize((p as pointer).address + n * std::mem::size_of::<T>()), (p as pointer).metadata) as *T
}

@*/

// `v.as_mut_ptr()`: the slice's data pointer, as for `<[T]>::as_ptr`.
fn slice_as_mut_ptr__VeriFast_wrapper<T>(v: &mut [T]) -> *mut T
//@ req true;
//@ ens result == v as *T;
//@ on_unwind_ens false;
//@ assume_correct
{
    v.as_mut_ptr()
}

// `m.as_mut_ptr()`: a pointer to the contained value; `MaybeUninit<U>` is `repr(transparent)`.
fn maybe_uninit_as_mut_ptr__VeriFast_wrapper<U>(m: &mut MaybeUninit<U>) -> *mut U
//@ req true;
//@ ens result == m as *U;
//@ on_unwind_ens false;
//@ assume_correct
{
    m.as_mut_ptr()
}

// `p.wrapping_sub(count)`: `count` elements down with wrapping address arithmetic, the same provenance,
// no in-bounds requirement (core: "the resulting pointer ... has the same provenance"). Specified for
// `count * size_of::<T>() <= isize::MAX` (one wrap-around at most).
fn const_ptr_wrapping_sub__VeriFast_wrapper<T>(p: *const T, count: usize) -> *const T
//@ req true;
//@ ens if count * std::mem::size_of::<T>() <= isize::MAX { result == ptr_wrapping_offset(p, -count) } else { true };
//@ on_unwind_ens false;
//@ assume_correct
{
    p.wrapping_sub(count)
}

// `p.wrapping_add(1)`: one element up with wrapping address arithmetic, the same provenance
// (refinement-checker does not accept constants as arguments of wrapper calls, so the constant is
// inside the wrapper). Specified for `size_of::<T>() <= isize::MAX` (true of every Rust type).
fn const_ptr_wrapping_add_1__VeriFast_wrapper<T>(p: *const T) -> *const T
//@ req true;
//@ ens if std::mem::size_of::<T>() <= isize::MAX { result == ptr_wrapping_offset(p, 1) } else { true };
//@ on_unwind_ens false;
//@ assume_correct
{
    p.wrapping_add(1)
}

// `IntoIterator::into_iter([0, b])`, the head of `for offset in [0, len_div_2]`. This and the next
// wrapper are `unsafe` only so that VeriFast does not also require the specs VeriFast generates for
// safe functions (it cannot express ownership of their array and `Option` values); the call site is
// inside an `unsafe` block, and refinement-checker checks it against the original `for` loop.
unsafe fn array_0_and_into_iter__VeriFast_wrapper(b: usize) -> core::array::IntoIter<usize, 2>
//@ req thread_token(?t);
//@ ens thread_token(t) &*& <core::array::IntoIter<usize, 2>>.own(t, result) &*& array_IntoIter_remaining(result) == [0, b];
//@ on_unwind_ens false;
//@ assume_correct
{
    IntoIterator::into_iter([0, b])
}

// `iter.next()` for the iterator above: yields the remaining elements in order.
unsafe fn array_usize_2_into_iter_next__VeriFast_wrapper(iter: &mut core::array::IntoIter<usize, 2>) -> Option<usize>
//@ req thread_token(?t) &*& *iter |-> ?it0 &*& <core::array::IntoIter<usize, 2>>.own(t, it0);
/*@
ens thread_token(t) &*& *iter |-> ?it1 &*& <core::array::IntoIter<usize, 2>>.own(t, it1) &*&
    match array_IntoIter_remaining(it0) {
        nil => result == std::option::Option::None && array_IntoIter_remaining(it1) == nil,
        cons(x, xs) => result == std::option::Option::Some(x) && array_IntoIter_remaining(it1) == xs
    };
@*/
//@ on_unwind_ens false;
//@ assume_correct
{
    Iterator::next(iter)
}

// `ptr::copy(src, dst, 1)`: memmove of one element (refinement-checker does not accept constants as
// arguments of wrapper calls, so the count is inside the wrapper). VeriFast 26.10's prelude spec of
// `std::ptr::copy` does not bound `offset` in its `some(offset)` branch: at a call whose regions are
// disjoint and farther apart than `count` elements, choosing that branch yields a chunk whose byte list
// is shorter than the chunk, from which `false` follows. This spec is that prelude spec at `count = 1`
// with `-1 <= offset <= 1` added to the `some(offset)` branch; regions farther apart use `none`.
unsafe fn ptr_copy_1__VeriFast_wrapper<T>(src: *const T, dst: *mut T)
/*@
req exists::<option<isize>>(?offset_opt) &*&
    match offset_opt {
        none => // No overlap
            [?f](src as *u8)[..1 * std::mem::size_of::<T>()] |-?-> ?bs &*& (dst as *u8)[..1 * std::mem::size_of::<T>()] |-> _ &*&
            ens [f](src as *u8)[..1 * std::mem::size_of::<T>()] |-?-> bs &*& (dst as *u8)[..1 * std::mem::size_of::<T>()] |-?-> bs,
        some(offset) =>
            dst == src + offset &*& -1 <= offset &*& offset <= 1 &*&
            if offset == 0 {
                (dst as *u8)[..1 * std::mem::size_of::<T>()] |-?-> ?bs &*&
                ens (dst as *u8)[..1 * std::mem::size_of::<T>()] |-?-> bs
            } else if offset > 0 {
                (src as *u8)[..1 * std::mem::size_of::<T>()] |-?-> ?bs &*& ((src + 1) as *u8)[..offset * std::mem::size_of::<T>()] |-> _ &*&
                ens (src as *u8)[..offset * std::mem::size_of::<T>()] |-?-> take(offset * std::mem::size_of::<T>(), bs) &*&
                    (dst as *u8)[..1 * std::mem::size_of::<T>()] |-?-> bs
            } else {
                (src as *u8)[..1 * std::mem::size_of::<T>()] |-?-> ?bs &*& (dst as *u8)[..-offset * std::mem::size_of::<T>()] |-> _ &*&
                ens ((dst + 1) as *u8)[..-offset * std::mem::size_of::<T>()] |-?-> drop((1 + offset) * std::mem::size_of::<T>(), bs) &*&
                    (dst as *u8)[..1 * std::mem::size_of::<T>()] |-?-> bs
            }
    };
@*/
//@ ens true;
//@ on_unwind_ens false;
//@ terminates;
//@ assume_correct
{
    ptr::copy(src, dst, 1)
}

// `a + 16` on `usize` (refinement-checker does not accept constants as arguments of wrapper calls, so
// the constant is inside the wrapper). Rust's checked semantics (a build with overflow checks): the
// result is `a + 16`, and the addition panics if that exceeds `usize::MAX`. (In a build without overflow
// checks it wraps instead; it can overflow only for zero-sized `T`, see README.md.)
fn usize_add_16__VeriFast_wrapper(a: usize) -> usize
//@ req true;
//@ ens a + 16 <= usize::MAX &*& result == a + 16;
//@ on_unwind_ens true;
//@ assume_correct
{
    a + 16
}

// `MaybeUninit::<U>::uninit()`: an uninitialized `MaybeUninit<U>` (VeriFast 26.10 has no spec for it).
// `unsafe` only so that VeriFast does not also require the spec it generates for safe functions; the call
// sites are rewritten (see rewrites/LOG.md) and refinement-checker checks them.
unsafe fn maybe_uninit_uninit__VeriFast_wrapper<U>() -> MaybeUninit<U>
//@ req true;
//@ ens result == std::mem::MaybeUninit::uninit::<U>();
//@ on_unwind_ens false;
//@ assume_correct
{
    MaybeUninit::uninit()
}

// ===== END TRUSTED STD WRAPPERS =====
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
